//! Native datatype solving for free variables by eager tag/field expansion
//! (ADR-0022 step B).
//!
//! After read-over-construct simplification ([`simplify_datatypes`]), a query
//! may still mention **free datatype variables** under `is-c`/`select`. This
//! module decides such queries by eagerly expanding each datatype variable
//! `o : D` into
//!
//! - a **tag** bit-vector `tag_o` (which constructor `o` uses), constrained to
//!   the constructor range, and
//! - a **field variable** `f_{o,c,i}` for every constructor `c` and field `i`
//!   (`Bool`/`BitVec`/`Int`/`Real`-sorted, matching the field's sort),
//!
//! then replacing `is-c(o)` with `tag_o == c` and `select_{c,i}(o)` with
//! `f_{o,c,i}`. Structural equality `o == o'` of two datatype variables reduces
//! to `tag_o == tag_o'` conjoined, per constructor `j`, with
//! `tag_o == j -> (j's fields agree)`.
//!
//! **A non-active field variable is FREE** (ADR-1930). It used to be pinned to
//! its sort's `well_founded_default` by a guard `tag_o == c OR f_{o,c,i} ==
//! default`, so that `select_{c,i}(o)` off `o`'s own constructor agreed with the
//! evaluator's total convention. SMT-LIB leaves that case UNSPECIFIED, so the
//! guard was not a convention but a MODEL RESTRICTION, and it manufactured wrong
//! `unsat`s: `((_ is none) o) AND (v o)` over `Opt = none | some(v: Bool)`
//! answered `unsat` here on 2026-09-12 while cvc5 1.3.4 and z3 both answer
//! `sat`. The value the search picks for a free non-active field is instead
//! recorded as the model's chosen selector interpretation and checked by the
//! replay. The residual is datatype-free and goes back through the
//! normal dispatcher ([`solve`] → `check_auto`), which routes its now-mixed
//! Bool/BitVec + Int/Real content to the bit-blaster and the arithmetic DPLL
//! respectively — so `Int`/`Real` field variables decided in congruence with the
//! rest of the query, not just bit-blasted.
//!
//! Soundness. The expansion is equisatisfiable with the input: from a model of
//! the input, set `tag_o` to `o`'s constructor and the field variables to `o`'s
//! fields (non-active fields to their default, satisfying the guards); from a
//! model of the expansion, project `o = c_{tag_o}(f_{o,c,i}...)` and the guards
//! make every `select` agree with the evaluator. So `unsat` transfers, and a
//! `sat` model is projected back to a `Value::Datatype` and **replayed against
//! the original assertions** with the ground evaluator before it is returned —
//! a projection bug surfaces as a replay error, never a wrong `sat`.
//!
//! `select_{c,i}(construct_d(...))` with `d != c` — the same unspecified case,
//! written out — is abstracted to a fresh free variable
//! ([`abstract_wrong_ctor_selects`]) instead of being refused. The chosen values
//! from both sources are folded into ONE interpretation keyed by
//! `(constructor, index, the operand's VALUE)`
//! ([`register_select_witnesses`]), which is what makes it congruent; a
//! candidate that wants two different results at one key describes no
//! interpretation and yields `unknown`.
//!
//! Recursive datatypes are handled two ways:
//!
//! - **Untraversed** datatype fields (never `select`ed into, never compared) get
//!   no expansion variable and are projected to their [`well_founded_default`];
//!   this stays equisatisfiable (sound `sat` *and* `unsat`).
//! - **Traversed** datatype fields (`select` into a datatype field) are unfolded:
//!   each such `select` becomes a fresh *free* child datatype variable
//!   ([`unfold_traversals`]), recursively, to exactly the depth the query
//!   accesses. This is a **relaxation** (the child is unconstrained), so it only
//!   enlarges the model space: reduced-`unsat` ⇒ original-`unsat` is sound with
//!   no guards, and a `sat` candidate is projected through the links and
//!   **replayed** — a replay failure (e.g. the parent's constructor was left
//!   free and the child does not match the wrong-constructor default) yields
//!   `unknown`, never a wrong answer. So traversal is *sound* always and
//!   *complete* when the accessed parents' constructors are determined.
//!
//! On `IntList = nil | cons(head, tail)`: `is-cons(l)`, `select head(l) == 5`,
//! `is-cons(l) ∧ is-nil(tail(l))`, `is-cons(l) ∧ is-cons(tail(l))` (tail forced
//! to a deeper cons), and the sound `unsat` of `is-cons(l) ∧ is-nil(l)` or of
//! `is-cons(tail(l)) ∧ is-nil(tail(l))` all decide.
//!
//! `==` over a datatype that *has* datatype fields is also handled: `build_dt_eq`
//! compares tag + scalar fields and skips datatype fields, which is a weaker
//! (relaxation) constraint — sound for `unsat`, and a `sat` candidate is
//! replay-checked (equal projections, e.g. both datatype fields defaulted, pass;
//! a real difference is `unknown`).
//!
//! Still outside the fragment: array/UF datatype fields, and `is`/`select`/`==`
//! over a datatype term that is neither a variable nor an abstracted
//! wrong-constructor read — these return [`SolverError::Unsupported`].
//! A fuller native theory (acyclicity + congruence, and exact field guards to
//! make the relaxed `unknown` cases complete) is future work.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{
    ConstructorId, DatatypeId, IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value,
    eval, well_founded_default,
};
use axeyum_rewrite::{replace_subterms, simplify_datatypes};

use crate::auto::solve;
use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::model::Model;

/// Decides a query with free datatype variables by eager tag/field expansion.
///
/// `assertions` are simplified (read-over-construct folded) first; the residual
/// free-variable fragment is expanded to a datatype-free query, solved by the
/// dispatcher, and on `sat` projected back to datatype values and replayed.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for datatype content outside the
/// non-recursive scalar-field free-variable fragment, or a [`SolverError`] from
/// the rewrite, the dispatcher, or a failed `sat` replay.
pub fn check_with_datatype_native(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let simplified =
        simplify_datatypes(arena, assertions).map_err(|e| SolverError::Backend(e.to_string()))?;

    // TWO ENCODINGS OF STRUCTURAL EQUALITY, AND WHICH VERDICT EACH MAY GIVE.
    //
    // The tag/field expansion can only compare fields that HAVE an expansion
    // variable, and a datatype-typed field has none. That leaves two honest
    // encodings of `o == o'`, and they are sound for opposite verdicts:
    //
    // - [`EqMode::Restriction`] — `tag_l == tag_r AND (comparable fields agree)`
    //   as a plain term. It is STRONGER than real equality under a negation
    //   (`o != o'` is made to demand a difference in the part we can see), so it
    //   can WITNESS a difference — which is what a `sat` model needs, and the
    //   replay against the original assertions confirms it. Its `unsat` means
    //   nothing: it has removed real models. This is what shipped, with its
    //   `unsat` believed, and `is-cons(a) AND is-cons(b) AND a != b` over a list
    //   whose every field is a datatype answered `unsat` where cvc5 and z3
    //   answer `sat` (ADR-1930).
    // - [`EqMode::Relaxation`] — a free Boolean carrying only the conditions the
    //   expansion can decide (see `build_dt_eq`). Every real model extends to it
    //   in BOTH polarities, so its `unsat` transfers. Its `sat` is replay-checked
    //   like any other, but it cannot witness a difference it cannot see, so on
    //   this fragment it mostly yields `unknown`.
    //
    // So: run the restriction for a `sat`, the relaxation for an `unsat`, and
    // never believe the other's verdict. When no equality is inexact the two
    // encodings coincide and one pass does.
    if has_inexact_equality(arena, &simplified) {
        if let Ok(CheckResult::Sat(model)) =
            decide_with_eq_mode(arena, &simplified, config, EqMode::Restriction)
        {
            return Ok(CheckResult::Sat(model));
        }
        return decide_with_eq_mode(arena, &simplified, config, EqMode::Relaxation);
    }
    decide_with_eq_mode(arena, &simplified, config, EqMode::Relaxation)
}

/// Which side of real equality the `==` encoding is allowed to fall on. See the
/// two-encoding note in [`check_with_datatype_native`].
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum EqMode {
    /// Weaker-or-exact: `unsat` transfers, `sat` is replay-checked.
    Relaxation,
    /// Stronger-or-exact: ONLY a replay-checked `sat` may be believed.
    Restriction,
}

/// Whether any structural equality in `assertions` is over a datatype with a
/// datatype-typed field — the case the expansion cannot compare exactly, and
/// therefore the only case where the two encodings differ.
fn has_inexact_equality(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        if *op == Op::Eq
            && let Sort::Datatype(dt) = arena.sort_of(args[0])
            && dt_has_datatype_field(arena, dt)
        {
            return true;
        }
        stack.extend(args.iter().copied());
    }
    false
}

/// The expansion proper, under one choice of equality encoding.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for datatype content outside the
/// fragment, or a [`SolverError`] from the rewrite, the dispatcher, or a failed
/// `sat` replay.
fn decide_with_eq_mode(
    arena: &mut TermArena,
    simplified: &[TermId],
    config: &SolverConfig,
    eq_mode: EqMode,
) -> Result<CheckResult, SolverError> {
    // Abstract every `select_{c,i}(construct_d(...))` with `d != c` — the
    // UNSPECIFIED case (ADR-1930) — into a fresh free variable. Read-over-
    // construct already folded the `d == c` case exactly, so this is precisely
    // the residue, and it is the single most common blocker in the QF_DT
    // corpus. Replacing it by an unconstrained variable is a *relaxation*, so
    // `unsat` transfers; a `sat` candidate's chosen values are recorded as a
    // selector interpretation and replayed (`register_select_witnesses`).
    let (abstracted, witnesses) = abstract_wrong_ctor_selects(arena, simplified)
        .map_err(|e| SolverError::Backend(e.to_string()))?;

    // Ackermann-expand every uninterpreted function applied to a datatype
    // argument (ADR-1935): each application becomes a fresh witness symbol and
    // each pair of applications of one function gains
    // `(arguments equal) -> (witnesses equal)`. The antecedent's datatype
    // conjuncts are plain `Op::Eq` terms, so the tag/field expansion below
    // encodes them through `build_dt_eq` like any other structural equality --
    // which is exactly why the precondition is that the encoding be EXACT.
    let (abstracted, ack_sites) = ackermannize_datatype_applications(arena, &abstracted)?;

    // Expand a structural equality over a datatype that HAS datatype fields into
    // the per-constructor field comparison, ONE level deep. Exact (it is the
    // definition of structural equality), and it is what lets the expansion
    // exhibit a DIFFERENCE: the nested `sel_{j,i}(x) = sel_{j,i}(y)` become
    // child-variable equalities under `unfold_traversals`, and a child's tag is
    // free, so `a != b` has a witness. Without it the tag/field encoding can
    // only decide equality at the top constructor and every `a != b` over a
    // recursive datatype degrades to `unknown`.
    //
    // RELAXATION MODE ONLY. The restriction already forces a witness at the top
    // constructor -- that is what makes it the `sat` arm -- and expanding under
    // it only enlarges the query for no gain; measured, it cost two files that
    // `main` decided.
    let expanded = if eq_mode == EqMode::Relaxation {
        expand_datatype_equalities(arena, &abstracted)
            .map_err(|e| SolverError::Backend(e.to_string()))?
    } else {
        abstracted.clone()
    };

    // Unfold `select` into datatype fields: each traversed datatype-field-select
    // becomes a fresh, free child datatype variable (a *relaxation* — children
    // are unconstrained), recorded in `links` so projection can reconstruct the
    // nested value. Because it only enlarges the model space, reduced-`unsat`
    // still implies original-`unsat` (sound, no guards); `sat` is replay-guarded.
    let (unfolded, links) =
        unfold_traversals(arena, &expanded).map_err(|e| SolverError::Backend(e.to_string()))?;

    // Immutable scan: validate the fragment and collect the datatype variables
    // used, the `is`/`select` sites to rewrite, and per-datatype layout.
    let scan = scan_fragment(arena, &unfolded)?;
    // The query is a relaxation (so a `sat` candidate must be replay-checked and
    // a mismatch is `unknown`) if it traverses datatype fields or compares
    // datatypes that have datatype fields.
    let mut relaxed = !links.is_empty() || scan.relaxed_eq || !witnesses.is_empty();
    // AN ACKERMANN-EXPANDED QUERY IS A RELAXED ONE, and this is a measured
    // correction rather than caution. `register_ack_interpretations` rebuilds
    // `f` from its witness values, and a site whose ARGUMENTS do not all
    // evaluate under the projected assignment -- an argument the inner model
    // never constrained -- contributes no entry, so the reconstruction is
    // partial by construction and the replay can reject a candidate that is not
    // actually wrong. Without this flag that rejection is a
    // `SolverError::Backend`, which ENDS the dispatch: measured 2026-09-12 on
    // UFDT/20170428-Barrett/.../x2015_09_10_17_05_36_652_2082452, a file `main`
    // answers `unsat` became `backend failure: datatype sat model replay failed
    // at assertion #6488` and the ladder never reached the route that decides
    // it. As a decline the replay still throws the candidate away -- it is doing
    // its job, which is why the `sat` is not returned -- and the next rung runs.
    relaxed |= !ack_sites.is_empty();
    if scan.dt_symbols.is_empty() {
        // No datatype variables remain (read-over-construct sufficed) — hand the
        // residual back to the dispatcher.
        //
        // TERMINATION GUARD (ADR-1920). `check_auto_dispatch` diverts on the
        // *sort* `Sort::Datatype(_)`, not on a datatype operator, and every
        // branch of that diversion returns. So if the residual still carries a
        // datatype-sorted term, `solve` routes it right back into this function
        // with the same input, forever — and the dispatcher recomputes its
        // deadline on each entry, so `config.timeout` cannot break the cycle
        // either. Measured on `(declare-fun p (D) Bool) (assert (p o))`: stack
        // overflow, SIGABRT, which a harness reads as a crash rather than the
        // first-class `unknown` it is entitled to. Refusing here is the fence
        // that makes the ADR-1920 gate lift safe for shapes the arm above does
        // not name individually.
        refuse_if_datatype_survives(arena, &unfolded)?;
        let result = solve(arena, &unfolded, config)?;
        let CheckResult::Sat(model) = result else {
            return Ok(result);
        };
        if ack_sites.is_empty() {
            return Ok(CheckResult::Sat(model));
        }
        // An Ackermann-expanded query can empty `dt_symbols` -- `(assert (p o))`
        // reduces to the witness variable alone -- and returning the inner model
        // straight out would be WRONG TWICE: it leaks the `!dt_ack_*` internal
        // symbols, and it omits `p`'s interpretation, so the model cannot be
        // checked by evaluating the original term. Both are what
        // `project_and_replay` exists to fix, and with an empty scan its
        // datatype loops are no-ops, so it is the same code rather than a second
        // copy of it.
        let empty_layout: BTreeMap<SymbolId, SymVars> = BTreeMap::new();
        return project_and_replay(
            arena,
            simplified,
            &scan,
            &empty_layout,
            &links,
            &witnesses,
            &ack_sites,
            relaxed,
            &model,
        );
    }

    // Mutable phase: declare tag/field symbols, build the replacement map and the
    // domain/guard constraints, then rewrite the assertions.
    let mut layout: BTreeMap<SymbolId, SymVars> = BTreeMap::new();
    let mut extra: Vec<TermId> = Vec::new();
    for (&sym, &dt) in &scan.dt_symbols {
        let vars = build_sym_vars(arena, sym, dt, &scan.layouts[&dt], &mut extra)?;
        layout.insert(sym, vars);
    }

    let mut replacements: HashMap<TermId, TermId> = HashMap::new();
    for site in &scan.tests {
        let vars = &layout[&site.symbol];
        let tag_const = arena
            .bv_const(vars.tag_width, site.ctor_index as u128)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let tag_var = arena.var(vars.tag);
        let eq = arena
            .eq(tag_var, tag_const)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        replacements.insert(site.term, eq);
    }
    for site in &scan.selects {
        let vars = &layout[&site.symbol];
        // The scan rejects selects of datatype-typed fields, so this is `Some`.
        let Some(field) = vars.fields[site.ctor_index][site.field_index] else {
            return Err(SolverError::Backend(
                "scalar-field select site mapped to a datatype field".to_owned(),
            ));
        };
        replacements.insert(site.term, arena.var(field));
    }
    let mut relaxed_eq_encoding = false;
    for site in &scan.eqs {
        let (eq_term, one_directional) = build_dt_eq(
            arena,
            &layout[&site.left],
            &layout[&site.right],
            &mut extra,
            eq_mode,
        )?;
        relaxed_eq_encoding |= one_directional;
        replacements.insert(site.term, eq_term);
    }

    relaxed |= relaxed_eq_encoding;

    let mut reduced = Vec::with_capacity(unfolded.len() + extra.len());
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    for &assertion in &unfolded {
        let rewritten = replace_subterms(arena, assertion, &replacements, &mut memo)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        reduced.push(rewritten);
    }
    reduced.extend(extra);

    // The SAME termination guard as the `dt_symbols.is_empty()` branch above,
    // and it is NOT redundant: `replacements` only covers the `is`/`select`/`==`
    // sites the scan collected, so a datatype-sorted symbol reached only through
    // some other op (an array `store`, say) is never rewritten and survives into
    // `reduced` even when `dt_symbols` is NON-empty. Measured 2026-09-12 on
    // AUFDTLIRA/20200306-Kanig/spark2014bench/P518-021__frame_for_max__…: a
    // 22 KB file that still overflowed the stack with a 1 GiB stack, i.e. an
    // unbounded cycle, not a deep term.
    refuse_if_datatype_survives(arena, &reduced)?;
    let result = solve(arena, &reduced, config)?;
    let CheckResult::Sat(model) = result else {
        // `unsat`/`unknown` transfer: the reduction (exact scalar fields,
        // relaxed datatype fields) only enlarges the model space, so `unsat` is
        // sound.
        return Ok(result);
    };

    // Replay against the *original* simplified assertions (which still reference
    // the select-chains), so a sound `sat` satisfies the real query.
    project_and_replay(
        arena, simplified, &scan, &layout, &links, &witnesses, &ack_sites, relaxed, &model,
    )
}

/// Per-symbol expansion variables.
struct SymVars {
    tag: SymbolId,
    tag_width: u32,
    /// `fields[constructor_index][field_index]` — the fresh field variable, or
    /// `None` for a datatype-typed field (not expanded in this slice; never
    /// traversed, so it is projected to a well-founded default).
    fields: Vec<Vec<Option<SymbolId>>>,
}

/// An `is-c(o)` rewrite site.
struct TestSite {
    term: TermId,
    symbol: SymbolId,
    ctor_index: usize,
}

/// A `select_{c,i}(o)` rewrite site.
struct SelectSite {
    term: TermId,
    symbol: SymbolId,
    ctor_index: usize,
    field_index: usize,
}

/// An `o == o'` rewrite site over two datatype variables.
struct EqSite {
    term: TermId,
    left: SymbolId,
    right: SymbolId,
}

/// Result of the immutable fragment scan.
struct Scan {
    dt_symbols: BTreeMap<SymbolId, DatatypeId>,
    /// Per datatype: its constructors with their field sorts (owned, so the
    /// mutable build phase need not re-borrow the arena).
    layouts: BTreeMap<DatatypeId, Vec<(ConstructorId, Vec<Sort>)>>,
    tests: Vec<TestSite>,
    selects: Vec<SelectSite>,
    eqs: Vec<EqSite>,
    /// True if some `==` is over a datatype with datatype-typed fields, whose
    /// reduction (`build_dt_eq`) compares only tag + scalar fields — a weaker
    /// (relaxation) constraint, so the candidate must be replay-checked and a
    /// mismatch is `unknown`, not a wrong answer.
    relaxed_eq: bool,
}

/// Links a parent slot's datatype field `(parent symbol, constructor index,
/// field index)` to the fresh child datatype variable that represents it.
type Links = BTreeMap<(SymbolId, usize, usize), SymbolId>;

/// Rewrites every `select` into a *datatype-typed* field into a fresh free child
/// datatype variable, iterating until none remain, so the rest of the pipeline
/// sees only scalar selects and `is`/`==` over (original or child) variables.
///
/// This is a **relaxation**: the child is unconstrained, so the reduced query's
/// model space contains the original's (set each child to the original field's
/// value). Hence reduced-`unsat` ⇒ original-`unsat` with no guards; a `sat`
/// witness is projected through `links` and replayed. Each pass rewrites the
/// innermost layer (a `select` whose operand is already a variable); the access
/// structure of a quantifier-free query is finite, so this terminates.
fn unfold_traversals(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<(Vec<TermId>, Links), IrError> {
    let mut current = assertions.to_vec();
    let mut links: Links = BTreeMap::new();
    loop {
        // Collect distinct datatype-field selects whose operand is a variable.
        let mut targets: Vec<(TermId, SymbolId, usize, usize, Sort)> = Vec::new();
        let mut seen_terms = BTreeSet::new();
        let mut seen_targets = BTreeSet::new();
        let mut stack: Vec<TermId> = current.clone();
        while let Some(term) = stack.pop() {
            if !seen_terms.insert(term) {
                continue;
            }
            let TermNode::App { op, args } = arena.node(term) else {
                continue;
            };
            let (op, args) = (*op, args.clone());
            if let Op::DtSelect { constructor, index } = op {
                let field_sort = arena.constructor_fields(constructor)[index as usize].1;
                if let (Sort::Datatype(_), TermNode::Symbol(sym)) =
                    (field_sort, arena.node(args[0]))
                {
                    let dt = arena.constructor_datatype(constructor);
                    let ctor_idx = ctor_position(arena, dt, constructor);
                    if seen_targets.insert(term) {
                        targets.push((term, *sym, ctor_idx, index as usize, field_sort));
                    }
                }
            }
            stack.extend(args.iter().copied());
        }
        if targets.is_empty() {
            return Ok((current, links));
        }

        // Map each to a fresh (or reused) child variable, then rebuild.
        let mut map: HashMap<TermId, TermId> = HashMap::new();
        for (term, sym, ctor_idx, field_idx, field_sort) in targets {
            let key = (sym, ctor_idx, field_idx);
            let child = if let Some(&c) = links.get(&key) {
                c
            } else {
                let name = format!("!dt_child_{}_{ctor_idx}_{field_idx}", sym.index());
                let c = arena.declare_internal(&name, field_sort)?;
                links.insert(key, c);
                c
            };
            let var = arena.var(child);
            map.insert(term, var);
        }
        let mut memo: HashMap<TermId, TermId> = HashMap::new();
        let mut next = Vec::with_capacity(current.len());
        for &assertion in &current {
            next.push(replace_subterms(arena, assertion, &map, &mut memo)?);
        }
        current = next;
    }
}

/// A `select_{c,i}(construct_d(...))` with `d != c` — SMT-LIB's UNSPECIFIED
/// selector case — replaced by a fresh free variable.
///
/// `operand` is the ORIGINAL constructor term, kept so the projection can
/// evaluate it and key the model's chosen value by the operand's VALUE (which
/// is what makes the recorded interpretation congruent).
struct WitnessSite {
    constructor: ConstructorId,
    index: u32,
    operand: TermId,
    witness: SymbolId,
    field_sort: Sort,
}

/// If `term` is `construct_c(args...)`, its constructor.
fn construct_of(arena: &TermArena, term: TermId) -> Option<ConstructorId> {
    match arena.node(term) {
        TermNode::App {
            op: Op::DtConstruct { constructor, .. },
            ..
        } => Some(*constructor),
        _ => None,
    }
}

/// Replaces every `select_{c,i}(construct_d(...))` with `d != c` by a fresh free
/// variable of the field's sort.
///
/// Read-over-construct ([`simplify_datatypes`]) already folded the `d == c` case
/// to the field itself, so this pass sees exactly the residue: the case SMT-LIB
/// leaves UNSPECIFIED. Before this pass such a term reached `expect_dt_symbol`
/// and the whole query was refused — measured 2026-09-12, the single most common
/// blocker in the `QF_DT` parity list.
///
/// Soundness. The fresh variable is unconstrained, so the rewritten query's
/// model space CONTAINS the original's under every selector interpretation
/// (set the variable to whatever that interpretation gives). Hence
/// rewritten-`unsat` implies original-`unsat` with no side conditions. It is a
/// relaxation in the `sat` direction too — two occurrences that a model must
/// make equal (congruence) get independent variables — which is why a `sat`
/// candidate is only returned after [`register_select_witnesses`] has folded the
/// chosen values into ONE interpretation keyed by the operand's value, and the
/// replay has re-evaluated the original assertions under it.
fn abstract_wrong_ctor_selects(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<(Vec<TermId>, Vec<WitnessSite>), IrError> {
    let mut targets: Vec<(TermId, ConstructorId, u32, TermId, Sort)> = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        let (op, args) = (*op, args.clone());
        if let Op::DtSelect { constructor, index } = op
            && let Some(built) = construct_of(arena, args[0])
            && built != constructor
        {
            let field_sort = arena.constructor_fields(constructor)[index as usize].1;
            targets.push((term, constructor, index, args[0], field_sort));
        }
        stack.extend(args.iter().copied());
    }
    if targets.is_empty() {
        return Ok((assertions.to_vec(), Vec::new()));
    }
    // Deterministic: the walk above is stack-ordered, so sort by the select
    // term's own id before minting any symbol.
    targets.sort_by_key(|&(term, ..)| term.index());

    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut sites = Vec::with_capacity(targets.len());
    for (term, constructor, index, operand, field_sort) in targets {
        let witness = arena.declare_internal(&format!("!dt_sel_{}", term.index()), field_sort)?;
        map.insert(term, arena.var(witness));
        sites.push(WitnessSite {
            constructor,
            index,
            operand,
            witness,
            field_sort,
        });
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        out.push(replace_subterms(arena, assertion, &map, &mut memo)?);
    }
    // Registration order matters: an operand may itself contain an abstracted
    // select, and the arena interns a subterm BEFORE its parent, so ascending
    // operand id registers inner witnesses before the outer ones that read them.
    sites.sort_by_key(|site| site.operand.index());
    Ok((out, sites))
}

/// Rewrites every structural equality over a datatype that HAS a datatype-typed
/// field into its per-constructor definition, ONE level deep:
///
/// ```text
/// (= x y)  ->  AND_j ( is_j(x) -> ( is_j(y) AND AND_i sel_{j,i}(x) = sel_{j,i}(y) ) )
/// ```
///
/// This is exact — it is the definition of structural equality, and exactly one
/// `is_j(x)` holds — so it is denotation-preserving and needs no model
/// projection. The nested equalities it leaves behind are NOT expanded again;
/// for a recursive datatype that would not terminate, and one level is what the
/// corpus needs.
///
/// # Why it exists
///
/// `build_dt_eq` can only compare fields that have an expansion variable, and a
/// datatype-typed field has none, so it answers a free Boolean with only the
/// conditions it can decide. That is sound in both polarities but it cannot
/// WITNESS a difference: two variables an assertion forces apart project to the
/// same well-founded default and the replay refuses the candidate. Expanding one
/// level turns the comparison into one over CHILD variables, whose tags are
/// free — so `a != b` gets a witness at depth 1. Measured on the `QF_DT` parity
/// list: without it, 30 files that were `sat` become `unknown`.
fn expand_datatype_equalities(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, IrError> {
    let mut targets: Vec<(TermId, DatatypeId, TermId, TermId)> = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        let (op, args) = (*op, args.clone());
        if op == Op::Eq
            && let Sort::Datatype(dt) = arena.sort_of(args[0])
            && dt_has_datatype_field(arena, dt)
        {
            targets.push((term, dt, args[0], args[1]));
        }
        stack.extend(args.iter().copied());
    }
    if targets.is_empty() {
        return Ok(assertions.to_vec());
    }
    targets.sort_by_key(|&(term, ..)| term.index());

    let mut map: HashMap<TermId, TermId> = HashMap::new();
    for (term, dt, left, right) in targets {
        let ctors: Vec<ConstructorId> = arena.datatype_constructors(dt).to_vec();
        let mut conj = arena.bool_const(true);
        for ctor in ctors {
            let arity = arena.constructor_fields(ctor).len();
            let mut branch = arena.dt_test(ctor, right)?;
            for index in 0..arity {
                let i = u32::try_from(index).expect("field index fits u32");
                let ls = arena.dt_select(ctor, i, left)?;
                let rs = arena.dt_select(ctor, i, right)?;
                let fe = arena.eq(ls, rs)?;
                branch = arena.and(branch, fe)?;
            }
            let guard = arena.dt_test(ctor, left)?;
            let implication = arena.implies(guard, branch)?;
            conj = arena.and(conj, implication)?;
        }
        map.insert(term, conj);
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        out.push(replace_subterms(arena, assertion, &map, &mut memo)?);
    }
    Ok(out)
}

fn scan_fragment(arena: &TermArena, roots: &[TermId]) -> Result<Scan, SolverError> {
    let mut dt_symbols: BTreeMap<SymbolId, DatatypeId> = BTreeMap::new();
    let mut layouts: BTreeMap<DatatypeId, Vec<(ConstructorId, Vec<Sort>)>> = BTreeMap::new();
    let mut tests = Vec::new();
    let mut selects = Vec::new();
    let mut eqs = Vec::new();
    let mut relaxed_eq = false;

    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        let op = *op;
        let args = args.clone();
        match op {
            Op::DtConstruct { .. } => {
                return Err(unsupported(
                    "a datatype constructor survives read-over-construct elimination \
                     (only `is`/`select` over free datatype variables are supported)",
                ));
            }
            Op::DtTest(ctor) => {
                let sym = expect_dt_symbol(arena, args[0])?;
                let dt = arena.constructor_datatype(ctor);
                register_datatype(arena, dt, &mut layouts)?;
                dt_symbols.insert(sym, dt);
                tests.push(TestSite {
                    term,
                    symbol: sym,
                    ctor_index: ctor_position(arena, dt, ctor),
                });
            }
            Op::DtSelect { constructor, index } => {
                let sym = expect_dt_symbol(arena, args[0])?;
                let dt = arena.constructor_datatype(constructor);
                // Selecting a *datatype-typed* field traverses into the recursive
                // structure, which needs depth-bounded unfolding (the next unit);
                // selecting a scalar field is in this fragment.
                if matches!(
                    arena.constructor_fields(constructor)[index as usize].1,
                    Sort::Datatype(_)
                ) {
                    return Err(unsupported(
                        "select of a datatype-typed field traverses recursive structure; \
                         needs depth-bounded unfolding",
                    ));
                }
                register_datatype(arena, dt, &mut layouts)?;
                dt_symbols.insert(sym, dt);
                selects.push(SelectSite {
                    term,
                    symbol: sym,
                    ctor_index: ctor_position(arena, dt, constructor),
                    field_index: index as usize,
                });
            }
            Op::Eq if matches!(arena.sort_of(args[0]), Sort::Datatype(_)) => {
                // Structural equality of two datatype variables. Constructors on
                // either side are not handled in this slice (they should fold
                // first; otherwise Unsupported).
                let Sort::Datatype(dt) = arena.sort_of(args[0]) else {
                    unreachable!("matched datatype sort");
                };
                // `build_dt_eq` compares tag + scalar fields and skips datatype
                // fields. For a datatype *with* datatype fields that is a weaker
                // (relaxation) constraint: sound for `unsat`, and a `sat`
                // candidate is replay-checked (equal projections — e.g. both
                // datatype fields defaulted — pass; a real difference is
                // `unknown`). Mark the query relaxed so replay downgrades rather
                // than errors.
                if dt_has_datatype_field(arena, dt) {
                    relaxed_eq = true;
                }
                let left = expect_dt_symbol(arena, args[0])?;
                let right = expect_dt_symbol(arena, args[1])?;
                register_datatype(arena, dt, &mut layouts)?;
                dt_symbols.insert(left, dt);
                dt_symbols.insert(right, dt);
                eqs.push(EqSite { term, left, right });
            }
            // An uninterpreted function applied to a datatype argument
            // (ADR-1920). [`ackermannize_datatype_applications`] runs BEFORE
            // this scan and replaces every such application with a fresh witness
            // symbol plus pairwise congruence (ADR-1935), so reaching one here
            // means it was not eliminable — the pre-pass refuses with its own,
            // more specific message in every case it recognises, and this arm is
            // the fence for anything it does not.
            //
            // It has to stay a REFUSAL rather than a fall-through: the tag/field
            // expansion has no rewrite for `p(o)`, so the datatype-sorted `o`
            // would survive into the residual and the dispatcher would route the
            // residual straight back here — an unbounded recursion, not an answer
            // (measured: `(assert (p o))` aborted the process with a stack
            // overflow).
            Op::Apply(_) if args.iter().any(|&a| is_datatype_sorted(arena, a)) => {
                return Err(unsupported(
                    "an uninterpreted function applied to a datatype argument that \
                     Ackermann expansion did not eliminate",
                ));
            }
            _ => {
                reject_stray_datatype_operands(arena, &args)?;
                stack.extend(args.iter().copied());
            }
        }
    }

    Ok(Scan {
        dt_symbols,
        layouts,
        tests,
        selects,
        eqs,
        relaxed_eq,
    })
}

/// One Ackermann-expanded application: `func(args)`, replaced by `witness`.
struct AckSite {
    func: axeyum_ir::FuncId,
    /// The application's argument terms, as they stood BEFORE the replacement
    /// map was applied. `project_and_replay` rewrites them itself when it
    /// rebuilds the interpretation, so a nested expanded application is read
    /// through its own witness.
    args: Vec<TermId>,
    witness: SymbolId,
}

/// The most congruence pairs one call will emit before refusing.
///
/// Ackermann is quadratic in the number of applications of one function, and the
/// SPARK/Ada divisions apply one accessor to hundreds of records. Refusing at a
/// bound is an `Unsupported` the harness reads as a decline; not refusing is a
/// term explosion that spends the whole budget and yields nothing. The bound is
/// on PAIRS rather than applications because that is what costs.
const MAX_ACK_PAIRS: usize = 20_000;

/// Replaces every uninterpreted-function application that has a datatype-sorted
/// argument with a fresh witness symbol, and asserts pairwise congruence
/// (ADR-1935).
///
/// For applications `p = f(a₁…aₙ)` and `q = f(b₁…bₙ)` this emits
/// `(⋀ᵢ aᵢ = bᵢ) → (wₚ = w_q)`, leaving the argument equalities as plain
/// `Op::Eq` terms for the tag/field expansion to encode.
///
/// # The checked precondition, and why it is this one
///
/// Every datatype-sorted argument must be a free variable of a datatype whose
/// expansion is EXACT ([`datatype_expansion_is_exact`]). ADR-1920 states the
/// reason and it is the whole soundness argument:
///
/// > For a datatype that *does* have datatype-typed fields, `build_dt_eq` is a
/// > **relaxation** — weaker than real equality — and a weaker antecedent makes
/// > the congruence constraint *stronger* than the true axiom, which can produce
/// > a wrong `unsat`.
///
/// A relaxed antecedent can be true of two values that really differ, and the
/// clause then forces `f` to agree on them — a constraint the true congruence
/// axiom does not impose. That is a MODEL RESTRICTION, the same shape as the
/// non-active field guard ADR-1930 removed after it manufactured a wrong
/// `unsat`, and it is why this is a checked call rather than a comment.
///
/// With exactness the transformation is equisatisfiable in both directions:
///
/// - *original ⇒ reduced.* Map `wₚ` to `f(a₁…aₙ)`'s value. Each antecedent is
///   real equality of the arguments (that is what exactness buys), so every
///   congruence clause holds by `f` being a function.
/// - *reduced ⇒ original.* Define `f` at each expanded tuple as that site's
///   witness value; the congruence clauses make the definition consistent
///   wherever two tuples are equal, so it is a function. [`AckSite`] carries
///   exactly what `register_ack_interpretations` needs to build it, and the
///   `sat` replay evaluates the original applications under it.
///
/// # Errors
///
/// [`SolverError::Unsupported`] if a datatype-sorted argument is not a free
/// variable, if its datatype's expansion is not exact, if the result sort
/// mentions a datatype (a datatype-valued UF result is a separate capability and
/// its witness would survive into the residual), or if the pair count exceeds
/// [`MAX_ACK_PAIRS`].
fn ackermannize_datatype_applications(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<(Vec<TermId>, Vec<AckSite>), SolverError> {
    // Collect the applications, grouped by function, in TermId order. TermId
    // order is a deterministic bottom-up order in a hash-consed arena (a child
    // is interned before its parent), which both keeps the output stable and
    // lets `register_ack_interpretations` process a nested site before the site
    // that reads it.
    let mut groups: BTreeMap<axeyum_ir::FuncId, Vec<TermId>> = BTreeMap::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        let op = *op;
        let args = args.clone();
        if let Op::Apply(func) = op
            && args.iter().any(|&a| is_datatype_sorted(arena, a))
        {
            groups.entry(func).or_default().push(term);
        }
        stack.extend(args);
    }
    if groups.is_empty() {
        return Ok((assertions.to_vec(), Vec::new()));
    }

    let mut pairs = 0usize;
    for sites in groups.values_mut() {
        sites.sort_unstable();
        pairs = pairs.saturating_add(sites.len().saturating_mul(sites.len() - 1) / 2);
    }
    if pairs > MAX_ACK_PAIRS {
        return Err(unsupported(&format!(
            "Ackermann congruence over datatype arguments needs {pairs} congruence pairs, \
             over the {MAX_ACK_PAIRS} bound"
        )));
    }

    // Validate BEFORE declaring anything, so a refusal leaves the arena clean.
    for (&func, sites) in &groups {
        let (_, _, result) = arena.function(func);
        if crate::datatype_elim::sort_mentions_datatype(result) {
            return Err(unsupported(
                "an uninterpreted function whose RESULT sort mentions a datatype \
                 (its Ackermann witness would itself be a datatype-sorted term)",
            ));
        }
        for &site in sites {
            let TermNode::App { args, .. } = arena.node(site) else {
                unreachable!("collected an application");
            };
            for &arg in &args.clone() {
                if !is_datatype_sorted(arena, arg) {
                    continue;
                }
                if !matches!(arena.node(arg), TermNode::Symbol(_)) {
                    return Err(unsupported(
                        "an uninterpreted function applied to a datatype term that is not a \
                         free variable (constructors should fold first)",
                    ));
                }
                let Sort::Datatype(dt) = arena.sort_of(arg) else {
                    unreachable!("datatype-sorted");
                };
                if !datatype_expansion_is_exact(arena, dt) {
                    // ADR-1920's soundness condition, restated as exactness
                    // (ADR-1935). This is the arm that must never be relaxed
                    // into a comment.
                    return Err(unsupported(
                        "congruence over a datatype argument whose expansion is not exact \
                         (a field with no expansion variable makes the encoded equality \
                         WEAKER than real equality, and a weaker congruence antecedent is \
                         STRONGER than the true axiom -- a wrong `unsat`)",
                    ));
                }
            }
        }
    }

    let mut replacements: HashMap<TermId, TermId> = HashMap::new();
    let mut ack_sites = Vec::new();
    let mut congruence = Vec::new();
    for (&func, sites) in &groups {
        let (_, _, result) = arena.function(func);
        let mut witnesses = Vec::with_capacity(sites.len());
        for &site in sites {
            let witness = arena
                .declare_internal(&format!("!dt_ack_{}", site.index()), result)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            let TermNode::App { args, .. } = arena.node(site) else {
                unreachable!("collected an application");
            };
            let args = args.clone();
            replacements.insert(site, arena.var(witness));
            ack_sites.push(AckSite {
                func,
                args: args.to_vec(),
                witness,
            });
            witnesses.push(witness);
        }
        for (pi, &p) in sites.iter().enumerate() {
            for (qi, &q) in sites.iter().enumerate().skip(pi + 1) {
                let (TermNode::App { args: pa, .. }, TermNode::App { args: qa, .. }) =
                    (arena.node(p), arena.node(q))
                else {
                    unreachable!("collected applications");
                };
                let (pa, qa) = (pa.clone(), qa.clone());
                let mut antecedent = arena.bool_const(true);
                for (&a, &b) in pa.iter().zip(&qa) {
                    if a == b {
                        // Hash-consed: identical argument terms are one TermId,
                        // so this conjunct is `true` and emitting it only grows
                        // the formula.
                        continue;
                    }
                    let eq = arena
                        .eq(a, b)
                        .map_err(|e| SolverError::Backend(e.to_string()))?;
                    antecedent = arena
                        .and(antecedent, eq)
                        .map_err(|e| SolverError::Backend(e.to_string()))?;
                }
                let pv = arena.var(witnesses[pi]);
                let qv = arena.var(witnesses[qi]);
                let consequent = arena
                    .eq(pv, qv)
                    .map_err(|e| SolverError::Backend(e.to_string()))?;
                let clause = arena
                    .implies(antecedent, consequent)
                    .map_err(|e| SolverError::Backend(e.to_string()))?;
                congruence.push(clause);
            }
        }
    }

    // Rewrite the assertions AND the congruence clauses through the same map, so
    // a nested expanded application inside an antecedent is read through its own
    // witness rather than surviving as an `Op::Apply` the scan would refuse.
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len() + congruence.len());
    for &assertion in assertions.iter().chain(&congruence) {
        let rewritten = replace_subterms(arena, assertion, &replacements, &mut memo)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        out.push(rewritten);
    }
    Ok((out, ack_sites))
}

/// Rebuilds each Ackermann-expanded function's interpretation from its witness
/// values, so the `sat` replay can evaluate the original `f(...)` applications.
///
/// Sites are visited in the order [`ackermannize_datatype_applications`]
/// produced them (TermId order within a function, functions in `FuncId` order),
/// and each argument is evaluated under the assignment as it stands — which by
/// this point already carries the projected datatype values. An argument that
/// does not evaluate (an unconstrained symbol the inner model never mentioned)
/// leaves that site out of the interpretation; the replay then reads the
/// function's default there and fails if that is not what the search assumed,
/// which is the correct outcome rather than a guessed one.
fn register_ack_interpretations(
    arena: &TermArena,
    ack_sites: &[AckSite],
    assignment: &mut axeyum_ir::Assignment,
) {
    // Bind every expanded function FIRST, with the total convention's default.
    // An `f` with no entry at all is `IrError::UnboundFunction` at replay, which
    // presents as "the model does not satisfy the query" and is indistinguishable
    // from a real projection bug. A constant interpretation is a claim the replay
    // can then check; an absent one is not.
    for site in ack_sites {
        if assignment.function(site.func).is_some() {
            continue;
        }
        let (_, params, result_sort) = arena.function(site.func);
        let Some(default) = well_founded_default(arena, result_sort) else {
            continue;
        };
        assignment.set_function(
            site.func,
            axeyum_ir::FuncValue::constant_value(params.to_vec(), result_sort, default),
        );
    }

    for site in ack_sites {
        // A witness nothing constrained takes the total convention's value: any
        // value satisfies the congruence clauses, and leaving the site out
        // instead would make the replay read the function's default at a key the
        // search never chose.
        let result = match assignment.get(site.witness) {
            Some(value) => value,
            None => {
                let (_, _, result_sort) = arena.function(site.func);
                match well_founded_default(arena, result_sort) {
                    Some(value) => value,
                    None => continue,
                }
            }
        };
        let mut vals = Vec::with_capacity(site.args.len());
        let mut ok = true;
        for &arg in &site.args {
            match eval(arena, arg, assignment) {
                Ok(value) => vals.push(value),
                Err(_) => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            continue;
        }
        let Some(current) = assignment.function(site.func).cloned() else {
            continue;
        };
        assignment.set_function(site.func, current.define_value(&vals, result));
    }
}

/// Whether `term` has a datatype sort.
fn is_datatype_sorted(arena: &TermArena, term: TermId) -> bool {
    matches!(arena.sort_of(term), Sort::Datatype(_))
}

/// TERMINATION GUARD (ADR-1920): refuse rather than hand a still-datatype-carrying
/// assertion set back to the dispatcher.
///
/// `check_auto_dispatch` diverts on the *sort* `Sort::Datatype(_)`, not on a
/// datatype operator, and every branch of that diversion returns — so a residual
/// that still carries a datatype-sorted term comes straight back into this
/// function with the same input, forever. The dispatcher also recomputes its
/// deadline on each entry, so `config.timeout` cannot break the cycle; the
/// observed failure is a stack overflow and a SIGABRT, which a harness reads as
/// a crash rather than the first-class `unknown` the query is entitled to.
///
/// # Errors
///
/// [`SolverError::Unsupported`] if any term reachable from `roots` has a
/// datatype sort.
fn refuse_if_datatype_survives(arena: &TermArena, roots: &[TermId]) -> Result<(), SolverError> {
    if first_datatype_sorted(arena, roots).is_some() {
        return Err(unsupported(
            "a datatype-sorted term survives tag/field expansion with nothing left to \
             expand it (the dispatcher would route it straight back here)",
        ));
    }
    Ok(())
}

/// The first subterm reachable from `roots` whose sort MENTIONS a datatype.
///
/// Deliberately wider than [`is_datatype_sorted`]: the dispatcher diverts on
/// `Features::note_sort`, which recurses into an array's component sorts, so an
/// `(Array Int Color)` term sets `has_datatype` while having sort `Array`. A
/// guard that tested only `Sort::Datatype(_)` let exactly that residual through
/// and the cycle came back — measured, after the first two guards were already
/// in place (ADR-1920). The guards and the divert condition must be the same
/// predicate, so both call [`sort_mentions_datatype`].
fn first_datatype_sorted(arena: &TermArena, roots: &[TermId]) -> Option<TermId> {
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if crate::datatype_elim::sort_mentions_datatype(arena.sort_of(term)) {
            return Some(term);
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    None
}

/// Rejects a datatype-sorted operand of a non-datatype op (e.g. `ite` of a
/// datatype) that is neither a free variable nor a constructor — such terms
/// cannot be expanded by this fragment.
fn reject_stray_datatype_operands(arena: &TermArena, args: &[TermId]) -> Result<(), SolverError> {
    for &arg in args {
        if matches!(arena.sort_of(arg), Sort::Datatype(_))
            && !matches!(
                arena.node(arg),
                TermNode::App {
                    op: Op::DtConstruct { .. },
                    ..
                }
            )
            && !matches!(arena.node(arg), TermNode::Symbol(_))
        {
            return Err(unsupported(
                "a datatype-sorted term other than a free variable or constructor \
                 reaches a non-datatype operator",
            ));
        }
    }
    Ok(())
}

/// Requires `term` to be a datatype-sorted variable; returns its symbol.
fn expect_dt_symbol(arena: &TermArena, term: TermId) -> Result<SymbolId, SolverError> {
    match arena.node(term) {
        TermNode::Symbol(s) => Ok(*s),
        _ => Err(unsupported(
            "`is`/`select` over a non-variable datatype term (constructors should fold first)",
        )),
    }
}

/// Records `dt`'s constructor/field layout.
///
/// Every field sort that [`field_sort_expands`] accepts gets an expansion
/// variable of that sort: `Bool`/`BitVec`/`Int`/`Real`, and — since ADR-1935 —
/// `(declare-sort …)` uninterpreted sorts and arrays whose component sorts
/// mention no datatype. Datatype-typed fields are recorded in `field_sorts` but
/// get no expansion variable; they are sound only as long as they are never
/// traversed by a `select` or compared exactly, which the scan and
/// [`datatype_expansion_is_exact`] enforce, so they are projected to a
/// well-founded default. Everything else is rejected.
fn register_datatype(
    arena: &TermArena,
    dt: DatatypeId,
    layouts: &mut BTreeMap<DatatypeId, Vec<(ConstructorId, Vec<Sort>)>>,
) -> Result<(), SolverError> {
    if layouts.contains_key(&dt) {
        return Ok(());
    }
    // Insert a placeholder first so a recursive field (`Sort::Datatype(dt)`)
    // does not recurse forever through `register_datatype`.
    layouts.insert(dt, Vec::new());
    let mut ctors = Vec::new();
    for &ctor in arena.datatype_constructors(dt) {
        let mut field_sorts = Vec::new();
        for (_, sort) in arena.constructor_fields(ctor) {
            match sort {
                Sort::Datatype(inner) => {
                    register_datatype(arena, *inner, layouts)?;
                    field_sorts.push(*sort);
                }
                _ if field_sort_expands(*sort) => field_sorts.push(*sort),
                _ => {
                    return Err(unsupported(
                        "a datatype field sort with no expansion variable (native datatype \
                         solving expands Bool/BitVec/Int/Real, uninterpreted sorts, and arrays \
                         whose component sorts mention no datatype)",
                    ));
                }
            }
        }
        ctors.push((ctor, field_sorts));
    }
    layouts.insert(dt, ctors);
    Ok(())
}

/// Whether a datatype FIELD of this sort gets an expansion variable.
///
/// **This is the ADR-1935 precondition, and it has exactly one definition on
/// purpose.** Three things must agree about a field sort — whether
/// [`register_datatype`] admits the datatype, whether [`build_sym_vars`]
/// declares a variable for the field, and whether
/// [`datatype_expansion_is_exact`] may call the datatype's equality encoding
/// exact — and ADR-1920's measured lesson is that two predicates written twice
/// in different words do not stay the same predicate. `build_sym_vars` skips
/// exactly `Sort::Datatype(_)` and declares a variable for everything else, so
/// "admitted by `register_datatype` and not a datatype" IS "has a variable",
/// and this function is the only place that decides it.
///
/// Uninterpreted sorts and arrays are admitted (ADR-1935); an array whose
/// component sorts mention a datatype is NOT, because its expansion variable
/// would carry datatype content into the residual, which
/// [`refuse_if_datatype_survives`] must then refuse — the same divert-vs-content
/// predicate mismatch ADR-1920 measured as a non-terminating cycle.
///
/// `Float`/`RoundingMode`/`Seq` fields stay rejected: no lane has measured a
/// datatype over them end to end, and ADR-1920's rule is that a gate is lifted
/// on a measurement, not on a symmetry.
fn field_sort_expands(sort: Sort) -> bool {
    match sort {
        Sort::Bool | Sort::BitVec(_) | Sort::Int | Sort::Real | Sort::Uninterpreted(_) => true,
        Sort::Array { .. } => !crate::datatype_elim::sort_mentions_datatype(sort),
        _ => false,
    }
}

/// Whether the tag/field expansion of `dt` is EXACT: every field of every
/// constructor gets an expansion variable, so `tag_l == tag_r` conjoined with
/// the per-constructor field agreement is real equality in BOTH directions.
///
/// **This is the checked precondition for emitting congruence over a datatype
/// argument** (ADR-1935), and it is a function rather than a comment because
/// ADR-1920 named exactly that requirement:
///
/// > For a datatype that *does* have datatype-typed fields, `build_dt_eq` is a
/// > **relaxation** — weaker than real equality — and a weaker antecedent makes
/// > the congruence constraint *stronger* than the true axiom, which can produce
/// > a wrong `unsat`.
///
/// ADR-1920 stated the precondition as "all fields scalar". That is *sufficient*
/// for exactness but not necessary, and measured over the three DT divisions it
/// holds for 6 of 600 sampled files, against 136 for exactness
/// (`docs/research/03-measurements/the-adr-1920-slice-is-6-of-600-files-2026-09-12.md`).
/// The property the soundness argument needs is exactness, so that is what is
/// checked.
fn datatype_expansion_is_exact(arena: &TermArena, dt: DatatypeId) -> bool {
    arena.datatype_constructors(dt).iter().all(|&ctor| {
        arena
            .constructor_fields(ctor)
            .iter()
            .all(|(_, sort)| field_sort_expands(*sort))
    })
}

/// Whether any constructor of `dt` has a datatype-typed field.
fn dt_has_datatype_field(arena: &TermArena, dt: DatatypeId) -> bool {
    arena.datatype_constructors(dt).iter().any(|&ctor| {
        arena
            .constructor_fields(ctor)
            .iter()
            .any(|(_, sort)| matches!(sort, Sort::Datatype(_)))
    })
}

fn ctor_position(arena: &TermArena, dt: DatatypeId, ctor: ConstructorId) -> usize {
    arena
        .datatype_constructors(dt)
        .iter()
        .position(|&c| c == ctor)
        .expect("constructor belongs to its datatype")
}

/// Bits needed to tag `count` constructors (at least 1).
fn tag_width_for(count: usize) -> u32 {
    if count <= 1 {
        1
    } else {
        let max = u32::try_from(count - 1).unwrap_or(u32::MAX);
        u32::BITS - max.leading_zeros()
    }
}

/// Declares the tag and field variables for one datatype symbol and emits the
/// domain and field-default guard constraints into `extra`.
fn build_sym_vars(
    arena: &mut TermArena,
    sym: SymbolId,
    _dt: DatatypeId,
    ctors: &[(ConstructorId, Vec<Sort>)],
    extra: &mut Vec<TermId>,
) -> Result<SymVars, SolverError> {
    let oidx = sym.index();
    let count = ctors.len();
    let tag_width = tag_width_for(count);

    let tag = arena
        .declare_internal(&format!("!dt_tag_{oidx}"), Sort::BitVec(tag_width))
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let tag_var = arena.var(tag);

    // Domain: tag < count, when count is not the full 2^tag_width range.
    if (count as u128) < (1u128 << tag_width) {
        let bound = arena
            .bv_const(tag_width, count as u128)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let lt = arena
            .bv_ult(tag_var, bound)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        extra.push(lt);
    }

    let mut fields = Vec::with_capacity(count);
    for (j, (_ctor, field_sorts)) in ctors.iter().enumerate() {
        let mut row = Vec::with_capacity(field_sorts.len());
        for (i, &fsort) in field_sorts.iter().enumerate() {
            // Datatype-typed fields are never traversed (the scan rejects such
            // `select`/`==`), so they get no variable and no guard — they are
            // projected to a well-founded default. Only scalar fields expand.
            if matches!(fsort, Sort::Datatype(_)) {
                row.push(None);
                continue;
            }
            let field = arena
                .declare_internal(&format!("!dt_fld_{oidx}_{j}_{i}"), fsort)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            row.push(Some(field));

            // NO GUARD. A NON-ACTIVE field variable is deliberately left FREE.
            //
            // This slot used to carry `tag_o == j OR f_{o,j,i} == default`,
            // pinning `select_{j,i}(o)` to `well_founded_default` whenever `o`'s
            // constructor is not `j`. That is not a conservative convention: it
            // is a MODEL RESTRICTION, and restricting the model space is exactly
            // how a solver manufactures a wrong `unsat`. Measured 2026-09-12 --
            // `is-none(o) AND (= (v o) 5)` over `Opt = none | some(v)` answered
            // `unsat` here while cvc5 1.3.4 and z3 4.x both answer `sat`,
            // because SMT-LIB leaves `sel_{c,i}` UNSPECIFIED off its own
            // constructor (ADR-1930). Leaving the variable free is a
            // relaxation -- `unsat` still transfers -- and the value the search
            // picks becomes the model's chosen selector interpretation, recorded
            // by `register_select_witnesses` and checked by the replay.
        }
        fields.push(row);
    }

    Ok(SymVars {
        tag,
        tag_width,
        fields,
    })
}

/// Builds the reduced term for `o == o'` over two same-datatype variables: a
/// fresh Boolean `e`, defined by the conditions the expansion can actually
/// decide.
///
/// **Why a fresh Boolean and not a formula.** The obvious encoding is
/// `tag_l == tag_r AND (fields agree)`, and it is what this function used to
/// build. Its fields conjunct SKIPS datatype-typed fields, which have no
/// expansion variable, so the formula is WEAKER than real equality. "Weaker is
/// a relaxation, so `unsat` is sound" — the comment this function used to carry
/// — is only true of a POSITIVE occurrence. Under a negation, weaker becomes
/// STRONGER, and that shipped a wrong `unsat`: on
/// `list = cons(car: tree, cdr: list) | null`, whose every field is a datatype,
/// `is-cons(a) AND is-cons(b) AND a != b` reduced to `tag_a == cons AND
/// tag_b == cons AND tag_a != tag_b` and answered **`unsat`**, where cvc5 1.3.4
/// and z3 both answer `sat` (measured 2026-09-12, and the defect predates this
/// lane).
///
/// So `e` is free, and it carries:
///
/// - the NECESSARY conditions, always: `e -> tag_l == tag_r`, and
///   `e AND tag_l == j -> (j's comparable fields agree)`. These cannot remove a
///   model, because a real model with `o == o'` satisfies them with `e` true.
/// - the SUFFICIENT condition, only for a constructor `j` every one of whose
///   fields has an expansion variable: `tag_l == j AND tag_r == j AND fields
///   agree -> e`. For such a constructor the comparison IS exact, so this cannot
///   remove a model either.
///
/// A real model with `o != o'` extends by setting `e` false: the only clauses
/// that could object are the sufficiency ones, and their antecedent says the two
/// values agree on every field of an exact constructor, which contradicts
/// `o != o'`. So BOTH polarities are relaxations, which is what the previous
/// encoding was not.
///
/// For a fully scalar datatype every constructor is exact and this is exactly
/// the old biconditional, so nothing that decided through that path loses.
/// Where a datatype-typed field is involved the equality is one-directional, the
/// caller marks the query `relaxed_eq`, and a `sat` candidate is replay-checked
/// against the original assertions.
fn build_dt_eq(
    arena: &mut TermArena,
    left: &SymVars,
    right: &SymVars,
    extra: &mut Vec<TermId>,
    mode: EqMode,
) -> Result<(TermId, bool), SolverError> {
    if mode == EqMode::Restriction {
        return build_dt_eq_restriction(arena, left, right);
    }
    let equal = arena
        .declare_internal(
            &format!("!dt_eq_{}_{}", left.tag.index(), right.tag.index()),
            Sort::Bool,
        )
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let ev = arena.var(equal);
    let lt = arena.var(left.tag);
    let rt = arena.var(right.tag);

    // Necessary: equal values carry the same tag.
    let tags_eq = arena
        .eq(lt, rt)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let necessary_tag = arena
        .implies(ev, tags_eq)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    extra.push(necessary_tag);

    let mut all_exact = true;
    let mut sufficient = arena.bool_const(true);
    for (j, (lrow, rrow)) in left.fields.iter().zip(&right.fields).enumerate() {
        let mut fields_eq = arena.bool_const(true);
        let mut comparable = 0usize;
        let mut exact = true;
        for (lf, rf) in lrow.iter().zip(rrow) {
            let (Some(lf), Some(rf)) = (lf, rf) else {
                // A datatype-typed field: no expansion variable, so this
                // constructor's comparison cannot be exact.
                exact = false;
                all_exact = false;
                continue;
            };
            let lfv = arena.var(*lf);
            let rfv = arena.var(*rf);
            let fe = arena
                .eq(lfv, rfv)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            fields_eq = arena
                .and(fields_eq, fe)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            comparable += 1;
        }
        let tag_j = arena
            .bv_const(left.tag_width, j as u128)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let l_is_j = arena
            .eq(lt, tag_j)
            .map_err(|e| SolverError::Backend(e.to_string()))?;

        if comparable > 0 {
            // Necessary: `e AND tag_l == j -> j's comparable fields agree`.
            // Skipped when there is nothing to compare -- a nullary constructor
            // would otherwise contribute `tag_l != j OR true` once PER
            // CONSTRUCTOR, and a pure enum has hundreds (the `vlsat3` family),
            // which cost two files that decided in under 24 s.
            let antecedent = arena
                .and(ev, l_is_j)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            let clause = arena
                .implies(antecedent, fields_eq)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            extra.push(clause);
        }

        // Sufficiency is accumulated into ONE clause below rather than emitted
        // per constructor. Per-constructor is the same explosion the necessary
        // side already hit: a pure enum has one nullary constructor PER VALUE
        // (`vlsat3` declares hundreds) and every equality would carry that many
        // clauses. Collectively it degenerates to `tag_l == tag_r -> e`.
        if exact {
            if comparable > 0 {
                let not_j = arena
                    .not(l_is_j)
                    .map_err(|e| SolverError::Backend(e.to_string()))?;
                let per_ctor = arena
                    .or(not_j, fields_eq)
                    .map_err(|e| SolverError::Backend(e.to_string()))?;
                sufficient = arena
                    .and(sufficient, per_ctor)
                    .map_err(|e| SolverError::Backend(e.to_string()))?;
            }
        } else {
            // Not decidable at this constructor, so the sufficiency clause only
            // speaks about the tags that ARE decidable.
            let not_j = arena
                .not(l_is_j)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            sufficient = arena
                .and(sufficient, not_j)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
        }
    }
    let sufficient = arena
        .and(sufficient, tags_eq)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let clause = arena
        .implies(sufficient, ev)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    extra.push(clause);
    Ok((ev, !all_exact))
}

/// The RESTRICTION encoding of `o == o'`: `tag_l == tag_r` conjoined, per
/// constructor `j`, with `tag_l == j -> (j's comparable fields agree)`, as a
/// plain term.
///
/// Datatype-typed fields have no expansion variable and are skipped, so this is
/// weaker than real equality in a POSITIVE occurrence and **stronger** in a
/// negative one. Only a `sat` may be believed, and only after the replay against
/// the original assertions — which is exactly what the caller does. See the
/// two-encoding note in [`check_with_datatype_native`].
fn build_dt_eq_restriction(
    arena: &mut TermArena,
    left: &SymVars,
    right: &SymVars,
) -> Result<(TermId, bool), SolverError> {
    let lt = arena.var(left.tag);
    let rt = arena.var(right.tag);
    let mut conj = arena
        .eq(lt, rt)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let mut all_exact = true;
    for (j, (lrow, rrow)) in left.fields.iter().zip(&right.fields).enumerate() {
        let mut fields_eq = arena.bool_const(true);
        let mut comparable = 0usize;
        for (lf, rf) in lrow.iter().zip(rrow) {
            let (Some(lf), Some(rf)) = (lf, rf) else {
                all_exact = false;
                continue;
            };
            let lfv = arena.var(*lf);
            let rfv = arena.var(*rf);
            let fe = arena
                .eq(lfv, rfv)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            fields_eq = arena
                .and(fields_eq, fe)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            comparable += 1;
        }
        if comparable == 0 {
            // Nothing to say about this constructor. Emitting the vacuous
            // conjunct once PER CONSTRUCTOR is what cost two `vlsat3` files
            // (hundreds of nullary constructors) their verdict.
            continue;
        }
        let tag_j = arena
            .bv_const(left.tag_width, j as u128)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let l_is_j = arena
            .eq(lt, tag_j)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let not_j = arena
            .not(l_is_j)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let guarded = arena
            .or(not_j, fields_eq)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        conj = arena
            .and(conj, guarded)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
    }
    Ok((conj, !all_exact))
}

/// Projects the expansion model back to datatype values and replays it against
/// the (simplified, equisatisfiable) assertions before returning `sat`.
#[allow(clippy::too_many_arguments)]
fn project_and_replay(
    arena: &TermArena,
    assertions: &[TermId],
    scan: &Scan,
    layout: &BTreeMap<SymbolId, SymVars>,
    links: &Links,
    witnesses: &[WitnessSite],
    ack_sites: &[AckSite],
    relaxed: bool,
    model: &Model,
) -> Result<CheckResult, SolverError> {
    let mut assignment = model.to_assignment();
    let mut memo: BTreeMap<SymbolId, Value> = BTreeMap::new();
    for &sym in scan.dt_symbols.keys() {
        let value = project_slot(arena, sym, scan, layout, links, &assignment, &mut memo)?;
        assignment.set(sym, value);
    }

    // Rebuild the interpretation of every Ackermann-expanded function from its
    // witnesses, so the replay below can evaluate the `f(...)` applications the
    // ORIGINAL assertions still contain. Without this every such replay fails at
    // `IrError::UnboundFunction` and a correct `sat` is thrown away.
    register_ack_interpretations(arena, ack_sites, &mut assignment);

    // Fold the model's choices for every UNSPECIFIED selector read into ONE
    // interpretation before replaying (ADR-1930). Without this the replay would
    // evaluate those reads with `well_founded_default` and reject every model
    // that used a different value, which is the whole class of query this change
    // exists to decide.
    register_select_witnesses(arena, scan, layout, links, witnesses, &mut assignment);

    // Replay against the original assertions. For the *relaxed* (traversal) path
    // a free child may not match the wrong-constructor default, so a replay
    // failure is `unknown`, never wrong; the exact path treats it as a bug.
    for &assertion in assertions {
        let ok = matches!(eval(arena, assertion, &assignment), Ok(Value::Bool(true)));
        if !ok {
            if relaxed {
                return Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail: format!(
                        "datatype unfolding produced a candidate that does not satisfy \
                         assertion #{}; the traversed-field relaxation is incomplete here",
                        assertion.index()
                    ),
                }));
            }
            return Err(SolverError::Backend(format!(
                "datatype sat model replay failed at assertion #{}",
                assertion.index()
            )));
        }
    }

    // Build a model over the original symbols, dropping the internal tag/field/
    // child variables introduced by the expansion.
    let mut out = Model::new();
    for (symbol, name, _sort) in arena.symbols() {
        if name.starts_with("!dt_") {
            continue;
        }
        if let Some(value) = assignment.get(symbol) {
            out.set(symbol, value);
        }
    }
    // Roadmap 2.11: this carried symbol entries only, while the replay above ran
    // against `assignment` -- which starts life as `model.to_assignment()` and so
    // carries whatever function interpretations and division-at-zero witnesses
    // the inner model held.
    out.carry_assignment_components(&assignment);
    Ok(CheckResult::Sat(out))
}

/// Folds the candidate model's choices for every WRONG-CONSTRUCTOR selector read
/// into a single selector interpretation on `assignment`, which the `sat` replay
/// then evaluates the original assertions under.
///
/// Two sources, both of them values the search chose freely:
///
/// - a `select_{c,i}(o)` over an expanded VARIABLE whose projected constructor
///   is not `c`: the field variable `f_{o,c,i}` (no longer pinned to a default,
///   see `build_sym_vars`);
/// - a `select_{c,i}(construct_d(...))` abstracted by
///   [`abstract_wrong_ctor_selects`]: its fresh witness variable.
///
/// The interpretation is keyed by `(constructor, index, the OPERAND'S VALUE)`,
/// so it is a genuine function of the value and therefore congruent: two
/// syntactically different operands that denote the same value get the same
/// answer, which is exactly what SMT-LIB requires of an unspecified selector and
/// what the relaxation above does NOT enforce on its own.
///
/// **A conflict is recorded, not rejected, and this is deliberate.** When the
/// candidate wants two different results at one key the FIRST stands, which
/// still leaves a total congruent interpretation -- and the replay against the
/// original assertions then decides under it. Rejecting the candidate here
/// instead would be a second, weaker checker in front of the real one: it can
/// only turn a `sat` the replay would have confirmed into an `unknown`, never
/// catch anything the replay misses. Mutation-checked: disabling the conflict
/// arm of `set_dt_select_witness` killed no test, because the replay was
/// already deciding every case it covered.
///
fn register_select_witnesses(
    arena: &TermArena,
    scan: &Scan,
    layout: &BTreeMap<SymbolId, SymVars>,
    links: &Links,
    witnesses: &[WitnessSite],
    assignment: &mut axeyum_ir::Assignment,
) {
    // A TRAVERSED DATATYPE FIELD read off the wrong constructor. `project_slot`
    // fills a slot's fields from the ACTIVE constructor's row only, so when the
    // parent's tag is not `ctor_idx` the child variable's value is dropped and
    // the replay falls back to `well_founded_default` -- which is exactly the
    // mismatch the `relaxed` path reported as "the traversed-field relaxation is
    // incomplete here" (19 of 74 remaining QF_DT unknowns, measured 2026-09-12).
    // The child IS the model's chosen value for that read; record it.
    for (&(sym, ctor_idx, field_idx), &child) in links {
        let Some(operand @ Value::Datatype { constructor, .. }) = assignment.get(sym) else {
            continue;
        };
        let Some(&dt) = scan.dt_symbols.get(&sym) else {
            continue;
        };
        let Some(entry) = scan.layouts[&dt].get(ctor_idx) else {
            continue;
        };
        let link_ctor = entry.0;
        if constructor == link_ctor {
            continue;
        }
        let Some(value) = assignment.get(child) else {
            continue;
        };
        let index = u32::try_from(field_idx).unwrap_or(u32::MAX);
        assignment.set_dt_select_witness(link_ctor, index, operand, value);
    }

    for site in &scan.selects {
        let Some(operand @ Value::Datatype { constructor, .. }) = assignment.get(site.symbol)
        else {
            continue;
        };
        let dt = scan.dt_symbols[&site.symbol];
        let site_ctor = scan.layouts[&dt][site.ctor_index].0;
        if constructor == site_ctor {
            // The ACTIVE constructor: the field variable IS the field, exactly.
            continue;
        }
        let Some(field) = layout[&site.symbol].fields[site.ctor_index][site.field_index] else {
            continue;
        };
        let Some(value) = assignment.get(field) else {
            continue;
        };
        let index = u32::try_from(site.field_index).unwrap_or(u32::MAX);
        assignment.set_dt_select_witness(site_ctor, index, operand, value);
    }

    // `witnesses` is ordered by operand id, so an operand that itself reads an
    // abstracted selector sees that entry already recorded.
    for site in witnesses {
        // An operand that cannot be evaluated (an unbound symbol, say) simply
        // gets no entry: the replay below then reads the total convention's
        // default there and fails if that is not what the search assumed.
        let Ok(operand) = eval(arena, site.operand, assignment) else {
            continue;
        };
        let value = match assignment.get(site.witness) {
            Some(value) => value,
            // The witness never reached the reduced query (nothing constrained
            // it): any value will do, so take the total convention's.
            None => match well_founded_default(arena, site.field_sort) {
                Some(value) => value,
                None => continue,
            },
        };
        assignment.set_dt_select_witness(site.constructor, site.index, operand, value);
    }
}

/// Reconstructs a slot's `Value::Datatype` from the model: scalar fields from
/// their expansion variables, datatype fields from their linked child slot
/// (recursively) or the well-founded default if untraversed.
fn project_slot(
    arena: &TermArena,
    sym: SymbolId,
    scan: &Scan,
    layout: &BTreeMap<SymbolId, SymVars>,
    links: &Links,
    assignment: &axeyum_ir::Assignment,
    memo: &mut BTreeMap<SymbolId, Value>,
) -> Result<Value, SolverError> {
    if let Some(value) = memo.get(&sym) {
        return Ok(value.clone());
    }
    let dt = scan.dt_symbols[&sym];
    let vars = &layout[&sym];
    let tag = match assignment.get(vars.tag) {
        Some(Value::Bv { value, .. }) => usize::try_from(value).unwrap_or(usize::MAX),
        _ => {
            return Err(SolverError::Backend(
                "datatype expansion model lacks a tag value".to_owned(),
            ));
        }
    };
    let ctors = &scan.layouts[&dt];
    if tag >= ctors.len() {
        return Err(SolverError::Backend(
            "datatype tag out of constructor range in expansion model".to_owned(),
        ));
    }
    let (ctor, field_sorts) = &ctors[tag];
    let mut field_vals = Vec::with_capacity(field_sorts.len());
    for (i, &fsort) in field_sorts.iter().enumerate() {
        let value = match vars.fields[tag][i] {
            Some(field) => assignment.get(field).ok_or_else(|| {
                SolverError::Backend("datatype expansion model lacks a field value".to_owned())
            })?,
            None => match links.get(&(sym, tag, i)) {
                // Traversed datatype field: project the linked child slot.
                Some(&child) if scan.dt_symbols.contains_key(&child) => {
                    project_slot(arena, child, scan, layout, links, assignment, memo)?
                }
                // Untraversed (or unconstrained child): the well-founded default.
                _ => well_founded_default(arena, fsort).ok_or_else(|| {
                    SolverError::Backend(
                        "uninhabited datatype field has no default for projection".to_owned(),
                    )
                })?,
            },
        };
        field_vals.push(value);
    }
    let value = Value::Datatype {
        datatype: dt,
        constructor: *ctor,
        fields: field_vals,
    };
    memo.insert(sym, value.clone());
    Ok(value)
}

fn unsupported(what: &str) -> SolverError {
    SolverError::Unsupported(format!("{what} (ADR-0022)"))
}
