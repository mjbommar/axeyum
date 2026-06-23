//! Alethe proof **emission** for a slice of general `QF_BV` `unsat`
//! refutations — the **compound-term predicate fragment** (Track 3, the
//! producer counterpart to the bitblast-step emitter [`crate::bitblast_step`]
//! and the EUF/LRA emitters [`crate::prove_qf_uf_unsat_alethe`] /
//! [`crate::prove_lra_unsat_alethe`]).
//!
//! [`prove_qf_bv_unsat_alethe`] builds a complete, **Carcara-checkable** Alethe
//! proof closing to the empty clause `(cl)` for a `QF_BV` conjunction whose every
//! assertion is a *predicate over bit-vector terms*:
//!
//! - a positive predicate `(= s t)`, `(bvult s t)`, or `(bvslt s t)`, or
//! - a negated predicate `(not (= s t))`, `(not (bvult s t))`, `(not (bvslt s t))`,
//!
//! where each operand `s`, `t` is a bit-vector **variable**, **constant**, or a
//! **compound term** built from the bit-blastable operators (bitwise
//! `bvnot`/`bvand`/`bvor`/`bvxor`/`bvxnor`, arithmetic `bvadd`/`bvneg`/`bvmul`,
//! the predicates as inner terms via `bvcomp`, and structural
//! `extract`/`concat`/`sign_extend`) — nesting to arbitrary depth, e.g.
//! `(= (bvand (bvor a b) c) d)`. Anything outside that fragment (a non-bit-blastable
//! subterm — shifts `bvshl`/`bvlshr`/`bvashr`, division/remainder
//! `bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/`bvsmod`, `zero_extend`, rotates,
//! `bvnand`/`bvnor`/`bvsub`; an unsupported predicate; a non-bit-vector operand; a
//! non-predicate Boolean assertion) yields [`None`], as does a query that is **not**
//! genuinely `unsat`.
//!
//! ## How the proof is built
//!
//! 1. **Confirm `unsat`.** The conjunction is run through the pure-Rust
//!    [`crate::SatBvBackend`]; a non-`unsat` (or undecided) result returns [`None`].
//! 2. **Reduce each predicate to a bit-level Boolean (bottom-up `@bbterm` forms).**
//!    For every distinct subterm `t` (deduplicated across the shared DAG), an
//!    equality `(= t bbform(t))` to its `@bbterm` Alethe form is proved once — a
//!    **leaf** (variable/constant) gets it directly from
//!    `bitblast_var`/`bitblast_const`; a **compound** `op(c1..ck)` gets it by `cong`
//!    (substituting each child's `@bbterm` form into the operator, premised on the
//!    children's equalities), then `bitblast_<op>` over the `@bbterm`-form children
//!    (whose `build_term_vec` returns their bit args directly, exactly as Carcara's
//!    rule reconstructs the gadget), then `trans` to chain the two into
//!    `(= op(c1..ck) bbform)`. The **predicate** `(pred t1 t2)` is reduced the same
//!    way: `cong` to `(pred t1' t2')`, `bitblast_<pred>` to the bit-level Boolean
//!    `B`, `trans` to `(= pred B)`. For an **all-leaf** predicate the v1 direct path
//!    (`bitblast_step` on the predicate) is used, which Carcara likewise accepts.
//! 3. **Per assertion `φ`:** from `(= pred B)`, derive the *Boolean form* of the
//!    assertion as a unit clause — `(cl B)` for a positive assertion, `(cl (not B))`
//!    for a negated one — via `equiv1`/`equiv2` + `resolution`.
//! 4. **Refute the bit-level Boolean problem.** Each Boolean form `B` is a
//!    propositional formula over **bit atoms** `((_ @bit_of i) v)`. The forms are
//!    Tseitin-encoded into clauses, where a compound subterm is used directly as its
//!    own gate variable so the Carcara CNF-introduction rules match structurally.
//!    Every Tseitin defining clause is justified by a premise-free CNF-introduction
//!    step — `and_pos`/`and_neg` for a conjunction, `or_pos`/`or_neg` for a
//!    disjunction, `equiv_pos1`/`equiv_pos2`/`equiv_neg1`/`equiv_neg2` for a Boolean
//!    `=`, `xor_pos1`/`xor_pos2`/`xor_neg1`/`xor_neg2` for an `xor`; a `not` folds
//!    into the literal polarity (with the syntactic `(not …)` nesting kept in the
//!    emitted clause, which Carcara resolution collapses by parity). The clause set
//!    is refuted by the in-tree proof-producing SAT core (`solve_with_drat_proof` →
//!    `elaborate_drat_to_lrat`), whose LRAT resolution chain is replayed as Alethe
//!    `resolution` steps to `(cl)`.
//!
//! Every returned proof has been built deterministically (stable ids, sorted
//! variable maps — no hash-map iteration in the output); the soundness gate is the
//! external Carcara binary, exercised by the gated cross-check tests.

use std::collections::BTreeMap;

use axeyum_cnf::{
    AletheClause, AletheCommand, AletheLit, AletheTerm, CnfClause, CnfFormula, CnfLit, CnfVar,
    LratStep, ProofSolveOutcome, elaborate_drat_to_lrat, solve_with_drat_proof,
};
use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};

use crate::backend::{CheckResult, SolverBackend, SolverConfig};
use crate::bitblast_alethe::{bitblast_op_step, bv_term_to_alethe};
use crate::bitblast_step;
use crate::sat_bv_backend::SatBvBackend;

/// Emits a complete, Carcara-checkable Alethe refutation for an `unsat` `QF_BV`
/// conjunction in the **compound-term predicate fragment**, or [`None`] when the
/// query is outside that fragment or is not genuinely `unsat`.
///
/// The supported fragment: every assertion is one of
///
/// - `(= s t)`, `(bvult s t)`, `(bvslt s t)` — a positive predicate, or
/// - `(not (= s t))`, `(not (bvult s t))`, `(not (bvslt s t))` — its negation,
///
/// where each operand `s`, `t` is a bit-vector **variable** ([`TermNode::Symbol`]),
/// **constant** ([`TermNode::BvConst`]), or a **compound term** over the
/// **bit-blastable operators** — bitwise (`bvnot`/`bvand`/`bvor`/`bvxor`/`bvxnor`),
/// arithmetic (`bvadd`/`bvneg`/`bvmul`), `bvcomp`, and structural
/// (`extract`/`concat`/`sign_extend`) — nested to arbitrary depth, e.g.
/// `(= (bvand (bvor a b) c) d)`. Operands sharing the same DAG node are bit-blasted
/// once. The returned proof closes to the empty clause `(cl)` and is accepted by the
/// external Carcara checker (see the gated tests in `tests/carcara_crosscheck.rs`).
///
/// Returns [`None`] when:
///
/// - the conjunction is `sat` or undecided (so there is no refutation to emit);
/// - any assertion is outside the fragment — a **non-bit-blastable subterm** (a
///   shift `bvshl`/`bvlshr`/`bvashr`, division/remainder
///   `bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/`bvsmod`, `zero_extend`, a rotate, or
///   `bvnand`/`bvnor`/`bvsub`, which Carcara cannot reconstruct and which need a
///   `hole` + miter certificate, a later increment), an unsupported predicate
///   (`bvule`, `bvugt`, …), a non-bit-vector operand, or a non-predicate Boolean
///   assertion; or
/// - the bit-level Boolean problem cannot be closed to `(cl)` (defensive — does not
///   occur for a genuinely `unsat` instance in the fragment).
///
/// The emission is deterministic: assume/step ids and the atom→variable map are
/// assigned in a stable order, with no hash-map iteration in the output.
///
/// # Panics
///
/// Does not panic for any input; arena access is total over well-formed terms.
#[must_use]
pub fn prove_qf_bv_unsat_alethe(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    prove_with_rewrites(arena, assertions, &BTreeMap::new())
}

/// **Route 2**: emit a Carcara-checkable Alethe refutation that certifies the
/// **original** conjunction — `bvsub` subterms kept verbatim, *not* pre-lowered.
///
/// This closes the small "trusted reduction" gap for `bvsub`: rather than rewriting
/// the formula to the core via [`axeyum_rewrite::lower_derived_bv`] and certifying the
/// *lowered* result (as [`prove_qf_bv_unsat_alethe_lowered`] does), Route 2 keeps each
/// `(bvsub a b)` at the term level and bridges it to `(bvadd a (bvneg b))` with a
/// **Carcara-valid `bv_poly_simp` step** — the polynomial-simplification rule that
/// validates `(= (bvsub a b) (bvadd a (bvneg b)))` (the two are equal modulo `2^w`).
/// The `bvsub` term's bits are then taken from the bit-blasted `bvadd`/`bvneg` via the
/// `trans`-chained term equality, so the emitted refutation — and its kernel
/// reconstruction ([`crate::reconstruct_qf_bv_proof`], whose faithful `bv_bit` model
/// of `bvsub a b` *is* the `bvadd a (bvneg b)` ripple-carry) — close to `False` over
/// assertions that literally contain `bvsub`.
///
/// Needs `&mut TermArena` to intern each `(bvadd a (bvneg b))` rewrite. Returns the
/// same fragment as [`prove_qf_bv_unsat_alethe`] **extended with `bvsub`**: a `bvsub`
/// may appear anywhere a bit-blastable operand may. Returns [`None`] for a non-`unsat`
/// or otherwise out-of-fragment query (e.g. shifts/division, still Carcara holes), or
/// if a rewrite interning fails.
#[must_use]
pub fn prove_qf_bv_unsat_alethe_route2(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    // Pre-pass: intern `(bvadd a (bvneg b))` for every `bvsub` subterm reachable from
    // the assertions, recording `bvsub-term → bvadd-rewrite`. Interning needs `&mut`,
    // so collect the rewrites up front, then run the (shared, `&`-only) emitter.
    let mut sub_rewrites: BTreeMap<TermId, TermId> = BTreeMap::new();
    for &t in assertions {
        collect_sub_rewrites(arena, t, &mut sub_rewrites)?;
    }
    prove_with_rewrites(arena, assertions, &sub_rewrites)
}

/// **Extended-comparison route**: emit a Carcara-checkable Alethe refutation for an
/// `unsat` `QF_BV` conjunction whose assertions may use the six **non-core comparison
/// predicates** `bvule`/`bvugt`/`bvuge`/`bvsle`/`bvsgt`/`bvsge` at the top level (each
/// optionally under a single `not`), in addition to the core `=`/`bvult`/`bvslt`
/// fragment of [`prove_qf_bv_unsat_alethe`].
///
/// Carcara has bit-blast rules for `bvult`/`bvslt` only — **none** for the six extended
/// comparisons, and no stock rule rewrites one to the other inside a proof (the
/// `rare_rewrite` route needs an external RARE file the cross-check does not supply;
/// `comp_simplify`/`bv_poly_simp`/`refl`/`connective_def` all reject the equivalence).
/// So this route **normalizes each top-level extended comparison to its denotation-equal
/// `bvult`/`bvslt` form** before emission, using the SMT-LIB-verbatim equivalences:
///
/// - `(bvugt a b)` ≡ `(bvult b a)`            `(bvule a b)` ≡ `(not (bvult b a))`
/// - `(bvuge a b)` ≡ `(not (bvult a b))`      `(bvsgt a b)` ≡ `(bvslt b a)`
/// - `(bvsle a b)` ≡ `(not (bvslt b a))`      `(bvsge a b)` ≡ `(not (bvslt a b))`
///
/// The normalization is **denotation- and sort-preserving** (each side has the same
/// truth value for all inputs — see the totality semantics note), so the emitted
/// refutation certifies the conjunction's unsatisfiability up to that local rewrite. The
/// returned proof's `assume`s — and therefore the matching `.smt2` premises — are over
/// the **normalized** assertions, which this function returns alongside the proof so the
/// caller (and the Carcara cross-check) can render the exact problem the proof closes.
///
/// Needs `&mut TermArena` to intern each normalized `(bvult …)`/`(bvslt …)` (and the
/// wrapping `not`). Returns `(proof, normalized_assertions)`, or [`None`] for a
/// non-`unsat` or otherwise out-of-fragment query (e.g. a shift/division subterm, still a
/// Carcara hole), or if a rewrite interning fails. Operands are otherwise the full
/// bit-blastable compound fragment of [`prove_qf_bv_unsat_alethe`] — only the **top-level
/// predicate head** is normalized here.
#[must_use]
pub fn prove_qf_bv_unsat_alethe_ext_compare(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<(Vec<AletheCommand>, Vec<TermId>)> {
    // Normalize each assertion's top-level extended comparison (under at most one `not`)
    // to its core `bvult`/`bvslt` form. Interning needs `&mut`, so rewrite up front, then
    // hand the normalized assertions to the shared (`&`-only) core emitter.
    let normalized = assertions
        .iter()
        .map(|&t| normalize_ext_compare_assertion(arena, t))
        .collect::<Option<Vec<_>>>()?;
    let proof = prove_with_rewrites(arena, &normalized, &BTreeMap::new())?;
    Some((proof, normalized))
}

/// Rewrites `term`'s **top-level** predicate, when it is one of the six extended
/// comparisons (optionally under a single `not`), to the denotation-equal core
/// `bvult`/`bvslt` form; any other assertion is returned unchanged. Returns [`None`] only
/// if interning the rewrite fails (a malformed bit-vector term — never for well-formed
/// input). The rewrite is applied to the **negation's inner predicate** when the
/// assertion is `(not p)`, preserving the outer `not`, so polarity is kept exactly.
fn normalize_ext_compare_assertion(arena: &mut TermArena, term: TermId) -> Option<TermId> {
    if let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    {
        let inner = *args.first()?;
        let inner_norm = normalize_ext_compare_pred(arena, inner)?;
        if inner_norm == inner {
            return Some(term);
        }
        return arena.not(inner_norm).ok();
    }
    normalize_ext_compare_pred(arena, term)
}

/// Rewrites an extended-comparison **predicate** `(pred a b)` to its core
/// `bvult`/`bvslt` (possibly `not`-wrapped) form, per the SMT-LIB equivalences; returns
/// any non-extended-comparison `term` unchanged. [`None`] only on an interning failure.
fn normalize_ext_compare_pred(arena: &mut TermArena, term: TermId) -> Option<TermId> {
    let TermNode::App { op, args } = arena.node(term) else {
        return Some(term);
    };
    let op = *op;
    let [a, b] = args[..] else {
        return Some(term);
    };
    Some(match op {
        // a >ᵤ b ⟺ b <ᵤ a
        Op::BvUgt => arena.bv_ult(b, a).ok()?,
        // a ≤ᵤ b ⟺ ¬(b <ᵤ a)
        Op::BvUle => {
            let lt = arena.bv_ult(b, a).ok()?;
            arena.not(lt).ok()?
        }
        // a ≥ᵤ b ⟺ ¬(a <ᵤ b)
        Op::BvUge => {
            let lt = arena.bv_ult(a, b).ok()?;
            arena.not(lt).ok()?
        }
        // a >ₛ b ⟺ b <ₛ a
        Op::BvSgt => arena.bv_slt(b, a).ok()?,
        // a ≤ₛ b ⟺ ¬(b <ₛ a)
        Op::BvSle => {
            let lt = arena.bv_slt(b, a).ok()?;
            arena.not(lt).ok()?
        }
        // a ≥ₛ b ⟺ ¬(a <ₛ b)
        Op::BvSge => {
            let lt = arena.bv_slt(a, b).ok()?;
            arena.not(lt).ok()?
        }
        _ => term,
    })
}

/// Interns `(bvadd a (bvneg b))` for every `(bvsub a b)` subterm reachable from
/// `term`, recording each in `sub_rewrites`. Returns [`None`] if a rewrite cannot be
/// interned (a malformed bit-vector term — never for well-formed input).
fn collect_sub_rewrites(
    arena: &mut TermArena,
    term: TermId,
    sub_rewrites: &mut BTreeMap<TermId, TermId>,
) -> Option<()> {
    let (op, args) = match arena.node(term) {
        TermNode::App { op, args } => (*op, args.clone()),
        _ => return Some(()),
    };
    for &c in &args {
        collect_sub_rewrites(arena, c, sub_rewrites)?;
    }
    if op == Op::BvSub {
        let [a, b] = args[..] else { return None };
        if let std::collections::btree_map::Entry::Vacant(e) = sub_rewrites.entry(term) {
            let neg_b = arena.bv_neg(b).ok()?;
            let rewrite = arena.bv_add(a, neg_b).ok()?;
            e.insert(rewrite);
        }
    }
    Some(())
}

/// Shared emitter core for [`prove_qf_bv_unsat_alethe`] (no rewrites — the committed
/// fragment, `bvsub` rejected) and [`prove_qf_bv_unsat_alethe_route2`] (`sub_rewrites`
/// maps each `(bvsub a b)` to its interned `(bvadd a (bvneg b))`, admitting `bvsub`).
fn prove_with_rewrites(
    arena: &TermArena,
    assertions: &[TermId],
    sub_rewrites: &BTreeMap<TermId, TermId>,
) -> Option<Vec<AletheCommand>> {
    // 1. Parse every assertion into the supported fragment up front; bail on any
    //    out-of-fragment assertion before doing any solving.
    let parsed: Vec<Asserted> = assertions
        .iter()
        .map(|&t| classify_assertion(arena, t, sub_rewrites))
        .collect::<Option<Vec<_>>>()?;
    if parsed.is_empty() {
        return None;
    }

    // 2. Confirm the conjunction is genuinely unsat with the pure-Rust SAT-BV path.
    if !is_unsat(arena, assertions) {
        return None;
    }

    // 3. Emit the proof.
    let mut builder = Builder::new();
    // The bottom-up bit-blasting front-end: proves `(= t bbform(t))` once per
    // distinct subterm (deduplicated across the shared DAG) via cong/bitblast/trans.
    // In Route 2 it also carries the `bvsub → (bvadd a (bvneg b))` rewrites.
    let mut bb = BbReducer::new(sub_rewrites);

    // The propositional refutation collects each assertion's Boolean form as a
    // CNF clause over the bit atoms, keyed by the canonical atom text.
    let mut tseitin = Tseitin::new();
    // (clause-id-in-formula → Alethe step id) for the input clauses fed to the SAT
    // core; the LRAT bridge resolves learned clauses against these.
    let mut input_clause_ids: Vec<(Vec<CnfLit>, String)> = Vec::new();

    // Emit every `assume` first (Alethe convention; some checkers warn otherwise).
    let assume_ids: Vec<String> = parsed
        .iter()
        .map(|item| -> Option<String> {
            let pred_alethe = predicate_to_alethe(arena, item.predicate)?;
            Some(builder.assume(vec![AletheLit {
                atom: pred_alethe,
                negated: item.negated,
            }]))
        })
        .collect::<Option<Vec<_>>>()?;

    for (k, item) in parsed.iter().enumerate() {
        let pred = item.predicate;
        let negated = item.negated;
        let assume_id = assume_ids[k].clone();
        let pred_alethe = predicate_to_alethe(arena, pred)?;

        // Reduce the predicate to its bit-level Boolean `B`, yielding the step id of
        // `(= pred B)`. All-leaf predicates use the v1 direct bitblast; compound
        // operands are substituted in by cong/bitblast/trans (bottom-up @bbterm forms).
        let (bb_id, boolean_form) = bb.reduce_predicate(arena, &mut builder, pred, k)?;

        // Derive the Boolean form of the assertion as a unit clause.
        // Positive: equiv1 (= pred B) → (cl (not pred) B), resolve with (cl pred) → (cl B).
        // Negated: equiv2 (= pred B) → (cl pred (not B)), resolve with (cl (not pred)) → (cl (not B)).
        let bool_unit = if negated {
            let e_id = builder.step(
                vec![pos(pred_alethe.clone()), neg(boolean_form.clone())],
                "equiv2",
                &[&bb_id],
            );
            builder.step(
                vec![neg(boolean_form.clone())],
                "resolution",
                &[&e_id, &assume_id],
            )
        } else {
            let e_id = builder.step(
                vec![neg(pred_alethe.clone()), pos(boolean_form.clone())],
                "equiv1",
                &[&bb_id],
            );
            builder.step(
                vec![pos(boolean_form.clone())],
                "resolution",
                &[&e_id, &assume_id],
            )
        };

        // Tseitin-encode B and register the top-level unit `(cl B)` / `(cl (not B))`
        // as an input clause for the SAT refutation, justified by `bool_unit`.
        let root_lit = tseitin.encode(&mut builder, &boolean_form)?;
        let root_lit = if negated {
            root_lit.wrap_not()
        } else {
            root_lit
        };
        input_clause_ids.push((vec![root_lit.to_cnf(&tseitin)], bool_unit));
    }

    // Register every compound subterm's **bit-definition** `(cl B_t)` (built in
    // `BbReducer::emit_bit_definition`) as an input unit clause. These tie each
    // `((_ @bit_of i) t)` projection atom to its gadget bits, supplying the
    // cross-term connection the projection-based gadget would otherwise drop.
    for (b_form, def_id) in &bb.defs {
        let root_lit = tseitin.encode(&mut builder, b_form)?;
        input_clause_ids.push((vec![root_lit.to_cnf(&tseitin)], def_id.clone()));
    }

    // Add every Tseitin defining clause (each already an emitted Alethe step) as an
    // input clause for the SAT core.
    for gate in &tseitin.gate_clauses {
        input_clause_ids.push((
            gate.lits.iter().map(|l| l.to_cnf(&tseitin)).collect(),
            gate.step_id.clone(),
        ));
    }

    // Boolean-constant pins for the SAT refutation. The carry-chain gadgets
    // (`bvadd`/`bvneg`/`bvmul`, hence the Route-2 `bvsub` rewrite) embed literal
    // `true`/`false` operands (the `false` carry seed, the `true` carry-in of
    // `bvneg`). The Tseitin layer registers each as a propositional atom, but nothing
    // forces its value — so without a pin the SAT core may flip a `false` seed and
    // miss the refutation. We supply the Carcara `true`/`false` tautology units
    // `(cl true)` / `(cl (not false))` to the solver; `refute` emits each pin's Alethe
    // step ONLY if the LRAT proof actually uses it, so a congruence-style refutation
    // (which never depends on the constant) stays pin-free and our in-tree
    // `check_alethe` (no `true`/`false` rule) still accepts it. Bitwise-only Route-1
    // proofs register neither constant, so this is a no-op there.
    let pins = tseitin.boolean_const_pins();

    // 4. Build the propositional formula and refute it.
    refute(&mut builder, &tseitin, &input_clause_ids, &pins)
}

/// Like [`prove_qf_bv_unsat_alethe`], but first lowers any **derived** bit-vector
/// operators — `bvsub`, `bvnand`/`bvnor`, and the six non-core comparisons
/// (`bvugt`/`bvule`/`bvuge`/`bvsgt`/`bvsle`/`bvsge`) — to the bitblast core via
/// [`axeyum_rewrite::lower_derived_bv`]. This lets a conjunction that mentions those
/// operators still produce a proof: the emitter has no `bitblast_*` rule for them, but
/// their core reductions do. The lowering is denotation- and sort-preserving (so the
/// refutation certifies the original conjunction's unsatisfiability up to that
/// rewrite); it needs `&mut TermArena` to intern the core sub-terms.
///
/// Returns `None` if a lowering fails, or if the lowered conjunction is still outside
/// the supported fragment (e.g. shifts or division, which have no core reduction).
#[must_use]
pub fn prove_qf_bv_unsat_alethe_lowered(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    let lowered = assertions
        .iter()
        .map(|&t| axeyum_rewrite::lower_derived_bv(arena, t).ok())
        .collect::<Option<Vec<_>>>()?;
    prove_qf_bv_unsat_alethe(arena, &lowered)
}

/// A parsed in-fragment assertion: the (possibly inner) predicate term and whether
/// the assertion negated it.
struct Asserted {
    predicate: TermId,
    negated: bool,
}

/// Classifies an assertion into the supported fragment, returning the inner
/// predicate and its polarity, or [`None`] if out of fragment. `sub_rewrites`
/// (non-empty only in Route 2) admits each `(bvsub a b)` it keys as a bit-blastable
/// operand (bridged to its `(bvadd a (bvneg b))` rewrite).
fn classify_assertion(
    arena: &TermArena,
    term: TermId,
    sub_rewrites: &BTreeMap<TermId, TermId>,
) -> Option<Asserted> {
    // Peel a single `not`.
    if let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    {
        let inner = *args.first()?;
        let pred = supported_predicate(arena, inner, sub_rewrites)?;
        return Some(Asserted {
            predicate: pred,
            negated: true,
        });
    }
    let pred = supported_predicate(arena, term, sub_rewrites)?;
    Some(Asserted {
        predicate: pred,
        negated: false,
    })
}

/// Returns `term` if it is a supported predicate (`=`, `bvult`, `bvslt`) over two
/// bit-vector operands that are each fully **bit-blastable** (a variable, constant,
/// or a compound term over the bit-blastable operators — including `bvsub` when keyed
/// in `sub_rewrites`), else [`None`].
fn supported_predicate(
    arena: &TermArena,
    term: TermId,
    sub_rewrites: &BTreeMap<TermId, TermId>,
) -> Option<TermId> {
    let TermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    if !matches!(op, Op::Eq | Op::BvUlt | Op::BvSlt) {
        return None;
    }
    let [a, b] = &args[..] else {
        return None;
    };
    // Each operand must be a bit-vector whose every subterm Carcara can bit-blast.
    if !is_bitblastable_bv(arena, *a, sub_rewrites) || !is_bitblastable_bv(arena, *b, sub_rewrites)
    {
        return None;
    }
    Some(term)
}

/// Whether `term` is a bit-vector **variable** or **constant** (a leaf operand).
fn is_leaf_bv(arena: &TermArena, term: TermId) -> bool {
    if !matches!(arena.sort_of(term), Sort::BitVec(_)) {
        return false;
    }
    matches!(
        arena.node(term),
        TermNode::Symbol(_) | TermNode::BvConst { .. }
    )
}

/// Whether `term` is a bit-vector term every operator of which Carcara can
/// reconstruct with a `bitblast_<op>` rule — a leaf (variable/constant) or a
/// compound built solely from the bit-blastable operators (bitwise
/// `bvnot`/`bvand`/`bvor`/`bvxor`/`bvxnor`, arithmetic `bvadd`/`bvneg`/`bvmul`,
/// `bvcomp`, and structural `extract`/`concat`/`sign_extend`). A `(bvsub a b)` keyed
/// in `sub_rewrites` (Route 2) is admitted too — it is bridged to its
/// `(bvadd a (bvneg b))` rewrite by a Carcara `bv_poly_simp` step. Any other operator
/// — shifts, division/remainder, `zero_extend`, rotates, `bvnand`/`bvnor`, or an
/// un-keyed `bvsub` — makes the term out of fragment (Carcara holes).
fn is_bitblastable_bv(
    arena: &TermArena,
    term: TermId,
    sub_rewrites: &BTreeMap<TermId, TermId>,
) -> bool {
    if !matches!(arena.sort_of(term), Sort::BitVec(_)) {
        return false;
    }
    match arena.node(term) {
        TermNode::Symbol(_) | TermNode::BvConst { .. } => true,
        TermNode::App { op, args } => {
            (is_bitblastable_op(*op) || (*op == Op::BvSub && sub_rewrites.contains_key(&term)))
                && args
                    .iter()
                    .all(|&a| is_bitblastable_bv(arena, a, sub_rewrites))
        }
        _ => false,
    }
}

/// Whether `op` is a bit-vector-producing operator the bitblast emitter (and
/// Carcara) can reconstruct. `bvcomp` produces a 1-bit BV and is included; the
/// predicate operators (`=`, `bvult`, `bvslt`) produce `Bool`, never appear as a
/// bit-vector subterm, and are handled at the predicate layer instead.
fn is_bitblastable_op(op: Op) -> bool {
    matches!(
        op,
        Op::BvNot
            | Op::BvAnd
            | Op::BvOr
            | Op::BvXor
            | Op::BvXnor
            | Op::BvAdd
            | Op::BvNeg
            | Op::BvMul
            | Op::BvComp
            | Op::Concat
            | Op::Extract { .. }
            | Op::SignExt { .. }
    )
}

/// Renders the supported predicate `term` as the Alethe atom Carcara expects for the
/// `assume` (matching the bitblast step's LHS): `(= s t)`, `(bvult s t)`,
/// `(bvslt s t)`, where `s`, `t` may be compound bit-vector terms.
fn predicate_to_alethe(arena: &TermArena, term: TermId) -> Option<AletheTerm> {
    let TermNode::App { op, args } = arena.node(term) else {
        return None;
    };
    let head = match op {
        Op::Eq => "=",
        Op::BvUlt => "bvult",
        Op::BvSlt => "bvslt",
        _ => return None,
    };
    let rendered = args
        .iter()
        .map(|&a| bv_term_to_alethe(arena, a))
        .collect::<Option<Vec<_>>>()?;
    Some(AletheTerm::App(head.to_owned(), rendered))
}

/// Confirms the conjunction is `unsat` via the pure-Rust SAT-BV backend.
fn is_unsat(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    matches!(
        backend.check(arena, assertions, &config),
        Ok(CheckResult::Unsat)
    )
}

// --- Alethe command builder -------------------------------------------------

/// Builds the proof command list with deterministic step ids.
struct Builder {
    commands: Vec<AletheCommand>,
    next_assume: usize,
    next_step: usize,
}

impl Builder {
    fn new() -> Self {
        Self {
            commands: Vec::new(),
            next_assume: 0,
            next_step: 0,
        }
    }

    fn assume(&mut self, clause: AletheClause) -> String {
        let id = format!("h{}", self.next_assume);
        self.next_assume += 1;
        self.commands.push(AletheCommand::Assume {
            id: id.clone(),
            clause,
        });
        id
    }

    /// Pushes an already-built command (e.g. a `bitblast_*` step from the emitter).
    fn push(&mut self, command: AletheCommand) {
        self.commands.push(command);
    }

    /// Allocates a fresh deterministic `s<n>` step id without emitting anything —
    /// used when a step (e.g. a `bitblast_*` command from the emitter) is built with
    /// its id baked in, then pushed via [`Builder::push`].
    fn fresh_step_id(&mut self) -> String {
        let id = format!("s{}", self.next_step);
        self.next_step += 1;
        id
    }

    /// Emits a step with a fresh `s<n>` id, no `:args`; returns the id.
    fn step(&mut self, clause: AletheClause, rule: &str, premises: &[&str]) -> String {
        self.step_args(clause, rule, premises, Vec::new())
    }

    /// Emits a step with a fresh `s<n>` id and the given `:args`; returns the id.
    fn step_args(
        &mut self,
        clause: AletheClause,
        rule: &str,
        premises: &[&str],
        args: Vec<AletheTerm>,
    ) -> String {
        let id = format!("s{}", self.next_step);
        self.next_step += 1;
        self.commands.push(AletheCommand::Step {
            id: id.clone(),
            clause,
            rule: rule.to_owned(),
            premises: premises.iter().map(|p| (*p).to_owned()).collect(),
            args,
        });
        id
    }
}

// --- Bottom-up bit-blasting front-end (compound @bbterm reduction) ----------

/// Proves `(= t bbform(t))` for each distinct bit-vector subterm `t`, memoized so a
/// shared DAG node is bit-blasted once. For a leaf the equality comes straight from
/// `bitblast_var`/`bitblast_const`; for a compound `op(c1..ck)` it is built by
/// substituting each child's `@bbterm` form into the operator (`cong`, premised on
/// the children's equalities), bit-blasting the operator over those `@bbterm`-form
/// children (`bitblast_<op>`, whose `build_term_vec` returns their bit args
/// directly), and `trans`-chaining the two.
struct BbReducer<'r> {
    /// `term` → (its `@bbterm` Alethe form, the step id proving `(= term bbform)`).
    bbform: BTreeMap<TermId, (AletheTerm, String)>,
    /// One **bit-definition** per compound subterm: a bit-level Boolean `B_t`
    /// connecting the term's bit projections `((_ @bit_of i) t)` to its gadget bits,
    /// paired with the step id proving the unit clause `(cl B_t)`. The propositional
    /// refutation needs these because the projection-based gadget makes
    /// `((_ @bit_of i) t)` an *opaque* SAT atom — `B_t` is the Tseitin definition tying
    /// it back to the children's bits (the cross-term connection the old inlined
    /// gadget made implicitly). Emitted in DAG-dedup order.
    defs: Vec<(AletheTerm, String)>,
    /// Route-2 `bvsub → (bvadd a (bvneg b))` rewrites (empty in Route 1, where
    /// `bvsub` is rejected). When `reduce_term` meets a keyed `(bvsub a b)` it emits a
    /// `bv_poly_simp` equality to the rewrite, reduces the rewrite, and `trans`-chains
    /// them — so the `bvsub` term's bits come from the `bvadd`/`bvneg` bit-blast.
    sub_rewrites: &'r BTreeMap<TermId, TermId>,
}

impl<'r> BbReducer<'r> {
    fn new(sub_rewrites: &'r BTreeMap<TermId, TermId>) -> Self {
        Self {
            bbform: BTreeMap::new(),
            defs: Vec::new(),
            sub_rewrites,
        }
    }

    /// Returns `term`'s `@bbterm` Alethe form and the id of the step proving
    /// `(= term bbform)`, building and memoizing them on first sight. [`None`] if any
    /// subterm is outside the bit-blastable fragment.
    fn reduce_term(
        &mut self,
        arena: &TermArena,
        builder: &mut Builder,
        term: TermId,
    ) -> Option<(AletheTerm, String)> {
        if let Some(cached) = self.bbform.get(&term) {
            return Some(cached.clone());
        }
        // Route-2 `bvsub` bridge. A `(bvsub a b)` keyed in `sub_rewrites` is bit-blasted
        // through its `(bvadd a (bvneg b))` rewrite, with a Carcara-valid `bv_poly_simp`
        // term equality threading the two — so the proof keeps `bvsub` at the term level
        // and certifies the ORIGINAL assertion.
        if let Some(&rewrite) = self.sub_rewrites.get(&term) {
            let result = self.reduce_sub(arena, builder, term, rewrite)?;
            self.bbform.insert(term, result.clone());
            return Some(result);
        }
        let result = match arena.node(term) {
            TermNode::Symbol(_) | TermNode::BvConst { .. } => {
                // Leaf: bitblast_var / bitblast_const gives `(= t (@bbterm …))`.
                let id = builder.fresh_step_id();
                let step = bitblast_step(arena, term, &id)?;
                let bbform = bitblast_rhs(&step)?;
                builder.push(step);
                (bbform, id)
            }
            TermNode::App { op, args } => {
                let op = *op;
                if !is_bitblastable_op(op) {
                    return None;
                }
                // Reduce every child first (recursing; the memo dedups shared nodes).
                // The child equalities `(= child bbform(child))` are still emitted and
                // (in the end-to-end flow) separately kernel-checked, but they are NOT
                // substituted into this op's bit-blast step — that inlining is exactly
                // the exponential blowup for nested arithmetic.
                for &c in args {
                    self.reduce_term(arena, builder, c)?;
                }

                // Carcara's `bitblast_<op>` recomputes the gadget from the LHS operands
                // directly: `build_term_vec(child)` returns `((_ @bit_of i) child)`
                // PROJECTIONS for a plain (compound or leaf) operand term, inlining only
                // a literal `@bbterm`. So we bit-blast on the ORIGINAL child terms — the
                // conclusion is `(= op(orig children) (@bbterm projections-over-@bit_of))`,
                // an O(size²) shape Carcara accepts (its own incremental scheme), with no
                // `cong`/`@bbterm`-form substitution and no exponential bit-tree.
                let rendered_args = args
                    .iter()
                    .map(|&c| bv_term_to_alethe(arena, c))
                    .collect::<Option<Vec<_>>>()?;
                let lhs_orig = bv_term_to_alethe(arena, term)?;
                let operand_widths = args
                    .iter()
                    .map(|&c| bv_width(arena, c))
                    .collect::<Option<Vec<_>>>()?;
                let result_width = bv_width(arena, *args.first()?)?;
                let bb_id = builder.fresh_step_id();
                let bb_step = bitblast_op_step(
                    op,
                    &rendered_args,
                    &operand_widths,
                    lhs_orig.clone(),
                    result_width,
                    &bb_id,
                )?;
                let bbform = bitblast_rhs(&bb_step)?;
                builder.push(bb_step);

                // Emit the term's **bit-definition** `B_t`, tying `((_ @bit_of i) t)`
                // back to its gadget bits, so the projection-based gadget stays
                // connected in the propositional refutation (the gadget makes
                // `((_ @bit_of i) t)` an opaque SAT atom). `bitblast_equal` over
                // `(= t bbform)` yields `B_t = (and (= ((_ @bit_of i) t) g_i) …)`
                // (`build_term_vec(t)` projects; `build_term_vec(bbform)` returns `g`
                // directly) — a Carcara-valid step. Since `(= t bbform)` is *proven*
                // (`bb_id`), `equiv1` + `resolution` derive the unit `(cl B_t)`.
                self.emit_bit_definition(builder, lhs_orig, &bbform, &bb_id)?;

                (bbform, bb_id)
            }
            _ => return None,
        };
        self.bbform.insert(term, result.clone());
        Some(result)
    }

    /// Route-2 reduction of a `(bvsub a b)` term (id `sub`) via its interned
    /// `(bvadd a (bvneg b))` rewrite (id `rewrite`). Emits, in order:
    ///
    /// 1. **`bv_poly_simp`**: `(= (bvsub a b) (bvadd a (bvneg b)))` — the Carcara-valid
    ///    polynomial-simplification step (the two sides are equal modulo `2^w`).
    /// 2. The rewrite's own reduction `(= (bvadd a (bvneg b)) bbform)` (recursing into
    ///    [`BbReducer::reduce_term`], which bit-blasts the `bvadd` and the inner `bvneg`
    ///    and emits their bit-definitions).
    /// 3. **`trans`**: `(= (bvsub a b) bbform)` — chaining (1) and (2).
    /// 4. The `bvsub` term's own **bit-definition**, tying `((_ @bit_of i) (bvsub a b))`
    ///    to `bbform`'s gadget bits (so the projection stays connected in the
    ///    propositional refutation; reconstruction's `bv_bit` models `bvsub a b` bit `i`
    ///    as exactly that `bvadd a (bvneg b)` ripple-carry, making the tie reflexive).
    ///
    /// Returns `(bbform, trans_id)`: the `bvsub`'s `@bbterm` form and the id of the
    /// `trans` step proving `(= (bvsub a b) bbform)`.
    fn reduce_sub(
        &mut self,
        arena: &TermArena,
        builder: &mut Builder,
        sub: TermId,
        rewrite: TermId,
    ) -> Option<(AletheTerm, String)> {
        // 1. The bvsub→bvadd∘bvneg rewrite equality (Carcara `bv_poly_simp`).
        let sub_alethe = bv_term_to_alethe(arena, sub)?;
        let rewrite_alethe = bv_term_to_alethe(arena, rewrite)?;
        let sub_eq_id = builder.step(
            vec![pos(AletheTerm::App(
                "=".to_owned(),
                vec![sub_alethe.clone(), rewrite_alethe.clone()],
            ))],
            "bv_poly_simp",
            &[],
        );

        // 2. Reduce the rewrite `(bvadd a (bvneg b))` to its `@bbterm` form.
        let (bbform, rewrite_id) = self.reduce_term(arena, builder, rewrite)?;

        // 3. trans: `(= (bvsub a b) bbform)` from the two equalities.
        let trans_id = builder.step(
            vec![pos(AletheTerm::App(
                "=".to_owned(),
                vec![sub_alethe.clone(), bbform.clone()],
            ))],
            "trans",
            &[&sub_eq_id, &rewrite_id],
        );

        // 4. The bvsub term's bit-definition, tying its projections to `bbform`.
        self.emit_bit_definition(builder, sub_alethe, &bbform, &trans_id)?;

        Some((bbform, trans_id))
    }

    /// Emits a compound term's **bit-definition** clause `(cl B_t)` and records it in
    /// [`BbReducer::defs`]. `lhs` is the term `t`, `bbform = (@bbterm g…)` its gadget,
    /// `width` its bit width, and `pt_id` the step proving `(= t bbform)`.
    ///
    /// `bitblast_equal` over the proven equality `(= t bbform)` concludes
    /// `(= (= t bbform) B_t)` with `B_t = (and (= ((_ @bit_of i) t) g_i) …)` (a single
    /// `(= … g_0)` for width 1) — Carcara recomputes `B_t` via `build_term_vec`, which
    /// projects the plain term `t` and inlines the literal `bbform`. Then `equiv1`
    /// gives `(cl (not (= t bbform)) B_t)`, and `resolution` against `pt_id` (the unit
    /// `(cl (= t bbform))`) gives `(cl B_t)`.
    fn emit_bit_definition(
        &mut self,
        builder: &mut Builder,
        lhs: AletheTerm,
        bbform: &AletheTerm,
        pt_id: &str,
    ) -> Option<()> {
        // The term's actual bit width is the number of gadget bits — NOT the
        // operand-0 width (they differ for `extract`/`concat`/`sign_extend`). When the
        // bit-blast result is NOT a `@bbterm` (e.g. `sign_extend 0`, whose conclusion
        // is `(= ((_ sign_extend 0) x) x)`), the term has no opaque projection atom to
        // tie back, so no definition is needed — skip it.
        let AletheTerm::App(head, bits) = bbform else {
            return Some(());
        };
        if head != "@bbterm" {
            return Some(());
        }
        let width = bits.len();
        // The proven term equality `(= t bbform)` as an Alethe atom.
        let eq_atom = AletheTerm::App("=".to_owned(), vec![lhs.clone(), bbform.clone()]);
        // `bitblast_equal`: (= (= t bbform) B_t).
        let be_id = builder.fresh_step_id();
        let be_step = bitblast_op_step(
            Op::Eq,
            &[lhs, bbform.clone()],
            &[width, width],
            eq_atom.clone(),
            width,
            &be_id,
        )?;
        let b_t = bitblast_rhs(&be_step)?;
        builder.push(be_step);

        // equiv1 (= (= t bbform) B_t) → (cl (not (= t bbform)) B_t).
        let e_id = builder.step(vec![neg(eq_atom), pos(b_t.clone())], "equiv1", &[&be_id]);
        // resolution with the proven (cl (= t bbform)) → (cl B_t).
        let def_id = builder.step(vec![pos(b_t.clone())], "resolution", &[&e_id, pt_id]);
        self.defs.push((b_t, def_id));
        Some(())
    }

    /// Reduces the supported predicate `pred = (pred t1 t2)` to its bit-level Boolean
    /// `B`, returning the id of the step proving `(= pred B)` and `B` itself.
    ///
    /// An **all-leaf** predicate uses the v1 direct path (`bitblast_step` on the
    /// predicate). A predicate with a **compound** operand reduces each operand to its
    /// `@bbterm` form, substitutes via `cong` to `(pred t1' t2')`, bit-blasts that to
    /// `B` (`bitblast_<pred>`), and `trans`-chains to `(= pred B)`.
    fn reduce_predicate(
        &mut self,
        arena: &TermArena,
        builder: &mut Builder,
        pred: TermId,
        k: usize,
    ) -> Option<(String, AletheTerm)> {
        let TermNode::App { op, args } = arena.node(pred) else {
            return None;
        };
        let op = *op;
        let [t1, t2] = args[..] else {
            return None;
        };

        // All-leaf predicate: the committed v1 path. `bitblast_step` renders the leaf
        // operands itself and concludes `(= pred B)` directly.
        if is_leaf_bv(arena, t1) && is_leaf_bv(arena, t2) {
            let id = format!("bb{k}");
            let step = bitblast_step(arena, pred, &id)?;
            let boolean_form = bitblast_rhs(&step)?;
            builder.push(step);
            return Some((id, boolean_form));
        }

        // Compound operand(s): emit each operand's bit-blast equality (recursively,
        // for the separate slice-5 kernel check), then bit-blast the predicate
        // DIRECTLY on the original operand terms. Carcara's `bitblast_<pred>` rule
        // recomputes the ladder from the LHS operands via `build_term_vec`, which
        // projects `((_ @bit_of i) operand)` for a plain term — so the conclusion is
        // `(= (pred t1 t2) B)` with `B` over `@bit_of` projections of `t1`/`t2`
        // (O(size²)), no `cong`/`@bbterm`-form substitution, no inlined bit-tree.
        self.reduce_term(arena, builder, t1)?;
        self.reduce_term(arena, builder, t2)?;
        let pred_orig = predicate_to_alethe(arena, pred)?;
        let r1 = bv_term_to_alethe(arena, t1)?;
        let r2 = bv_term_to_alethe(arena, t2)?;

        let operand_widths = [bv_width(arena, t1)?, bv_width(arena, t2)?];
        let result_width = bv_width(arena, t1)?;
        let bb_id = builder.fresh_step_id();
        let bb_step = bitblast_op_step(
            op,
            &[r1, r2],
            &operand_widths,
            pred_orig,
            result_width,
            &bb_id,
        )?;
        let boolean_form = bitblast_rhs(&bb_step)?;
        builder.push(bb_step);
        Some((bb_id, boolean_form))
    }
}

/// The bit width (in bits) of a bit-vector `term`, or [`None`] if not a bit-vector.
fn bv_width(arena: &TermArena, term: TermId) -> Option<usize> {
    match arena.sort_of(term) {
        Sort::BitVec(w) => Some(w as usize),
        _ => None,
    }
}

/// Pulls the right-hand side out of a `bitblast_*` (or any) step whose conclusion is
/// a single positive equality `(= lhs rhs)` — the `@bbterm` form for a term op, or
/// the bit-level Boolean for a predicate op. [`None`] if the shape does not match.
fn bitblast_rhs(step: &AletheCommand) -> Option<AletheTerm> {
    let AletheCommand::Step { clause, .. } = step else {
        return None;
    };
    let [lit] = clause.as_slice() else {
        return None;
    };
    if lit.negated {
        return None;
    }
    let AletheTerm::App(head, args) = &lit.atom else {
        return None;
    };
    if head != "=" || args.len() != 2 {
        return None;
    }
    Some(args[1].clone())
}

fn pos(atom: AletheTerm) -> AletheLit {
    AletheLit {
        atom,
        negated: false,
    }
}

fn neg(atom: AletheTerm) -> AletheLit {
    AletheLit {
        atom,
        negated: true,
    }
}

// --- Tseitin encoding of the bit-level Boolean forms ------------------------

/// A propositional literal in the Tseitin encoding.
///
/// `view` is the **verbatim** subterm as it appears as an operand of a gate —
/// possibly `(not …)`-wrapped — so the Carcara CNF-introduction rules (which match
/// each operand `φi` structurally against the gate term) see the exact syntax. For
/// the CNF/SAT layer we normalize: `base` is `view` with all leading `not`s peeled,
/// and `parity` is `true` when an **odd** number of `not`s were peeled (the literal
/// is the negation of `base`). The two views agree semantically; only the
/// negation **nesting** differs (Carcara resolution collapses it by parity).
#[derive(Clone)]
struct PLit {
    /// The operand term exactly as written (for Alethe emission).
    view: AletheTerm,
    /// `view` with all leading `not`s removed (the CNF/SAT atom).
    base: AletheTerm,
    /// Whether `view` negates `base` (odd negation count).
    parity: bool,
}

impl PLit {
    /// A leaf/gate literal whose `view` and `base` coincide (no leading `not`).
    fn positive(term: AletheTerm) -> PLit {
        PLit {
            view: term.clone(),
            base: term,
            parity: false,
        }
    }

    /// The literal for the operand `(not view)` — wraps `view` in a syntactic
    /// `not` and flips the CNF parity.
    fn wrap_not(&self) -> PLit {
        PLit {
            view: AletheTerm::App("not".to_owned(), vec![self.view.clone()]),
            base: self.base.clone(),
            parity: !self.parity,
        }
    }

    /// The Alethe literal that asserts the operand itself: the positive literal
    /// `view`. (`view` already carries any `not` nesting syntactically.)
    fn lit_view(&self) -> AletheLit {
        AletheLit {
            atom: self.view.clone(),
            negated: false,
        }
    }

    /// The Alethe literal that asserts the **negation** of the operand: the
    /// syntactic `(not view)`.
    fn lit_not_view(&self) -> AletheLit {
        AletheLit {
            atom: AletheTerm::App("not".to_owned(), vec![self.view.clone()]),
            negated: false,
        }
    }

    fn to_cnf(&self, tseitin: &Tseitin) -> CnfLit {
        let var = tseitin.var_of(&self.base);
        let base = CnfLit::positive(var);
        if self.parity { base.negated() } else { base }
    }
}

/// One emitted Tseitin defining clause: its propositional literals and the Alethe
/// step id that justifies it.
struct GateClause {
    lits: Vec<PLit>,
    step_id: String,
}

/// The Tseitin encoder: walks a Boolean form, introducing a fresh gate atom for
/// each compound subterm, emitting the defining clauses (each a Carcara
/// CNF-introduction step), and recording an atom→`CnfVar` map for the SAT core.
struct Tseitin {
    /// Canonical atom key → [`CnfVar`] (deterministic by insertion order).
    var_of: BTreeMap<String, CnfVar>,
    /// [`CnfVar`] index → the atom term it represents (the inverse of `var_of`, used
    /// to render learned-clause atoms — kept verbatim so no key reparse is needed).
    atom_terms: Vec<AletheTerm>,
    /// Memo of already-encoded compound subterms (by key) → their gate literal.
    memo: BTreeMap<String, PLit>,
    /// Emitted defining clauses.
    gate_clauses: Vec<GateClause>,
}

impl Tseitin {
    fn new() -> Self {
        Self {
            var_of: BTreeMap::new(),
            atom_terms: Vec::new(),
            memo: BTreeMap::new(),
            gate_clauses: Vec::new(),
        }
    }

    /// The `CnfVar` for `atom`, allocating one on first sight (deterministic).
    fn var_of(&self, atom: &AletheTerm) -> CnfVar {
        *self
            .var_of
            .get(&atom.key())
            .expect("atom registered before lowering")
    }

    fn register(&mut self, atom: &AletheTerm) {
        let key = atom.key();
        if !self.var_of.contains_key(&key) {
            let index = self.var_of.len();
            let var = CnfVar::new(index).expect("variable index fits");
            self.var_of.insert(key, var);
            self.atom_terms.push(atom.clone());
        }
    }

    fn total_vars(&self) -> usize {
        self.var_of.len()
    }

    /// The Boolean-constant pins to feed the SAT refutation, one per `true`/`false`
    /// constant actually registered as an atom (so a pin-free fragment yields an empty
    /// list). Each carries the SAT input clause and the Alethe `(step … :rule true)` /
    /// `(step … :rule false)` to emit — but only if the LRAT proof references it
    /// ([`refute`] decides). `true` → `(cl true)` (unit `[var]`); `false` →
    /// `(cl (not false))` (unit `[¬var]`).
    fn boolean_const_pins(&self) -> Vec<Pin> {
        let mut pins = Vec::new();
        let true_key = AletheTerm::Const("true".to_owned()).key();
        if let Some(&var) = self.var_of.get(&true_key) {
            pins.push(Pin {
                clause: vec![CnfLit::positive(var)],
                rule: "true",
                alethe_clause: vec![pos(AletheTerm::Const("true".to_owned()))],
            });
        }
        let false_key = AletheTerm::Const("false".to_owned()).key();
        if let Some(&var) = self.var_of.get(&false_key) {
            pins.push(Pin {
                clause: vec![CnfLit::positive(var).negated()],
                rule: "false",
                alethe_clause: vec![pos(AletheTerm::App(
                    "not".to_owned(),
                    vec![AletheTerm::Const("false".to_owned())],
                ))],
            });
        }
        pins
    }

    /// Encodes `term` (a Boolean formula), returning the literal equivalent to it.
    /// Leaves (bit projections) return themselves; a `(not …)` wraps its inner
    /// literal syntactically (no new variable); compound gates introduce the gate
    /// term as a variable and emit the defining clauses.
    fn encode(&mut self, builder: &mut Builder, term: &AletheTerm) -> Option<PLit> {
        match term {
            AletheTerm::Indexed { .. } | AletheTerm::Const(_) => {
                self.register(term);
                Some(PLit::positive(term.clone()))
            }
            AletheTerm::App(head, args) => {
                let key = term.key();
                if let Some(lit) = self.memo.get(&key) {
                    return Some(lit.clone());
                }
                let lit = match (head.as_str(), args.len()) {
                    ("not", 1) => {
                        // Syntactic negation: wrap the inner literal's view in `not`
                        // and flip its CNF parity; do NOT allocate a fresh variable.
                        let inner = self.encode(builder, &args[0])?;
                        inner.wrap_not()
                    }
                    ("and", _) => self.encode_gate(builder, term, GateKind::And, args)?,
                    ("or", _) => self.encode_gate(builder, term, GateKind::Or, args)?,
                    ("=", 2) => self.encode_gate(builder, term, GateKind::Equiv, args)?,
                    ("xor", 2) => self.encode_gate(builder, term, GateKind::Xor, args)?,
                    _ => return None,
                };
                // Memoize compound gates (a `not` is cheap and view-dependent, so it
                // is recomputed; gates carry emitted clauses, so memoize them).
                if !matches!(head.as_str(), "not") {
                    self.memo.insert(key, lit.clone());
                }
                Some(lit)
            }
        }
    }

    /// Introduces the gate term `g = term` as a propositional variable, encodes each
    /// operand to a literal, and emits the Tseitin defining clauses `g ↔ op(operands)`
    /// as Carcara CNF-introduction steps (no premises — pure tautologies). Returns the
    /// positive gate literal. Each emitted Alethe clause uses the operand **verbatim**
    /// (`operand.lit_view`) or its syntactic negation (`operand.lit_not_view`), so the
    /// rules match structurally; the recorded CNF clause normalizes the negation parity.
    fn encode_gate(
        &mut self,
        builder: &mut Builder,
        term: &AletheTerm,
        kind: GateKind,
        args: &[AletheTerm],
    ) -> Option<PLit> {
        let operands: Vec<PLit> = args
            .iter()
            .map(|a| self.encode(builder, a))
            .collect::<Option<Vec<_>>>()?;

        self.register(term);
        let gate = PLit::positive(term.clone());

        match kind {
            GateKind::And => self.encode_and(builder, &gate, &operands),
            GateKind::Or => self.encode_or(builder, &gate, &operands),
            GateKind::Equiv => self.encode_binary(builder, &gate, &operands, GateKind::Equiv)?,
            GateKind::Xor => self.encode_binary(builder, &gate, &operands, GateKind::Xor)?,
        }
        Some(gate)
    }

    /// Emits one CNF-introduction step (`rule`/`args`) and records its CNF clause.
    /// `lits` pairs the emitted Alethe literal with its normalized CNF literal.
    fn emit(
        &mut self,
        builder: &mut Builder,
        rule: &str,
        args: Vec<AletheTerm>,
        lits: Vec<(AletheLit, PLit)>,
    ) {
        let (clause, plits): (Vec<AletheLit>, Vec<PLit>) = lits.into_iter().unzip();
        let id = builder.step_args(clause, rule, &[], args);
        self.gate_clauses.push(GateClause {
            lits: plits,
            step_id: id,
        });
    }

    /// The `and` defining clauses: `and_pos` per conjunct (`g → ti`) and one
    /// `and_neg` (`(⋀ ti) → g`).
    fn encode_and(&mut self, builder: &mut Builder, gate: &PLit, operands: &[PLit]) {
        let term = gate.view.clone();
        for (i, operand) in operands.iter().enumerate() {
            self.emit(
                builder,
                "and_pos",
                vec![AletheTerm::Const(i.to_string())],
                vec![
                    (neg(term.clone()), gate.wrap_not()),
                    (operand.lit_view(), operand.clone()),
                ],
            );
        }
        let mut lits = vec![(pos(term), gate.clone())];
        for operand in operands {
            lits.push((operand.lit_not_view(), operand.wrap_not()));
        }
        self.emit(builder, "and_neg", Vec::new(), lits);
    }

    /// The `or` defining clauses: one `or_pos` (`g → (⋁ ti)`) and `or_neg` per
    /// disjunct (`ti → g`).
    fn encode_or(&mut self, builder: &mut Builder, gate: &PLit, operands: &[PLit]) {
        let term = gate.view.clone();
        let mut lits = vec![(neg(term.clone()), gate.wrap_not())];
        for operand in operands {
            lits.push((operand.lit_view(), operand.clone()));
        }
        self.emit(builder, "or_pos", Vec::new(), lits);
        for (i, operand) in operands.iter().enumerate() {
            self.emit(
                builder,
                "or_neg",
                vec![AletheTerm::Const(i.to_string())],
                vec![
                    (pos(term.clone()), gate.clone()),
                    (operand.lit_not_view(), operand.wrap_not()),
                ],
            );
        }
    }

    /// The four defining clauses for a binary `=` (`Equiv`) or `xor` gate.
    fn encode_binary(
        &mut self,
        builder: &mut Builder,
        gate: &PLit,
        operands: &[PLit],
        kind: GateKind,
    ) -> Option<()> {
        let [a, b] = operands else {
            return None;
        };
        let term = gate.view.clone();
        // Per row: (rule, gate polarity wraps `term`, a's negation, b's negation).
        // `equiv`/`xor` differ only in which (a,b) polarity combinations land in the
        // positive vs negative `term` rows.
        let rows: [(&str, bool, bool, bool); 4] = match kind {
            GateKind::Equiv => [
                ("equiv_pos1", true, false, true),
                ("equiv_pos2", true, true, false),
                ("equiv_neg1", false, true, true),
                ("equiv_neg2", false, false, false),
            ],
            GateKind::Xor => [
                ("xor_pos1", true, false, false),
                ("xor_pos2", true, true, true),
                ("xor_neg1", false, false, true),
                ("xor_neg2", false, true, false),
            ],
            _ => return None,
        };
        for (rule, gate_neg, a_neg, b_neg) in rows {
            let gate_lit = if gate_neg {
                (neg(term.clone()), gate.wrap_not())
            } else {
                (pos(term.clone()), gate.clone())
            };
            let a_lit = if a_neg {
                (a.lit_not_view(), a.wrap_not())
            } else {
                (a.lit_view(), a.clone())
            };
            let b_lit = if b_neg {
                (b.lit_not_view(), b.wrap_not())
            } else {
                (b.lit_view(), b.clone())
            };
            self.emit(builder, rule, Vec::new(), vec![gate_lit, a_lit, b_lit]);
        }
        Some(())
    }
}

/// The Boolean connective a Tseitin gate encodes.
#[derive(Clone, Copy)]
enum GateKind {
    And,
    Or,
    Equiv,
    Xor,
}

// --- Propositional refutation: SAT core → LRAT → Alethe resolution ----------

/// A Boolean-constant pin candidate: its SAT input clause, the Alethe rule
/// (`"true"`/`"false"`) and clause to emit. Emitted into the proof only if the LRAT
/// refutation references it (see [`refute`]).
struct Pin {
    clause: Vec<CnfLit>,
    rule: &'static str,
    alethe_clause: AletheClause,
}

/// Refutes the collected input clauses (each already an emitted Alethe step), plus the
/// Boolean-constant `pins`, with the proof-producing SAT core, replaying the LRAT
/// resolution chain as Alethe `resolution` steps down to `(cl)`. A pin's `:rule
/// true`/`:rule false` step is emitted **only if** the LRAT proof references that pin
/// clause — keeping a refutation that never depends on a `true`/`false` value
/// completely pin-free. Returns the full command list, or [`None`] if the formula is
/// unexpectedly not refuted.
fn refute(
    builder: &mut Builder,
    tseitin: &Tseitin,
    input_clause_ids: &[(Vec<CnfLit>, String)],
    pins: &[Pin],
) -> Option<Vec<AletheCommand>> {
    // First attempt the refutation WITHOUT the Boolean-constant pins: most fragments
    // (every bitwise/congruence-style one) are unsat over the bit atoms alone, so the
    // proof stays pin-free and our in-tree `check_alethe` (which has no `true`/`false`
    // rule) still accepts it. Only when the bit atoms alone are satisfiable — the
    // carry-chain-semantics case, e.g. the Route-2 `bvsub` refutation — do we add the
    // pins and retry, fixing the `true`/`false` seeds the gadgets depend on.
    let build_formula = |with_pins: bool| -> Option<CnfFormula> {
        let mut formula = CnfFormula::new(tseitin.total_vars());
        for (lits, _) in input_clause_ids {
            formula.add_clause(CnfClause::new(lits.clone())).ok()?;
        }
        if with_pins {
            for pin in pins {
                formula
                    .add_clause(CnfClause::new(pin.clause.clone()))
                    .ok()?;
            }
        }
        Some(formula)
    };
    let pin_base = input_clause_ids.len();

    // Whether the refutation used the pinned formula (so the pin clauses are present
    // as input clauses `pin_base+1..`); a bare-unsat fragment never includes them.
    let used_pins;
    let lrat = {
        let bare = build_formula(false)?;
        match solve_with_drat_proof(&bare) {
            ProofSolveOutcome::Unsat(drat) => {
                used_pins = false;
                elaborate_drat_to_lrat(&bare, &drat).ok()?
            }
            _ if !pins.is_empty() => {
                // Bit atoms alone are satisfiable; retry with the constant pins.
                let pinned = build_formula(true)?;
                let ProofSolveOutcome::Unsat(drat) = solve_with_drat_proof(&pinned) else {
                    return None;
                };
                used_pins = true;
                elaborate_drat_to_lrat(&pinned, &drat).ok()?
            }
            _ => return None,
        }
    };

    // clause index in formula (1-based) → Alethe step id of its (cl …) form.
    let mut clause_step: BTreeMap<u64, String> = BTreeMap::new();
    for (i, (_, step_id)) in input_clause_ids.iter().enumerate() {
        clause_step.insert(i as u64 + 1, step_id.clone());
    }
    // Emit each pin's tautology step iff the pinned formula was used AND its clause is
    // referenced by an LRAT hint; wire its id. (Only meaningful when `used_pins`.)
    if used_pins {
        let mut used: std::collections::BTreeSet<u64> = std::collections::BTreeSet::new();
        for step in &lrat {
            if let LratStep::Add { hints, .. } = step {
                used.extend(hints.iter().copied());
            }
        }
        for (j, pin) in pins.iter().enumerate() {
            let clause_no = (pin_base + j) as u64 + 1;
            if used.contains(&clause_no) {
                let id = builder.step(pin.alethe_clause.clone(), pin.rule, &[]);
                clause_step.insert(clause_no, id);
            }
        }
    }

    // Replay each LRAT addition as an Alethe resolution step over the antecedent
    // clauses' Alethe ids. The learned clause is RUP from its hints, so the
    // resolution entailment holds; the final empty clause closes the proof.
    for step in &lrat {
        let LratStep::Add { id, clause, hints } = step else {
            continue;
        };
        let alethe_clause = cnf_clause_to_alethe(tseitin, clause)?;
        let premises: Vec<String> = hints
            .iter()
            .map(|h| clause_step.get(h).cloned())
            .collect::<Option<Vec<_>>>()?;
        let premise_refs: Vec<&str> = premises.iter().map(String::as_str).collect();
        let step_id = builder.step(alethe_clause, "resolution", &premise_refs);
        clause_step.insert(*id, step_id);
    }

    Some(builder.commands_snapshot())
}

/// Maps a CNF clause back to an Alethe clause over the original bit/gate atoms,
/// inverting the `Tseitin` variable map.
fn cnf_clause_to_alethe(tseitin: &Tseitin, clause: &[CnfLit]) -> Option<AletheClause> {
    clause
        .iter()
        .map(|lit| {
            let atom = tseitin.atom_of_var(lit.var())?;
            Some(AletheLit {
                atom,
                negated: lit.is_negated(),
            })
        })
        .collect()
}

impl Tseitin {
    /// The Alethe atom for a `CnfVar` (inverse of [`Tseitin::var_of`]); returns the
    /// verbatim term recorded at registration, with no key reparse.
    fn atom_of_var(&self, var: CnfVar) -> Option<AletheTerm> {
        self.atom_terms.get(var.index()).cloned()
    }
}

impl Builder {
    fn commands_snapshot(&self) -> Vec<AletheCommand> {
        self.commands.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::prove_qf_bv_unsat_alethe;
    use axeyum_cnf::AletheCommand;
    use axeyum_ir::{Sort, TermArena, TermId};

    fn bv(arena: &mut TermArena, name: &str, width: u32) -> TermId {
        let s = arena.declare(name, Sort::BitVec(width)).expect("declare");
        arena.var(s)
    }

    /// The emitted proof must end in an empty-clause `resolution` step (`(cl)`),
    /// regardless of the external checker.
    fn closes_to_empty(proof: &[AletheCommand]) -> bool {
        matches!(
            proof.last(),
            Some(AletheCommand::Step { clause, rule, .. })
                if clause.is_empty() && rule == "resolution"
        )
    }

    #[test]
    fn template_instance_emits_a_closing_proof() {
        // (= a b) ∧ (bvult a b), 1-bit — the committed template, reproduced.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 1);
        let b = bv(&mut arena, "b", 1);
        let eq = arena.eq(a, b).unwrap();
        let ult = arena.bv_ult(a, b).unwrap();
        let proof = prove_qf_bv_unsat_alethe(&arena, &[eq, ult]).expect("unsat proof");
        assert!(closes_to_empty(&proof), "proof must close to (cl)");
    }

    #[test]
    fn negated_equality_emits_a_closing_proof() {
        // (= a b) ∧ (not (= a b)) over width 2.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let eq = arena.eq(a, b).unwrap();
        let neq = arena.not(eq).unwrap();
        let proof = prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("unsat proof");
        assert!(closes_to_empty(&proof));
    }

    #[test]
    fn deterministic_emission() {
        // The driver is deterministic: two runs over the same query emit identical
        // command lists (no hash-map iteration in the output).
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let ab = arena.bv_ult(a, b).unwrap();
        let ba = arena.bv_ult(b, a).unwrap();
        let p1 = prove_qf_bv_unsat_alethe(&arena, &[ab, ba]).expect("unsat proof");
        let p2 = prove_qf_bv_unsat_alethe(&arena, &[ab, ba]).expect("unsat proof");
        assert_eq!(p1, p2);
    }

    #[test]
    fn sat_instance_is_none() {
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let ult = arena.bv_ult(a, b).unwrap();
        assert!(prove_qf_bv_unsat_alethe(&arena, &[ult]).is_none());
    }

    #[test]
    fn compound_operand_emits_a_closing_proof() {
        // (= (bvand a b) a) ∧ (not …) is unsat; the compound operand `(bvand a b)`
        // is now reduced bottom-up, so the driver emits a closing proof.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let and = arena.bv_and(a, b).unwrap();
        let eq = arena.eq(and, a).unwrap();
        let neq = arena.not(eq).unwrap();
        let proof = prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("unsat proof");
        assert!(closes_to_empty(&proof));
    }

    #[test]
    fn nested_compound_emits_a_closing_proof() {
        // (= (bvand (bvor a b) c) (bvand (bvor a b) c)) negated is unsat; a deep,
        // shared nested compound exercises the recursive reduction + DAG dedup.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let c = bv(&mut arena, "c", 2);
        let or = arena.bv_or(a, b).unwrap();
        let inner = arena.bv_and(or, c).unwrap();
        let eq = arena.eq(inner, inner).unwrap();
        let neq = arena.not(eq).unwrap();
        let proof = prove_qf_bv_unsat_alethe(&arena, &[neq]).expect("unsat proof");
        assert!(closes_to_empty(&proof));
    }

    #[test]
    fn shift_subterm_is_none() {
        // A `bvshl` subterm is a Carcara hole (not bit-blastable), so even an unsat
        // instance over it is out of fragment → None.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let shl = arena.bv_shl(a, b).unwrap();
        let eq = arena.eq(shl, a).unwrap();
        let neq = arena.not(eq).unwrap();
        assert!(prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).is_none());
    }

    #[test]
    fn div_subterm_is_none() {
        // A `bvudiv` subterm is likewise a Carcara hole → out of fragment.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let div = arena.bv_udiv(a, b).unwrap();
        let eq = arena.eq(div, a).unwrap();
        let neq = arena.not(eq).unwrap();
        assert!(prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).is_none());
    }

    #[test]
    fn unsupported_predicate_is_none() {
        // bvule is not in the v1 predicate set, even when the instance is unsat.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let le = arena.bv_ule(a, b).unwrap();
        let lt = arena.bv_ult(b, a).unwrap();
        // a <= b ∧ b < a is unsat, but bvule is unsupported → None.
        assert!(prove_qf_bv_unsat_alethe(&arena, &[le, lt]).is_none());
    }

    #[test]
    fn empty_assertions_is_none() {
        let arena = TermArena::new();
        assert!(prove_qf_bv_unsat_alethe(&arena, &[]).is_none());
    }

    // --- Route 2 (bvsub kept at the term level) -----------------------------

    #[test]
    fn route1_still_rejects_bvsub() {
        // The committed Route-1 emitter keeps `bvsub` OUT of fragment, even for an
        // unsat instance — this is the gap Route 2 closes.
        use super::prove_qf_bv_unsat_alethe;
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let sub = arena.bv_sub(a, b).unwrap();
        let eq1 = arena.eq(sub, a).unwrap();
        let lt = arena.bv_ult(a, b).unwrap();
        assert!(prove_qf_bv_unsat_alethe(&arena, &[eq1, lt]).is_none());
    }

    #[test]
    fn route2_bvsub_emits_a_closing_proof() {
        use super::prove_qf_bv_unsat_alethe_route2;
        // (= (bvsub a b) a) ∧ (bvult a b): `a - b = a` forces `b = 0`, but then
        // `a < b = a < 0` is impossible (unsigned) — unsat over the ORIGINAL `bvsub`
        // assertion, all-variable (no constant operands), genuinely exercising the
        // two's-complement subtract carry semantics.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let sub = arena.bv_sub(a, b).unwrap();
        let eq1 = arena.eq(sub, a).unwrap();
        let lt = arena.bv_ult(a, b).unwrap();
        let proof = prove_qf_bv_unsat_alethe_route2(&mut arena, &[eq1, lt]).expect("unsat proof");
        assert!(closes_to_empty(&proof), "Route-2 proof must close to (cl)");
        // The proof must keep `bvsub` at the term level: a `bv_poly_simp` rewrite step
        // bridging it to `(bvadd a (bvneg b))` is present.
        assert!(
            proof.iter().any(|c| matches!(
                c,
                AletheCommand::Step { rule, .. } if rule == "bv_poly_simp"
            )),
            "Route-2 must emit a bv_poly_simp bvsub-rewrite step"
        );
    }

    #[test]
    fn route2_without_bvsub_matches_route1() {
        use super::{prove_qf_bv_unsat_alethe, prove_qf_bv_unsat_alethe_route2};
        // With no bvsub, Route 2 collects no rewrites and emits the same proof as
        // Route 1 (the rewrites map is empty).
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let eq = arena.eq(a, b).unwrap();
        let neq = arena.not(eq).unwrap();
        let p1 = prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("route1");
        let p2 = prove_qf_bv_unsat_alethe_route2(&mut arena, &[eq, neq]).expect("route2");
        assert_eq!(p1, p2);
    }

    #[test]
    fn route2_sat_instance_is_none() {
        use super::prove_qf_bv_unsat_alethe_route2;
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let c = bv(&mut arena, "c", 2);
        let sub = arena.bv_sub(a, b).unwrap();
        let eq = arena.eq(sub, c).unwrap();
        // (bvsub a b) = c alone is satisfiable.
        assert!(prove_qf_bv_unsat_alethe_route2(&mut arena, &[eq]).is_none());
    }

    // --- Extended comparisons (bvule/bvugt/bvuge/bvsle/bvsgt/bvsge) ----------

    #[test]
    fn ext_compare_bvugt_emits_a_closing_proof() {
        use super::prove_qf_bv_unsat_alethe_ext_compare;
        // (bvugt a b) ∧ (= a b) over width 2 — unsat: a > b yet a = b. The top-level
        // `bvugt` normalizes to `(bvult b a)`.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let gt = arena.bv_ugt(a, b).unwrap();
        let eq = arena.eq(a, b).unwrap();
        let (proof, normalized) =
            prove_qf_bv_unsat_alethe_ext_compare(&mut arena, &[gt, eq]).expect("unsat proof");
        assert!(closes_to_empty(&proof));
        // The normalized assertion is `(bvult b a)`, no longer `bvugt`.
        assert_ne!(normalized[0], gt);
    }

    #[test]
    fn ext_compare_bvule_emits_a_closing_proof() {
        use super::prove_qf_bv_unsat_alethe_ext_compare;
        // (bvule a b) ∧ (bvult b a) — unsat: a ≤ b contradicts b < a. `bvule` normalizes
        // to `(not (bvult b a))`, a negated predicate.
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let le = arena.bv_ule(a, b).unwrap();
        let lt = arena.bv_ult(b, a).unwrap();
        let (proof, _norm) =
            prove_qf_bv_unsat_alethe_ext_compare(&mut arena, &[le, lt]).expect("unsat proof");
        assert!(closes_to_empty(&proof));
    }

    #[test]
    fn ext_compare_passthrough_matches_core() {
        use super::{prove_qf_bv_unsat_alethe, prove_qf_bv_unsat_alethe_ext_compare};
        // With no extended comparison, normalization is a no-op and the proof equals the
        // core driver's (the normalized assertions are the inputs unchanged).
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let eq = arena.eq(a, b).unwrap();
        let neq = arena.not(eq).unwrap();
        let core = prove_qf_bv_unsat_alethe(&arena, &[eq, neq]).expect("core");
        let (ext, norm) =
            prove_qf_bv_unsat_alethe_ext_compare(&mut arena, &[eq, neq]).expect("ext");
        assert_eq!(core, ext);
        assert_eq!(norm, vec![eq, neq]);
    }

    #[test]
    fn ext_compare_sat_instance_is_none() {
        use super::prove_qf_bv_unsat_alethe_ext_compare;
        let mut arena = TermArena::new();
        let a = bv(&mut arena, "a", 2);
        let b = bv(&mut arena, "b", 2);
        let ge = arena.bv_uge(a, b).unwrap();
        // (bvuge a b) alone is satisfiable.
        assert!(prove_qf_bv_unsat_alethe_ext_compare(&mut arena, &[ge]).is_none());
    }
}
