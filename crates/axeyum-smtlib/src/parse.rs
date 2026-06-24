//! SMT-LIB 2 script parser for the `QF_BV` benchmark slice.
//!
//! Scope (formats note): benchmarks-as-data — `set-logic`, `set-info`,
//! `declare-fun` (0-ary constants and n-ary uninterpreted functions, ADR-0013),
//! `declare-const`, `define-fun` (0-ary aliases and n-ary macros), `assert`,
//! `check-sat`, `exit`, plus `let` and `forall`/`exists` binders (ADR-0016).
//! Incremental scripting (`push`/`pop` with multiple `check-sat`) is recorded as
//! an ordered [`ScriptCommand`] sequence for scoped, per-`check-sat` solving
//! (ADR-0009 lifecycle). Term conversion is iterative, so deep benchmark terms
//! cannot overflow the stack.

use std::collections::HashMap;

use axeyum_fp::{FloatFormat, RoundingMode};
use axeyum_ir::{Rational, Sort, TermArena, TermId, TermNode};

use crate::SmtError;
use crate::sexpr::{SExpr, read_all};

/// An ordered command from an (incremental) SMT-LIB script. Only the commands
/// that affect the assertion stack and its `check-sat` queries are recorded;
/// declarations mutate the shared arena directly (and stay global).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScriptCommand {
    /// `(assert t)` — push `t` onto the current assertion scope.
    Assert(TermId),
    /// `(push n)` — open `n` nested assertion scopes.
    Push(u32),
    /// `(pop n)` — close `n` scopes, dropping assertions made within them.
    Pop(u32),
    /// `(check-sat)` — decide the conjunction of the currently-active assertions.
    CheckSat,
    /// `(check-sat-assuming (l ...))` — decide the active assertions together with
    /// the assumption literals `l`, without retaining them afterwards.
    CheckSatAssuming(Vec<TermId>),
    /// `(reset-assertions)` — remove **all** assertions (and open scopes), keeping
    /// declarations and definitions. Modeled explicitly because treating it as a
    /// no-op would silently solve a *different* problem than the script asked.
    ResetAssertions,
}

/// A parsed benchmark script.
#[derive(Debug, Default)]
#[non_exhaustive]
pub struct Script {
    /// Arena holding all parsed terms.
    pub arena: TermArena,
    /// Every asserted formula, in script order (ignoring `push`/`pop` scoping —
    /// for the flat, non-incremental view). Use [`Script::commands`] for the
    /// scoped, incremental sequence.
    pub assertions: Vec<TermId>,
    /// `set-logic` value, if present.
    pub logic: Option<String>,
    /// `(set-info :status ...)` value, if present (benchmark ground truth).
    pub status: Option<String>,
    /// Number of `check-sat` commands seen.
    pub check_sats: u32,
    /// Per-assertion `:named` label (parallel to [`Script::assertions`]; `None`
    /// when the assertion was not named), for `(get-unsat-core)`.
    pub assertion_names: Vec<Option<String>>,
    /// Terms requested by `(get-value (t …))`, in script order, to be evaluated
    /// against a `sat` model.
    pub get_value_terms: Vec<TermId>,
    /// Optimization objectives `(maximize t)` / `(minimize t)`, in script order;
    /// the flag is `true` for `maximize`, `false` for `minimize` (ADR-pending OMT).
    pub objectives: Vec<(TermId, bool)>,
    /// The ordered `assert`/`push`/`pop`/`check-sat` sequence — the incremental
    /// view of the script (ADR-0009 lifecycle), for per-`check-sat` solving.
    pub commands: Vec<ScriptCommand>,
}

/// Parses an SMT-LIB script.
///
/// # Errors
///
/// [`SmtError::Syntax`] for malformed input, [`SmtError::Unsupported`] for
/// constructs outside the `QF_BV` benchmark slice, and sort errors surfaced
/// as [`SmtError::Ir`].
pub fn parse_script(input: &str) -> Result<Script, SmtError> {
    let mut exprs = read_all(input)?;
    // Finite-set theory: model every `(Set E)` as a `BitVec(W)` over the finite
    // element domain and rewrite the sound subset of set operations to bit-vector
    // operations *in place* on the s-expression tree, before any term is built.
    // A no-op (and no allocation) for scripts that use no sets; an
    // [`SmtError::Unsupported`] for a script whose set usage falls outside the
    // provably-sound subset (see [`desugar_sets`]).
    desugar_sets(&mut exprs)?;
    let mut script = Script::default();
    let mut aliases: HashMap<String, TermId> = HashMap::new();
    let mut macros: HashMap<String, MacroDef<'_>> = HashMap::new();
    let mut sort_aliases: HashMap<String, Sort> = HashMap::new();
    // `:named` term annotations: `(! t :named foo)` binds `foo` as an alias for
    // the term `t` (SMT-LIB `:named` attribute). The binding is script-global
    // (not lexically scoped), so the map persists across commands; a later bare
    // reference to `foo` resolves to `t`. Declared symbols take precedence (see
    // `parse_atom`), so a real declaration never gets shadowed by a `:named`.
    let mut named: HashMap<String, TermId> = HashMap::new();

    // Width used to model every arity-0 `(declare-sort U 0)` uninterpreted sort
    // as a `BitVec(W)` (see [`uninterpreted_sort_width`]). Computed once from a
    // rigorous upper bound on the number of distinct `U`-typed terms the whole
    // script can possibly contain — the soundness argument lives on that
    // function.
    let uninterpreted_width = uninterpreted_sort_width(&exprs);

    for command in &exprs {
        parse_command(
            &mut script,
            &mut aliases,
            &mut macros,
            &mut sort_aliases,
            &mut named,
            uninterpreted_width,
            command,
        )?;
    }
    Ok(script)
}

/// The bit-width `W` used to model **every** arity-0 uninterpreted sort
/// `(declare-sort U 0)` as a `BitVec(W)`, turning `QF_UF`/`QF_UFLIA` over
/// uninterpreted sorts into `QF_UFBV`/`QF_UFLIA`-over-BV (which axeyum already
/// fully decides) without touching the IR `Sort` enum.
///
/// # Soundness — why no wrong `unsat` is possible
///
/// In a quantifier-free formula, an uninterpreted sort `U` only needs as many
/// **distinct** values as there are **distinct `U`-typed terms** in the formula:
/// any satisfying model can be collapsed so that every `U`-typed term takes a
/// value drawn from a set of size at most `k`, where `k` is the number of
/// distinct `U`-typed terms (a Herbrand-style bound — you cannot assert more
/// pairwise-`distinct` `U`-elements than there are `U`-terms to name them).
///
/// Every `U`-typed term is itself an s-expression node somewhere in the script,
/// so the **total s-expression node count** `n` of the entire script is a
/// rigorous upper bound on `k`: `k ≤ n`. We pick
/// `W = max(1, ceil(log2(n)) + MARGIN)` with `MARGIN = 2`, which guarantees
/// `2^W ≥ 4·n ≥ n ≥ k`. Hence the `BitVec(W)` domain always has at least `k`
/// distinct values available, so a satisfiable `distinct`/inequality constraint
/// over `U` can never be forced `unsat` by running out of tokens. The `MARGIN`
/// is pure slack (never required for soundness); it only keeps the encoding off
/// the exact boundary. The width is intentionally uniform across all declared
/// sorts in the script: the global node count is still a sound
/// over-approximation of any single sort's own term count, and it keeps the
/// single-pass parser simple.
///
/// `n` is computed once over the parsed s-expressions and is bounded by the
/// input size; a parseable benchmark cannot hold `2^usize::BITS` nodes, so the
/// `ceil(log2)` cannot saturate in practice.
fn uninterpreted_sort_width(exprs: &[SExpr]) -> u32 {
    const MARGIN: u32 = 2;
    let n: usize = exprs.iter().map(count_sexpr_nodes).sum();
    // ceil(log2(n)): the number of bits needed to index `n` distinct values.
    // For n ≤ 1 a single bit already provides 2 ≥ n values, so 0 base bits.
    let bits = if n <= 1 { 0 } else { (n - 1).ilog2() + 1 };
    (bits + MARGIN).max(1)
}

/// Total number of s-expression nodes (every atom, and every list node plus its
/// children) in `e`. An over-approximation of the number of distinct terms any
/// declaration/assertion in the script can introduce; see
/// [`uninterpreted_sort_width`] for how this bounds the modeling width.
fn count_sexpr_nodes(e: &SExpr) -> usize {
    match e {
        SExpr::Atom(_) => 1,
        SExpr::List(items) => 1 + items.iter().map(count_sexpr_nodes).sum::<usize>(),
    }
}

// --- finite-set theory: `(Set E)` modeled as `BitVec(W)` ---------------------
//
// SMT-LIB's finite-set theory (cvc5 `set.*`) over a finite element domain is
// isomorphic to the powerset of the domain, which is exactly a bit-set. We model
// `(Set E)` as a `BitVec(W)` where each bit position is a distinct element of the
// modeled domain, and rewrite the **denotation-preserving subset** of the set
// operators to bit-vector operators, entirely at the s-expression level (so no IR
// `Sort`/`Op` change is needed — just like uninterpreted sorts, `79a0679`).
//
// # The modeled element domain and its bit positions
//
// The only set elements a quantifier-free formula can *name* are the terms that
// appear as the element argument of `set.singleton`/`set.member`. We give each
// **distinct** such element term its own bit index `0..D` (`D` distinct element
// terms), plus a `MARGIN` of extra high "junk" bits standing for elements the
// formula never names. The width is `W = D + MARGIN` (at least `1`).
//
// # Soundness — when is this denotation-preserving?
//
// The encoding is exact (isomorphic to the real powerset semantics) provided two
// conditions hold, which [`scan_set_ops`] enforces by **declining** (leaving the
// whole script [`SmtError::Unsupported`]) otherwise:
//
//  1. **Distinct element terms denote distinct elements.** We only accept element
//     terms that are *constant literals* (numerals, decimals, `#b`/`#x`/`(_ bvN
//     W)` bit-vectors, `true`/`false`). Two syntactically-distinct literals are
//     two distinct values, so giving them distinct bits introduces no spurious
//     (dis)equality. (Arithmetic element terms such as `(* v0 7)` can *alias*
//     another element term — `(* 7 v0)` — so a per-term bit would be unsound
//     without congruence constraints; those files are declined for a later
//     slice.)
//
//  2. **Only finite-domain-safe operators.** `set.empty`, `set.singleton`,
//     `set.member`, `set.union`, `set.inter`, `set.minus`, `set.subset`, and set
//     `=`/`distinct` are all pointwise over the membership function, so they
//     commute with projecting onto the modeled domain: `union=bvor`,
//     `inter=bvand`, `minus=bvand-bvnot`, `member=bit test`, `subset=(a = a&b)`.
//     The `MARGIN` junk bits let a *free* set variable differ from another set on
//     unnamed elements (so `(not (= x y))` over two free sets is `sat`, and an
//     equality never wrongly forces two free sets equal on the unnamed tail).
//     `set.card`, `set.complement`, and `set.universe` are **not** pointwise on a
//     finite projection — they quantify over the *whole* (possibly infinite)
//     element sort — so they are declined (a `BitVec` popcount/complement over the
//     modeled domain would give a *wrong* cardinality/complement for the unnamed
//     tail). `set.comprehension`/`set.choose`/`set.insert` are likewise declined.
//
// Under (1) and (2) every set term denotes a subset of the modeled domain and
// every operator is computed exactly on that domain, so a model of the `BitVec`
// encoding lifts to a set model (map bit `i` to element `i`, and realize the
// junk bits with that many fresh distinct unnamed elements) and vice-versa: the
// encoding is **equisatisfiable**, so neither a wrong `sat` nor a wrong `unsat`
// is possible.

/// Operators that quantify over the *entire* element sort (not just the modeled
/// finite projection) or otherwise fall outside the sound `BitVec` subset; any
/// occurrence makes [`desugar_sets`] decline the whole script.
const UNSUPPORTED_SET_OPS: &[&str] = &[
    "set.card",
    "set.complement",
    "set.universe",
    "set.comprehension",
    "set.choose",
    "set.insert",
    "set.filter",
    "set.map",
    "set.fold",
];

/// Margin of extra high "junk" bits added beyond the `D` named-element bits, so a
/// free set variable can differ from another set on elements the formula never
/// names. See the module-level soundness note.
const SET_MARGIN_BITS: u32 = 2;

/// Cap on the modeled set width. The single-bit `set.singleton` constant is
/// emitted as `(_ bv(1<<i) W)`, whose value must fit a `u128`, so more than 127
/// distinct element terms is declined (rare; these benchmarks have a handful).
const MAX_SET_WIDTH: u32 = 128;

/// Rewrites the sound subset of finite-set operations to bit-vector operations,
/// in place on the whole s-expression script `exprs`, modeling every `(Set E)` as
/// a `BitVec(W)` (see the module-level soundness note).
///
/// Fast path: a script that mentions no set sort or `set.*` operator is left
/// untouched (and unallocated).
///
/// # Errors
///
/// [`SmtError::Unsupported`] if the script's set usage falls outside the
/// provably-sound subset (an unsupported operator, a non-literal element term, or
/// a modeled width over [`MAX_SET_WIDTH`]). Declining is *sound*: an unsupported
/// file is reported as such rather than risking a wrong verdict.
fn desugar_sets(exprs: &mut [SExpr]) -> Result<(), SmtError> {
    // Fast path: nothing set-related anywhere.
    if !exprs.iter().any(mentions_sets) {
        return Ok(());
    }
    // Collect the distinct (literal) element terms, in first-appearance order, and
    // validate the sound-subset conditions.
    let mut element_keys: Vec<String> = Vec::new();
    scan_set_ops(exprs, &mut element_keys)?;
    let d = u32::try_from(element_keys.len()).unwrap_or(u32::MAX);
    let width = d
        .checked_add(SET_MARGIN_BITS)
        .filter(|&w| w <= MAX_SET_WIDTH)
        .ok_or_else(|| {
            SmtError::Unsupported(format!(
                "finite-set modeling needs {d} element bits, over the {MAX_SET_WIDTH}-bit cap"
            ))
        })?
        .max(1);
    let bit_index: HashMap<String, u32> = element_keys
        .into_iter()
        .enumerate()
        .map(|(i, k)| (k, u32::try_from(i).expect("index fits (width capped)")))
        .collect();
    for e in exprs.iter_mut() {
        rewrite_set_sexpr(e, width, &bit_index);
    }
    Ok(())
}

/// Whether `e` mentions the `Set` sort head or any `set.*` operator anywhere.
fn mentions_sets(e: &SExpr) -> bool {
    match e {
        SExpr::Atom(a) => a.starts_with("set."),
        SExpr::List(items) => {
            items.first().and_then(SExpr::atom) == Some("Set") || items.iter().any(mentions_sets)
        }
    }
}

/// Validates the sound-subset conditions and collects the distinct literal element
/// terms (first-appearance order) into `element_keys`.
///
/// # Errors
///
/// [`SmtError::Unsupported`] for an [`UNSUPPORTED_SET_OPS`] operator or a
/// non-literal `set.singleton`/`set.member` element term.
fn scan_set_ops(exprs: &[SExpr], element_keys: &mut Vec<String>) -> Result<(), SmtError> {
    for e in exprs {
        if let SExpr::List(items) = e {
            if let Some(head) = items.first().and_then(SExpr::atom) {
                if UNSUPPORTED_SET_OPS.contains(&head) {
                    return Err(SmtError::Unsupported(format!(
                        "finite-set operator `{head}` is outside the sound BitVec subset \
                         (it ranges over the whole element sort, not the named finite domain)"
                    )));
                }
                if (head == "set.singleton" || head == "set.member") && items.len() >= 2 {
                    // The element is the LAST argument: `(set.singleton e)` and
                    // `(set.member e S)`.
                    let elem = &items[items.len() - if head == "set.member" { 2 } else { 1 }];
                    let key = set_element_key(elem).ok_or_else(|| {
                        SmtError::Unsupported(format!(
                            "finite-set element `{elem:?}` is not a constant literal; only \
                             literal elements are soundly modeled (non-literal elements may \
                             alias and need congruence — a later slice)"
                        ))
                    })?;
                    if !element_keys.contains(&key) {
                        element_keys.push(key);
                    }
                }
            }
            scan_set_ops(items, element_keys)?;
        }
    }
    Ok(())
}

/// The canonical bit-position key for a set element term, or `None` if the term is
/// not a constant literal (so giving it its own bit could be unsound; see the
/// module note, condition 1).
///
/// Accepts numerals (`7`), decimals (`1.5`), `#b`/`#x` bit-vector literals,
/// indexed bit-vector constants `(_ bvN W)`, and the booleans `true`/`false`. The
/// key is the literal's normalized text, so two syntactically-equal literals share
/// a bit and two distinct literals get distinct bits.
fn set_element_key(e: &SExpr) -> Option<String> {
    match e {
        SExpr::Atom(a) => is_set_element_literal_atom(a).then(|| a.clone()),
        SExpr::List(items) => {
            // `(_ bvN W)` indexed bit-vector constant.
            if items.len() == 3
                && items[0].atom() == Some("_")
                && items[1].atom().is_some_and(|n| n.starts_with("bv"))
                && items[2].atom().is_some_and(|w| w.parse::<u32>().is_ok())
            {
                let n = items[1].atom().expect("checked");
                let w = items[2].atom().expect("checked");
                Some(format!("(_ {n} {w})"))
            } else {
                None
            }
        }
    }
}

/// Whether an atom is a constant literal usable as a finite-set element bit key:
/// a numeral, a decimal, a `#b`/`#x` bit-vector literal, or `true`/`false`.
fn is_set_element_literal_atom(a: &str) -> bool {
    if a == "true" || a == "false" {
        return true;
    }
    if let Some(rest) = a.strip_prefix("#b") {
        return !rest.is_empty() && rest.bytes().all(|c| c == b'0' || c == b'1');
    }
    if let Some(rest) = a.strip_prefix("#x") {
        return !rest.is_empty() && rest.bytes().all(|c| c.is_ascii_hexdigit());
    }
    // Numeral or decimal: digits with at most one `.`.
    let mut seen_dot = false;
    let mut seen_digit = false;
    for c in a.bytes() {
        match c {
            b'0'..=b'9' => seen_digit = true,
            b'.' if !seen_dot => seen_dot = true,
            _ => return false,
        }
    }
    seen_digit
}

/// Recursively rewrites every finite-set sort/operator in `e` (in place) to its
/// bit-vector encoding at width `width`, using `bit_index` for element positions.
fn rewrite_set_sexpr(e: &mut SExpr, width: u32, bit_index: &HashMap<String, u32>) {
    let SExpr::List(items) = e else { return };
    // Rewrite children first (bottom-up), so set sub-terms become BV before the
    // parent operator consumes them.
    for child in items.iter_mut() {
        rewrite_set_sexpr(child, width, bit_index);
    }
    // `(Set E)` in a sort position → `(_ BitVec W)`.
    if items.len() == 2 && items[0].atom() == Some("Set") {
        *e = bitvec_sort(width);
        return;
    }
    let Some(head) = items.first().and_then(SExpr::atom) else {
        return;
    };
    match head {
        // `(as set.empty (Set E))` and the bare `set.empty` (handled as an atom
        // elsewhere) → the all-zeros bit-set. The `(Set E)` argument has already
        // been rewritten to `(_ BitVec W)` above; we ignore it.
        "as" if items.len() == 3 && items[1].atom() == Some("set.empty") => {
            *e = bv_zero(width);
        }
        "set.empty" => *e = bv_zero(width),
        "set.singleton" if items.len() == 2 => {
            *e = singleton_sexpr(&items[1], width, bit_index);
        }
        "set.member" if items.len() == 3 => {
            // `(set.member e S)` → bit `i` of `S` is set:
            //   `(= ((_ extract i i) S) #b1)`.
            *e = member_sexpr(&items[1], &items[2], bit_index);
        }
        "set.union" if items.len() >= 2 => {
            *e = fold_set_sexpr("bvor", &items[1..]);
        }
        "set.inter" if items.len() >= 2 => {
            *e = fold_set_sexpr("bvand", &items[1..]);
        }
        "set.minus" if items.len() == 3 => {
            // `a \ b` = `a & ~b`.
            *e = SExpr::List(vec![
                atom("bvand"),
                items[1].clone(),
                SExpr::List(vec![atom("bvnot"), items[2].clone()]),
            ]);
        }
        "set.subset" if items.len() == 3 => {
            // `a ⊆ b` ⇔ `a = a & b`.
            let a = items[1].clone();
            let b = items[2].clone();
            *e = SExpr::List(vec![
                atom("="),
                a.clone(),
                SExpr::List(vec![atom("bvand"), a, b]),
            ]);
        }
        _ => {}
    }
}

/// `(_ BitVec width)` sort s-expr.
fn bitvec_sort(width: u32) -> SExpr {
    SExpr::List(vec![atom("_"), atom("BitVec"), atom(&width.to_string())])
}

/// `(_ bv0 width)` — the empty bit-set / all-zeros constant.
fn bv_zero(width: u32) -> SExpr {
    SExpr::List(vec![atom("_"), atom("bv0"), atom(&width.to_string())])
}

/// `(set.singleton e)` → the one-hot constant `(_ bv(1<<i) W)` for `e`'s bit `i`.
/// An element with no registered bit (impossible after [`scan_set_ops`]) maps to
/// the empty set, which is sound (it can only under-constrain, never wrong-`unsat`
/// — but the scan guarantees every singleton element is registered).
fn singleton_sexpr(elem: &SExpr, width: u32, bit_index: &HashMap<String, u32>) -> SExpr {
    let value = set_element_key(elem)
        .and_then(|k| bit_index.get(&k).copied())
        .map_or(0u128, |i| 1u128 << i);
    SExpr::List(vec![
        atom("_"),
        atom(&format!("bv{value}")),
        atom(&width.to_string()),
    ])
}

/// `(set.member e S)` → `(= ((_ extract i i) S) #b1)`, the bit-`i` membership test.
/// A `set.member` whose element has no bit (impossible after [`scan_set_ops`])
/// becomes `false` (the element is in no modeled set), which is sound here.
fn member_sexpr(elem: &SExpr, set: &SExpr, bit_index: &HashMap<String, u32>) -> SExpr {
    let Some(i) = set_element_key(elem).and_then(|k| bit_index.get(&k).copied()) else {
        return atom("false");
    };
    let extract = SExpr::List(vec![
        SExpr::List(vec![
            atom("_"),
            atom("extract"),
            atom(&i.to_string()),
            atom(&i.to_string()),
        ]),
        set.clone(),
    ]);
    SExpr::List(vec![atom("="), extract, atom("#b1")])
}

/// Folds a set operator `op` (`bvor`/`bvand`) over `args` (≥ 1), left-associating.
fn fold_set_sexpr(op: &str, args: &[SExpr]) -> SExpr {
    let mut acc = args[0].clone();
    for next in &args[1..] {
        acc = SExpr::List(vec![atom(op), acc, next.clone()]);
    }
    acc
}

/// A borrowed-free atom s-expr.
fn atom(s: &str) -> SExpr {
    SExpr::Atom(s.to_owned())
}

// A flat dispatch over the SMT-LIB command keywords; one match arm per command.
#[allow(clippy::too_many_lines)]
fn parse_command<'a>(
    script: &mut Script,
    aliases: &mut HashMap<String, TermId>,
    macros: &mut HashMap<String, MacroDef<'a>>,
    sort_aliases: &mut HashMap<String, Sort>,
    named: &mut HashMap<String, TermId>,
    uninterpreted_width: u32,
    command: &'a SExpr,
) -> Result<(), SmtError> {
    let items = command
        .list()
        .ok_or_else(|| SmtError::Syntax("top-level atom".to_owned()))?;
    let head = items
        .first()
        .and_then(SExpr::atom)
        .ok_or_else(|| SmtError::Syntax("empty command".to_owned()))?;
    match head {
        "set-logic" => {
            exact_len(items, 2, head)?;
            script.logic = items.get(1).and_then(SExpr::atom).map(str::to_owned);
        }
        "set-info" => {
            exact_len(items, 3, head)?;
            if items.get(1).and_then(SExpr::atom) == Some(":status") {
                script.status = items.get(2).and_then(SExpr::atom).map(str::to_owned);
            }
        }
        "set-option" => exact_len(items, 3, head)?,
        // Output/query commands: accepted as no-ops at parse time. The core is
        // produced by the solver (`solve_smtlib_unsat_core`), the model by the
        // `sat` result — the parser just records a well-formed script.
        "get-model"
        | "exit"
        | "get-unsat-core"
        | "get-proof"
        | "get-assertions"
        | "get-assignment"
        | "get-unsat-assumptions"
        | "get-objectives" => exact_len(items, 1, head)?,
        // `(reset-assertions)` clears assertions but keeps declarations — modeled
        // explicitly (a no-op here would silently keep stale assertions across the
        // reset, solving a different problem than the script asked).
        "reset-assertions" => {
            exact_len(items, 1, head)?;
            script.commands.push(ScriptCommand::ResetAssertions);
        }
        // `(reset)` is a FULL reset (assertions + declarations + options back to the
        // initial state). In this parse-then-execute model declarations are interned
        // into a single shared arena, so clearing them mid-script is not soundly
        // supported — reject explicitly rather than silently ignore (which would
        // leave stale declarations/assertions in effect).
        "reset" => {
            exact_len(items, 1, head)?;
            return Err(SmtError::Unsupported(
                "reset (full reset of declarations + assertions); use reset-assertions, or run \
                 each benchmark in a fresh solver instance"
                    .to_owned(),
            ));
        }
        // Optimization objectives (OMT): `(maximize t)` / `(minimize t)`.
        "maximize" | "minimize" => {
            exact_len(items, 2, head)?;
            let t = parse_term(
                &mut script.arena,
                sexpr_at(items, 1)?,
                aliases,
                macros,
                named,
            )?;
            script.objectives.push((t, head == "maximize"));
        }
        // `(get-info k)` and `(echo "string")`: 2-token output/query commands,
        // accepted (well-formed) and otherwise ignored so full-standard scripts parse.
        "get-info" | "echo" => exact_len(items, 2, head)?,
        "get-value" => {
            exact_len(items, 2, head)?;
            let list = items
                .get(1)
                .and_then(SExpr::list)
                .ok_or_else(|| SmtError::Syntax("get-value expects (t …)".to_owned()))?;
            for t in list {
                let term = parse_term(&mut script.arena, t, aliases, macros, named)?;
                script.get_value_terms.push(term);
            }
        }
        "check-sat-assuming" => {
            exact_len(items, 2, head)?;
            let list = items
                .get(1)
                .and_then(SExpr::list)
                .ok_or_else(|| SmtError::Syntax("check-sat-assuming expects (l ...)".to_owned()))?;
            let mut assumptions = Vec::with_capacity(list.len());
            for lit in list {
                assumptions.push(parse_term(&mut script.arena, lit, aliases, macros, named)?);
            }
            script.check_sats += 1;
            script
                .commands
                .push(ScriptCommand::CheckSatAssuming(assumptions));
        }
        "check-sat" => {
            exact_len(items, 1, head)?;
            script.check_sats += 1;
            script.commands.push(ScriptCommand::CheckSat);
        }
        "declare-fun" => parse_declare_fun(script, sort_aliases, items)?,
        "declare-const" => parse_declare_const(script, sort_aliases, items)?,
        "declare-datatype" => parse_declare_datatype(script, sort_aliases, items)?,
        "declare-datatypes" => parse_declare_datatypes(script, sort_aliases, items)?,
        "define-fun" => parse_define_fun(script, aliases, macros, sort_aliases, named, items)?,
        // `(define-const c S body)` is exact sugar for `(define-fun c () S body)`
        // (SMT-LIB §3.7.2 abbreviation): a nullary definition. We reuse the
        // no-args alias path verbatim, so soundness is identical to `define-fun`.
        "define-const" => parse_define_const(script, aliases, macros, sort_aliases, named, items)?,
        "define-sort" => parse_define_sort(script, sort_aliases, items)?,
        // `(declare-sort U 0)` — an arity-0 uninterpreted sort, modeled as a
        // `BitVec(W)` (soundness on [`uninterpreted_sort_width`]). Arity ≥ 1
        // (parametric, e.g. `(declare-sort List 1)`) is out of scope.
        "declare-sort" => parse_declare_sort(script, sort_aliases, uninterpreted_width, items)?,
        "assert" => {
            exact_len(items, 2, head)?;
            let body = sexpr_at(items, 1)?;
            let name = named_label(body);
            let t = parse_term(&mut script.arena, body, aliases, macros, named)?;
            script.assertions.push(t);
            script.assertion_names.push(name);
            script.commands.push(ScriptCommand::Assert(t));
        }
        // Incremental scoping (ADR-0009): `(push)`/`(pop)` default to one scope.
        "push" | "pop" => {
            let count = match items.get(1) {
                None => 1,
                Some(e) => e
                    .atom()
                    .and_then(|s| s.parse::<u32>().ok())
                    .ok_or_else(|| SmtError::Syntax(format!("`{head}` count")))?,
            };
            if items.len() > 2 {
                return Err(SmtError::Syntax(format!(
                    "`{head}` takes at most one count"
                )));
            }
            script.commands.push(if head == "push" {
                ScriptCommand::Push(count)
            } else {
                ScriptCommand::Pop(count)
            });
        }
        other => return Err(SmtError::Unsupported(format!("command `{other}`"))),
    }
    Ok(())
}

/// The `:named` attribute value of an attributed term `(! t :attr v … :named
/// name …)`, returned as a borrowed name to bind script-globally as an alias for
/// the inner term `t`. `items` is the full `!` application list. Scans the
/// `:attr value` pairs after the term (index 2 onward), mirroring
/// [`named_label`] but yielding the borrowed `&str` the iterative parser needs.
fn attribute_named_name(items: &[SExpr]) -> Option<&str> {
    let mut i = 2;
    while i + 1 < items.len() {
        if items[i].atom() == Some(":named") {
            return items[i + 1].atom();
        }
        i += 2;
    }
    None
}

/// The `:named` label of an attributed assertion `(! t :named name …)`, if any.
fn named_label(body: &SExpr) -> Option<String> {
    let items = body.list()?;
    if items.first().and_then(SExpr::atom) != Some("!") {
        return None;
    }
    // Scan `:attr value` pairs after the term for `:named`.
    let mut i = 2;
    while i + 1 < items.len() {
        if items[i].atom() == Some(":named") {
            return items[i + 1].atom().map(str::to_owned);
        }
        i += 2;
    }
    None
}

fn parse_declare_fun(
    script: &mut Script,
    sort_aliases: &HashMap<String, Sort>,
    items: &[SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 4, "declare-fun")?;
    let name = atom_at(items, 1)?;
    let args = items
        .get(2)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("declare-fun args".to_owned()))?;
    // A 0-ary `String` constant is the packed bounded-string bit-vector plus its
    // canonical well-formedness constraint (ADR-0029), exactly like
    // `declare-const ... String`. Detected syntactically (not by the resolved
    // `BitVec(STRING_TOTAL)` sort) so a genuine `(_ BitVec 68)` constant is never
    // forced into the string well-formedness shape.
    if args.is_empty() && sexpr_at(items, 3)?.atom() == Some("String") {
        declare_string_symbol(script, name)?;
        return Ok(());
    }
    let result = parse_sort(&script.arena, sort_aliases, sexpr_at(items, 3)?)?;
    if args.is_empty() {
        // 0-ary: a plain constant symbol.
        script.arena.declare(name, result)?;
    } else {
        // n-ary: an uninterpreted function (ADR-0013).
        let params = args
            .iter()
            .map(|s| parse_sort(&script.arena, sort_aliases, s))
            .collect::<Result<Vec<Sort>, SmtError>>()?;
        script.arena.declare_fun(name, &params, result)?;
    }
    Ok(())
}

/// Adds the constructors `(cname (sel sort) …)` of one datatype `dt` to the
/// arena. Sorts resolve through `parse_sort`, so a field may reference any
/// already-declared datatype (the sorts in a `declare-datatypes` group are all
/// declared before their constructors, supporting (mutual) recursion).
fn add_datatype_constructors(
    script: &mut Script,
    sort_aliases: &HashMap<String, Sort>,
    dt: axeyum_ir::DatatypeId,
    ctors: &[SExpr],
) -> Result<(), SmtError> {
    for ctor in ctors {
        let parts = ctor
            .list()
            .filter(|p| !p.is_empty())
            .ok_or_else(|| SmtError::Syntax("datatype constructor".to_owned()))?;
        let cname = parts[0]
            .atom()
            .ok_or_else(|| SmtError::Syntax("constructor name".to_owned()))?
            .to_owned();
        let mut fields = Vec::with_capacity(parts.len() - 1);
        for field in &parts[1..] {
            let fp = field
                .list()
                .filter(|p| p.len() == 2)
                .ok_or_else(|| SmtError::Syntax("(selector sort)".to_owned()))?;
            let sname = fp[0]
                .atom()
                .ok_or_else(|| SmtError::Syntax("selector name".to_owned()))?
                .to_owned();
            let fsort = parse_sort(&script.arena, sort_aliases, &fp[1])?;
            fields.push((sname, fsort));
        }
        script.arena.add_constructor(dt, &cname, &fields);
    }
    Ok(())
}

/// `(declare-datatype Name (ctor …))` — a single (non-parametric) datatype.
fn parse_declare_datatype(
    script: &mut Script,
    sort_aliases: &HashMap<String, Sort>,
    items: &[SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 3, "declare-datatype")?;
    let name = atom_at(items, 1)?;
    let ctors = items
        .get(2)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("datatype constructor list".to_owned()))?;
    let dt = script.arena.declare_datatype(name);
    add_datatype_constructors(script, sort_aliases, dt, ctors)
}

/// `(declare-datatypes ((Name 0) …) ((ctors) …))` (SMT-LIB 2.6) — one or more
/// non-parametric datatypes (mutual recursion supported; parametric `arity > 0`
/// is rejected). All sorts are declared first, then their constructors, so a
/// field sort may reference any datatype in the group.
fn parse_declare_datatypes(
    script: &mut Script,
    sort_aliases: &HashMap<String, Sort>,
    items: &[SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 3, "declare-datatypes")?;
    let sort_decls = items
        .get(1)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("datatype sort declarations".to_owned()))?;
    let groups = items
        .get(2)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("datatype constructor groups".to_owned()))?;
    if sort_decls.len() != groups.len() {
        return Err(SmtError::Syntax(
            "declare-datatypes: sort and constructor lists differ in length".to_owned(),
        ));
    }
    // First pass: declare every datatype sort (so constructor fields can recurse).
    let mut ids = Vec::with_capacity(sort_decls.len());
    for decl in sort_decls {
        let pair = decl
            .list()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| SmtError::Syntax("(Name arity)".to_owned()))?;
        let name = pair[0]
            .atom()
            .ok_or_else(|| SmtError::Syntax("datatype name".to_owned()))?;
        let arity = pair[1].atom().and_then(|s| s.parse::<u32>().ok());
        if arity != Some(0) {
            return Err(SmtError::Unsupported(
                "parametric datatypes (arity > 0)".to_owned(),
            ));
        }
        ids.push(script.arena.declare_datatype(name));
    }
    // Second pass: add each datatype's constructors.
    for (dt, group) in ids.into_iter().zip(groups) {
        let ctors = group
            .list()
            .ok_or_else(|| SmtError::Syntax("datatype constructor list".to_owned()))?;
        add_datatype_constructors(script, sort_aliases, dt, ctors)?;
    }
    Ok(())
}

fn parse_declare_const(
    script: &mut Script,
    sort_aliases: &HashMap<String, Sort>,
    items: &[SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 3, "declare-const")?;
    let name = atom_at(items, 1)?;
    // String front-end (ADR-0029, first slice): a String constant is a packed
    // bit-vector plus its canonical well-formedness constraint, asserted in both
    // the flat and incremental views so equality/disequality decide via the BV path.
    if sexpr_at(items, 2)?.atom() == Some("String") {
        return declare_string_symbol(script, name);
    }
    let sort = parse_sort(&script.arena, sort_aliases, sexpr_at(items, 2)?)?;
    script.arena.declare(name, sort)?;
    Ok(())
}

/// Declares a 0-ary `String` symbol: a packed bounded-string bit-vector plus its
/// canonical well-formedness constraint (length ≤ max, padding bytes zero),
/// asserted in both the flat and incremental views so equality/disequality and
/// the `str.*` operators decide via the BV path (ADR-0029). Shared by
/// `declare-const ... String` and 0-ary `declare-fun ... String`.
fn declare_string_symbol(script: &mut Script, name: &str) -> Result<(), SmtError> {
    let sym = script.arena.declare(name, Sort::BitVec(STRING_TOTAL))?;
    let v = script.arena.var(sym);
    let wf = string_wellformed(&mut script.arena, v)?;
    script.assertions.push(wf);
    script.assertion_names.push(None);
    script.commands.push(ScriptCommand::Assert(wf));
    Ok(())
}

fn parse_define_fun<'a>(
    script: &mut Script,
    aliases: &mut HashMap<String, TermId>,
    macros: &mut HashMap<String, MacroDef<'a>>,
    sort_aliases: &HashMap<String, Sort>,
    named: &mut HashMap<String, TermId>,
    items: &'a [SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 5, "define-fun")?;
    let name = atom_at(items, 1)?;
    let args = items
        .get(2)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("define-fun args".to_owned()))?;
    let declared_sort = parse_sort(&script.arena, sort_aliases, sexpr_at(items, 3)?)?;
    let body_expr = sexpr_at(items, 4)?;
    if args.is_empty() {
        parse_define_fun_alias(
            script,
            aliases,
            macros,
            named,
            name,
            declared_sort,
            body_expr,
        )
    } else {
        macros.insert(
            name.to_owned(),
            MacroDef {
                params: parse_params(&script.arena, sort_aliases, args)?,
                result_sort: declared_sort,
                body: body_expr,
            },
        );
        Ok(())
    }
}

/// `(define-const c S body)` — the nullary `define-fun` abbreviation
/// (SMT-LIB §3.7.2). Items are `[define-const, c, S, body]` (length 4), versus
/// `define-fun`'s `[define-fun, c, (), S, body]`. We parse the same pieces and
/// dispatch straight to [`parse_define_fun_alias`], so the binding semantics
/// (sort check + `aliases` insertion) are byte-for-byte identical to a no-args
/// `define-fun`.
fn parse_define_const<'a>(
    script: &mut Script,
    aliases: &mut HashMap<String, TermId>,
    macros: &mut HashMap<String, MacroDef<'a>>,
    sort_aliases: &HashMap<String, Sort>,
    named: &mut HashMap<String, TermId>,
    items: &'a [SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 4, "define-const")?;
    let name = atom_at(items, 1)?;
    let declared_sort = parse_sort(&script.arena, sort_aliases, sexpr_at(items, 2)?)?;
    let body_expr = sexpr_at(items, 3)?;
    parse_define_fun_alias(
        script,
        aliases,
        macros,
        named,
        name,
        declared_sort,
        body_expr,
    )
}

fn parse_define_fun_alias(
    script: &mut Script,
    aliases: &mut HashMap<String, TermId>,
    macros: &HashMap<String, MacroDef<'_>>,
    named: &mut HashMap<String, TermId>,
    name: &str,
    declared_sort: Sort,
    body_expr: &SExpr,
) -> Result<(), SmtError> {
    let body = parse_term(&mut script.arena, body_expr, aliases, macros, named)?;
    let body_sort = script.arena.sort_of(body);
    if body_sort != declared_sort {
        return Err(SmtError::Ir(axeyum_ir::IrError::SortsDiffer(
            declared_sort,
            body_sort,
        )));
    }
    aliases.insert(name.to_owned(), body);
    Ok(())
}

#[derive(Clone, Copy)]
struct Param<'a> {
    name: &'a str,
    sort: Sort,
}

struct MacroDef<'a> {
    params: Vec<Param<'a>>,
    result_sort: Sort,
    body: &'a SExpr,
}

fn parse_params<'a>(
    arena: &TermArena,
    sort_aliases: &HashMap<String, Sort>,
    args: &'a [SExpr],
) -> Result<Vec<Param<'a>>, SmtError> {
    let mut params = Vec::with_capacity(args.len());
    for arg in args {
        let pair = arg
            .list()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| SmtError::Syntax("define-fun parameter".to_owned()))?;
        let name = pair[0]
            .atom()
            .ok_or_else(|| SmtError::Syntax("define-fun parameter name".to_owned()))?;
        if params.iter().any(|p: &Param<'_>| p.name == name) {
            return Err(SmtError::Syntax(format!(
                "duplicate define-fun parameter `{name}`"
            )));
        }
        params.push(Param {
            name,
            sort: parse_sort(arena, sort_aliases, &pair[1])?,
        });
    }
    Ok(params)
}

fn exact_len(items: &[SExpr], expected: usize, head: &str) -> Result<(), SmtError> {
    if items.len() == expected {
        Ok(())
    } else {
        Err(SmtError::Syntax(format!(
            "`{head}` expects {} arguments, got {}",
            expected.saturating_sub(1),
            items.len().saturating_sub(1)
        )))
    }
}

fn atom_at(items: &[SExpr], i: usize) -> Result<&str, SmtError> {
    items
        .get(i)
        .and_then(SExpr::atom)
        .ok_or_else(|| SmtError::Syntax(format!("expected atom at position {i}")))
}

fn sexpr_at(items: &[SExpr], i: usize) -> Result<&SExpr, SmtError> {
    items
        .get(i)
        .ok_or_else(|| SmtError::Syntax(format!("expected argument at position {i}")))
}

fn parse_sort(
    arena: &TermArena,
    sort_aliases: &HashMap<String, Sort>,
    e: &SExpr,
) -> Result<Sort, SmtError> {
    match e {
        SExpr::Atom(a) if a == "Bool" => Ok(Sort::Bool),
        SExpr::Atom(a) if a == "Int" => Ok(Sort::Int),
        SExpr::Atom(a) if a == "Real" => Ok(Sort::Real),
        // Floating-point sorts are first-class `Sort::Float` (ADR-0026), lowered
        // structurally to `BitVec(exp + sig)`; the distinct sort lets conversions
        // tell a float operand from a plain bit-vector.
        SExpr::Atom(a) if a == "Float16" => Ok(Sort::Float { exp: 5, sig: 11 }),
        SExpr::Atom(a) if a == "Float32" => Ok(Sort::Float { exp: 8, sig: 24 }),
        SExpr::Atom(a) if a == "Float64" => Ok(Sort::Float { exp: 11, sig: 53 }),
        SExpr::Atom(a) if a == "Float128" => Ok(Sort::Float { exp: 15, sig: 113 }),
        // The `String` sort is the bounded-model fragment (ADR-0029): a string of
        // up to `STRING_MAX_LEN` bytes is one bit-vector packing a length (low) and
        // the content bytes (above). The sort resolves to that `BitVec`; declared
        // string symbols additionally carry a canonical well-formedness constraint
        // (asserted at `declare-*` time) so equal strings share one bit pattern and
        // `=`/`distinct` decide via the BV path. `Seq` (unbounded sequences) has no
        // sound bounded lowering yet, so it stays a scoped `Unsupported`.
        SExpr::Atom(a) if a == "String" => Ok(Sort::BitVec(STRING_TOTAL)),
        SExpr::Atom(a) if a == "Seq" => Err(SmtError::Unsupported(format!(
            "the `{a}` sort is not yet wired into the SMT-LIB front end; the bounded-string \
             theory exists at the API level (ADR-0025/0029)"
        ))),
        SExpr::List(items) => {
            if items.len() == 4
                && items[0].atom() == Some("_")
                && items[1].atom() == Some("FloatingPoint")
                && let (Some(eb), Some(sb)) = (
                    items[2].atom().and_then(|s| s.parse::<u32>().ok()),
                    items[3].atom().and_then(|s| s.parse::<u32>().ok()),
                )
            {
                return Ok(Sort::Float { exp: eb, sig: sb });
            }
            if items.len() == 3
                && items[0].atom() == Some("_")
                && items[1].atom() == Some("BitVec")
                && let Some(w) = items[2].atom().and_then(|s| s.parse::<u32>().ok())
            {
                return Ok(Sort::BitVec(w));
            }
            if items.len() == 3 && items[0].atom() == Some("Array") {
                let index = parse_sort(arena, sort_aliases, &items[1])?;
                let element = parse_sort(arena, sort_aliases, &items[2])?;
                if let (Sort::BitVec(index), Sort::BitVec(element)) = (index, element) {
                    return Ok(Sort::Array { index, element });
                }
                return Err(SmtError::Unsupported(format!(
                    "only bit-vector-indexed/valued arrays are supported: {e:?}"
                )));
            }
            Err(SmtError::Unsupported(format!("sort {e:?}")))
        }
        // A declared datatype sort (ADR-0022), referenced by name, or a
        // `define-sort` alias (looked up after builtins/datatypes so a builtin
        // sort name can never be shadowed).
        SExpr::Atom(a) => arena
            .find_datatype(a)
            .map(Sort::Datatype)
            .or_else(|| sort_aliases.get(a).copied())
            .ok_or_else(|| SmtError::Unsupported(format!("sort `{a}`"))),
    }
}

/// `(define-sort name () body)` — a 0-arity sort alias (ADR-pending command
/// parity): `name` resolves to `body` wherever a sort is expected. The body is
/// parsed through [`parse_sort`], so an alias may reference an earlier alias.
/// Parametric aliases (`(define-sort Pair (X) …)`) are not supported.
///
/// # Errors
///
/// [`SmtError::Unsupported`] for a parametric (non-empty parameter list) alias,
/// and [`SmtError::Syntax`] for a malformed form, a name that is a builtin sort,
/// or a duplicate alias.
fn parse_define_sort(
    script: &mut Script,
    sort_aliases: &mut HashMap<String, Sort>,
    items: &[SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 4, "define-sort")?;
    let name = atom_at(items, 1)?;
    let params = items
        .get(2)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("define-sort parameter list".to_owned()))?;
    if !params.is_empty() {
        return Err(SmtError::Unsupported("parametric define-sort".to_owned()));
    }
    if is_builtin_sort_name(name) || script.arena.find_datatype(name).is_some() {
        return Err(SmtError::Syntax(format!(
            "define-sort: `{name}` is a builtin or declared sort"
        )));
    }
    if sort_aliases.contains_key(name) {
        return Err(SmtError::Syntax(format!(
            "define-sort: duplicate sort alias `{name}`"
        )));
    }
    let body = parse_sort(&script.arena, sort_aliases, sexpr_at(items, 3)?)?;
    sort_aliases.insert(name.to_owned(), body);
    Ok(())
}

/// `(declare-sort U n)` — an uninterpreted sort.
///
/// The arity-0 case `(declare-sort U 0)` is the common `QF_UF`/`QF_UFLIA` shape:
/// `U` is registered (in the shared `sort_aliases` map, alongside `define-sort`
/// aliases) as `BitVec(uninterpreted_width)`. Every later use of `U` as a sort —
/// in `declare-fun` parameter/result positions, `=`, `distinct`, `ite`, array
/// index/element, etc. — then resolves through [`parse_sort`] to that bit-vector
/// width, so the whole script becomes `QF_UFBV`/`QF_UFLIA`-over-BV, which axeyum
/// already decides. The modeling is sound for any width chosen by
/// [`uninterpreted_sort_width`]; see its soundness argument for why no wrong
/// `unsat` is possible.
///
/// Parametric declared sorts (`(declare-sort List 1)` and higher) would model a
/// *family* of sorts, which the scalar BV encoding cannot express, so they are
/// rejected as [`SmtError::Unsupported`] (rare in practice).
///
/// # Errors
///
/// [`SmtError::Unsupported`] for a parametric (arity ≥ 1) sort; [`SmtError::Syntax`]
/// for a malformed form, a non-numeric arity, a name that is a builtin sort, or a
/// duplicate sort name (mirroring [`parse_define_sort`]).
fn parse_declare_sort(
    script: &mut Script,
    sort_aliases: &mut HashMap<String, Sort>,
    uninterpreted_width: u32,
    items: &[SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 3, "declare-sort")?;
    let name = atom_at(items, 1)?;
    let arity = atom_at(items, 2)?
        .parse::<u32>()
        .map_err(|_| SmtError::Syntax("declare-sort arity must be a numeral".to_owned()))?;
    if arity != 0 {
        return Err(SmtError::Unsupported(format!(
            "parametric/arity-{arity} declared sort `{name}` (only arity-0 \
             uninterpreted sorts are modeled, as BitVec)"
        )));
    }
    if is_builtin_sort_name(name) || script.arena.find_datatype(name).is_some() {
        return Err(SmtError::Syntax(format!(
            "declare-sort: `{name}` is a builtin or declared sort"
        )));
    }
    if sort_aliases.contains_key(name) {
        return Err(SmtError::Syntax(format!(
            "declare-sort: duplicate sort name `{name}`"
        )));
    }
    sort_aliases.insert(name.to_owned(), Sort::BitVec(uninterpreted_width));
    Ok(())
}

/// Whether `name` is a builtin (atom-named) sort keyword, so a `define-sort`
/// alias may not redefine it. Indexed/compound sort heads (`BitVec`, `Array`,
/// `FloatingPoint`) only ever appear inside a list, never as a bare alias name,
/// so they are covered by the parser, not this guard.
fn is_builtin_sort_name(name: &str) -> bool {
    matches!(
        name,
        "Bool" | "Int" | "Real" | "Float16" | "Float32" | "Float64" | "Float128" | "String" | "Seq"
    )
}

/// One frame of the iterative term converter.
enum Frame<'a> {
    /// Evaluate this expression (pushing children first when needed).
    Eval(&'a SExpr),
    /// After the inner term of `(! t :named name)` is on the result stack, bind
    /// `name → t` in the script-global `:named` map (the term itself stays on
    /// the stack as the attributed term's value).
    RegisterNamed { name: &'a str },
    /// Pop `argc` results and apply the operator list.
    Apply { items: &'a [SExpr], argc: usize },
    /// Pop `argc` results and apply a rounding-mode FP op. The mode is the first
    /// child (a `RoundingMode` value, not a term) parsed before queueing.
    ApplyFpRounded {
        items: &'a [SExpr],
        mode: RoundingMode,
        argc: usize,
    },
    /// Like [`Frame::ApplyFpRounded`] but for an *indexed* head, e.g.
    /// `((_ to_fp 8 24) RM x)` or `((_ fp.to_sbv 32) RM x)`.
    ApplyFpRoundedIndexed {
        items: &'a [SExpr],
        mode: RoundingMode,
        argc: usize,
    },
    /// Pop `argc` results and expand a parameterized `define-fun` body.
    ApplyMacro { name: &'a str, argc: usize },
    /// Check the sort of the most recent result.
    CheckSort { expected: Sort, context: &'a str },
    /// Pop one binding scope after a `let` body finishes.
    PopScope,
    /// Pop `count` evaluated binding values, bind them, then queue the body.
    BindLet {
        names: Vec<&'a str>,
        body: &'a SExpr,
    },
    /// Enter a quantifier scope (bound names → fresh symbol vars), then queue
    /// the body, scope pop, and the quantifier wrap.
    BindQuantifier {
        bindings: Vec<(&'a str, TermId)>,
        syms: Vec<axeyum_ir::SymbolId>,
        is_forall: bool,
        body: &'a SExpr,
    },
    /// Pop the quantifier body and wrap it in `forall`/`exists` over `syms`.
    ApplyQuantifier {
        syms: Vec<axeyum_ir::SymbolId>,
        is_forall: bool,
    },
    /// Pop the just-evaluated scrutinee `e` and set up the `match` desugaring
    /// (ADR-pending datatype `match`): plan per-case testers and binding scopes,
    /// queue each case body's evaluation under its scope, then a [`Frame::CombineMatch`]
    /// to fold the case results into a right-nested `ite`.
    MatchScrutinee { cases: &'a [SExpr] },
    /// Push a precomputed binding scope (a `match` case's pattern variables →
    /// selector terms); paired with a later [`Frame::PopScope`].
    PushScope(HashMap<&'a str, TermId>),
    /// Pop the `n = testers.len()` evaluated case-result terms and fold them into
    /// a right-nested `ite`: each `Some(t)` is the `is-C` guard for that case, and
    /// the final (innermost else) case carries `None` (unconditional, exhaustive).
    CombineMatch { testers: Vec<Option<TermId>> },
}

#[allow(clippy::too_many_lines)]
fn parse_term<'a>(
    arena: &mut TermArena,
    root: &'a SExpr,
    aliases: &HashMap<String, TermId>,
    macros: &HashMap<String, MacroDef<'a>>,
    named: &mut HashMap<String, TermId>,
) -> Result<TermId, SmtError> {
    let mut frames: Vec<Frame> = vec![Frame::Eval(root)];
    let mut results: Vec<TermId> = Vec::new();
    let mut scopes: Vec<HashMap<&'a str, TermId>> = Vec::new();

    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Eval(e) => queue_eval(
                arena,
                e,
                aliases,
                macros,
                named,
                &scopes,
                &mut frames,
                &mut results,
            )?,
            Frame::RegisterNamed { name } => {
                // The just-evaluated `(! t :named name)` inner term is on top of
                // the stack; bind `name → t` script-globally (it stays on the
                // stack as the attributed term's value).
                let t = *results
                    .last()
                    .ok_or_else(|| SmtError::Syntax("`:named` term".to_owned()))?;
                named.insert(name.to_owned(), t);
            }
            Frame::Apply { items, argc } => {
                let args = results.split_off(results.len() - argc);
                results.push(apply_op(arena, items, &args)?);
            }
            Frame::ApplyFpRounded { items, mode, argc } => {
                let args = results.split_off(results.len() - argc);
                results.push(apply_fp_rounded(arena, items, mode, &args)?);
            }
            Frame::ApplyFpRoundedIndexed { items, mode, argc } => {
                let args = results.split_off(results.len() - argc);
                results.push(apply_fp_rounded_indexed(arena, items, mode, &args)?);
            }
            Frame::ApplyMacro { name, argc } => {
                queue_macro_expansion(
                    arena,
                    macros,
                    &mut scopes,
                    &mut frames,
                    &mut results,
                    name,
                    argc,
                )?;
            }
            Frame::CheckSort { expected, context } => {
                check_recent_sort(arena, &results, expected, context)?;
            }
            Frame::BindLet { names, body } => {
                bind_let_scope(&mut scopes, &mut results, names);
                frames.push(Frame::PopScope);
                frames.push(Frame::Eval(body));
            }
            Frame::BindQuantifier {
                bindings,
                syms,
                is_forall,
                body,
            } => {
                let mut scope = HashMap::new();
                for (name, term) in bindings {
                    scope.insert(name, term);
                }
                scopes.push(scope);
                frames.push(Frame::ApplyQuantifier { syms, is_forall });
                frames.push(Frame::PopScope);
                frames.push(Frame::Eval(body));
            }
            Frame::ApplyQuantifier { syms, is_forall } => {
                let mut acc = results
                    .pop()
                    .ok_or_else(|| SmtError::Syntax("quantifier body".to_owned()))?;
                for &sym in syms.iter().rev() {
                    acc = if is_forall {
                        arena.forall(sym, acc)?
                    } else {
                        arena.exists(sym, acc)?
                    };
                }
                results.push(acc);
            }
            Frame::PopScope => {
                scopes.pop();
            }
            Frame::MatchScrutinee { cases } => {
                let scrutinee = results
                    .pop()
                    .ok_or_else(|| SmtError::Syntax("match scrutinee".to_owned()))?;
                queue_match(arena, scrutinee, cases, &mut frames)?;
            }
            Frame::PushScope(scope) => {
                scopes.push(scope);
            }
            Frame::CombineMatch { testers } => {
                combine_match(arena, &mut results, &testers)?;
            }
        }
    }
    if results.len() == 1 {
        Ok(results.pop().expect("one result"))
    } else {
        Err(SmtError::Syntax(format!(
            "term conversion produced {} results",
            results.len()
        )))
    }
}

#[allow(clippy::too_many_arguments)]
fn queue_eval<'a>(
    arena: &mut TermArena,
    expr: &'a SExpr,
    aliases: &HashMap<String, TermId>,
    macros: &HashMap<String, MacroDef<'a>>,
    named: &HashMap<String, TermId>,
    scopes: &[HashMap<&'a str, TermId>],
    frames: &mut Vec<Frame<'a>>,
    results: &mut Vec<TermId>,
) -> Result<(), SmtError> {
    match expr {
        SExpr::Atom(a) => results.push(parse_atom(arena, a, aliases, named, scopes)?),
        SExpr::List(items) => queue_list_eval(arena, items, macros, frames, results)?,
    }
    Ok(())
}

fn queue_list_eval<'a>(
    arena: &mut TermArena,
    items: &'a [SExpr],
    macros: &HashMap<String, MacroDef<'a>>,
    frames: &mut Vec<Frame<'a>>,
    results: &mut Vec<TermId>,
) -> Result<(), SmtError> {
    let head = items
        .first()
        .ok_or_else(|| SmtError::Syntax("empty application".to_owned()))?;
    if head.atom() == Some("_") {
        results.push(parse_indexed_constant(arena, items)?);
    } else if head.atom() == Some("!") {
        // Attributed term `(! t :attr v ...)` denotes `t`. Non-`:named`
        // annotations (`:pattern` triggers, …) are hints we drop. A `:named foo`
        // attribute additionally binds `foo` as a script-global alias for `t`,
        // so later bare references to `foo` resolve — we queue a
        // [`Frame::RegisterNamed`] to record the binding once `t` is evaluated.
        let inner = items
            .get(1)
            .ok_or_else(|| SmtError::Syntax("`!` expects a term".to_owned()))?;
        if let Some(name) = attribute_named_name(items) {
            frames.push(Frame::RegisterNamed { name });
        }
        frames.push(Frame::Eval(inner));
    } else if head.atom() == Some("let") {
        queue_let(items, frames)?;
    } else if head.atom() == Some("match") {
        queue_match_scrutinee(items, frames)?;
    } else if head.atom() == Some("forall") || head.atom() == Some("exists") {
        let is_forall = head.atom() == Some("forall");
        queue_quantifier(arena, items, is_forall, frames)?;
    } else if head.atom() == Some("as") && items.len() == 3 {
        // Sort ascription `(as t S)` denotes `t` — it only annotates the sort of
        // an otherwise-determined term (SMT-LIB §3.6, "qualified identifier").
        // Quantifier-free axeyum already infers every term's sort, so the
        // ascription is an identity we drop: evaluate the inner term and ignore
        // the trailing sort s-expr (which is a *sort*, not a term, so it must
        // not be queued for term evaluation). The `((as const S) v)` constant-
        // array form is an *application* whose head is itself `(as const S)`;
        // it has a list head and is handled in [`apply_op`], not here.
        frames.push(Frame::Eval(&items[1]));
    } else if let Some(name) = head.atom()
        && is_fp_rounded_op(name)
    {
        // Rounding-mode FP ops `(fp.add RM x y)`: the first argument is a
        // `RoundingMode` value (not a term), so parse it here and queue only the
        // operand children.
        let mode_expr = items
            .get(1)
            .ok_or_else(|| SmtError::Syntax(format!("{name} expects a rounding mode")))?;
        let mode = parse_rounding_mode(mode_expr)
            .ok_or_else(|| SmtError::Syntax(format!("{name}: unrecognized rounding mode")))?;
        let operands = &items[2..];
        frames.push(Frame::ApplyFpRounded {
            items,
            mode,
            argc: operands.len(),
        });
        for child in operands.iter().rev() {
            frames.push(Frame::Eval(child));
        }
    } else if let Some(idx) = head.list()
        && idx.first().and_then(SExpr::atom) == Some("_")
        && idx
            .get(1)
            .and_then(SExpr::atom)
            .is_some_and(is_fp_indexed_conversion)
        && items
            .get(1)
            .is_some_and(|e| parse_rounding_mode(e).is_some())
    {
        // Indexed rounding-mode FP conversions `((_ to_fp eb sb) RM x)`,
        // `((_ fp.to_sbv m) RM x)`, …: the leading `RM` is a value, not a term.
        // (The mode-free bit-reinterpret `((_ to_fp eb sb) x)` has no RM here, so
        // it falls through to the generic indexed-application path.)
        let mode = parse_rounding_mode(&items[1]).expect("checked");
        let operands = &items[2..];
        frames.push(Frame::ApplyFpRoundedIndexed {
            items,
            mode,
            argc: operands.len(),
        });
        for child in operands.iter().rev() {
            frames.push(Frame::Eval(child));
        }
    } else if let Some(name) = head.atom()
        && macros.contains_key(name)
    {
        queue_children(
            items,
            frames,
            Frame::ApplyMacro {
                name,
                argc: items.len() - 1,
            },
        );
    } else {
        queue_children(
            items,
            frames,
            Frame::Apply {
                items,
                argc: items.len() - 1,
            },
        );
    }
    Ok(())
}

fn queue_children<'a>(items: &'a [SExpr], frames: &mut Vec<Frame<'a>>, apply: Frame<'a>) {
    frames.push(apply);
    for child in items[1..].iter().rev() {
        frames.push(Frame::Eval(child));
    }
}

/// Queues a quantifier `(forall ((x T) ..) body)`: each bound variable becomes
/// a fresh arena symbol (uniquely named to avoid capture), scoped to `body`,
/// and the body is wrapped in `forall`/`exists` over those symbols (ADR-0016).
fn queue_quantifier<'a>(
    arena: &mut TermArena,
    items: &'a [SExpr],
    is_forall: bool,
    frames: &mut Vec<Frame<'a>>,
) -> Result<(), SmtError> {
    let keyword = if is_forall { "forall" } else { "exists" };
    exact_len(items, 3, keyword)?;
    let binding_list = items
        .get(1)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax(format!("{keyword} bindings")))?;
    if binding_list.is_empty() {
        return Err(SmtError::Syntax(format!(
            "{keyword} needs >= 1 bound variable"
        )));
    }
    let body = sexpr_at(items, 2)?;

    let mut bindings = Vec::with_capacity(binding_list.len());
    let mut syms = Vec::with_capacity(binding_list.len());
    for binding in binding_list {
        let pair = binding
            .list()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| SmtError::Syntax(format!("{keyword} binding pair")))?;
        let name = pair[0]
            .atom()
            .ok_or_else(|| SmtError::Syntax(format!("{keyword} binding name")))?;
        // Quantifier binder sorts are parsed in term-conversion context; sort
        // aliases are resolved at declaration sites, not threaded here.
        let no_aliases: HashMap<String, Sort> = HashMap::new();
        let sort = parse_sort(arena, &no_aliases, &pair[1])?;
        let sym = fresh_quantifier_symbol(arena, name, sort)?;
        bindings.push((name, arena.var(sym)));
        syms.push(sym);
    }
    frames.push(Frame::BindQuantifier {
        bindings,
        syms,
        is_forall,
        body,
    });
    Ok(())
}

/// Declares a uniquely-named fresh symbol for a quantifier's bound variable, so
/// it cannot capture a free symbol or another binder's variable.
fn fresh_quantifier_symbol(
    arena: &mut TermArena,
    base: &str,
    sort: Sort,
) -> Result<axeyum_ir::SymbolId, SmtError> {
    let mut index = 0u32;
    loop {
        let candidate = format!("!q.{base}.{index}");
        if arena.find_symbol(&candidate).is_none() {
            return Ok(arena.declare(&candidate, sort)?);
        }
        index += 1;
    }
}

/// A fresh, unconstrained `BitVec(width)` value standing for the *unspecified*
/// result of an out-of-domain FP→int conversion (NaN/∞/out-of-range; ADR-0026).
/// Keyed deterministically by `(tag, operand, width, mode)` so two occurrences of
/// the **same** conversion share one value — an FP→int conversion is a function,
/// so `(= (fp.to_ubv x) (fp.to_ubv x))` must hold even when the value is
/// unspecified.
fn fresh_conversion_value(
    arena: &mut TermArena,
    tag: &str,
    operand: TermId,
    width: u32,
    mode: RoundingMode,
) -> Result<TermId, SmtError> {
    let name = format!("!fp.{tag}.{}.{width}.{mode:?}", operand.index());
    let sym = match arena.find_symbol(&name) {
        Some(s) => s,
        None => arena.declare(&name, Sort::BitVec(width))?,
    };
    Ok(arena.var(sym))
}

fn queue_let<'a>(items: &'a [SExpr], frames: &mut Vec<Frame<'a>>) -> Result<(), SmtError> {
    exact_len(items, 3, "let")?;
    let bindings = items
        .get(1)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("let bindings".to_owned()))?;
    let body = sexpr_at(items, 2)?;
    let names = parse_let_names(bindings)?;
    frames.push(Frame::BindLet { names, body });
    for b in bindings.iter().rev() {
        frames.push(Frame::Eval(&b.list().expect("checked")[1]));
    }
    Ok(())
}

fn parse_let_names(bindings: &[SExpr]) -> Result<Vec<&str>, SmtError> {
    let mut names = Vec::with_capacity(bindings.len());
    for binding in bindings {
        let pair = binding
            .list()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| SmtError::Syntax("let binding pair".to_owned()))?;
        names.push(
            pair[0]
                .atom()
                .ok_or_else(|| SmtError::Syntax("let name".to_owned()))?,
        );
    }
    for (i, name) in names.iter().enumerate() {
        if names[..i].contains(name) {
            return Err(SmtError::Syntax(format!("duplicate let binding `{name}`")));
        }
    }
    Ok(names)
}

fn queue_macro_expansion<'a>(
    arena: &TermArena,
    macros: &HashMap<String, MacroDef<'a>>,
    scopes: &mut Vec<HashMap<&'a str, TermId>>,
    frames: &mut Vec<Frame<'a>>,
    results: &mut Vec<TermId>,
    name: &'a str,
    arity: usize,
) -> Result<(), SmtError> {
    let actuals = results.split_off(results.len() - arity);
    let def = macros
        .get(name)
        .ok_or_else(|| SmtError::Unsupported(format!("operator `{name}`")))?;
    if actuals.len() != def.params.len() {
        return Err(SmtError::Syntax(format!(
            "`{name}` expects {} arguments, got {}",
            def.params.len(),
            actuals.len()
        )));
    }
    let mut scope = HashMap::new();
    for (param, arg) in def.params.iter().zip(actuals) {
        let actual = arena.sort_of(arg);
        if actual != param.sort {
            return Err(SmtError::Ir(axeyum_ir::IrError::SortsDiffer(
                param.sort, actual,
            )));
        }
        scope.insert(param.name, arg);
    }
    scopes.push(scope);
    frames.push(Frame::PopScope);
    frames.push(Frame::CheckSort {
        expected: def.result_sort,
        context: name,
    });
    frames.push(Frame::Eval(def.body));
    Ok(())
}

fn check_recent_sort(
    arena: &TermArena,
    results: &[TermId],
    expected: Sort,
    context: &str,
) -> Result<(), SmtError> {
    let Some(&term) = results.last() else {
        return Err(SmtError::Syntax(format!(
            "`{context}` body produced no result"
        )));
    };
    let actual = arena.sort_of(term);
    if actual != expected {
        return Err(SmtError::Ir(axeyum_ir::IrError::SortsDiffer(
            expected, actual,
        )));
    }
    Ok(())
}

fn bind_let_scope<'a>(
    scopes: &mut Vec<HashMap<&'a str, TermId>>,
    results: &mut Vec<TermId>,
    names: Vec<&'a str>,
) {
    let values = results.split_off(results.len() - names.len());
    let mut scope = HashMap::new();
    for (name, value) in names.into_iter().zip(values) {
        scope.insert(name, value);
    }
    scopes.push(scope);
}

// --- datatype `match` desugaring (parse-time) --------------------------------
//
// SMT-LIB 2.6 `(match e ((pat result) ...))` is desugared at parse time to the
// datatype primitives the IR already has — `is-C` testers (`Op::DtTest`), field
// selectors (`Op::DtSelect`), and `ite` — so no IR or solver change is needed.
//
//   (match e ((C1 x y) r1) ((C2) r2) (z r3))
//     ⇒  (ite (is-C1 e) r1[x:=(selC1_0 e), y:=(selC1_1 e)]
//           (ite (is-C2 e) r2
//             r3[z := e]))
//
// Pattern variables bind by substitution into the case result via the same
// scope stack `let` uses, so nested matches/lets and shadowing work. The LAST
// case is always the unconditional `else` (SMT-LIB requires the match to be
// exhaustive); a non-exhaustive match (no trailing default and not all
// constructors covered) is rejected.

/// Queues `(match e (case ...))`: evaluate the scrutinee `e`, then the
/// [`Frame::MatchScrutinee`] plan that sets up the desugaring once `e`'s term
/// (and sort) is known.
fn queue_match_scrutinee<'a>(
    items: &'a [SExpr],
    frames: &mut Vec<Frame<'a>>,
) -> Result<(), SmtError> {
    if items.len() != 3 {
        return Err(SmtError::Syntax(
            "match expects `(match e (case ...))`".to_owned(),
        ));
    }
    let cases = items[2]
        .list()
        .filter(|c| !c.is_empty())
        .ok_or_else(|| SmtError::Syntax("match expects a non-empty case list".to_owned()))?;
    frames.push(Frame::MatchScrutinee { cases });
    frames.push(Frame::Eval(&items[1]));
    Ok(())
}

/// One planned `match` case: the `is-C` guard (`None` for the unconditional,
/// final/else case) and the pattern-variable scope to evaluate its body under.
struct MatchCasePlan<'a> {
    tester: Option<TermId>,
    scope: HashMap<&'a str, TermId>,
    body: &'a SExpr,
}

/// Sets up the `match` desugaring once the scrutinee term `scrutinee` is known:
/// resolves its datatype, plans every case (tester + pattern-variable scope),
/// checks exhaustiveness, and queues each case body's evaluation (under its
/// scope) followed by a [`Frame::CombineMatch`] fold.
///
/// # Errors
///
/// [`SmtError::Syntax`]/[`SmtError::Unsupported`] for a non-datatype scrutinee,
/// an unknown constructor, a wrong constructor field-arity, a default that is not
/// last, or a non-exhaustive match.
fn queue_match<'a>(
    arena: &mut TermArena,
    scrutinee: TermId,
    cases: &'a [SExpr],
    frames: &mut Vec<Frame<'a>>,
) -> Result<(), SmtError> {
    let dt = match arena.sort_of(scrutinee) {
        Sort::Datatype(dt) => dt,
        other => {
            return Err(SmtError::Syntax(format!(
                "match scrutinee must be a datatype value, got {other:?}"
            )));
        }
    };
    let plans = plan_match_cases(arena, scrutinee, dt, cases)?;
    let testers: Vec<Option<TermId>> = plans.iter().map(|p| p.tester).collect();
    frames.push(Frame::CombineMatch { testers });
    // Push each case's [PushScope, Eval(body), PopScope] block in reverse case
    // order so the results land case0, case1, … on the stack for CombineMatch.
    for plan in plans.into_iter().rev() {
        frames.push(Frame::PopScope);
        frames.push(Frame::Eval(plan.body));
        frames.push(Frame::PushScope(plan.scope));
    }
    Ok(())
}

/// Plans each `match` case over datatype `dt`: builds the `is-C` tester and the
/// pattern-variable → selector-term bindings, and validates the case set.
fn plan_match_cases<'a>(
    arena: &mut TermArena,
    scrutinee: TermId,
    dt: axeyum_ir::DatatypeId,
    cases: &'a [SExpr],
) -> Result<Vec<MatchCasePlan<'a>>, SmtError> {
    let mut plans: Vec<MatchCasePlan<'a>> = Vec::with_capacity(cases.len());
    let mut covered: Vec<axeyum_ir::ConstructorId> = Vec::new();
    let mut has_default = false;
    for (idx, case) in cases.iter().enumerate() {
        let parts = case
            .list()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| SmtError::Syntax("match case `(pattern result)`".to_owned()))?;
        let pattern = &parts[0];
        let body = &parts[1];
        if has_default {
            return Err(SmtError::Syntax(
                "match: a default (variable/wildcard) pattern must be the last case".to_owned(),
            ));
        }
        let is_last = idx + 1 == cases.len();
        match plan_one_case(arena, scrutinee, dt, pattern)? {
            CasePattern::Default { scope } => {
                has_default = true;
                plans.push(MatchCasePlan {
                    tester: None,
                    scope,
                    body,
                });
            }
            CasePattern::Constructor { ctor, scope } => {
                if covered.contains(&ctor) {
                    return Err(SmtError::Syntax(format!(
                        "match: duplicate case for constructor `{}`",
                        arena.constructor_name(ctor)
                    )));
                }
                covered.push(ctor);
                // The final case is the unconditional `else` of the right-nested
                // `ite`; for an exhaustive match its `is-C` guard is redundant.
                let tester = if is_last {
                    None
                } else {
                    Some(arena.dt_test(ctor, scrutinee)?)
                };
                plans.push(MatchCasePlan {
                    tester,
                    scope,
                    body,
                });
            }
        }
    }
    // Exhaustiveness: either a trailing default, or every constructor covered.
    if !has_default && covered.len() != arena.datatype_constructors(dt).len() {
        return Err(SmtError::Syntax(format!(
            "non-exhaustive match on `{}`: add the missing constructor cases or a default",
            arena.datatype_name(dt)
        )));
    }
    Ok(plans)
}

/// A single resolved `match` pattern.
enum CasePattern<'a> {
    /// A constructor pattern `(C x …)` or nullary `C`: matched by `is-C`, with
    /// each field variable bound to its selector applied to the scrutinee.
    Constructor {
        ctor: axeyum_ir::ConstructorId,
        scope: HashMap<&'a str, TermId>,
    },
    /// A variable `x` or wildcard `_` default: binds the whole scrutinee to `x`
    /// (`_` binds nothing) and always matches.
    Default { scope: HashMap<&'a str, TermId> },
}

/// Resolves one `match` pattern against datatype `dt`, building its binding scope.
fn plan_one_case<'a>(
    arena: &mut TermArena,
    scrutinee: TermId,
    dt: axeyum_ir::DatatypeId,
    pattern: &'a SExpr,
) -> Result<CasePattern<'a>, SmtError> {
    match pattern {
        // Bare symbol: a nullary constructor of `dt`, or a variable/wildcard.
        SExpr::Atom(name) => {
            if name == "_" {
                return Ok(CasePattern::Default {
                    scope: HashMap::new(),
                });
            }
            match arena.find_constructor(name) {
                Some(ctor) if arena.constructor_datatype(ctor) == dt => {
                    if !arena.constructor_fields(ctor).is_empty() {
                        return Err(SmtError::Syntax(format!(
                            "match: constructor `{name}` takes fields; use `({name} x …)`"
                        )));
                    }
                    Ok(CasePattern::Constructor {
                        ctor,
                        scope: HashMap::new(),
                    })
                }
                // A constructor of a *different* datatype is a name clash, not a
                // valid variable binder here; reject it.
                Some(_) => Err(SmtError::Syntax(format!(
                    "match: `{name}` is a constructor of another datatype, not a valid pattern \
                     for `{}`",
                    arena.datatype_name(dt)
                ))),
                // Not a constructor: a variable pattern binding the whole scrutinee.
                None => {
                    let mut scope = HashMap::new();
                    scope.insert(name.as_str(), scrutinee);
                    Ok(CasePattern::Default { scope })
                }
            }
        }
        // Constructor pattern `(C x1 … xk)`: bind each field variable to its
        // selector applied to the scrutinee.
        SExpr::List(parts) => {
            let cname = parts
                .first()
                .and_then(SExpr::atom)
                .ok_or_else(|| SmtError::Syntax("match constructor pattern head".to_owned()))?;
            let ctor = arena
                .find_constructor(cname)
                .filter(|&c| arena.constructor_datatype(c) == dt)
                .ok_or_else(|| {
                    SmtError::Unsupported(format!(
                        "match: unknown constructor `{cname}` for `{}`",
                        arena.datatype_name(dt)
                    ))
                })?;
            let field_count = arena.constructor_fields(ctor).len();
            let vars = &parts[1..];
            if vars.len() != field_count {
                return Err(SmtError::Syntax(format!(
                    "match: constructor `{cname}` binds {field_count} field(s), pattern has {}",
                    vars.len()
                )));
            }
            let mut scope = HashMap::new();
            for (i, var) in vars.iter().enumerate() {
                let vname = var
                    .atom()
                    .ok_or_else(|| SmtError::Syntax("match pattern variable".to_owned()))?;
                let sel =
                    arena.dt_select(ctor, u32::try_from(i).expect("field fits u32"), scrutinee)?;
                if vname != "_" && scope.insert(vname, sel).is_some() {
                    return Err(SmtError::Syntax(format!(
                        "match: duplicate pattern variable `{vname}`"
                    )));
                }
            }
            Ok(CasePattern::Constructor { ctor, scope })
        }
    }
}

/// Folds the `match` case results (top `testers.len()` results, in case order)
/// into the right-nested `ite`: each guarded case `Some(t)` becomes
/// `(ite t result <rest>)`, and the final case (`None`) is the innermost else.
fn combine_match(
    arena: &mut TermArena,
    results: &mut Vec<TermId>,
    testers: &[Option<TermId>],
) -> Result<(), SmtError> {
    let n = testers.len();
    let case_results = results.split_off(results.len() - n);
    // Fold from the last case inward. The last case is the unconditional else.
    let mut acc = *case_results
        .last()
        .ok_or_else(|| SmtError::Syntax("match has no cases".to_owned()))?;
    for i in (0..n - 1).rev() {
        let tester = testers[i].ok_or_else(|| {
            SmtError::Syntax(
                "match: only the final case may be an unconditional default".to_owned(),
            )
        })?;
        acc = arena.ite(tester, case_results[i], acc)?;
    }
    results.push(acc);
    Ok(())
}

// --- bounded string front-end (ADR-0029, first slice) ------------------------
//
// A `String` is represented as one bit-vector packing a length in the low
// `STRING_LEN_WIDTH` bits and up to `STRING_MAX_LEN` content bytes above it
// (byte `i` at bits `[LEN_WIDTH + 8i, +8)`). String variables carry a
// canonical well-formedness constraint (length ≤ max; padding bytes zero), so
// two equal strings share exactly one bit pattern and `=` / `distinct` over
// strings are decided as plain bit-vector equality / inequality through the
// existing BV path — no operator-dispatch changes. This is the bounded-model
// fragment; `str.*` operations and lengths beyond the bound are future slices.

/// Maximum bounded string length in bytes.
const STRING_MAX_LEN: u32 = 8;
/// Bits holding a length in `0..=STRING_MAX_LEN`.
const STRING_LEN_WIDTH: u32 = 4;
/// Total packed width: length bits plus `STRING_MAX_LEN` content bytes.
const STRING_TOTAL: u32 = STRING_LEN_WIDTH + STRING_MAX_LEN * 8;

/// Packs a string literal's bytes into the canonical bit-vector representation
/// (length low, content above, padding zero). Errors if it exceeds the bound.
fn pack_string_literal(arena: &mut TermArena, bytes: &[u8]) -> Result<TermId, SmtError> {
    if bytes.len() > STRING_MAX_LEN as usize {
        return Err(SmtError::Unsupported(format!(
            "string literal longer than the bounded length {STRING_MAX_LEN} (ADR-0029)"
        )));
    }
    let mut content: u128 = 0;
    for (i, &b) in bytes.iter().enumerate() {
        content |= u128::from(b) << (8 * i);
    }
    let packed = u128::from(u32::try_from(bytes.len()).expect("len ≤ STRING_MAX_LEN"))
        | (content << STRING_LEN_WIDTH);
    arena.bv_const(STRING_TOTAL, packed).map_err(SmtError::Ir)
}

/// The length field (a `BitVec(STRING_LEN_WIDTH)`) of a packed string.
fn string_len(arena: &mut TermArena, v: TermId) -> Result<TermId, SmtError> {
    arena
        .extract(STRING_LEN_WIDTH - 1, 0, v)
        .map_err(SmtError::Ir)
}

/// Content byte `i` (a `BitVec(8)`) of a packed string.
fn string_byte(arena: &mut TermArena, v: TermId, i: u32) -> Result<TermId, SmtError> {
    let lo = STRING_LEN_WIDTH + i * 8;
    arena.extract(lo + 7, lo, v).map_err(SmtError::Ir)
}

/// `str.prefixof x y` — `x` is a prefix of `y`: `len(x) ≤ len(y)` and the first
/// `len(x)` bytes match. A pure bit-vector/Boolean formula over the packed
/// strings, so it decides both directions (no Int / theory-combination gap).
fn string_prefixof(arena: &mut TermArena, x: TermId, y: TermId) -> Result<TermId, SmtError> {
    let xlen = string_len(arena, x)?;
    let ylen = string_len(arena, y)?;
    let mut acc = arena.bv_ule(xlen, ylen)?;
    for i in 0..STRING_MAX_LEN {
        let xb = string_byte(arena, x, i)?;
        let yb = string_byte(arena, y, i)?;
        let beq = arena.eq(xb, yb)?;
        let idx = arena.bv_const(STRING_LEN_WIDTH, u128::from(i))?;
        let active = arena.bv_ult(idx, xlen)?; // i < len(x)
        let nactive = arena.not(active)?;
        let ok = arena.or(nactive, beq)?; // i ≥ len(x) ∨ bytes equal
        acc = arena.and(acc, ok)?;
    }
    Ok(acc)
}

/// `str.contains x y` — `y` occurs in `x` as a contiguous substring. A pure
/// bit-vector/Boolean formula: the disjunction over each start offset `d` of
/// "`y` fits at `d` (`d + len(y) ≤ len(x)`) and matches there". Bounded
/// (`O(MAX_LEN²)`), decides both directions.
fn string_contains(arena: &mut TermArena, x: TermId, y: TermId) -> Result<TermId, SmtError> {
    let xlen = string_len(arena, x)?;
    let ylen = string_len(arena, y)?;
    // Widen lengths by one bit so `d + len(y)` cannot overflow the length width.
    let xlen_w = arena.zero_ext(1, xlen)?;
    let ylen_w = arena.zero_ext(1, ylen)?;
    let wlen = STRING_LEN_WIDTH + 1;
    let mut any = arena.bool_const(false);
    for d in 0..STRING_MAX_LEN {
        let dconst = arena.bv_const(wlen, u128::from(d))?;
        let sum = arena.bv_add(dconst, ylen_w)?;
        let fits = arena.bv_ule(sum, xlen_w)?; // d + len(y) ≤ len(x)
        let mut matched = fits;
        for j in 0..STRING_MAX_LEN {
            if d + j >= STRING_MAX_LEN {
                break; // x has no byte at d+j; under `fits` this forces j ≥ len(y)
            }
            let xb = string_byte(arena, x, d + j)?;
            let yb = string_byte(arena, y, j)?;
            let beq = arena.eq(xb, yb)?;
            let jconst = arena.bv_const(STRING_LEN_WIDTH, u128::from(j))?;
            let jactive = arena.bv_ult(jconst, ylen)?; // j < len(y)
            let njactive = arena.not(jactive)?;
            let ok = arena.or(njactive, beq)?; // j ≥ len(y) ∨ bytes equal
            matched = arena.and(matched, ok)?;
        }
        any = arena.or(any, matched)?;
    }
    Ok(any)
}

/// `str.suffixof x y` — `x` is a suffix of `y`: aligned at offset
/// `o = len(y) − len(x)`, the bytes match. Disjunction over `o` (pure BV/Bool,
/// decides both directions).
fn string_suffixof(arena: &mut TermArena, x: TermId, y: TermId) -> Result<TermId, SmtError> {
    let xlen = string_len(arena, x)?;
    let ylen = string_len(arena, y)?;
    let xlen_w = arena.zero_ext(1, xlen)?;
    let ylen_w = arena.zero_ext(1, ylen)?;
    let wlen = STRING_LEN_WIDTH + 1;
    let mut any = arena.bool_const(false);
    for o in 0..=STRING_MAX_LEN {
        let oconst = arena.bv_const(wlen, u128::from(o))?;
        let sum = arena.bv_add(oconst, xlen_w)?;
        let aligned = arena.eq(sum, ylen_w)?; // len(y) == o + len(x)
        let mut matched = aligned;
        for i in 0..STRING_MAX_LEN {
            if o + i >= STRING_MAX_LEN {
                break; // y has no byte at o+i; under `aligned` this forces i ≥ len(x)
            }
            let xb = string_byte(arena, x, i)?;
            let yb = string_byte(arena, y, o + i)?;
            let beq = arena.eq(xb, yb)?;
            let iconst = arena.bv_const(STRING_LEN_WIDTH, u128::from(i))?;
            let iactive = arena.bv_ult(iconst, xlen)?; // i < len(x)
            let niactive = arena.not(iactive)?;
            let ok = arena.or(niactive, beq)?;
            matched = arena.and(matched, ok)?;
        }
        any = arena.or(any, matched)?;
    }
    Ok(any)
}

/// `str.at s k` for a **constant** index `k`: the length-1 string holding byte
/// `s[k]` when `0 ≤ k < len(s)` (and within the bound), else the empty string.
/// The result is another packed string (no width growth), canonical, so it
/// composes with equality. Pure BV/Bool — decides both directions.
fn string_at_const(arena: &mut TermArena, s: TermId, k: i128) -> Result<TermId, SmtError> {
    // Out of the representable range: always the empty string (all-zero packing).
    if k < 0 || k >= i128::from(STRING_MAX_LEN) {
        return arena.bv_const(STRING_TOTAL, 0).map_err(SmtError::Ir);
    }
    let kk = u32::try_from(k).expect("0 ≤ k < STRING_MAX_LEN");
    let slen = string_len(arena, s)?;
    let kconst = arena.bv_const(STRING_LEN_WIDTH, u128::from(kk))?;
    let active = arena.bv_ult(kconst, slen)?; // k < len(s)
    let byte_k = string_byte(arena, s, kk)?;
    let zero8 = arena.bv_const(8, 0)?;
    let one_len = arena.bv_const(STRING_LEN_WIDTH, 1)?;
    let zero_len = arena.bv_const(STRING_LEN_WIDTH, 0)?;
    let rlen = arena.ite(active, one_len, zero_len)?;
    let rbyte = arena.ite(active, byte_k, zero8)?;
    // Pack: content = zero-padding ++ byte0(rbyte); packed = content ++ length.
    let zeros_hi = arena.bv_const((STRING_MAX_LEN - 1) * 8, 0)?;
    let content = arena.concat(zeros_hi, rbyte)?;
    arena.concat(content, rlen).map_err(SmtError::Ir)
}

/// `str.++` over **constant** strings: concatenate their bytes and pack the
/// result (a literal of the true total length, so no width-growth/equality
/// issue). Variable concatenation grows the bound and needs the typed-result
/// front end (ADR-0029) — a clean `Unsupported`. An over-bound result is also
/// `Unsupported` (handled by [`pack_string_literal`]).
fn string_concat_const(arena: &mut TermArena, args: &[TermId]) -> Result<Vec<u8>, SmtError> {
    let mut bytes: Vec<u8> = Vec::new();
    for &arg in args {
        let (len, content) = match arena.node(arg) {
            TermNode::BvConst { width, value } if *width == STRING_TOTAL => {
                let len = usize::try_from(*value & ((1u128 << STRING_LEN_WIDTH) - 1))
                    .expect("length fits usize");
                (len, *value >> STRING_LEN_WIDTH)
            }
            _ => {
                return Err(SmtError::Unsupported(
                    "str.++ is supported only for constant strings; variable concatenation \
                     needs the typed-result front end (ADR-0029)"
                        .to_owned(),
                ));
            }
        };
        for i in 0..len {
            bytes.push(u8::try_from((content >> (8 * i)) & 0xff).expect("byte fits u8"));
        }
    }
    Ok(bytes)
}

/// The canonical well-formedness constraint for a packed string `v`: its length
/// is `≤ STRING_MAX_LEN`, and every content byte at or above the length is zero.
fn string_wellformed(arena: &mut TermArena, v: TermId) -> Result<TermId, SmtError> {
    let len = arena.extract(STRING_LEN_WIDTH - 1, 0, v)?;
    let max = arena.bv_const(STRING_LEN_WIDTH, u128::from(STRING_MAX_LEN))?;
    let mut wf = arena.bv_ule(len, max)?;
    let zero8 = arena.bv_const(8, 0)?;
    for i in 0..STRING_MAX_LEN {
        let lo = STRING_LEN_WIDTH + i * 8;
        let byte = arena.extract(lo + 7, lo, v)?;
        let byte_zero = arena.eq(byte, zero8)?;
        let idx = arena.bv_const(STRING_LEN_WIDTH, u128::from(i))?;
        let active = arena.bv_ult(idx, len)?;
        let ok = arena.or(active, byte_zero)?;
        wf = arena.and(wf, ok)?;
    }
    Ok(wf)
}

fn parse_atom(
    arena: &mut TermArena,
    a: &str,
    aliases: &HashMap<String, TermId>,
    named: &HashMap<String, TermId>,
    scopes: &[HashMap<&str, TermId>],
) -> Result<TermId, SmtError> {
    for scope in scopes.iter().rev() {
        if let Some(&t) = scope.get(a) {
            return Ok(t);
        }
    }
    match a {
        "true" => return Ok(arena.bool_const(true)),
        "false" => return Ok(arena.bool_const(false)),
        _ => {}
    }
    if let Some(hex) = a.strip_prefix("#x") {
        let value = u128::from_str_radix(hex, 16)
            .map_err(|_| SmtError::Syntax(format!("bad hex literal `{a}`")))?;
        return Ok(arena.bv_const(
            4 * u32::try_from(hex.len())
                .map_err(|_| SmtError::Syntax("literal too wide".to_owned()))?,
            value,
        )?);
    }
    if let Some(bin) = a.strip_prefix("#b") {
        let value = u128::from_str_radix(bin, 2)
            .map_err(|_| SmtError::Syntax(format!("bad binary literal `{a}`")))?;
        return Ok(arena.bv_const(
            u32::try_from(bin.len())
                .map_err(|_| SmtError::Syntax("literal too wide".to_owned()))?,
            value,
        )?);
    }
    // SMT-LIB string literal `"..."` (the lexer keeps the surrounding quotes;
    // a doubled `""` escapes one quote). Pack into the canonical bit-vector.
    if a.len() >= 2 && a.starts_with('"') && a.ends_with('"') {
        let inner = &a[1..a.len() - 1];
        let unescaped = inner.replace("\"\"", "\"");
        return pack_string_literal(arena, unescaped.as_bytes());
    }
    if let Some(&t) = aliases.get(a) {
        return Ok(t);
    }
    if let Some(sym) = arena.find_symbol(a) {
        return Ok(arena.var(sym));
    }
    // A `:named` alias bound earlier by `(! t :named a)`. Consulted *after*
    // declared symbols so a real declaration is never shadowed by a `:named`.
    if let Some(&t) = named.get(a) {
        return Ok(t);
    }
    // A bare numeral is a non-negative integer literal (negatives are `(- n)`).
    if a.bytes().all(|b| b.is_ascii_digit()) {
        let value = a
            .parse::<i128>()
            .map_err(|_| SmtError::Syntax(format!("integer literal `{a}` out of range")))?;
        return Ok(arena.int_const(value));
    }
    // A decimal literal `d.ddd` is a non-negative real (ADR-0015).
    if let Some(rational) = parse_decimal(a) {
        return Ok(arena.real_const(rational));
    }
    // A nullary datatype constructor (e.g. an enum value `red`) used as a term.
    if let Some(ctor) = arena.find_constructor(a) {
        if arena.constructor_fields(ctor).is_empty() {
            return Ok(arena.construct(ctor, &[])?);
        }
        return Err(SmtError::Syntax(format!(
            "constructor `{a}` needs arguments"
        )));
    }
    // Nullary string/regex constants outside the wired bounded subset
    // (`re.none`/`re.all`/`re.allchar`, …) are declined cleanly (ADR-0029) so a
    // benchmark using them returns `Unsupported`, never a wrong verdict.
    if a.starts_with("re.") || a.starts_with("str.") {
        return Err(SmtError::Unsupported(format!(
            "string/regex constant `{a}` is outside the wired bounded subset (ADR-0029)"
        )));
    }
    Err(SmtError::Unsupported(format!("unknown identifier `{a}`")))
}

/// The IEEE format of a floating-point operand: read directly from a
/// `Sort::Float` (ADR-0026), or inferred from a bit-vector width as a fallback
/// (`16→F16`, `32→F32`, `64→F64`) for terms not yet float-typed.
fn fp_format(arena: &TermArena, t: TermId) -> Result<FloatFormat, SmtError> {
    match arena.sort_of(t) {
        Sort::Float { exp, sig } => Ok(FloatFormat {
            exp_bits: exp,
            sig_bits: sig,
        }),
        Sort::BitVec(16) => Ok(FloatFormat::F16),
        Sort::BitVec(32) => Ok(FloatFormat::F32),
        Sort::BitVec(64) => Ok(FloatFormat::F64),
        s => Err(SmtError::Unsupported(format!(
            "floating-point op on unsupported width/sort {s:?}"
        ))),
    }
}

/// Stamps the floating-point sort of `fmt` onto a bit-vector result `t` produced
/// by an FP formula builder, so downstream conversions can tell it is a float
/// (ADR-0026). If `t` is already that float sort this is a no-op.
fn as_float(arena: &mut TermArena, fmt: FloatFormat, t: TermId) -> Result<TermId, SmtError> {
    if arena.sort_of(t)
        == (Sort::Float {
            exp: fmt.exp_bits,
            sig: fmt.sig_bits,
        })
    {
        return Ok(t);
    }
    Ok(arena.fp_from_bits(t, fmt.exp_bits, fmt.sig_bits)?)
}

/// Reinterprets a `Float`-typed term to its `BitVec(exp + sig)` bits (identity on
/// bits) so the FP formula builders — which operate on bit-vectors and freely mix
/// operands with bit-vector constants — never see a `Float` operand. A non-float
/// term is returned unchanged.
fn to_bits(arena: &mut TermArena, t: TermId) -> Result<TermId, SmtError> {
    // A float built by `fp_from_bits` wraps a bit-vector directly: peel the
    // reinterpret to recover that exact term (preserving any `BvConst`, so the
    // constant-folding conversions still see a literal).
    if let TermNode::App { op, args } = arena.node(t)
        && let axeyum_ir::Op::FpFromBits { .. } = op
    {
        return Ok(args[0]);
    }
    match arena.sort_of(t) {
        Sort::Float { exp, sig } => Ok(arena.extract(exp + sig - 1, 0, t)?),
        _ => Ok(t),
    }
}

/// Whether `name` is a floating-point op whose first argument is a rounding mode.
fn is_fp_rounded_op(name: &str) -> bool {
    matches!(
        name,
        "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.fma" | "fp.sqrt" | "fp.roundToIntegral"
    )
}

/// Parses an SMT-LIB `RoundingMode` value (short or long form). Returns `None`
/// for anything that isn't a recognized mode symbol.
fn parse_rounding_mode(expr: &SExpr) -> Option<RoundingMode> {
    match expr.atom()? {
        "RNE" | "roundNearestTiesToEven" => Some(RoundingMode::NearestEven),
        "RNA" | "roundNearestTiesToAway" => Some(RoundingMode::NearestAway),
        "RTZ" | "roundTowardZero" => Some(RoundingMode::TowardZero),
        "RTP" | "roundTowardPositive" => Some(RoundingMode::TowardPositive),
        "RTN" | "roundTowardNegative" => Some(RoundingMode::TowardNegative),
        _ => None,
    }
}

/// Whether `name` is an indexed FP conversion op taking a leading rounding mode.
fn is_fp_indexed_conversion(name: &str) -> bool {
    matches!(name, "to_fp" | "to_fp_unsigned" | "fp.to_sbv" | "fp.to_ubv")
}

/// Applies an *indexed* rounding-mode FP conversion (`mode` already parsed). With
/// the first-class `Sort::Float` (ADR-0026) every overload is sort-disambiguated:
/// `(_ to_fp eb sb)` from a **real** constant (dyadic only — sound), from a
/// **float** (FP→FP reformat), or from a **bit-vector** (signed-BV→FP);
/// `(_ to_fp_unsigned eb sb)` from an unsigned bit-vector; and `(_ fp.to_sbv/
/// to_ubv m)` from a floating-point value.
#[allow(clippy::too_many_lines)]
fn apply_fp_rounded_indexed(
    arena: &mut TermArena,
    items: &[SExpr],
    mode: RoundingMode,
    args: &[TermId],
) -> Result<TermId, SmtError> {
    let head = items[0].list().expect("indexed head");
    let name = head.get(1).and_then(SExpr::atom).unwrap_or("");
    let index = |i: usize| -> Result<u32, SmtError> {
        head.get(i)
            .and_then(SExpr::atom)
            .and_then(|s| s.parse::<u32>().ok())
            .ok_or_else(|| SmtError::Syntax(format!("`{name}` index {i}")))
    };
    if args.len() != 1 {
        return Err(SmtError::Syntax(format!(
            "`{name}` expects 1 operand, got {}",
            args.len()
        )));
    }
    let x = args[0];
    let term = match name {
        "to_fp" => {
            let (eb, sb) = (index(2)?, index(3)?);
            let dst = FloatFormat {
                exp_bits: eb,
                sig_bits: sb,
            };
            match arena.sort_of(x) {
                Sort::Real => {
                    // Real → FP: fold a dyadic real *constant*; non-dyadic or
                    // symbolic reals are unsupported (sound — never double-rounded).
                    let TermNode::RealConst(r) = *arena.node(x) else {
                        return Err(SmtError::Unsupported(
                            "(_ to_fp …) from a non-constant real".to_owned(),
                        ));
                    };
                    let bits = axeyum_fp::round_rational_to_format(
                        eb,
                        sb,
                        r.numerator(),
                        r.denominator(),
                        mode,
                    )
                    .ok_or_else(|| {
                        SmtError::Unsupported(format!(
                            "(_ to_fp {eb} {sb}) from non-dyadic real {}/{}",
                            r.numerator(),
                            r.denominator()
                        ))
                    })?;
                    let bv = arena.bv_const(eb + sb, bits)?;
                    as_float(arena, dst, bv)?
                }
                Sort::Float { .. } => {
                    // FP → FP reformat: now sort-disambiguated from a signed-BV
                    // source (ADR-0026); the validated symbolic `to_fp` builder
                    // runs on the unwrapped bits.
                    let src = fp_format(arena, x)?;
                    let xb = to_bits(arena, x)?;
                    let r = axeyum_fp::to_fp(arena, src, dst, mode, xb)?;
                    as_float(arena, dst, r)?
                }
                Sort::BitVec(_) => {
                    // Signed bit-vector → FP (symbolic circuit via pack_value;
                    // None only if the working width exceeds MAX_BV_WIDTH).
                    let r = axeyum_fp::sbv_to_fp(arena, dst, x, mode)?.ok_or_else(|| {
                        SmtError::Unsupported(
                            "(_ to_fp …) from a signed bit-vector: integer width too large \
                             for the conversion circuit"
                                .to_owned(),
                        )
                    })?;
                    as_float(arena, dst, r)?
                }
                s => {
                    return Err(SmtError::Syntax(format!(
                        "(_ to_fp …) operand must be Real, Float, or BitVec, got {s:?}"
                    )));
                }
            }
        }
        "to_fp_unsigned" => {
            let fmt = FloatFormat {
                exp_bits: index(2)?,
                sig_bits: index(3)?,
            };
            let r = axeyum_fp::ubv_to_fp(arena, fmt, x, mode)?.ok_or_else(|| {
                SmtError::Unsupported(
                    "(_ to_fp_unsigned …): integer width too large for the conversion circuit"
                        .to_owned(),
                )
            })?;
            as_float(arena, fmt, r)?
        }
        "fp.to_ubv" => {
            let width = index(2)?;
            let fmt = fp_format(arena, x)?;
            let xb = to_bits(arena, x)?;
            // Constant + well-defined folds to a clean value; otherwise build the
            // symbolic circuit, routing NaN/∞/out-of-range to a fresh value
            // (SMT-LIB underspecification; ADR-0026).
            if let Some(c) = axeyum_fp::to_ubv(arena, fmt, mode, xb, width)? {
                c
            } else {
                let fresh = fresh_conversion_value(arena, "to_ubv", xb, width, mode)?;
                axeyum_fp::to_ubv_sym(arena, fmt, mode, xb, width, fresh)?
            }
        }
        "fp.to_sbv" => {
            let width = index(2)?;
            let fmt = fp_format(arena, x)?;
            let xb = to_bits(arena, x)?;
            if let Some(c) = axeyum_fp::to_sbv(arena, fmt, mode, xb, width)? {
                c
            } else {
                let fresh = fresh_conversion_value(arena, "to_sbv", xb, width, mode)?;
                axeyum_fp::to_sbv_sym(arena, fmt, mode, xb, width, fresh)?
            }
        }
        other => {
            return Err(SmtError::Unsupported(format!(
                "indexed rounding-mode FP op `{other}`"
            )));
        }
    };
    Ok(term)
}

/// Applies a rounding-mode FP op (`mode` already parsed from the first argument);
/// `args` are the evaluated operands. The format is recovered from operand width.
fn apply_fp_rounded(
    arena: &mut TermArena,
    items: &[SExpr],
    mode: RoundingMode,
    args: &[TermId],
) -> Result<TermId, SmtError> {
    let head = items[0].atom().unwrap_or("");
    let need = |n: usize| -> Result<(), SmtError> {
        if args.len() == n {
            Ok(())
        } else {
            Err(SmtError::Syntax(format!(
                "{head} expects {n} operand(s), got {}",
                args.len()
            )))
        }
    };
    // Format from the (float-typed) operand; builders run on the unwrapped bits.
    let fmt = fp_format(arena, args[0])?;
    let b = args
        .iter()
        .map(|&a| to_bits(arena, a))
        .collect::<Result<Vec<_>, _>>()?;
    let term = match head {
        "fp.add" => {
            need(2)?;
            axeyum_fp::add(arena, fmt, b[0], b[1], mode)?
        }
        "fp.sub" => {
            need(2)?;
            axeyum_fp::sub(arena, fmt, b[0], b[1], mode)?
        }
        "fp.mul" => {
            need(2)?;
            axeyum_fp::mul(arena, fmt, b[0], b[1], mode)?
        }
        "fp.div" => {
            need(2)?;
            axeyum_fp::div(arena, fmt, b[0], b[1], mode)?
        }
        "fp.sqrt" => {
            need(1)?;
            axeyum_fp::sqrt(arena, fmt, b[0], mode)?
        }
        "fp.fma" => {
            need(3)?;
            axeyum_fp::fma(arena, fmt, b[0], b[1], b[2], mode)?
        }
        "fp.roundToIntegral" => {
            need(1)?;
            axeyum_fp::round_to_integral_sym(arena, fmt, mode, b[0])?
        }
        other => {
            return Err(SmtError::Unsupported(format!(
                "rounding-mode FP op `{other}`"
            )));
        }
    };
    // Every rounding-mode op here is FP-valued; stamp the float sort (ADR-0026).
    as_float(arena, fmt, term)
}

fn parse_indexed_constant(arena: &mut TermArena, items: &[SExpr]) -> Result<TermId, SmtError> {
    if items.len() == 3
        && let Some(name) = items[1].atom()
        && let Some(num) = name.strip_prefix("bv")
        && let (Ok(value), Some(Ok(width))) =
            (num.parse::<u128>(), items[2].atom().map(str::parse::<u32>))
    {
        return Ok(arena.bv_const(width, value)?);
    }
    // FP special constants `(_ <name> eb sb)` → the matching bit pattern in a
    // BitVec(eb+sb) (FP values are bit-vectors; ADR-0023).
    if items.len() == 4
        && let Some(name) = items[1].atom()
        && let (Some(Ok(eb)), Some(Ok(sb))) = (
            items[2].atom().map(str::parse::<u32>),
            items[3].atom().map(str::parse::<u32>),
        )
    {
        let total = eb + sb;
        let sign = 1u128 << (total - 1);
        let exp_ones = ((1u128 << eb) - 1) << (sb - 1);
        let bits = match name {
            "+zero" => Some(0),
            "-zero" => Some(sign),
            "+oo" => Some(exp_ones),
            "-oo" => Some(sign | exp_ones),
            "NaN" => Some(exp_ones | (1u128 << (sb - 2))), // canonical qNaN
            _ => None,
        };
        if let Some(bits) = bits {
            let bv = arena.bv_const(total, bits)?;
            return Ok(arena.fp_from_bits(bv, eb, sb)?); // float-typed (ADR-0026)
        }
    }
    Err(SmtError::Unsupported(format!("indexed term {items:?}")))
}

/// Applies an operator list head to evaluated arguments.
// Flat dispatch over the operator vocabulary; length is inherent.
#[allow(clippy::too_many_lines)]
fn apply_op(arena: &mut TermArena, items: &[SExpr], args: &[TermId]) -> Result<TermId, SmtError> {
    // Parameterized head: ((_ extract h l) x) etc.
    if let Some(head_items) = items[0].list() {
        return apply_parameterized(arena, head_items, args);
    }
    let op = items[0].atom().expect("list head checked");
    let need = |n: usize| -> Result<(), SmtError> {
        if args.len() == n {
            Ok(())
        } else {
            Err(SmtError::Syntax(format!(
                "`{op}` expects {n} arguments, got {}",
                args.len()
            )))
        }
    };
    let fold = |arena: &mut TermArena,
                f: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>|
     -> Result<TermId, SmtError> {
        if args.len() < 2 {
            return Err(SmtError::Syntax(format!("`{op}` expects >= 2 arguments")));
        }
        let mut acc = args[0];
        for &next in &args[1..] {
            acc = f(arena, acc, next)?;
        }
        Ok(acc)
    };
    Ok(match op {
        "not" => {
            need(1)?;
            arena.not(args[0])?
        }
        // `str.len` over a packed bounded string (ADR-0029): the length field as
        // an `Int`, so it composes with the existing integer arithmetic
        // (`(>= (str.len s) 3)`, `(= (str.len s) 0)`, …).
        "str.len" => {
            need(1)?;
            let len = arena.extract(STRING_LEN_WIDTH - 1, 0, args[0])?;
            arena.bv2nat(len)?
        }
        // `str.prefixof x y` — pure BV/Bool over packed strings; decides both
        // directions (no Int bridge, no theory-combination gap).
        "str.prefixof" => {
            need(2)?;
            string_prefixof(arena, args[0], args[1])?
        }
        // `str.contains x y` — y occurs in x; pure BV/Bool, decides both directions.
        "str.contains" => {
            need(2)?;
            string_contains(arena, args[0], args[1])?
        }
        "str.suffixof" => {
            need(2)?;
            string_suffixof(arena, args[0], args[1])?
        }
        // `str.at s k` — constant index only (symbolic indices need the Int↔
        // position bridge); returns a length-≤1 packed string.
        "str.at" => {
            need(2)?;
            let k = match arena.node(args[1]) {
                TermNode::IntConst(k) => *k,
                _ => {
                    return Err(SmtError::Unsupported(
                        "str.at with a non-constant index is not yet supported (ADR-0029)"
                            .to_owned(),
                    ));
                }
            };
            string_at_const(arena, args[0], k)?
        }
        // `str.++` over constant strings folds to a literal (ADR-0029).
        "str.concat" | "str.++" => {
            let bytes = string_concat_const(arena, args)?;
            pack_string_literal(arena, &bytes)?
        }
        // `(and x)` / `(or x)` with a single operand denote `x`: an n-ary
        // connective folded over one argument is that argument (the identity of
        // `∧`/`∨`). SMT-LIB's `:left-assoc` grammar nominally wants ≥2 operands,
        // but cvc5/Z3 both accept the unary form, so we mirror them. Zero or ≥2
        // operands keep the existing `fold` path (which rejects 0 and folds ≥2).
        "and" | "or" if args.len() == 1 => args[0],
        "and" => fold(arena, TermArena::and)?,
        "or" => fold(arena, TermArena::or)?,
        "xor" => fold(arena, TermArena::xor)?,
        "=>" => {
            // Right-associative.
            if args.len() < 2 {
                return Err(SmtError::Syntax("`=>` expects >= 2 arguments".to_owned()));
            }
            let mut acc = *args.last().expect("nonempty");
            for &prev in args[..args.len() - 1].iter().rev() {
                acc = arena.implies(prev, acc)?;
            }
            acc
        }
        "=" => {
            // n-ary chaining: pairwise equalities conjoined. Coerce integer
            // constants to `Real` when any operand is real (numeral coercion).
            if args.len() < 2 {
                return Err(SmtError::Syntax("`=` expects >= 2 arguments".to_owned()));
            }
            let eq_args = if args.iter().any(|&a| arena.sort_of(a) == Sort::Real) {
                numeric_args(arena, args)?.1
            } else {
                args.to_vec()
            };
            let mut acc = arena.eq(eq_args[0], eq_args[1])?;
            for pair in eq_args.windows(2).skip(1) {
                let e = arena.eq(pair[0], pair[1])?;
                acc = arena.and(acc, e)?;
            }
            acc
        }
        "distinct" => {
            if args.len() < 2 {
                return Err(SmtError::Syntax(
                    "`distinct` expects >= 2 arguments".to_owned(),
                ));
            }
            let mut acc = None;
            for i in 0..args.len() {
                for j in i + 1..args.len() {
                    let e = arena.eq(args[i], args[j])?;
                    let ne = arena.not(e)?;
                    acc = Some(match acc {
                        Some(prev) => arena.and(prev, ne)?,
                        None => ne,
                    });
                }
            }
            acc.expect("args length checked")
        }
        "ite" => {
            need(3)?;
            arena.ite(args[0], args[1], args[2])?
        }
        "bvnot" => {
            need(1)?;
            arena.bv_not(args[0])?
        }
        "bvneg" => {
            need(1)?;
            arena.bv_neg(args[0])?
        }
        "bvand" => fold(arena, TermArena::bv_and)?,
        "bvor" => fold(arena, TermArena::bv_or)?,
        "bvxor" => fold(arena, TermArena::bv_xor)?,
        "bvadd" => fold(arena, TermArena::bv_add)?,
        "bvmul" => fold(arena, TermArena::bv_mul)?,
        "concat" => fold(arena, TermArena::concat)?,
        "bvsub" => {
            need(2)?;
            arena.bv_sub(args[0], args[1])?
        }
        "bvnand" => bin(arena, TermArena::bv_nand, args, op)?,
        "bvnor" => bin(arena, TermArena::bv_nor, args, op)?,
        "bvxnor" => bin(arena, TermArena::bv_xnor, args, op)?,
        "bvudiv" => bin(arena, TermArena::bv_udiv, args, op)?,
        "bvurem" => bin(arena, TermArena::bv_urem, args, op)?,
        "bvsdiv" => bin(arena, TermArena::bv_sdiv, args, op)?,
        "bvsrem" => bin(arena, TermArena::bv_srem, args, op)?,
        "bvsmod" => bin(arena, TermArena::bv_smod, args, op)?,
        "bvshl" => bin(arena, TermArena::bv_shl, args, op)?,
        "bvlshr" => bin(arena, TermArena::bv_lshr, args, op)?,
        "bvashr" => bin(arena, TermArena::bv_ashr, args, op)?,
        "bvult" => bin(arena, TermArena::bv_ult, args, op)?,
        "bvule" => bin(arena, TermArena::bv_ule, args, op)?,
        "bvugt" => bin(arena, TermArena::bv_ugt, args, op)?,
        "bvuge" => bin(arena, TermArena::bv_uge, args, op)?,
        "bvslt" => bin(arena, TermArena::bv_slt, args, op)?,
        "bvsle" => bin(arena, TermArena::bv_sle, args, op)?,
        "bvsgt" => bin(arena, TermArena::bv_sgt, args, op)?,
        "bvsge" => bin(arena, TermArena::bv_sge, args, op)?,
        "bvcomp" => bin(arena, TermArena::bv_comp, args, op)?,
        // Overflow-detection predicates (SMT-LIB 2.6).
        "bvuaddo" => bin(arena, TermArena::bv_uaddo, args, op)?,
        "bvsaddo" => bin(arena, TermArena::bv_saddo, args, op)?,
        "bvusubo" => bin(arena, TermArena::bv_usubo, args, op)?,
        "bvssubo" => bin(arena, TermArena::bv_ssubo, args, op)?,
        "bvumulo" => bin(arena, TermArena::bv_umulo, args, op)?,
        "bvsmulo" => bin(arena, TermArena::bv_smulo, args, op)?,
        "bvnego" => {
            need(1)?;
            arena.bv_nego(args[0])?
        }
        // Unary BV→BitVec(1) reductions (SMT-LIB 2.6), desugared to existing BV
        // ops per cvc5/bitwuzla's authoritative elimination rules. See
        // [`bv_reduce`] for the exact desugaring and soundness note. The result
        // is always one bit wide.
        "bvredor" | "bvredand" | "bvredxor" => {
            need(1)?;
            bv_reduce(arena, op, args[0])?
        }
        // Floating-point: a value is its bit-vector pattern carried by a
        // `Sort::Float` (ADR-0026); the format is recovered from the operand sort.
        // Rounding-mode-free ops only; `(fp s e m)` assembles a literal.
        "fp" => {
            need(3)?;
            // sign(1) · exp(eb) · significand(sb-1)  →  Float { exp: eb, sig: sb }.
            let eb = arena.sort_of(args[1]).lowered_width().ok_or_else(|| {
                SmtError::Syntax("fp exponent field must be a bit-vector".to_owned())
            })?;
            let sig_field = arena.sort_of(args[2]).lowered_width().ok_or_else(|| {
                SmtError::Syntax("fp significand field must be a bit-vector".to_owned())
            })?;
            let sb = sig_field + 1;
            // Concatenate sign·exp·significand MSB-first. When all three fields are
            // constant, fold to a single `BvConst` so constant-folding ops
            // (`fp.to_real`, `fp.roundToIntegral`, …) see a literal value.
            let as_const = |t: TermId| match arena.node(t) {
                &TermNode::BvConst { width, value } => Some((width, value)),
                _ => None,
            };
            let bv = if let (Some((ws, vs)), Some((we, ve)), Some((wm, vm))) =
                (as_const(args[0]), as_const(args[1]), as_const(args[2]))
            {
                let total = ws + we + wm;
                let value = (vs << (we + wm)) | (ve << wm) | vm;
                arena.bv_const(total, value)?
            } else {
                let se = arena.concat(args[0], args[1])?;
                arena.concat(se, args[2])?
            };
            arena.fp_from_bits(bv, eb, sb)?
        }
        // FP ops: read the format from the (float-typed) operand, then run the
        // bit-vector builders on the unwrapped bits (ADR-0026). FP-valued results
        // are re-stamped to `Float`; predicates/`to_real` are Bool/Real.
        "fp.abs" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            let r = axeyum_fp::abs(arena, fmt, x)?;
            as_float(arena, fmt, r)?
        }
        "fp.neg" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            let r = axeyum_fp::neg(arena, fmt, x)?;
            as_float(arena, fmt, r)?
        }
        "fp.eq" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            axeyum_fp::eq(arena, fmt, a, b)?
        }
        "fp.lt" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            axeyum_fp::lt(arena, fmt, a, b)?
        }
        "fp.leq" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            axeyum_fp::leq(arena, fmt, a, b)?
        }
        "fp.gt" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            axeyum_fp::gt(arena, fmt, a, b)?
        }
        "fp.geq" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            axeyum_fp::geq(arena, fmt, a, b)?
        }
        "fp.min" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            let r = axeyum_fp::min(arena, fmt, a, b)?;
            as_float(arena, fmt, r)?
        }
        "fp.max" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            let r = axeyum_fp::max(arena, fmt, a, b)?;
            as_float(arena, fmt, r)?
        }
        "fp.rem" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            let r = axeyum_fp::rem_sym(arena, fmt, a, b)?;
            as_float(arena, fmt, r)?
        }
        "fp.isNaN" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_nan(arena, fmt, x)?
        }
        "fp.isInfinite" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_infinite(arena, fmt, x)?
        }
        "fp.isZero" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_zero(arena, fmt, x)?
        }
        "fp.isNormal" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_normal(arena, fmt, x)?
        }
        "fp.isSubnormal" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_subnormal(arena, fmt, x)?
        }
        "fp.isNegative" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_negative(arena, fmt, x)?
        }
        "fp.isPositive" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_positive(arena, fmt, x)?
        }
        "fp.to_real" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::to_real(arena, fmt, x)?.ok_or_else(|| {
                SmtError::Unsupported(
                    "fp.to_real is only supported on constant operands".to_owned(),
                )
            })?
        }
        "select" => {
            need(2)?;
            arena.select(args[0], args[1])?
        }
        "store" => {
            need(3)?;
            arena.store(args[0], args[1], args[2])?
        }
        // --- linear arithmetic, sort-directed Int/Real (ADR-0014/0015) ----
        // `+`/`-`/`*`/comparisons are polymorphic: if any operand is `Real`,
        // integer-constant operands are coerced to `Real` and the real builders
        // are used; otherwise the integer builders.
        "+" => {
            let (real, a) = numeric_args(arena, args)?;
            if real {
                fold_args(arena, &a, op, TermArena::real_add)?
            } else {
                fold_args(arena, &a, op, TermArena::int_add)?
            }
        }
        "*" => {
            let (real, a) = numeric_args(arena, args)?;
            if real {
                fold_args(arena, &a, op, TermArena::real_mul)?
            } else {
                fold_args(arena, &a, op, TermArena::int_mul)?
            }
        }
        "-" => {
            let (real, a) = numeric_args(arena, args)?;
            match a.len() {
                1 if real => arena.real_neg(a[0])?,
                1 => arena.int_neg(a[0])?,
                0 => return Err(SmtError::Syntax("`-` expects >= 1 argument".to_owned())),
                _ => {
                    let mut acc = a[0];
                    for &next in &a[1..] {
                        acc = if real {
                            arena.real_sub(acc, next)?
                        } else {
                            arena.int_sub(acc, next)?
                        };
                    }
                    acc
                }
            }
        }
        "/" => {
            // `/` is always Real-typed (SMT-LIB `Reals_Ints`): every operand is
            // coerced to `Real`, including the all-integer-constant case
            // `(/ 177 366500000)`, which `numeric_args` would leave as `Int`.
            let a = real_args(arena, args)?;
            real_division(arena, &a)?
        }
        "div" | "mod" => {
            // SMT-LIB integer Euclidean division/modulo (binary, left-assoc for div).
            let (_, a) = numeric_args(arena, args)?;
            if a.len() < 2 {
                return Err(SmtError::Syntax(format!("`{op}` expects >= 2 arguments")));
            }
            let f = if op == "div" {
                TermArena::int_div
            } else {
                TermArena::int_mod
            };
            let mut acc = a[0];
            for &next in &a[1..] {
                acc = f(arena, acc, next)?;
            }
            acc
        }
        "abs" => {
            let (_, a) = numeric_args(arena, args)?;
            if a.len() != 1 {
                return Err(SmtError::Syntax("`abs` expects 1 argument".to_owned()));
            }
            arena.int_abs(a[0])?
        }
        // Int↔Real coercions. Constant operands fold exactly; symbolic operands
        // need cross-sort (Nelson-Oppen) reasoning and are not yet supported.
        "to_real" => {
            need(1)?;
            match *arena.node(args[0]) {
                TermNode::IntConst(n) => arena.real_const(Rational::integer(n)),
                _ => arena.int_to_real(args[0])?,
            }
        }
        "to_int" => {
            need(1)?;
            match *arena.node(args[0]) {
                TermNode::RealConst(r) => {
                    arena.int_const(r.numerator().div_euclid(r.denominator()))
                }
                _ => arena.real_to_int(args[0])?,
            }
        }
        "is_int" => {
            need(1)?;
            match *arena.node(args[0]) {
                TermNode::RealConst(r) => arena.bool_const(r.denominator() == 1),
                _ => arena.real_is_int(args[0])?,
            }
        }
        // `bv2nat` (SMT-LIB 2.6) and `ubv_to_int` (the SMT-LIB 2.7 / cvc5 spelling)
        // are the *same* operator: the unsigned (natural) value of a bit-vector.
        // Both map to [`TermArena::bv2nat`] verbatim.
        "bv2nat" | "ubv_to_int" => {
            if args.len() != 1 {
                return Err(SmtError::Syntax(format!("`{op}` expects 1 argument")));
            }
            arena.bv2nat(args[0])?
        }
        "<" | "<=" | ">" | ">=" => {
            let (real, a) = numeric_args(arena, args)?;
            let int_f = match op {
                "<" => TermArena::int_lt,
                "<=" => TermArena::int_le,
                ">" => TermArena::int_gt,
                _ => TermArena::int_ge,
            };
            let real_f = match op {
                "<" => TermArena::real_lt,
                "<=" => TermArena::real_le,
                ">" => TermArena::real_gt,
                _ => TermArena::real_ge,
            };
            if real {
                chain_args(arena, &a, op, real_f)?
            } else {
                chain_args(arena, &a, op, int_f)?
            }
        }
        // A declared uninterpreted function applied to arguments (ADR-0013).
        // Builtins above take priority, matching SMT-LIB reserved names.
        other => {
            // String/regex operators outside the wired bounded subset
            // (`str.replace`, `str.indexof`, `str.substr`, `str.<`, `str.to_int`,
            // `str.in_re`, the `re.*` constructors, …) are declined cleanly
            // (ADR-0029) so a benchmark using them returns `Unknown`/`Unsupported`
            // — never a wrong verdict, never a confusing "unknown operator".
            if other.starts_with("str.") || other.starts_with("re.") {
                return Err(SmtError::Unsupported(format!(
                    "string/regex operator `{other}` is outside the wired bounded subset \
                     (ADR-0029); supported: str.len, str.prefixof, str.contains, str.suffixof, \
                     str.at (const idx), str.++ (const args), = / distinct over String"
                )));
            }
            if let Some(func) = arena.find_function(other) {
                arena.apply(func, args)?
            } else if let Some(ctor) = arena.find_constructor(other) {
                // Datatype constructor application `(C a …)` (ADR-0022).
                arena.construct(ctor, args)?
            } else if let Some((ctor, field)) = find_selector(arena, other) {
                // Selector application `(sel x)`: project a constructor's field.
                need(1)?;
                arena.dt_select(ctor, field, args[0])?
            } else {
                return Err(SmtError::Unsupported(format!("operator `{other}`")));
            }
        }
    })
}

/// Resolves a datatype selector name to its `(constructor, field index)`, by
/// scanning the constructors' field lists. `None` if no constructor has a field
/// with that name.
fn find_selector(arena: &TermArena, name: &str) -> Option<(axeyum_ir::ConstructorId, u32)> {
    for dt in arena.datatype_ids() {
        for &ctor in arena.datatype_constructors(dt) {
            if let Some(field) = arena
                .constructor_fields(ctor)
                .iter()
                .position(|(fname, _)| fname == name)
            {
                return Some((ctor, u32::try_from(field).expect("field index fits u32")));
            }
        }
    }
    None
}

/// Parses a non-negative decimal literal `d.ddd` into an exact rational, or
/// `None` if `a` is not a decimal numeral.
fn parse_decimal(a: &str) -> Option<Rational> {
    let (int_part, frac_part) = a.split_once('.')?;
    if int_part.is_empty() && frac_part.is_empty() {
        return None;
    }
    let digits = |s: &str| s.bytes().all(|b| b.is_ascii_digit());
    if !digits(int_part) || !digits(frac_part) {
        return None;
    }
    let combined = format!("{int_part}{frac_part}");
    let num: i128 = combined.parse().ok()?;
    let mut den: i128 = 1;
    for _ in 0..frac_part.len() {
        den = den.checked_mul(10)?;
    }
    Some(Rational::new(num, den))
}

/// Classifies numeric `args` as real (any operand `Real`) and, if real, coerces
/// integer operands to `Real` (SMT-LIB numeral coercion). Integer *constants*
/// fold directly to a `RealConst`; non-constant `Int` terms are wrapped in the
/// exact `Int → Real` embedding (`arena.int_to_real`, the `to_real` operator).
///
/// This is the SMT-LIB / Z3 `Reals_Ints` mixed-arithmetic rule: an `Int`
/// subterm appearing in a `Real` context is embedded via `to_real`
/// (`to_real n = n`), which is denotation-preserving. The coercion fires *only*
/// when at least one operand is already `Real` (a genuine Real context);
/// pure-`Int` calls return early below, so `div`/`mod`/`abs`/comparisons over
/// `Int` keep their integer semantics untouched.
fn numeric_args(arena: &mut TermArena, args: &[TermId]) -> Result<(bool, Vec<TermId>), SmtError> {
    let is_real = args.iter().any(|&a| arena.sort_of(a) == Sort::Real);
    if !is_real {
        return Ok((false, args.to_vec()));
    }
    let mut out = Vec::with_capacity(args.len());
    for &a in args {
        match arena.sort_of(a) {
            Sort::Real => out.push(a),
            Sort::Int => match *arena.node(a) {
                // Integer constant: fold to the exact real constant.
                TermNode::IntConst(value) => out.push(arena.real_const(Rational::integer(value))),
                // Non-constant Int term: embed via the exact `to_real` operator.
                _ => out.push(arena.int_to_real(a)?),
            },
            _ => {
                return Err(SmtError::Syntax(
                    "mixed real and non-arithmetic operands".to_owned(),
                ));
            }
        }
    }
    Ok((true, out))
}

/// Coerces *every* numeric operand to `Real`, for the always-`Real` operator
/// `/` (SMT-LIB `Reals_Ints` real division). Unlike [`numeric_args`], this
/// fires even when no operand is already `Real` — e.g. `(/ 177 366500000)` over
/// two integer constants, which denotes the rational `177/366500000`. Integer
/// constants fold to `RealConst`; non-constant `Int` terms use the exact
/// `to_real` embedding. The coercion is denotation-preserving, matching Z3/cvc5.
fn real_args(arena: &mut TermArena, args: &[TermId]) -> Result<Vec<TermId>, SmtError> {
    let mut out = Vec::with_capacity(args.len());
    for &a in args {
        match arena.sort_of(a) {
            Sort::Real => out.push(a),
            Sort::Int => match *arena.node(a) {
                TermNode::IntConst(value) => out.push(arena.real_const(Rational::integer(value))),
                _ => out.push(arena.int_to_real(a)?),
            },
            _ => {
                return Err(SmtError::Syntax(
                    "`/` expects real or integer operands".to_owned(),
                ));
            }
        }
    }
    Ok(out)
}

/// Folds a binary arithmetic builder over `args` (left-associative), requiring
/// at least one argument.
fn fold_args(
    arena: &mut TermArena,
    args: &[TermId],
    op: &str,
    f: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
) -> Result<TermId, SmtError> {
    let mut iter = args.iter();
    let Some(&first) = iter.next() else {
        return Err(SmtError::Syntax(format!("`{op}` expects >= 1 argument")));
    };
    let mut acc = first;
    for &next in iter {
        acc = f(arena, acc, next)?;
    }
    Ok(acc)
}

/// Real division `(/ a b ...)`; only constant operands are in the linear
/// fragment, so each must be a real constant.
fn real_division(arena: &mut TermArena, args: &[TermId]) -> Result<TermId, SmtError> {
    if args.len() < 2 {
        return Err(SmtError::Syntax("`/` expects >= 2 arguments".to_owned()));
    }
    let value = |arena: &TermArena, t: TermId| -> Option<Rational> {
        match *arena.node(t) {
            TermNode::RealConst(r) => Some(r),
            _ => None,
        }
    };
    // Constant-fold when every operand is a real constant (and no zero divisor);
    // otherwise build symbolic `RealDiv` terms (left-associative), decided by the
    // NRA layer.
    if let Some(mut acc) = value(arena, args[0]) {
        let mut all_const = true;
        for &next in &args[1..] {
            match value(arena, next) {
                Some(divisor) if !divisor.is_zero() => acc = acc / divisor,
                _ => {
                    all_const = false;
                    break;
                }
            }
        }
        if all_const {
            return Ok(arena.real_const(acc));
        }
    }
    let mut acc = args[0];
    for &next in &args[1..] {
        acc = arena.real_div(acc, next)?;
    }
    Ok(acc)
}

/// Chains a comparison over `args` pairwise, conjoining the results: `(< a b c)`
/// becomes `(and (< a b) (< b c))` (SMT-LIB chainable relations).
fn chain_args(
    arena: &mut TermArena,
    args: &[TermId],
    op: &str,
    f: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
) -> Result<TermId, SmtError> {
    if args.len() < 2 {
        return Err(SmtError::Syntax(format!("`{op}` expects >= 2 arguments")));
    }
    let mut acc = f(arena, args[0], args[1])?;
    for pair in args.windows(2).skip(1) {
        let next = f(arena, pair[0], pair[1])?;
        acc = arena.and(acc, next)?;
    }
    Ok(acc)
}

fn bin(
    arena: &mut TermArena,
    f: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
    args: &[TermId],
    op: &str,
) -> Result<TermId, SmtError> {
    if args.len() != 2 {
        return Err(SmtError::Syntax(format!(
            "`{op}` expects 2 arguments, got {}",
            args.len()
        )));
    }
    Ok(f(arena, args[0], args[1])?)
}

/// Desugars a unary BV reduction (`bvredor` / `bvredand` / `bvredxor`) over the
/// `w`-bit operand `x` into a one-bit (`BitVec(1)`) result using existing BV
/// operators only. The semantics follow SMT-LIB 2.6 verbatim, matching the
/// authoritative elimination rules in cvc5
/// (`src/theory/bv/rewrites-elimination`) and bitwuzla
/// (`BV_RED{OR,AND,XOR}_ELIM`):
///
/// - `(bvredor x)`  = `#b1` iff `x != 0`. Desugared as `(bvnot (bvcomp x 0))`:
///   `bvcomp x 0` is the one-bit equality `#b1` iff `x = 0`, so the `bvnot`
///   flips it to `#b1` iff `x != 0`.
/// - `(bvredand x)` = `#b1` iff every bit of `x` is set, i.e. `x` equals the
///   all-ones value of its width. Desugared as `(bvcomp x (bvnot 0))`, where
///   `(bvnot 0)` is the `w`-bit all-ones constant.
/// - `(bvredxor x)` = the parity of `x` (XOR of all its bits). Desugared as the
///   left-fold `(bvxor … (bvxor (extract 0 0 x) (extract 1 1 x)) …)` over every
///   single-bit slice `((_ extract i i) x)` for `i` in `0..w`, each itself a
///   `BitVec(1)`.
///
/// All three desugarings are denotation-preserving by construction (each named
/// op is replaced by its definitional expansion in terms of ops axeyum already
/// decides), so they can never produce a wrong `sat`/`unsat`.
fn bv_reduce(arena: &mut TermArena, op: &str, x: TermId) -> Result<TermId, SmtError> {
    let Sort::BitVec(w) = arena.sort_of(x) else {
        return Err(SmtError::Syntax(format!(
            "`{op}` expects a bit-vector operand, got {:?}",
            arena.sort_of(x)
        )));
    };
    Ok(match op {
        "bvredor" => {
            let zero = arena.bv_const(w, 0)?;
            let eq = arena.bv_comp(x, zero)?;
            arena.bv_not(eq)?
        }
        "bvredand" => {
            let zero = arena.bv_const(w, 0)?;
            let ones = arena.bv_not(zero)?;
            arena.bv_comp(x, ones)?
        }
        "bvredxor" => {
            let mut acc = arena.extract(0, 0, x)?;
            for i in 1..w {
                let bit = arena.extract(i, i, x)?;
                acc = arena.bv_xor(acc, bit)?;
            }
            acc
        }
        _ => unreachable!("bv_reduce called with non-reduction op `{op}`"),
    })
}

/// Desugars `((_ iand N) a b)` — the SMT-LIB integer bitwise-AND at bit-width
/// `N` — into existing Int↔BV ops. Per the SMT-LIB `Ints` theory definition,
/// for integer operands `a`, `b`:
///
/// ```text
/// ((_ iand N) a b) = bv2nat( bvand( ((_ int2bv N) a), ((_ int2bv N) b) ) )
/// ```
///
/// `((_ int2bv N) x)` reduces `x` modulo `2^N` to an `N`-bit two's-complement
/// pattern (axeyum's [`TermArena::int2bv`] is exactly "the operand integer
/// reduced mod `2^N`"), `bvand` is the bitwise AND of those patterns, and
/// `bv2nat` ([`TermArena::bv2nat`]) reinterprets the `N`-bit result as the
/// non-negative integer in `[0, 2^N)`. This is the operator's *definition*, so
/// the desugaring is denotation-preserving and cannot yield a wrong verdict.
///
/// The index `N` must be a positive numeral; the application is binary.
///
/// # Errors
///
/// [`SmtError::Syntax`] for a missing/non-numeric/zero index, a wrong argument
/// count, or non-integer operands.
fn apply_iand(arena: &mut TermArena, head: &[SExpr], args: &[TermId]) -> Result<TermId, SmtError> {
    if head.len() != 3 {
        return Err(SmtError::Syntax(format!(
            "`iand` expects 1 index, got {}",
            head.len().saturating_sub(2)
        )));
    }
    let n = head
        .get(2)
        .and_then(SExpr::atom)
        .and_then(|s| s.parse::<u32>().ok())
        .filter(|&n| n > 0)
        .ok_or_else(|| SmtError::Syntax("`iand` index must be a positive numeral".to_owned()))?;
    if args.len() != 2 {
        return Err(SmtError::Syntax(format!(
            "`(_ iand {n})` expects 2 arguments, got {}",
            args.len()
        )));
    }
    if arena.sort_of(args[0]) != Sort::Int || arena.sort_of(args[1]) != Sort::Int {
        return Err(SmtError::Syntax(
            "`iand` expects two integer arguments".to_owned(),
        ));
    }
    let a_bv = arena.int2bv(n, args[0])?;
    let b_bv = arena.int2bv(n, args[1])?;
    let anded = arena.bv_and(a_bv, b_bv)?;
    Ok(arena.bv2nat(anded)?)
}

#[allow(clippy::too_many_lines)]
fn apply_parameterized(
    arena: &mut TermArena,
    head: &[SExpr],
    args: &[TermId],
) -> Result<TermId, SmtError> {
    // Constant array `((as const (Array (_ BitVec i) (_ BitVec e))) v)`.
    if head.first().and_then(SExpr::atom) == Some("as") {
        if head.get(1).and_then(SExpr::atom) == Some("const") && head.len() == 3 && args.len() == 1
        {
            // The `as const` sort is the explicit array form; sort aliases are
            // resolved at declaration sites, not threaded into term conversion,
            // so an empty alias map is correct here.
            let no_aliases: HashMap<String, Sort> = HashMap::new();
            let Sort::Array { index, .. } = parse_sort(arena, &no_aliases, &head[2])? else {
                return Err(SmtError::Unsupported(format!(
                    "`as const` non-array sort {head:?}"
                )));
            };
            return Ok(arena.const_array(index, args[0])?);
        }
        return Err(SmtError::Unsupported(format!("`as` form {head:?}")));
    }
    // `((_ iand N) a b)` — integer bitwise-AND at bit-width `N` (QF_NIA,
    // SMT-LIB). This is the one indexed op here that is *binary*, so it is
    // handled before the unary-arity guard below. See [`apply_iand`].
    if head.first().and_then(SExpr::atom) == Some("_")
        && head.get(1).and_then(SExpr::atom) == Some("iand")
    {
        return apply_iand(arena, head, args);
    }
    if head.first().and_then(SExpr::atom) != Some("_") || args.len() != 1 {
        return Err(SmtError::Unsupported(format!("application head {head:?}")));
    }
    let name = head
        .get(1)
        .and_then(SExpr::atom)
        .ok_or_else(|| SmtError::Syntax("indexed operator name".to_owned()))?;
    let expect_head_len = |n: usize| -> Result<(), SmtError> {
        if head.len() == n {
            Ok(())
        } else {
            Err(SmtError::Syntax(format!(
                "`{name}` expects {} indices, got {}",
                n.saturating_sub(2),
                head.len().saturating_sub(2)
            )))
        }
    };
    let index = |i: usize| -> Result<u32, SmtError> {
        head.get(i)
            .and_then(SExpr::atom)
            .and_then(|s| s.parse::<u32>().ok())
            .ok_or_else(|| SmtError::Syntax(format!("`{name}` index {i}")))
    };
    Ok(match name {
        "extract" => {
            expect_head_len(4)?;
            arena.extract(index(2)?, index(3)?, args[0])?
        }
        "zero_extend" => {
            expect_head_len(3)?;
            arena.zero_ext(index(2)?, args[0])?
        }
        "sign_extend" => {
            expect_head_len(3)?;
            arena.sign_ext(index(2)?, args[0])?
        }
        "rotate_left" => {
            expect_head_len(3)?;
            arena.rotate_left(index(2)?, args[0])?
        }
        "rotate_right" => {
            expect_head_len(3)?;
            arena.rotate_right(index(2)?, args[0])?
        }
        "repeat" => {
            expect_head_len(3)?;
            let n = index(2)?;
            if n == 0 {
                return Err(SmtError::Syntax("`repeat` index must be >= 1".to_owned()));
            }
            let mut acc = args[0];
            for _ in 1..n {
                acc = arena.concat(acc, args[0])?;
            }
            acc
        }
        "divisible" => {
            expect_head_len(3)?;
            let n: i128 = head
                .get(2)
                .and_then(SExpr::atom)
                .and_then(|s| s.parse().ok())
                .ok_or_else(|| SmtError::Syntax("`divisible` index".to_owned()))?;
            arena.int_divisible(args[0], n)?
        }
        // `(_ int2bv N)` (SMT-LIB 2.6) and `(_ int_to_bv N)` (the SMT-LIB 2.7 /
        // cvc5 spelling) are the *same* indexed operator: the `N`-bit two's-
        // complement pattern of an integer reduced modulo `2^N`. Both map to
        // [`TermArena::int2bv`] verbatim.
        "int2bv" | "int_to_bv" => {
            expect_head_len(3)?;
            arena.int2bv(index(2)?, args[0])?
        }
        "to_fp" => {
            expect_head_len(4)?;
            let (eb, sb) = (index(2)?, index(3)?);
            // `((_ to_fp eb sb) x)` over a single bit-vector argument is an IEEE
            // bit-pattern reinterpret to a `Float { eb, sb }` (ADR-0026). The
            // rounding-mode forms (from FP, real, or signed BV) take a leading
            // `RoundingMode` and are handled in `apply_fp_rounded_indexed`.
            if args.len() != 1 {
                return Err(SmtError::Unsupported(
                    "(_ to_fp …) bit reinterpret expects exactly one bit-vector operand".to_owned(),
                ));
            }
            match arena.sort_of(args[0]) {
                Sort::BitVec(bw) if bw == eb + sb => arena.fp_from_bits(args[0], eb, sb)?,
                s => {
                    return Err(SmtError::Syntax(format!(
                        "(_ to_fp {eb} {sb}) bit reinterpret expects a BitVec({}), got {s:?}",
                        eb + sb
                    )));
                }
            }
        }
        // Datatype tester `((_ is C) x)` → is `x` built by constructor `C`?
        "is" => {
            expect_head_len(3)?;
            let cname = head
                .get(2)
                .and_then(SExpr::atom)
                .ok_or_else(|| SmtError::Syntax("`(_ is C)` constructor name".to_owned()))?;
            let ctor = arena
                .find_constructor(cname)
                .ok_or_else(|| SmtError::Unsupported(format!("unknown constructor `{cname}`")))?;
            arena.dt_test(ctor, args[0])?
        }
        other => return Err(SmtError::Unsupported(format!("indexed operator `{other}`"))),
    })
}
