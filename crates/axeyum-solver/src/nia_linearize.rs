//! Phase E first slice (P2.5): integer nonlinear reasoning via product
//! abstraction + valid integer sign/monotonicity lemmas + variable-divisor
//! Euclidean `div`/`mod` linearization, solved over the integer DPLL(T).
//!
//! [`check_with_nia`] is the integer analog of [`crate::nra::check_with_nra`]:
//!
//! 1. **Div/mod linearization.** Constant-divisor `div`/`mod`/`abs` are first
//!    eliminated exactly by [`axeyum_rewrite::eliminate_int_divmod`]. Then each
//!    `div`/`mod` with a **variable** divisor `b` introduces fresh `q, r` with the
//!    theory-valid Euclidean constraints, **guarded by `b ≠ 0`**:
//!    `b > 0 → (a = b·q + r ∧ 0 ≤ r ≤ b−1)` and
//!    `b < 0 → (a = b·q + r ∧ 0 ≤ r ≤ −b−1)`. When `b = 0` the fresh `q, r` are
//!    left **unconstrained** (SMT-LIB leaves `div`/`mod` by zero underspecified —
//!    a relaxation of the evaluator's total `div a 0 = 0` / `mod a 0 = a`
//!    convention), so an `unsat` of the relaxation still transfers soundly. A
//!    **self-division** identity `b ≠ 0 → (div b b = 1 ∧ mod b b = 0)` is added
//!    when the dividend and divisor are the same term.
//! 2. **Product abstraction.** Each integer product `a·b` (both operands
//!    non-constant — including the `b·q` introduced above) is replaced by a fresh
//!    `Int` variable `r`, and the valid integer sign/zero lemmas relating `r` to
//!    `a` and `b` are added.
//! 3. **Integer relaxation.** The result is solved with
//!    [`crate::dpll_lia::check_with_lia_dpll`]. An `unsat` transfers to the
//!    original (the abstraction only enlarges the model space and every lemma is a
//!    valid consequence). A `sat` is returned **only** after the model **replays**
//!    against the true original assertions under the ground evaluator (a
//!    mis-linearization ⇒ replay fails ⇒ `unknown`, never a wrong verdict).
//!
//! Unlike the real relaxation (`int_real_relax` → `check_with_nra`), it keeps
//! **integrality**, so integer bound tightening (`q < 1 ⟹ q ≤ 0`, valid only over
//! ℤ) combines with a sign lemma (`q ≤ 0 ∧ n ≥ 0 ⟹ q·n ≤ 0`) to refute e.g.
//! `div.03` (`n>0 ∧ x≥n ∧ (div x n)<1`), which is unsat over ℤ but *sat over ℝ*
//! (so the real relaxation cannot refute it).

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_rewrite::replace_subterms;

use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::dpll_lia::check_with_lia_dpll;
use crate::model::Model;

// Takes `IrError` by value so it can be used directly as a `.map_err(err)`
// adapter over the IR builders (which yield owned errors); the value is only
// formatted, hence the localized allow.
#[allow(clippy::needless_pass_by_value)]
fn err(e: IrError) -> SolverError {
    SolverError::Backend(e.to_string())
}

/// Wall-clock slice (ms) for the integer-relaxation DPLL(T) solve. Bounds this
/// pre-ladder pass so it can never hang: the div/mod refutations are tiny and
/// decide well within it, and a harder relaxation declines to the width ladder.
const NIA_SLICE_MS: u64 = 600;

/// Distinct integer products `a·b` reachable from `roots`, with both operands
/// non-constant (a `const·term` is linear and not abstracted).
fn int_products(arena: &TermArena, roots: &[TermId]) -> BTreeSet<TermId> {
    let mut products = BTreeSet::new();
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
        if op == Op::IntMul && args.len() == 2 {
            let a_const = matches!(arena.node(args[0]), TermNode::IntConst(_));
            let b_const = matches!(arena.node(args[1]), TermNode::IntConst(_));
            if !a_const && !b_const {
                products.insert(term);
            }
        }
        stack.extend(args);
    }
    products
}

/// The valid integer sign/zero lemmas for `r = a·b` (each is a consequence of the
/// abstracted equality, so adding them only restricts the relaxation's models).
/// Deliberately kept to the six cheap sign/zero facts — they suffice for the
/// div/mod targets (`div.03` refutes from `q≤0 ∧ n≥0 ⇒ n·q≤0`) and keep the
/// abstracted relaxation small for the DPLL(T) search.
fn sign_lemmas(
    arena: &mut TermArena,
    a: TermId,
    b: TermId,
    r: TermId,
    zero: TermId,
) -> Result<Vec<TermId>, SolverError> {
    let a_nonneg = arena.int_ge(a, zero).map_err(err)?;
    let a_nonpos = arena.int_le(a, zero).map_err(err)?;
    let b_nonneg = arena.int_ge(b, zero).map_err(err)?;
    let b_nonpos = arena.int_le(b, zero).map_err(err)?;
    let prod_nonneg = arena.int_ge(r, zero).map_err(err)?;
    let prod_nonpos = arena.int_le(r, zero).map_err(err)?;
    let a_zero = arena.eq(a, zero).map_err(err)?;
    let b_zero = arena.eq(b, zero).map_err(err)?;
    let prod_zero = arena.eq(r, zero).map_err(err)?;

    let mut out = Vec::with_capacity(6);
    // (a≥0 ∧ b≥0) → r≥0 ; (a≤0 ∧ b≤0) → r≥0
    let p = arena.and(a_nonneg, b_nonneg).map_err(err)?;
    out.push(arena.implies(p, prod_nonneg).map_err(err)?);
    let p = arena.and(a_nonpos, b_nonpos).map_err(err)?;
    out.push(arena.implies(p, prod_nonneg).map_err(err)?);
    // (a≥0 ∧ b≤0) → r≤0 ; (a≤0 ∧ b≥0) → r≤0
    let p = arena.and(a_nonneg, b_nonpos).map_err(err)?;
    out.push(arena.implies(p, prod_nonpos).map_err(err)?);
    let p = arena.and(a_nonpos, b_nonneg).map_err(err)?;
    out.push(arena.implies(p, prod_nonpos).map_err(err)?);
    // a=0 → r=0 ; b=0 → r=0 (the two easy halves of `r=0 ⟺ a=0 ∨ b=0`)
    out.push(arena.implies(a_zero, prod_zero).map_err(err)?);
    out.push(arena.implies(b_zero, prod_zero).map_err(err)?);
    Ok(out)
}

/// A `div`/`mod` group keyed by `(dividend, variable-divisor)`.
#[derive(Default)]
struct VarDivMod {
    div: Vec<TermId>,
    mod_: Vec<TermId>,
}

/// Collects every `div`/`mod` term whose divisor is a **non-constant** term,
/// grouped by `(dividend, divisor)` (deterministic key order). Constant-divisor
/// terms are ignored here — they are eliminated exactly beforehand by
/// [`axeyum_rewrite::eliminate_int_divmod`].
fn collect_var_divmod(
    arena: &TermArena,
    roots: &[TermId],
) -> BTreeMap<(TermId, TermId), VarDivMod> {
    let mut groups: BTreeMap<(TermId, TermId), VarDivMod> = BTreeMap::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        let (op, args) = (*op, args.clone());
        if matches!(op, Op::IntDiv | Op::IntMod)
            && !matches!(arena.node(args[1]), TermNode::IntConst(_))
        {
            let entry = groups.entry((args[0], args[1])).or_default();
            if op == Op::IntDiv {
                entry.div.push(term);
            } else {
                entry.mod_.push(term);
            }
        }
        stack.extend(args);
    }
    groups
}

/// Eliminate every **variable-divisor** `div`/`mod` in `assertions` into fresh
/// `q`/`r` variables plus their theory-valid, `divisor ≠ 0`-guarded Euclidean
/// constraints (and a self-division identity when dividend and divisor coincide).
/// Returns the rewritten assertions followed by the new constraints; when there is
/// no variable-divisor `div`/`mod`, returns `None` (the caller declines).
///
/// The `divisor = 0` case is intentionally left **unconstrained** — a sound
/// relaxation of the evaluator's total `div a 0 = 0` / `mod a 0 = a` convention:
/// every SMT-LIB model induces a model of the relaxation (Euclidean when the
/// divisor is nonzero; free when it is zero), so an `unsat` of the relaxation
/// transfers soundly, while a `sat` is only ever accepted after replay against the
/// original under the evaluator's total convention.
fn eliminate_variable_divmod(
    arena: &mut TermArena,
    assertions: &[TermId],
    counter: &mut u32,
) -> Result<Option<Vec<TermId>>, SolverError> {
    let groups = collect_var_divmod(arena, assertions);
    if groups.is_empty() {
        return Ok(None);
    }
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut constraints: Vec<TermId> = Vec::new();

    for ((dividend, divisor), terms) in groups {
        let q = fresh_int(arena, counter)?;
        let r = fresh_int(arena, counter)?;
        for t in terms.div {
            map.insert(t, q);
        }
        for t in terms.mod_ {
            map.insert(t, r);
        }
        // a = b·q + r  (the product `b·q` is abstracted downstream by
        // `int_products`; `0 ≤ r` and the upper bound are split by the sign of `b`).
        let bq = arena.int_mul(divisor, q).map_err(err)?;
        let sum = arena.int_add(bq, r).map_err(err)?;
        let euclid = arena.eq(dividend, sum).map_err(err)?;
        let r_ge0 = arena.int_ge(r, zero).map_err(err)?;

        // b > 0 → (a = b·q + r ∧ 0 ≤ r ≤ b − 1)
        let b_pos = arena.int_gt(divisor, zero).map_err(err)?;
        let b_minus_1 = arena.int_sub(divisor, one).map_err(err)?;
        let r_le_hi = arena.int_le(r, b_minus_1).map_err(err)?;
        let range = arena.and(r_ge0, r_le_hi).map_err(err)?;
        let body = arena.and(euclid, range).map_err(err)?;
        constraints.push(arena.implies(b_pos, body).map_err(err)?);

        // b < 0 → (a = b·q + r ∧ 0 ≤ r ≤ −b − 1)
        let b_neg = arena.int_lt(divisor, zero).map_err(err)?;
        let neg_b = arena.int_neg(divisor).map_err(err)?;
        let neg_b_minus_1 = arena.int_sub(neg_b, one).map_err(err)?;
        let r_le_hi = arena.int_le(r, neg_b_minus_1).map_err(err)?;
        let range = arena.and(r_ge0, r_le_hi).map_err(err)?;
        let body = arena.and(euclid, range).map_err(err)?;
        constraints.push(arena.implies(b_neg, body).map_err(err)?);

        // Self-division identity: b ≠ 0 → (div b b = 1 ∧ mod b b = 0).
        if dividend == divisor {
            let q_is_1 = arena.eq(q, one).map_err(err)?;
            let r_is_0 = arena.eq(r, zero).map_err(err)?;
            let both = arena.and(q_is_1, r_is_0).map_err(err)?;
            let b_zero = arena.eq(divisor, zero).map_err(err)?;
            let b_ne_0 = arena.not(b_zero).map_err(err)?;
            constraints.push(arena.implies(b_ne_0, both).map_err(err)?);
        }
    }

    // Substitute the eliminated terms throughout the assertions and constraints
    // (nested div/mod inside a dividend/constraint are handled too).
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len() + constraints.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
    }
    for c in constraints {
        out.push(replace_subterms(arena, c, &map, &mut memo).map_err(err)?);
    }
    Ok(Some(out))
}

fn fresh_int(arena: &mut TermArena, counter: &mut u32) -> Result<TermId, SolverError> {
    let name = format!("!nia_dm_{counter}");
    *counter += 1;
    let sym = arena.declare(&name, Sort::Int).map_err(err)?;
    Ok(arena.var(sym))
}

/// The declared symbols occurring in `roots` (used to restrict a relaxation `sat`
/// model to the original vocabulary before returning it).
fn collect_symbols(arena: &TermArena, roots: &[TermId]) -> BTreeSet<SymbolId> {
    let mut syms = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        match arena.node(term) {
            TermNode::Symbol(s) => {
                syms.insert(*s);
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    syms
}

/// Integer nonlinear decider (Phase E first slice) — the integer analog of
/// [`crate::nra::check_with_nra`]. Linearizes variable-divisor `div`/`mod`,
/// abstracts each integer product with its valid sign/zero lemmas, and
/// solves the relaxation over the integer DPLL(T). Returns `Some(Unsat)` (a sound
/// transfer), `Some(Sat)` (only after the model replays against the **original**
/// assertions under the ground evaluator), or `None` (declines) — never a wrong
/// verdict.
///
/// # Errors
///
/// Propagates [`SolverError`] from term construction. Solver-side errors are
/// swallowed into a decline (`None`): this path only ever turns `unknown` into a
/// decision, so it must never propagate a hard error.
pub fn check_with_nia(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    // 1. Eliminate constant-divisor div/mod + abs exactly (equisatisfiable).
    let lin = axeyum_rewrite::eliminate_int_divmod(arena, assertions).map_err(err)?;
    // 2. Eliminate variable-divisor div/mod (guarded Euclidean + self-division).
    let mut counter = 0u32;
    let after_divmod = eliminate_variable_divmod(arena, &lin, &mut counter)?;
    let had_var_divmod = after_divmod.is_some();
    let working = after_divmod.unwrap_or(lin);

    // 3. Abstract integer products and add their valid lemmas.
    let products = int_products(arena, &working);
    if products.is_empty() && !had_var_divmod {
        // Nothing nonlinear to exploit — a pure-linear query the LIA path already
        // owns; decline rather than re-solve it.
        return Ok(None);
    }
    let zero = arena.int_const(0);
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut triples: Vec<(TermId, TermId, TermId)> = Vec::new();
    for (i, &product) in products.iter().enumerate() {
        let TermNode::App { args, .. } = arena.node(product) else {
            continue;
        };
        let (a, b) = (args[0], args[1]);
        let fresh = arena
            .declare(&format!("!nia_{i}"), Sort::Int)
            .map_err(err)?;
        let r = arena.var(fresh);
        map.insert(product, r);
        triples.push((a, b, r));
    }

    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut relaxed: Vec<TermId> = Vec::with_capacity(working.len() + triples.len() * 6);
    for &a in &working {
        relaxed.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
    }
    for &(a, b, r) in &triples {
        let a = replace_subterms(arena, a, &map, &mut memo).map_err(err)?;
        let b = replace_subterms(arena, b, &map, &mut memo).map_err(err)?;
        relaxed.extend(sign_lemmas(arena, a, b, r, zero)?);
    }

    // 4. Solve the relaxation over the integer DPLL(T), under a bounded slice.
    //    `unsat` transfers soundly. `sat` is accepted only after the model replays
    //    against the ORIGINAL assertions (with div/mod intact) under the ground
    //    evaluator — a mis-linearization ⇒ replay fails ⇒ decline. Any solver error
    //    is a decline (this path only upgrades `unknown` to a decision).
    //
    //    The relaxation is Boolean-structured (guarded implications + sign lemmas),
    //    so an unbounded DPLL(T) search can grind; this pass runs *before* the
    //    width ladder on every nonlinear-int query, so it must never hang. Cap it
    //    at a short slice (respecting a smaller configured timeout): the targeted
    //    div/mod refutations decide in milliseconds, and any harder relaxation
    //    declines to the ladder rather than starving it.
    let capped = {
        let slice = std::time::Duration::from_millis(NIA_SLICE_MS);
        let bound = config.timeout.map_or(slice, |t| t.min(slice));
        config.clone().with_timeout(bound)
    };
    match check_with_lia_dpll(arena, &relaxed, &capped) {
        Ok(CheckResult::Unsat) => Ok(Some(CheckResult::Unsat)),
        Ok(CheckResult::Sat(model)) => Ok(replay_sat(arena, assertions, &model)),
        Ok(CheckResult::Unknown(_)) | Err(_) => Ok(None),
    }
}

/// Accepts a relaxation `sat` model only if it replays every **original**
/// assertion true under the ground evaluator; returns the model restricted to the
/// original vocabulary (dropping the fresh abstraction/Euclidean variables).
fn replay_sat(arena: &TermArena, assertions: &[TermId], model: &Model) -> Option<CheckResult> {
    let assignment = model.to_assignment();
    let all_true = assertions
        .iter()
        .all(|&a| matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))));
    if !all_true {
        return None;
    }
    // Restrict the model to the symbols actually present in the original query, so
    // the returned witness carries no internal `!nia_*` scaffolding.
    let originals = collect_symbols(arena, assertions);
    let mut clean = Model::new();
    for (sym, value) in model.iter() {
        if originals.contains(&sym) {
            clean.set(sym, value);
        }
    }
    Some(CheckResult::Sat(clean))
}
