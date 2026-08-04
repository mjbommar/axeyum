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
//!    On top of those, every product whose factors carry constant bounds
//!    **entailed by the relaxation** ([`harvest_const_bounds`]) also gets the
//!    four linear `McCormick` envelope inequalities ([`mccormick_lemmas`]). The
//!    sign lemmas fix only the *quadrant* of a product, never its magnitude, so a
//!    Farkas / ranking-function system would otherwise relax to one free variable
//!    per product and be trivially satisfiable. The envelopes are consequences of
//!    those entailed bounds, so they cannot change the relaxation's
//!    satisfiability — they only hand the linear engine the coupling it needs.
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
use crate::route_trace::DeclineReason;

// Takes `IrError` by value so it can be used directly as a `.map_err(err)`
// adapter over the IR builders (which yield owned errors); the value is only
// formatted, hence the localized allow.
#[allow(clippy::needless_pass_by_value)]
fn err(e: IrError) -> SolverError {
    SolverError::Backend(e.to_string())
}

/// Default wall-clock slice (ms) for the integer-relaxation DPLL(T) solve.
/// Bounds this pre-ladder pass so it can never hang: the div/mod refutations are
/// tiny and decide well within it, and a harder relaxation declines to the width
/// ladder. Raised to a share of the caller's remaining budget only when `McCormick`
/// envelopes were actually emitted — see [`NIA_MCCORMICK_BUDGET_SHARE`].
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

/// Whether any assertion reachable from `roots` contains a genuinely nonlinear
/// integer product (both operands non-constant) — the exact predicate
/// [`int_products`] uses, exposed so the arithmetic dispatcher can tell a
/// nonlinear-integer query from a linear one *before* spending budget on a
/// purely-linear decision procedure that structurally cannot decide it.
pub(crate) fn has_nonlinear_int_product(arena: &TermArena, roots: &[TermId]) -> bool {
    !int_products(arena, roots).is_empty()
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

/// Per-group data retained by [`eliminate_variable_divmod`] for the pairwise
/// Ackermann congruence pass (the fresh quotient `q` / remainder `r` and whether
/// the group actually contributed a `div` / `mod` term).
struct GroupInfo {
    dividend: TermId,
    divisor: TermId,
    q: TermId,
    r: TermId,
    has_div: bool,
    has_mod: bool,
}

/// Upper bound on the number of variable-divisor `div`/`mod` groups over which the
/// eager Ackermann congruence lemmas are emitted (the pass is `O(k²)` in the group
/// count). Beyond this the lemmas are skipped — still sound, only less complete.
const MAX_CONGRUENCE_GROUPS: usize = 48;

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
/// The `divisor = 0` case is intentionally left **unconstrained by the Euclidean
/// identity** — a sound relaxation of the evaluator's total `div a 0 = 0` /
/// `mod a 0 = a` convention: every SMT-LIB model induces a model of the relaxation
/// (Euclidean when the divisor is nonzero; free when it is zero), so an `unsat` of
/// the relaxation transfers soundly, while a `sat` is only ever accepted after
/// replay against the original under the evaluator's total convention.
///
/// The free `q, r` are nevertheless kept **congruent** across groups: `div` and
/// `mod` are *total binary functions*, so for groups `(a, b)` and `(c, d)` the
/// eager Ackermann lemma `(a = c ∧ b = d) → q_ab = q_cd` (and the same for `r`) is
/// a valid consequence for **every** divisor value, including `b = d = 0`. Adding
/// these lemmas is monotone-sound (the true model satisfies every congruence
/// lemma, so no satisfiable formula can be turned unsat), yet it recovers the
/// value-independent structural contradictions a fresh-per-term relaxation loses:
/// e.g. the nested `div(div n n) n` chains where an asserted `t2 = t3` propagates
/// by congruence to `t3 = t4 = t5`, contradicting an asserted `t2 ≠ t5` regardless
/// of the underspecified div-by-zero value.
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
    // Per-group metadata retained for the pairwise Ackermann congruence pass.
    let mut infos: Vec<GroupInfo> = Vec::new();

    for ((dividend, divisor), terms) in groups {
        let q = fresh_int(arena, counter)?;
        let r = fresh_int(arena, counter)?;
        let has_div = !terms.div.is_empty();
        let has_mod = !terms.mod_.is_empty();
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

        infos.push(GroupInfo {
            dividend,
            divisor,
            q,
            r,
            has_div,
            has_mod,
        });
    }

    // Eager Ackermann congruence over every pair of groups: `div`/`mod` are total
    // binary functions, so `(a_i = a_j ∧ b_i = b_j) → q_i = q_j` (and the same for
    // the remainders `r`) holds for ALL divisor values, INCLUDING zero. This is the
    // sound recovery for the div-by-zero *structural* unsats: the antecedent's
    // dividend/divisor terms are rewritten downstream by `replace_subterms`, so
    // when a dividend is itself a nested `div`/`mod` term the equality links the
    // quotient variables and an asserted equality among nested quotients propagates
    // by congruence (contradicting an asserted `distinct`), regardless of the
    // underspecified div-by-zero value. Adding these lemmas is monotone-sound (the
    // true model satisfies every congruence lemma, so no satisfiable formula can be
    // turned unsat). Bounded by `MAX_CONGRUENCE_GROUPS` to keep the O(k²) lemma
    // count small — a larger group set simply forgoes the lemmas (still sound, just
    // less complete) and relies on the width ladder / other routes.
    if infos.len() <= MAX_CONGRUENCE_GROUPS {
        for first in 0..infos.len() {
            for second in (first + 1)..infos.len() {
                let (left, right) = (&infos[first], &infos[second]);
                let same_dividend = arena.eq(left.dividend, right.dividend).map_err(err)?;
                let same_divisor = arena.eq(left.divisor, right.divisor).map_err(err)?;
                let same_args = arena.and(same_dividend, same_divisor).map_err(err)?;
                if left.has_div && right.has_div {
                    let q_eq = arena.eq(left.q, right.q).map_err(err)?;
                    constraints.push(arena.implies(same_args, q_eq).map_err(err)?);
                }
                if left.has_mod && right.has_mod {
                    let r_eq = arena.eq(left.r, right.r).map_err(err)?;
                    constraints.push(arena.implies(same_args, r_eq).map_err(err)?);
                }
            }
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
    let sym = arena.declare_internal(&name, Sort::Int).map_err(err)?;
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

/// Distinct `int.pow2` terms reachable from `roots` (hash-consed ⇒ each surface
/// occurrence of the same `pow2(x)` is one `TermId`, so the abstraction is
/// congruent — identical arguments map to one fresh variable — by construction).
fn collect_pow2(arena: &TermArena, roots: &[TermId]) -> BTreeSet<TermId> {
    let mut pow2s = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        if *op == Op::IntPow2 {
            pow2s.insert(term);
        }
        stack.extend(args.iter().copied());
    }
    pow2s
}

/// Every distinct subterm reachable from `roots` (used for cheap membership tests).
fn all_subterms(arena: &TermArena, roots: &[TermId]) -> BTreeSet<TermId> {
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    seen
}

/// An integer literal's value, or `None` for a non-constant term.
fn as_int_const(arena: &TermArena, t: TermId) -> Option<i128> {
    match arena.node(t) {
        TermNode::IntConst(v) => Some(*v),
        _ => None,
    }
}

/// The exact cvc5 `pow2` value at a *constant* exponent `k`: `0` for `k < 0`,
/// `2^k` for `0 ≤ k`; `None` when `2^k` would leave the safe `i128` table range.
fn pow2_value(k: i128) -> Option<i128> {
    if k < 0 {
        Some(0)
    } else if k <= POW2_TABLE_MAX_EXP {
        Some(1i128 << k)
    } else {
        None
    }
}

/// Largest exponent enumerated in a value table (`2^62 < i128::MAX`).
const POW2_TABLE_MAX_EXP: i128 = 62;
/// Largest number of `x = k` cases emitted in one value table.
const POW2_TABLE_MAX_CASES: i128 = 128;

/// Sound constant bounds `[lo, hi]` on `target`, derived ONLY from top-level
/// asserted conjuncts (descending exclusively through `and` — never through
/// `or`/`not`/`ite`, whose sub-atoms would not be *implied*). Either endpoint may
/// be absent. Every returned bound is a logical consequence of `assertions`, so
/// enumerating `target ∈ [lo, hi]` is a theorem.
fn const_bounds_of_term(
    arena: &TermArena,
    assertions: &[TermId],
    target: TermId,
) -> (Option<i128>, Option<i128>) {
    // Ignore constants outside a sane band: they can only widen the range past
    // the table cap anyway, and `c ± 1` stays in-range.
    const BAND: i128 = 1 << 62;
    let mut lo: Option<i128> = None;
    let mut hi: Option<i128> = None;
    let mut tighten_lo = |v: i128| lo = Some(lo.map_or(v, |c| c.max(v)));
    let mut tighten_hi = |v: i128| hi = Some(hi.map_or(v, |c| c.min(v)));
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(t) else {
            continue;
        };
        let op = *op;
        if op == Op::BoolAnd {
            stack.extend(args.iter().copied());
            continue;
        }
        if args.len() != 2 {
            continue;
        }
        let (a, b) = (args[0], args[1]);
        let ac = as_int_const(arena, a).filter(|c| c.abs() < BAND);
        let bc = as_int_const(arena, b).filter(|c| c.abs() < BAND);
        match op {
            // a ≤ b
            Op::IntLe => {
                if a == target
                    && let Some(c) = bc
                {
                    tighten_hi(c);
                }
                if b == target
                    && let Some(c) = ac
                {
                    tighten_lo(c);
                }
            }
            // a < b
            Op::IntLt => {
                if a == target
                    && let Some(c) = bc
                {
                    tighten_hi(c - 1);
                }
                if b == target
                    && let Some(c) = ac
                {
                    tighten_lo(c + 1);
                }
            }
            // a ≥ b
            Op::IntGe => {
                if a == target
                    && let Some(c) = bc
                {
                    tighten_lo(c);
                }
                if b == target
                    && let Some(c) = ac
                {
                    tighten_hi(c);
                }
            }
            // a > b
            Op::IntGt => {
                if a == target
                    && let Some(c) = bc
                {
                    tighten_lo(c + 1);
                }
                if b == target
                    && let Some(c) = ac
                {
                    tighten_hi(c - 1);
                }
            }
            // a = b pins both endpoints.
            Op::Eq => {
                if a == target
                    && let Some(c) = bc
                {
                    tighten_lo(c);
                    tighten_hi(c);
                }
                if b == target
                    && let Some(c) = ac
                {
                    tighten_lo(c);
                    tighten_hi(c);
                }
            }
            _ => {}
        }
    }
    (lo, hi)
}

/// Constant lower/upper endpoints entailed for one term (either may be absent).
type ConstBounds = (Option<i128>, Option<i128>);

/// Raises the recorded lower endpoint for `t` to `v` (keeping the tightest).
fn tighten_lo(map: &mut BTreeMap<TermId, ConstBounds>, t: TermId, v: i128) {
    let e = map.entry(t).or_insert((None, None));
    e.0 = Some(e.0.map_or(v, |c: i128| c.max(v)));
}

/// Lowers the recorded upper endpoint for `t` to `v` (keeping the tightest).
fn tighten_hi(map: &mut BTreeMap<TermId, ConstBounds>, t: TermId, v: i128) {
    let e = map.entry(t).or_insert((None, None));
    e.1 = Some(e.1.map_or(v, |c: i128| c.min(v)));
}

/// One **single pass** harvest of the constant bounds entailed by `assertions`,
/// for **every** term that appears on one side of a top-level comparison against
/// an integer literal. This is [`const_bounds_of_term`] generalized from one
/// target to a map, so a query with thousands of products costs one traversal
/// instead of one per product operand.
///
/// Exactly the same soundness discipline: the walk descends **only** through
/// `and` (never `or`/`not`/`ite`/`=>`, whose sub-atoms are not implied), so every
/// recorded endpoint is a logical consequence of `assertions`.
fn harvest_const_bounds(arena: &TermArena, assertions: &[TermId]) -> BTreeMap<TermId, ConstBounds> {
    // Same sanity band as `const_bounds_of_term`: `c ± 1` stays in range.
    const BAND: i128 = 1 << 62;
    let mut out: BTreeMap<TermId, ConstBounds> = BTreeMap::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(t) else {
            continue;
        };
        let op = *op;
        if op == Op::BoolAnd {
            stack.extend(args.iter().copied());
            continue;
        }
        if args.len() != 2 {
            continue;
        }
        let (a, b) = (args[0], args[1]);
        let ac = as_int_const(arena, a).filter(|c| c.abs() < BAND);
        let bc = as_int_const(arena, b).filter(|c| c.abs() < BAND);
        match op {
            // a ≤ b
            Op::IntLe => {
                if let Some(c) = bc {
                    tighten_hi(&mut out, a, c);
                }
                if let Some(c) = ac {
                    tighten_lo(&mut out, b, c);
                }
            }
            // a < b
            Op::IntLt => {
                if let Some(c) = bc {
                    tighten_hi(&mut out, a, c - 1);
                }
                if let Some(c) = ac {
                    tighten_lo(&mut out, b, c + 1);
                }
            }
            // a ≥ b
            Op::IntGe => {
                if let Some(c) = bc {
                    tighten_lo(&mut out, a, c);
                }
                if let Some(c) = ac {
                    tighten_hi(&mut out, b, c);
                }
            }
            // a > b
            Op::IntGt => {
                if let Some(c) = bc {
                    tighten_lo(&mut out, a, c + 1);
                }
                if let Some(c) = ac {
                    tighten_hi(&mut out, b, c - 1);
                }
            }
            // a = b pins both endpoints (only when the term's sort is Int — an
            // `Eq` over another sort cannot have an `IntConst` side, so the
            // constant filter above already restricts this to integer equalities).
            Op::Eq => {
                if let Some(c) = bc {
                    tighten_lo(&mut out, a, c);
                    tighten_hi(&mut out, a, c);
                }
                if let Some(c) = ac {
                    tighten_lo(&mut out, b, c);
                    tighten_hi(&mut out, b, c);
                }
            }
            _ => {}
        }
    }
    // A literal is its own bound but carries no information for a product
    // operand; drop those entries so the McCormick pass only sees real terms.
    out.retain(|t, _| !matches!(arena.node(*t), TermNode::IntConst(_)));
    out
}

/// Largest absolute value of an **entailed** endpoint used to build a `McCormick`
/// envelope. Every emitted lemma multiplies two endpoints, so this keeps the
/// constant term at `|aᴸ·bᴸ| ≤ 2^40` — far inside `i128`, so no lemma can
/// overflow the downstream rational arithmetic. Wider bounds are simply skipped
/// (still sound; just no envelope for that product).
const MCCORMICK_MAX_ABS_BOUND: i128 = 1 << 20;

/// Largest number of abstracted products for which `McCormick` envelopes are
/// emitted at all. Beyond this the envelope pass is skipped wholesale (sound,
/// only less complete) so the relaxation handed to the DPLL(T) stays bounded.
const MAX_MCCORMICK_PRODUCTS: usize = 8192;

/// The **`McCormick` envelope** for an abstracted product `r = a·b` under the
/// *entailed* constant bounds `a ∈ [aᴸ, aᵁ]`, `b ∈ [bᴸ, bᵁ]` (any endpoint may be
/// absent). Each of the four inequalities is the expansion of a product of two
/// non-negative quantities, so each is a **valid consequence** of the bounds it
/// uses — and therefore of the assertions those bounds were harvested from:
///
/// | source                 | needs      | lemma                              |
/// |------------------------|------------|------------------------------------|
/// | `(a−aᴸ)(b−bᴸ) ≥ 0`     | `aᴸ`, `bᴸ` | `r ≥ aᴸ·b + bᴸ·a − aᴸ·bᴸ`          |
/// | `(aᵁ−a)(bᵁ−b) ≥ 0`     | `aᵁ`, `bᵁ` | `r ≥ aᵁ·b + bᵁ·a − aᵁ·bᵁ`          |
/// | `(aᵁ−a)(b−bᴸ) ≥ 0`     | `aᵁ`, `bᴸ` | `r ≤ aᵁ·b + bᴸ·a − aᵁ·bᴸ`          |
/// | `(a−aᴸ)(bᵁ−b) ≥ 0`     | `aᴸ`, `bᵁ` | `r ≤ aᴸ·b + bᵁ·a − aᴸ·bᵁ`          |
///
/// Each row is emitted **independently**, only when both endpoints it needs are
/// present — so a `λ ≥ 0` (lower bound only) multiplied by a template
/// coefficient `c ∈ [−1, 1]` still yields the two useful rows `r ≥ −λ` and
/// `r ≤ λ`, which is exactly the Farkas/ranking shape of the `QF_NIA` residuals.
/// Every lemma is linear in `a`, `b`, `r`, so it lands in the LIA relaxation the
/// DPLL(T) already decides. Adding consequences of the relaxation's own
/// assertions cannot change its satisfiability, so the `unsat` transfer to the
/// original query is untouched.
fn mccormick_lemmas(
    arena: &mut TermArena,
    a: TermId,
    b: TermId,
    r: TermId,
    a_bounds: ConstBounds,
    b_bounds: ConstBounds,
) -> Result<Vec<TermId>, SolverError> {
    let clamp = |v: Option<i128>| v.filter(|c| c.abs() <= MCCORMICK_MAX_ABS_BOUND);
    let (a_lo, a_hi) = (clamp(a_bounds.0), clamp(a_bounds.1));
    let (b_lo, b_hi) = (clamp(b_bounds.0), clamp(b_bounds.1));
    let mut out = Vec::with_capacity(4);
    // `(coeff on b, coeff on a, r ≥ rhs?)` — see the table above.
    for &(on_b, on_a, ge) in &[
        (a_lo, b_lo, true),
        (a_hi, b_hi, true),
        (a_hi, b_lo, false),
        (a_lo, b_hi, false),
    ] {
        let (Some(on_b), Some(on_a)) = (on_b, on_a) else {
            continue;
        };
        let left = {
            let k = arena.int_const(on_b);
            arena.int_mul(k, b).map_err(err)?
        };
        let right = {
            let k = arena.int_const(on_a);
            arena.int_mul(k, a).map_err(err)?
        };
        let sum = arena.int_add(left, right).map_err(err)?;
        // In range by `MCCORMICK_MAX_ABS_BOUND` (|product| ≤ 2^40).
        let offset = arena.int_const(on_b * on_a);
        let rhs = arena.int_sub(sum, offset).map_err(err)?;
        out.push(if ge {
            arena.int_ge(r, rhs).map_err(err)?
        } else {
            arena.int_le(r, rhs).map_err(err)?
        });
    }
    Ok(out)
}

/// Widest **entailed** integer interval on a product factor for which the exact
/// case-split linearization ([`small_domain_lemmas`]) is emitted: `aᵁ − aᴸ ≤ 4`,
/// i.e. at most five cases per product.
const MAX_SMALL_DOMAIN_WIDTH: i128 = 4;

/// Largest number of products that receive the exact case split. Past this the
/// remaining products keep only their sign lemmas and envelopes — still sound,
/// just less complete — so the Boolean structure handed to the DPLL(T) is bounded.
const MAX_SMALL_DOMAIN_PRODUCTS: usize = 1024;

/// The **exact** linearization of `r = a·b` when `a` is provably confined to a
/// narrow integer interval `[lo, hi]`:
///
/// ```text
/// (a = lo ∨ … ∨ a = hi)                     -- entailed: lo ≤ a ≤ hi over ℤ
/// a = k  →  r = k·b        for each k       -- valid: a = k ∧ r = a·b ⟹ r = k·b
/// ```
///
/// Every `k·b` is a *constant* times a term, so the whole family is linear. Unlike
/// the [`mccormick_lemmas`] relaxation this is **exact** for that product — which
/// is what a Farkas/ranking system needs, because there the narrow factor is
/// typically a `0/1` template switch multiplying an *unbounded* multiplier, a
/// shape where the envelope degenerates to the sign lemmas it already has.
///
/// Both parts are consequences of the relaxation (`lo ≤ a ≤ hi` was harvested from
/// its own top-level conjuncts, and `r` is its abstraction of `a·b`), so adding
/// them cannot change its satisfiability and the `unsat` transfer is untouched.
fn small_domain_lemmas(
    arena: &mut TermArena,
    a: TermId,
    b: TermId,
    r: TermId,
    lo: i128,
    hi: i128,
) -> Result<Vec<TermId>, SolverError> {
    debug_assert!(lo <= hi && hi - lo <= MAX_SMALL_DOMAIN_WIDTH);
    let mut out = Vec::new();
    let mut cases: Option<TermId> = None;
    for k in lo..=hi {
        let k_term = arena.int_const(k);
        let a_is_k = arena.eq(a, k_term).map_err(err)?;
        let scaled = arena.int_mul(k_term, b).map_err(err)?;
        let r_is_kb = arena.eq(r, scaled).map_err(err)?;
        out.push(arena.implies(a_is_k, r_is_kb).map_err(err)?);
        cases = Some(match cases {
            None => a_is_k,
            Some(acc) => arena.or(acc, a_is_k).map_err(err)?,
        });
    }
    if let Some(cases) = cases {
        out.push(cases);
    }
    Ok(out)
}

/// The interval an abstracted product `r = a·b` is confined to, given the bounds
/// already established for `a` and `b`. Only two cases are derived, both by exact
/// integer arithmetic inside the [`MCCORMICK_MAX_ABS_BOUND`] guard:
///
///  - **both factors fully bounded** ⇒ `r` lies in the hull of the four corner
///    products;
///  - **both factors provably non-negative** ⇒ `r ≥ aᴸ·bᴸ ≥ 0` (no upper bound).
///
/// Anything else yields no bound. This propagates a narrow window UP a nested
/// product chain (`b·x·y` parses as `(b·x)·y`, so without it the outer product
/// sees a fresh, unconstrained inner variable and neither the envelope nor the
/// exact split can fire).
///
/// These bounds hold of `r` **in the intended extension** of an original model —
/// the one that sets `r := a·b` — which is exactly the standing soundness
/// contract of this relaxation (the sign lemmas rely on the same argument). Every
/// original model still extends to a model of the relaxation, so `unsat` transfers.
fn derived_product_bounds(a: ConstBounds, b: ConstBounds) -> ConstBounds {
    let guard = |v: Option<i128>| v.filter(|c| c.abs() <= MCCORMICK_MAX_ABS_BOUND);
    let (a_lo, a_hi) = (guard(a.0), guard(a.1));
    let (b_lo, b_hi) = (guard(b.0), guard(b.1));
    if let (Some(a_lo), Some(a_hi), Some(b_lo), Some(b_hi)) = (a_lo, a_hi, b_lo, b_hi) {
        // |corner| ≤ 2^40 by the guard, so the products are exact in `i128`.
        let corners = [a_lo * b_lo, a_lo * b_hi, a_hi * b_lo, a_hi * b_hi];
        let lo = corners.iter().copied().min().unwrap_or(0);
        let hi = corners.iter().copied().max().unwrap_or(0);
        return (Some(lo), Some(hi));
    }
    if let (Some(a_lo), Some(b_lo)) = (a_lo, b_lo)
        && a_lo >= 0
        && b_lo >= 0
    {
        return (Some(a_lo * b_lo), None);
    }
    (None, None)
}

/// The factor of `r = a·b` with the narrowest entailed integer domain, when one of
/// them is narrow enough for the exact case split. Returns `(narrow, other, lo,
/// hi)` — deterministic: `a` wins a tie.
fn narrow_factor(
    a: TermId,
    b: TermId,
    a_bounds: ConstBounds,
    b_bounds: ConstBounds,
) -> Option<(TermId, TermId, i128, i128)> {
    let window = |bounds: ConstBounds| match bounds {
        (Some(lo), Some(hi)) if lo <= hi && hi - lo <= MAX_SMALL_DOMAIN_WIDTH => Some((lo, hi)),
        _ => None,
    };
    match (window(a_bounds), window(b_bounds)) {
        (Some((lo, hi)), Some((other_lo, other_hi))) => {
            if hi - lo <= other_hi - other_lo {
                Some((a, b, lo, hi))
            } else {
                Some((b, a, other_lo, other_hi))
            }
        }
        (Some((lo, hi)), None) => Some((a, b, lo, hi)),
        (None, Some((lo, hi))) => Some((b, a, lo, hi)),
        (None, None) => None,
    }
}

/// The output of [`abstract_pow2`]: `(rewritten_assertions, axioms)`.
type Pow2Abstraction = (Vec<TermId>, Vec<TermId>);

/// The exact value table `⋁_{k=lo}^{hi} (x = k ∧ p = pow2(k))` for a `pow2`
/// exponent `x` provably confined to `[lo, hi]`, or `None` when the window is
/// empty, too wide, or reaches an out-of-range exponent (a partial table is never
/// emitted — it would forbid legitimate values and could refute a real model).
/// Given `lo ≤ x ≤ hi`, the returned disjunction is a genuine theorem.
fn pow2_value_table(
    arena: &mut TermArena,
    x: TermId,
    p: TermId,
    lo: i128,
    hi: i128,
) -> Result<Option<TermId>, SolverError> {
    // `hi - lo < N` ⟺ at most `N` cases; guards against an unbounded/huge table.
    if lo > hi || hi > POW2_TABLE_MAX_EXP || hi - lo >= POW2_TABLE_MAX_CASES {
        return Ok(None);
    }
    let mut table: Option<TermId> = None;
    for k in lo..=hi {
        let Some(val) = pow2_value(k) else {
            return Ok(None); // out-of-range exponent ⇒ decline the whole table
        };
        let k_const = arena.int_const(k);
        let val_const = arena.int_const(val);
        let x_is_k = arena.eq(x, k_const).map_err(err)?;
        let p_is_val = arena.eq(p, val_const).map_err(err)?;
        let case = arena.and(x_is_k, p_is_val).map_err(err)?;
        table = Some(match table {
            None => case,
            Some(acc) => arena.or(acc, case).map_err(err)?,
        });
    }
    Ok(table)
}

/// Replaces every `int.pow2(x)` subterm with a fresh `Int` variable `p` and
/// returns `(rewritten_assertions, axioms)` — or `None` when the query has no
/// `pow2` terms. Every axiom is a genuine theorem of cvc5's total semantics
/// (`pow2(x) = 2^x` for `x ≥ 0`, `pow2(x) = 0` for `x < 0`), so it only shrinks
/// the abstracted relaxation's model space and an `unsat` transfers soundly:
///
///  - **negative (defined, not underspecified):** `x < 0 ⇒ p = 0`;
///  - **positivity:** `x ≥ 0 ⇒ p ≥ 1`;
///  - **super-linear lower bound:** `x ≥ 0 ⇒ p ≥ x + 1` (i.e. `2^x ≥ x+1`);
///  - **evenness:** `x ≠ 0 ⇒ p = 2·q` for a fresh `q` (`2^x` is even for `x ≥ 1`,
///    and `p = 0` is even for `x < 0`);
///  - **strict monotonicity (pairwise):** `0 ≤ x_i ∧ x_i < x_j ⇒ p_i < p_j`;
///  - **exact value table (bounded `x`):** when the other assertions pin
///    `lo ≤ x ≤ hi` with a small enough range, the complete disjunction
///    `⋁_{k=lo}^{hi} (x = k ∧ p = pow2(k))`, which decides the value exactly.
fn abstract_pow2(
    arena: &mut TermArena,
    assertions: &[TermId],
    counter: &mut u32,
) -> Result<Option<Pow2Abstraction>, SolverError> {
    let pow2_terms = collect_pow2(arena, assertions);
    if pow2_terms.is_empty() {
        return Ok(None);
    }

    // A fresh Int variable per distinct pow2 term.
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    // (original pow2 term t, raw argument x, fresh replacement variable p).
    let mut args: Vec<(TermId, TermId, TermId)> = Vec::new();
    for &t in &pow2_terms {
        let TermNode::App { args: a, .. } = arena.node(t) else {
            continue;
        };
        let x = a[0];
        let sym = arena
            .declare_internal(&format!("!pow2_{counter}"), Sort::Int)
            .map_err(err)?;
        *counter += 1;
        let p = arena.var(sym);
        map.insert(t, p);
        args.push((t, x, p));
    }

    // Rewrite the assertions (pow2 → fresh var).
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut rewritten = Vec::with_capacity(assertions.len());
    for &a in assertions {
        rewritten.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
    }
    // Every subterm of the abstracted query, used to add the `div`/`mod`-of-pow2
    // lemmas only when the corresponding term is actually present.
    let rewritten_subterms = all_subterms(arena, &rewritten);

    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let mut axioms: Vec<TermId> = Vec::new();
    // The rewritten argument of each pow2 (a nested pow2 in `x` is abstracted too),
    // retained for the pairwise monotonicity lemmas.
    let mut rewritten_args: Vec<(TermId, TermId)> = Vec::with_capacity(args.len());

    for &(_t, x_raw, p) in &args {
        let x = replace_subterms(arena, x_raw, &map, &mut memo).map_err(err)?;
        rewritten_args.push((x, p));

        let x_ge0 = arena.int_ge(x, zero).map_err(err)?;
        let x_lt0 = arena.int_lt(x, zero).map_err(err)?;

        // x < 0 ⇒ p = 0   (cvc5 defines the negative case as exactly 0).
        let p_eq0 = arena.eq(p, zero).map_err(err)?;
        axioms.push(arena.implies(x_lt0, p_eq0).map_err(err)?);
        // x ≥ 0 ⇒ p ≥ 1.
        let p_ge1 = arena.int_ge(p, one).map_err(err)?;
        axioms.push(arena.implies(x_ge0, p_ge1).map_err(err)?);
        // x ≥ 0 ⇒ p ≥ x + 1   (2^x ≥ x + 1 for x ≥ 0).
        let x_plus1 = arena.int_add(x, one).map_err(err)?;
        let p_ge_x1 = arena.int_ge(p, x_plus1).map_err(err)?;
        axioms.push(arena.implies(x_ge0, p_ge_x1).map_err(err)?);
        // x ≠ 0 ⇒ p = 2·q   (p is even off zero; q fresh existential witness).
        let x_nonzero = {
            let x_eq0 = arena.eq(x, zero).map_err(err)?;
            arena.not(x_eq0).map_err(err)?
        };
        let q_sym = arena
            .declare_internal(&format!("!pow2_even_{counter}"), Sort::Int)
            .map_err(err)?;
        *counter += 1;
        let q = arena.var(q_sym);
        let two_q = arena.int_mul(two, q).map_err(err)?;
        let p_even = arena.eq(p, two_q).map_err(err)?;
        axioms.push(arena.implies(x_nonzero, p_even).map_err(err)?);

        // `div`/`mod` OF a `pow2` BY its own exponent: for `x ≥ 0` we have
        // `0 ≤ x < pow2(x)` (from `p ≥ x + 1`), hence the exact Euclidean facts
        // `div(x, pow2(x)) = 0` and `mod(x, pow2(x)) = x`. Both are theorems; add
        // them only when the term is present (otherwise they would introduce a new
        // variable-divisor `div`/`mod` for nothing). The abstracted divisor is `p`.
        let div_xp = arena.int_div(x, p).map_err(err)?;
        if rewritten_subterms.contains(&div_xp) {
            let div_eq0 = arena.eq(div_xp, zero).map_err(err)?;
            axioms.push(arena.implies(x_ge0, div_eq0).map_err(err)?);
        }
        let mod_xp = arena.int_mod(x, p).map_err(err)?;
        if rewritten_subterms.contains(&mod_xp) {
            let mod_eq_x = arena.eq(mod_xp, x).map_err(err)?;
            axioms.push(arena.implies(x_ge0, mod_eq_x).map_err(err)?);
        }

        // Exact value table when `x` is pinned to a small constant window.
        let (lo, hi) = const_bounds_of_term(arena, assertions, x_raw);
        if let (Some(lo), Some(hi)) = (lo, hi)
            && let Some(table) = pow2_value_table(arena, x, p, lo, hi)?
        {
            axioms.push(table);
        }
    }

    // Pairwise strict monotonicity: 0 ≤ x_i ∧ x_i < x_j ⇒ p_i < p_j (both orders).
    for i in 0..rewritten_args.len() {
        for j in (i + 1)..rewritten_args.len() {
            let (xi, pi) = rewritten_args[i];
            let (xj, pj) = rewritten_args[j];
            for &((xa, pa), (xb, pb)) in &[((xi, pi), (xj, pj)), ((xj, pj), (xi, pi))] {
                let xa_ge0 = arena.int_ge(xa, zero).map_err(err)?;
                let xa_lt_xb = arena.int_lt(xa, xb).map_err(err)?;
                let hyp = arena.and(xa_ge0, xa_lt_xb).map_err(err)?;
                let concl = arena.int_lt(pa, pb).map_err(err)?;
                axioms.push(arena.implies(hyp, concl).map_err(err)?);
            }
        }
    }

    Ok(Some((rewritten, axioms)))
}

/// Emits the entailed-bound lemma families for every abstracted product and
/// appends them to `relaxed`. Returns `(mccormick_lemmas, split_lemmas)` — the
/// counts are the signal for whether this query has linearization structure worth
/// spending budget on.
///
/// Soundness: the bounds come from [`harvest_const_bounds`] (top-level `and` only,
/// so each is a consequence of `relaxed`) and from [`derived_product_bounds`]
/// (which holds of the intended extension `r := a·b`). Every emitted lemma is a
/// consequence of those, so every original model still extends to a model of the
/// enlarged relaxation and the `unsat` transfer is untouched.
fn add_entailed_bound_lemmas(
    arena: &mut TermArena,
    triples: &[(TermId, TermId, TermId)],
    relaxed: &mut Vec<TermId>,
) -> Result<(usize, usize), SolverError> {
    if triples.is_empty() || triples.len() > MAX_MCCORMICK_PRODUCTS {
        return Ok((0, 0));
    }
    let mut bounds = harvest_const_bounds(arena, relaxed);
    let mut lemmas_out: Vec<TermId> = Vec::new();
    let (mut mccormick, mut splits, mut split_products) = (0usize, 0usize, 0usize);
    // Ascending `TermId` order: hash-consing builds an inner product before the
    // outer one that contains it, and the fresh abstraction variables are declared
    // in the same order, so a chain's inner bound is always derived before the
    // outer product that needs it.
    for &(a, b, r) in triples {
        let a_bounds = bounds.get(&a).copied().unwrap_or((None, None));
        let b_bounds = bounds.get(&b).copied().unwrap_or((None, None));
        // Propagate the product's own interval up the chain before deciding what to
        // emit for it (an endpoint already recorded for `r` wins — it came from the
        // assertions themselves).
        let derived = derived_product_bounds(a_bounds, b_bounds);
        if derived != (None, None) {
            let entry = bounds.entry(r).or_insert((None, None));
            if let Some(lo) = derived.0 {
                entry.0 = Some(entry.0.map_or(lo, |c: i128| c.max(lo)));
            }
            if let Some(hi) = derived.1 {
                entry.1 = Some(entry.1.map_or(hi, |c: i128| c.min(hi)));
            }
        }
        if a_bounds == (None, None) && b_bounds == (None, None) {
            continue; // no entailed endpoint at all ⇒ nothing valid to add
        }
        // The exact case split first — it subsumes the envelope for that product.
        if split_products < MAX_SMALL_DOMAIN_PRODUCTS
            && let Some((narrow, other, lo, hi)) = narrow_factor(a, b, a_bounds, b_bounds)
        {
            let lemmas = small_domain_lemmas(arena, narrow, other, r, lo, hi)?;
            splits += lemmas.len();
            split_products += 1;
            lemmas_out.extend(lemmas);
            continue;
        }
        if a_bounds == (None, None) || b_bounds == (None, None) {
            continue; // no entailed endpoint on one side ⇒ no valid envelope
        }
        let lemmas = mccormick_lemmas(arena, a, b, r, a_bounds, b_bounds)?;
        mccormick += lemmas.len();
        lemmas_out.extend(lemmas);
    }
    relaxed.extend(lemmas_out);
    Ok((mccormick, splits))
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
/// Denominator of the remaining query budget granted to the relaxation solve on a
/// product-bearing query whose entailed bounds actually produced `McCormick`
/// envelopes (a third). See [`NIA_SLICE_MS`] for why the default slice is tiny.
const NIA_MCCORMICK_BUDGET_SHARE: u32 = 3;

/// `why` is a **write-only** telemetry channel recording the decline reason for the
/// route trace; without it this route declined silently, which is precisely why an
/// unrefuted nonlinear-integer query used to leave no trace of the cause. The
/// verdict never depends on it.
pub(crate) fn check_with_nia(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    why: &mut Option<DeclineReason>,
) -> Result<Option<CheckResult>, SolverError> {
    let mut counter = 0u32;
    // 0. Abstract `int.pow2` terms to fresh integer variables + theory-valid
    //    axioms, BEFORE div/mod elimination so a `div`/`mod` whose divisor is a
    //    `pow2` term (e.g. `(div x (int.pow2 x))`) still linearizes through the
    //    variable-divisor Euclidean route below. Every axiom is a genuine theorem
    //    of cvc5's total semantics, so an `unsat` of the abstracted query
    //    transfers; a `sat` is (as always) accepted only after replaying the
    //    ORIGINAL assertions — with `int.pow2` intact — under the ground
    //    evaluator, so a mis-abstraction can never yield a wrong `sat`.
    let pow2_abstraction = abstract_pow2(arena, assertions, &mut counter)?;
    let had_pow2 = pow2_abstraction.is_some();
    let base: Vec<TermId> = match &pow2_abstraction {
        Some((rewritten, axioms)) => {
            let mut v = axioms.clone();
            v.extend_from_slice(rewritten);
            v
        }
        None => assertions.to_vec(),
    };

    // 1. Eliminate constant-divisor div/mod + abs exactly (equisatisfiable).
    let lin = axeyum_rewrite::eliminate_int_divmod(arena, &base).map_err(err)?;
    // 2. Eliminate variable-divisor div/mod (guarded Euclidean + self-division).
    let after_divmod = eliminate_variable_divmod(arena, &lin, &mut counter)?;
    let had_var_divmod = after_divmod.is_some();
    let working = after_divmod.unwrap_or(lin);

    // 3. Abstract integer products and add their valid lemmas.
    let products = int_products(arena, &working);
    if products.is_empty() && !had_var_divmod && !had_pow2 {
        // Nothing nonlinear to exploit — a pure-linear query the LIA path already
        // owns; decline rather than re-solve it.
        *why = Some(DeclineReason::NotApplicable);
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
            .declare_internal(&format!("!nia_{i}"), Sort::Int)
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
    // The abstracted operand pair per product, retained for the McCormick pass.
    let mut rewritten_triples: Vec<(TermId, TermId, TermId)> = Vec::with_capacity(triples.len());
    for &(a, b, r) in &triples {
        let a = replace_subterms(arena, a, &map, &mut memo).map_err(err)?;
        let b = replace_subterms(arena, b, &map, &mut memo).map_err(err)?;
        relaxed.extend(sign_lemmas(arena, a, b, r, zero)?);
        rewritten_triples.push((a, b, r));
    }

    // 3b. **McCormick envelopes.** The sign lemmas alone only fix the *quadrant*
    //     of each abstracted product; they say nothing about its magnitude, so a
    //     Farkas/ranking-function system (`λ ≥ 0` multipliers times template
    //     coefficients pinned into a narrow interval) relaxes to a system with a
    //     free variable per product and is trivially satisfiable. Harvesting the
    //     bounds the relaxation ITSELF entails and adding the four linear
    //     McCormick inequalities per product ties `r` back to `a` and `b`.
    //
    //     Soundness: the bounds come from [`harvest_const_bounds`], which walks
    //     only through top-level `and`, so each is a consequence of `relaxed`;
    //     each envelope row is in turn a consequence of the bounds it uses. A
    //     formula's own consequences cannot change its satisfiability, so `relaxed
    //     ∧ envelopes` is unsat exactly when `relaxed` is — the existing `unsat`
    //     transfer to the original query is untouched, and `sat` still only ever
    //     returns after the ground-evaluator replay below.
    //
    //     A one-sided bound on both factors (`a ≥ 0 ∧ b ≥ 0`, the common Farkas
    //     multiplier shape) makes the envelope degenerate to `r ≥ 0`, which the
    //     sign lemmas already give. The lever for those is [`small_domain_lemmas`]:
    //     when one factor is pinned to a NARROW integer window (the `0/1` template
    //     switches these benchmarks assert explicitly), the product linearizes
    //     EXACTLY by a case split, no relaxation involved.
    let (mccormick, splits) = add_entailed_bound_lemmas(arena, &rewritten_triples, &mut relaxed)?;
    if std::env::var_os("AXEYUM_NIA_DEBUG").is_some() {
        eprintln!(
            "[nia] products={} mccormick={} splits={} relaxed={} timeout={:?}",
            rewritten_triples.len(),
            mccormick,
            splits,
            relaxed.len(),
            config.timeout
        );
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
    //
    //    When the entailed bounds actually produced McCormick envelopes the
    //    relaxation is no longer a long-shot: it is a genuine linear refutation
    //    route for the Farkas/ranking shapes the width ladder structurally cannot
    //    answer, and 600 ms is far too short for a system with thousands of
    //    products. Grant it a SHARE of the caller's REMAINING budget in that case
    //    (never more than the caller allows), and keep the tiny default slice
    //    everywhere else so the ladder is never starved.
    let capped = {
        let base = std::time::Duration::from_millis(NIA_SLICE_MS);
        let slice = match (mccormick + splits > 0, config.timeout) {
            (true, Some(total)) => base.max(total / NIA_MCCORMICK_BUDGET_SHARE),
            _ => base,
        };
        let bound = config.timeout.map_or(slice, |t| t.min(slice));
        config.clone().with_timeout(bound)
    };
    //
    // 5. **Refinement loop (incremental linearization).** A one-shot relaxation is
    //    hopeless on a Farkas/ranking system: the products whose factors are only
    //    bounded below relax to free variables, so the linear engine reports `sat`
    //    on a model that does not satisfy `r = a·b`, the replay rejects it, and the
    //    whole pass declines with budget to spare. Instead, when the model is
    //    spurious, CUT IT OFF with valid linear lemmas at that point
    //    ([`tangent_lemmas`]) and re-solve, until the slice or the round cap runs
    //    out. Every added lemma holds of the intended extension `r := a·b`, so an
    //    `unsat` at any round still transfers, and a `sat` is still only ever
    //    accepted after replay against the ORIGINAL assertions.
    solve_with_refinement(
        arena,
        assertions,
        &relaxed,
        &rewritten_triples,
        &capped,
        mccormick + splits > 0,
        why,
    )
}

/// Runs the relaxation solve under `capped`, refining with tangent planes whenever
/// the model is spurious. `refine` is the "this query has entailed-bound structure"
/// signal; without it the loop is a pure budget tax (see the call site).
///
/// # Errors
///
/// Propagates term-construction failures; a solver error is a decline, not an error.
fn solve_with_refinement(
    arena: &mut TermArena,
    assertions: &[TermId],
    base: &[TermId],
    triples: &[(TermId, TermId, TermId)],
    capped: &SolverConfig,
    refine: bool,
    why: &mut Option<DeclineReason>,
) -> Result<Option<CheckResult>, SolverError> {
    let mut relaxed = base.to_vec();
    let slice_deadline = std::time::Instant::now() + capped.timeout.unwrap_or_default();
    let debug = std::env::var_os("AXEYUM_NIA_DEBUG").is_some();
    let mut emitted: BTreeSet<TermId> = relaxed.iter().copied().collect();
    let mut round = 0usize;
    loop {
        let remaining = slice_deadline.checked_duration_since(std::time::Instant::now());
        let Some(remaining) = remaining.filter(|d| !d.is_zero()) else {
            *why = Some(DeclineReason::Budget(
                "nia relaxation slice expired during refinement".into(),
            ));
            return Ok(None);
        };
        let round_config = capped.clone().with_timeout(remaining);
        let outcome = check_with_lia_dpll(arena, &relaxed, &round_config);
        if debug {
            eprintln!(
                "[nia] round {round}: {:?} (relaxed={}, {remaining:?} left)",
                outcome.as_ref().map(|r| match r {
                    CheckResult::Sat(_) => "sat",
                    CheckResult::Unsat => "unsat",
                    CheckResult::Unknown(_) => "unknown",
                }),
                relaxed.len(),
            );
        }
        match outcome {
            Ok(CheckResult::Unsat) => return Ok(Some(CheckResult::Unsat)),
            Ok(CheckResult::Sat(model)) => {
                if let Some(sat) = replay_sat(arena, assertions, &model) {
                    return Ok(Some(sat));
                }
                if !refine {
                    *why = Some(DeclineReason::VerifierRejected(
                        "relaxation model failed ground-evaluator replay against the originals"
                            .into(),
                    ));
                    return Ok(None);
                }
                if round >= MAX_REFINEMENT_ROUNDS {
                    *why = Some(DeclineReason::Budget(
                        "nia refinement round cap reached with a spurious relaxation model".into(),
                    ));
                    return Ok(None);
                }
                let added =
                    refine_with_tangents(arena, triples, &model, &mut emitted, &mut relaxed)?;
                if debug {
                    eprintln!("[nia] round {round}: refined with {added} tangent lemmas");
                }
                if added == 0 {
                    // Nothing new to cut off — the loop cannot make progress.
                    *why = Some(DeclineReason::VerifierRejected(
                        "relaxation model failed replay and no new refinement lemma applies".into(),
                    ));
                    return Ok(None);
                }
                round += 1;
            }
            Ok(CheckResult::Unknown(reason)) => {
                *why = Some(DeclineReason::from_unknown(&reason));
                return Ok(None);
            }
            Err(e) => {
                *why = Some(DeclineReason::Incomplete(crate::backend::UnknownReason {
                    kind: crate::backend::UnknownKind::Other,
                    detail: format!("nia relaxation solve failed: {e}"),
                }));
                return Ok(None);
            }
        }
    }
}

/// Largest number of refinement rounds. Each round adds lemmas, so the relaxation
/// grows; the wall-clock slice is the real bound and this only stops a pathological
/// spin on a tiny formula.
const MAX_REFINEMENT_ROUNDS: usize = 64;

/// Largest number of products refined in ONE round (deterministic order), so a
/// query with thousands of products cannot add thousands of lemmas per round.
const MAX_REFINED_PER_ROUND: usize = 64;

/// Largest absolute factor value at which a tangent lemma is built. Keeps
/// `a_val · b_val` exact in `i128` and the emitted coefficients sane.
const MAX_TANGENT_ABS_VALUE: i128 = 1 << 40;

/// The integer value of `term` under `assignment`, or `None` when it does not
/// ground-evaluate to an integer.
fn int_value(arena: &TermArena, term: TermId, assignment: &axeyum_ir::Assignment) -> Option<i128> {
    match eval(arena, term, assignment) {
        Ok(Value::Int(v)) => Some(v),
        _ => None,
    }
}

/// The **tangent-plane** lemmas for `r = a·b` at the point `(a_val, b_val)`.
///
/// With `p = a_val·b_val`, the expansion of `(a − a_val)·(b − b_val)` equals
/// `r − a_val·b − b_val·a + p`, whose sign is determined by the signs of the two
/// differences. That gives four linear consequences, each valid **unconditionally**
/// of the intended extension `r := a·b`:
///
/// ```text
/// a ≥ a_val ∧ b ≥ b_val  →  r ≥ a_val·b + b_val·a − p
/// a ≤ a_val ∧ b ≤ b_val  →  r ≥ a_val·b + b_val·a − p
/// a ≥ a_val ∧ b ≤ b_val  →  r ≤ a_val·b + b_val·a − p
/// a ≤ a_val ∧ b ≥ b_val  →  r ≤ a_val·b + b_val·a − p
/// ```
///
/// Together they pin `r` exactly at the point (`a = a_val ∧ b = b_val ⇒ r = p`),
/// so a spurious model with `r ≠ a_val·b_val` is always cut off, while every real
/// model survives. This is the standard incremental-linearization refinement.
fn tangent_lemmas(
    arena: &mut TermArena,
    a: TermId,
    b: TermId,
    r: TermId,
    a_val: i128,
    b_val: i128,
) -> Result<Vec<TermId>, SolverError> {
    let a_const = arena.int_const(a_val);
    let b_const = arena.int_const(b_val);
    // rhs = a_val·b + b_val·a − a_val·b_val  (exact: |values| ≤ 2^40).
    let left = arena.int_mul(a_const, b).map_err(err)?;
    let right = arena.int_mul(b_const, a).map_err(err)?;
    let sum = arena.int_add(left, right).map_err(err)?;
    let offset = arena.int_const(a_val * b_val);
    let rhs = arena.int_sub(sum, offset).map_err(err)?;

    let above_a = arena.int_ge(a, a_const).map_err(err)?;
    let below_a = arena.int_le(a, a_const).map_err(err)?;
    let above_b = arena.int_ge(b, b_const).map_err(err)?;
    let below_b = arena.int_le(b, b_const).map_err(err)?;
    let over = arena.int_ge(r, rhs).map_err(err)?;
    let under = arena.int_le(r, rhs).map_err(err)?;

    let mut out = Vec::with_capacity(4);
    for &(first, second, concl) in &[
        (above_a, above_b, over),
        (below_a, below_b, over),
        (above_a, below_b, under),
        (below_a, above_b, under),
    ] {
        let hyp = arena.and(first, second).map_err(err)?;
        out.push(arena.implies(hyp, concl).map_err(err)?);
    }
    Ok(out)
}

/// Adds tangent lemmas at the spurious model's point for every abstracted product
/// the model gets WRONG (`r ≠ a·b`), skipping lemmas already present. Returns how
/// many genuinely new lemmas were appended; `0` means the loop cannot progress.
fn refine_with_tangents(
    arena: &mut TermArena,
    triples: &[(TermId, TermId, TermId)],
    model: &Model,
    emitted: &mut BTreeSet<TermId>,
    relaxed: &mut Vec<TermId>,
) -> Result<usize, SolverError> {
    let assignment = model.to_assignment();
    let mut added = 0usize;
    let mut refined = 0usize;
    for &(a, b, r) in triples {
        if refined >= MAX_REFINED_PER_ROUND {
            break;
        }
        let (Some(a_val), Some(b_val), Some(r_val)) = (
            int_value(arena, a, &assignment),
            int_value(arena, b, &assignment),
            int_value(arena, r, &assignment),
        ) else {
            continue;
        };
        if a_val.abs() > MAX_TANGENT_ABS_VALUE || b_val.abs() > MAX_TANGENT_ABS_VALUE {
            continue;
        }
        // Exact by the magnitude guard (|a_val·b_val| ≤ 2^80).
        if a_val * b_val == r_val {
            continue; // this product is already faithful in the model
        }
        refined += 1;
        for lemma in tangent_lemmas(arena, a, b, r, a_val, b_val)? {
            if emitted.insert(lemma) {
                relaxed.push(lemma);
                added += 1;
            }
        }
    }
    Ok(added)
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

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Assignment;

    /// Builds `a`, `b`, `r` as three fresh `Int` variables over a fresh arena.
    fn triple() -> (
        TermArena,
        SymbolId,
        SymbolId,
        SymbolId,
        TermId,
        TermId,
        TermId,
    ) {
        let mut arena = TermArena::new();
        let sa = arena.declare("a", Sort::Int).unwrap();
        let sb = arena.declare("b", Sort::Int).unwrap();
        let sr = arena.declare("r", Sort::Int).unwrap();
        let (a, b, r) = (arena.var(sa), arena.var(sb), arena.var(sr));
        (arena, sa, sb, sr, a, b, r)
    }

    fn holds(arena: &TermArena, lemma: TermId, assignment: &Assignment) -> bool {
        matches!(eval(arena, lemma, assignment), Ok(Value::Bool(true)))
    }

    fn point(sa: SymbolId, sb: SymbolId, sr: SymbolId, av: i128, bv: i128, rv: i128) -> Assignment {
        let mut assignment = Assignment::new();
        assignment.set(sa, Value::Int(av));
        assignment.set(sb, Value::Int(bv));
        assignment.set(sr, Value::Int(rv));
        assignment
    }

    /// **Soundness.** Every `McCormick` row must hold at EVERY integer point of the
    /// declared box with `r = a·b` — including the degenerate corners (a factor
    /// pinned at zero, a factor sitting exactly on its bound). A row that failed
    /// anywhere would be a lemma that can refute a real model, i.e. a wrong-unsat
    /// generator.
    #[test]
    fn mccormick_rows_hold_at_every_faithful_point_of_the_box() {
        for &(a_lo, a_hi) in &[(0_i128, 1_i128), (-1, 1), (0, 0), (-3, 4), (2, 2)] {
            for &(b_lo, b_hi) in &[(0_i128, 1_i128), (-1, 1), (0, 0), (-5, 2)] {
                let (mut arena, sa, sb, sr, a, b, r) = triple();
                let lemmas = mccormick_lemmas(
                    &mut arena,
                    a,
                    b,
                    r,
                    (Some(a_lo), Some(a_hi)),
                    (Some(b_lo), Some(b_hi)),
                )
                .unwrap();
                assert_eq!(lemmas.len(), 4, "a fully bounded box emits all four rows");
                for av in a_lo..=a_hi {
                    for bv in b_lo..=b_hi {
                        let assignment = point(sa, sb, sr, av, bv, av * bv);
                        for &lemma in &lemmas {
                            assert!(
                                holds(&arena, lemma, &assignment),
                                "McCormick row false at a={av}, b={bv}, r={} for \
                                 a∈[{a_lo},{a_hi}], b∈[{b_lo},{b_hi}]",
                                av * bv
                            );
                        }
                    }
                }
            }
        }
    }

    /// A one-sided bound on each factor still yields only VALID rows (and, for the
    /// `λ ≥ 0` × `c ∈ [−1,1]` Farkas shape, the two useful ones `−λ ≤ r ≤ λ`).
    #[test]
    fn mccormick_emits_only_the_rows_whose_endpoints_exist() {
        let (mut arena, sa, sb, sr, a, b, r) = triple();
        // a ≥ 0 (no upper), b ∈ [−1, 1].
        let lemmas =
            mccormick_lemmas(&mut arena, a, b, r, (Some(0), None), (Some(-1), Some(1))).unwrap();
        assert_eq!(
            lemmas.len(),
            2,
            "only the two rows needing aᴸ are available"
        );
        for av in 0..=6_i128 {
            for bv in -1..=1_i128 {
                let assignment = point(sa, sb, sr, av, bv, av * bv);
                for &lemma in &lemmas {
                    assert!(holds(&arena, lemma, &assignment), "row false at {av},{bv}");
                }
            }
        }
        // The rows do bite: r = λ + 1 with b = 1 violates `r ≤ λ`.
        let spurious = point(sa, sb, sr, 3, 1, 4);
        assert!(
            lemmas.iter().any(|&l| !holds(&arena, l, &spurious)),
            "a magnitude-violating point must be cut off"
        );
    }

    /// **Soundness + exactness** of the narrow-domain case split, degenerate cases
    /// included: a factor pinned to the single value `0` (so the product is `0·b`,
    /// the underspecified-looking corner where a wrong constant would be fatal),
    /// and a factor at each end of its window.
    #[test]
    fn small_domain_split_is_exact_including_the_pinned_zero_factor() {
        for &(lo, hi) in &[(0_i128, 0_i128), (0, 1), (-1, 1), (-2, 2), (3, 3)] {
            let (mut arena, sa, sb, sr, a, b, r) = triple();
            let lemmas = small_domain_lemmas(&mut arena, a, b, r, lo, hi).unwrap();
            for av in lo..=hi {
                for bv in -4..=4_i128 {
                    // Faithful point: every lemma holds.
                    let faithful = point(sa, sb, sr, av, bv, av * bv);
                    for &lemma in &lemmas {
                        assert!(
                            holds(&arena, lemma, &faithful),
                            "split lemma false at a={av}, b={bv} for [{lo},{hi}]"
                        );
                    }
                    // Spurious point: `r` off by one is always cut off (exactness).
                    let spurious = point(sa, sb, sr, av, bv, av * bv + 1);
                    assert!(
                        lemmas.iter().any(|&l| !holds(&arena, l, &spurious)),
                        "split failed to cut r = a·b + 1 at a={av}, b={bv}"
                    );
                }
            }
            // The completeness clause forbids `a` outside its entailed window.
            let outside = point(sa, sb, sr, hi + 1, 2, (hi + 1) * 2);
            assert!(
                lemmas.iter().any(|&l| !holds(&arena, l, &outside)),
                "the case clause must exclude a = {} for [{lo},{hi}]",
                hi + 1
            );
        }
    }

    /// **Soundness + cutting power** of the tangent planes: valid everywhere on the
    /// faithful surface `r = a·b`, and guaranteed to cut off the spurious point they
    /// were built at — including the degenerate point `a = 0` (`0·b`), where the
    /// plane degenerates to `r = 0·b + b_val·a − 0`.
    #[test]
    fn tangent_planes_are_valid_and_cut_the_point_they_are_built_at() {
        for &(a_val, b_val) in &[(0_i128, 0_i128), (0, 5), (5, 0), (1, 1), (-2, 3), (4, -4)] {
            let (mut arena, sa, sb, sr, a, b, r) = triple();
            let lemmas = tangent_lemmas(&mut arena, a, b, r, a_val, b_val).unwrap();
            assert_eq!(lemmas.len(), 4);
            for av in -6..=6_i128 {
                for bv in -6..=6_i128 {
                    let faithful = point(sa, sb, sr, av, bv, av * bv);
                    for &lemma in &lemmas {
                        assert!(
                            holds(&arena, lemma, &faithful),
                            "tangent at ({a_val},{b_val}) false at faithful ({av},{bv})"
                        );
                    }
                }
            }
            for delta in [-3_i128, -1, 1, 3] {
                let spurious = point(sa, sb, sr, a_val, b_val, a_val * b_val + delta);
                assert!(
                    lemmas.iter().any(|&l| !holds(&arena, l, &spurious)),
                    "tangent at ({a_val},{b_val}) failed to cut r = {} + {delta}",
                    a_val * b_val
                );
            }
        }
    }

    /// The derived interval for `r = a·b` must contain `a·b` at every point of the
    /// factors' boxes — the bound is fed back into the map and used to build further
    /// lemmas, so an over-tight one would be a wrong-unsat generator.
    #[test]
    fn derived_product_bounds_contain_every_corner() {
        let boxes = [
            (Some(0_i128), Some(1_i128)),
            (Some(-1), Some(1)),
            (Some(-3), Some(4)),
            (Some(0), None),
            (Some(2), None),
            (None, Some(5)),
            (None, None),
        ];
        for &a_bounds in &boxes {
            for &b_bounds in &boxes {
                let (lo, hi) = derived_product_bounds(a_bounds, b_bounds);
                for av in a_bounds.0.unwrap_or(-6)..=a_bounds.1.unwrap_or(6) {
                    for bv in b_bounds.0.unwrap_or(-6)..=b_bounds.1.unwrap_or(6) {
                        let p = av * bv;
                        assert!(lo.is_none_or(|l| l <= p), "derived lo {lo:?} > {av}·{bv}");
                        assert!(hi.is_none_or(|h| h >= p), "derived hi {hi:?} < {av}·{bv}");
                    }
                }
            }
        }
    }

    /// Bounds are harvested ONLY through top-level `and` — never from a disjunct or
    /// a negation, whose atoms are not implied. A leak there would let a
    /// non-entailed bound build a lemma that refutes a real model.
    #[test]
    fn harvest_ignores_bounds_under_or_and_not() {
        let mut arena = TermArena::new();
        let sx = arena.declare("x", Sort::Int).unwrap();
        let sy = arena.declare("y", Sort::Int).unwrap();
        let (x, y) = (arena.var(sx), arena.var(sy));
        let zero = arena.int_const(0);
        let one = arena.int_const(1);

        let x_low = arena.int_ge(x, zero).unwrap();
        let x_high = arena.int_le(x, one).unwrap();
        let entailed = arena.and(x_low, x_high).unwrap();
        let y_low = arena.int_ge(y, zero).unwrap();
        let y_high = arena.int_le(y, one).unwrap();
        let disjoined = arena.or(y_low, y_high).unwrap();
        let negated = arena.not(y_low).unwrap();

        let bounds = harvest_const_bounds(&arena, &[entailed, disjoined, negated]);
        assert_eq!(bounds.get(&x).copied(), Some((Some(0), Some(1))));
        assert_eq!(
            bounds.get(&y).copied(),
            None,
            "no bound may leak from ∨ / ¬"
        );
    }

    /// An `unsat` produced through the new lemma families must be a REAL `unsat`.
    /// `0 ≤ s ≤ 1 ∧ 0 ≤ t ≤ 1 ∧ s·t ≥ 1 ∧ s + t ≤ 1` is unsatisfiable over ℤ
    /// (`s·t ≥ 1` forces `s = t = 1`, contradicting `s + t ≤ 1`) and is decided by
    /// the exact case split.
    #[test]
    fn narrow_domain_product_system_is_refuted() {
        let mut arena = TermArena::new();
        let ss = arena.declare("s", Sort::Int).unwrap();
        let st = arena.declare("t", Sort::Int).unwrap();
        let (s, t) = (arena.var(ss), arena.var(st));
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let product = arena.int_mul(s, t).unwrap();
        let sum = arena.int_add(s, t).unwrap();
        let assertions = vec![
            arena.int_ge(s, zero).unwrap(),
            arena.int_le(s, one).unwrap(),
            arena.int_ge(t, zero).unwrap(),
            arena.int_le(t, one).unwrap(),
            arena.int_ge(product, one).unwrap(),
            arena.int_le(sum, one).unwrap(),
        ];
        let config = SolverConfig::default().with_timeout(std::time::Duration::from_secs(5));
        let mut why = None;
        let verdict = check_with_nia(&mut arena, &assertions, &config, &mut why).unwrap();
        assert!(
            matches!(verdict, Some(CheckResult::Unsat)),
            "expected unsat, got {verdict:?} (decline reason {why:?})"
        );
    }

    /// The mirror-image negative: the SAME shape with `s + t ≤ 2` is satisfiable
    /// (`s = t = 1`), and the pass must never report `unsat` for it. A lemma family
    /// that over-constrained would fail here, not in a corpus sweep.
    #[test]
    fn narrow_domain_product_system_stays_satisfiable() {
        let mut arena = TermArena::new();
        let ss = arena.declare("s", Sort::Int).unwrap();
        let st = arena.declare("t", Sort::Int).unwrap();
        let (s, t) = (arena.var(ss), arena.var(st));
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let two = arena.int_const(2);
        let product = arena.int_mul(s, t).unwrap();
        let sum = arena.int_add(s, t).unwrap();
        let assertions = vec![
            arena.int_ge(s, zero).unwrap(),
            arena.int_le(s, one).unwrap(),
            arena.int_ge(t, zero).unwrap(),
            arena.int_le(t, one).unwrap(),
            arena.int_ge(product, one).unwrap(),
            arena.int_le(sum, two).unwrap(),
        ];
        let config = SolverConfig::default().with_timeout(std::time::Duration::from_secs(5));
        let mut why = None;
        let verdict = check_with_nia(&mut arena, &assertions, &config, &mut why).unwrap();
        assert!(
            !matches!(verdict, Some(CheckResult::Unsat)),
            "a satisfiable narrow-domain system must never be refuted"
        );
        if let Some(CheckResult::Sat(model)) = verdict {
            let assignment = model.to_assignment();
            for &a in &assertions {
                assert!(
                    matches!(eval(&arena, a, &assignment), Ok(Value::Bool(true))),
                    "a returned sat model must replay against the originals"
                );
            }
        }
    }

    /// Degenerate product `0 · b`: a constant-zero factor must not be turned into a
    /// bogus refutation. `x = 0 ∧ x·y ≥ 1` is unsat (correctly), while `x = 0 ∧
    /// x·y = 0 ∧ y ≥ 7` is satisfiable and must not be refuted.
    #[test]
    fn degenerate_zero_factor_products() {
        for &(rhs, expect_unsat) in &[(1_i128, true), (0, false)] {
            let mut arena = TermArena::new();
            let sx = arena.declare("x", Sort::Int).unwrap();
            let sy = arena.declare("y", Sort::Int).unwrap();
            let (x, y) = (arena.var(sx), arena.var(sy));
            let zero = arena.int_const(0);
            let seven = arena.int_const(7);
            let rhs_term = arena.int_const(rhs);
            let product = arena.int_mul(x, y).unwrap();
            let assertions = vec![
                arena.eq(x, zero).unwrap(),
                arena.int_ge(product, rhs_term).unwrap(),
                arena.int_ge(y, seven).unwrap(),
            ];
            let config = SolverConfig::default().with_timeout(std::time::Duration::from_secs(5));
            let mut why = None;
            let verdict = check_with_nia(&mut arena, &assertions, &config, &mut why).unwrap();
            if expect_unsat {
                assert!(
                    matches!(verdict, Some(CheckResult::Unsat)),
                    "x = 0 ∧ x·y ≥ 1 is unsat, got {verdict:?}"
                );
            } else {
                assert!(
                    !matches!(verdict, Some(CheckResult::Unsat)),
                    "x = 0 ∧ x·y ≥ 0 ∧ y ≥ 7 is satisfiable and must not be refuted"
                );
            }
        }
    }
}
