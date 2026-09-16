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
use crate::lazy_smt_counters::{LazySmtLoop, RoundOutcome};
use crate::model::Model;
use crate::route_trace::{Budget, DeclineReason, VerifierRejected};

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
    // ADR-1762. This gate is the registry's worked example of a bound that
    // changes behaviour with NO branch and NO signal: the `if` below has no
    // `else`, so above the cap the congruence lemmas are simply never emitted
    // and nothing downstream can tell. Recording the consultation does not add
    // the missing signal — the verdict is byte-identical either way, and the
    // `sat` side stays guarded by `replay_sat` against the ORIGINAL assertions
    // — but it does make the mode visible under `--trace`, where before it was
    // visible nowhere. Off by default: one thread-local `Cell<bool>` read.
    crate::config_registry::note_consulted(
        "crates/axeyum-solver/src/nia_linearize.rs::MAX_CONGRUENCE_GROUPS",
    );
    if infos.len() > MAX_CONGRUENCE_GROUPS {
        // The `else` this gate never had. The verdict is unchanged either way;
        // what changes is that a `--trace` run can now say the lemmas were
        // forgone, and at what group count.
        crate::config_registry::note_crossed(
            "crates/axeyum-solver/src/nia_linearize.rs::MAX_CONGRUENCE_GROUPS",
            infos.len() as u64,
            MAX_CONGRUENCE_GROUPS as u64,
        );
    }
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

/// Drops an endpoint whose magnitude is outside [`MCCORMICK_MAX_ABS_BOUND`],
/// recording the crossing.
///
/// One function rather than the two byte-identical closures this replaced, in
/// `mccormick_lemmas` and `derived_product_bounds`. The predicate is unchanged;
/// what is new is that dropping an endpoint is now visible under `--trace`,
/// where before an endpoint discarded for magnitude and an endpoint that was
/// never entailed produced the same `None`.
fn clamp_to_mccormick_bound(v: Option<i128>) -> Option<i128> {
    let c = v?;
    if c.abs() <= MCCORMICK_MAX_ABS_BOUND {
        return Some(c);
    }
    crate::config_registry::note_crossed(
        "crates/axeyum-solver/src/nia_linearize.rs::MCCORMICK_MAX_ABS_BOUND",
        u64::try_from(c.unsigned_abs()).unwrap_or(u64::MAX),
        u64::try_from(MCCORMICK_MAX_ABS_BOUND).unwrap_or(u64::MAX),
    );
    None
}

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
    let (a_lo, a_hi) = (
        clamp_to_mccormick_bound(a_bounds.0),
        clamp_to_mccormick_bound(a_bounds.1),
    );
    let (b_lo, b_hi) = (
        clamp_to_mccormick_bound(b_bounds.0),
        clamp_to_mccormick_bound(b_bounds.1),
    );
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
    let (a_lo, a_hi) = (clamp_to_mccormick_bound(a.0), clamp_to_mccormick_bound(a.1));
    let (b_lo, b_hi) = (clamp_to_mccormick_bound(b.0), clamp_to_mccormick_bound(b.1));
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
        // A factor that HAS an entailed interval and is merely too wide for the
        // exact split. Reported in the constant's own unit (interval width);
        // a factor with no interval at all is not a crossing and is not
        // recorded, which is what keeps the count meaningful.
        (Some(lo), Some(hi)) if lo <= hi => {
            crate::config_registry::note_crossed(
                "crates/axeyum-solver/src/nia_linearize.rs::MAX_SMALL_DOMAIN_WIDTH",
                u64::try_from(hi - lo).unwrap_or(u64::MAX),
                u64::try_from(MAX_SMALL_DOMAIN_WIDTH).unwrap_or(u64::MAX),
            );
            None
        }
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
    if hi > POW2_TABLE_MAX_EXP {
        // Split out of the shared `||` so each disjunct can be recorded on its
        // own. The caller does not decline a route on this: it omits the value
        // table and keeps emitting its other axiom families, so the omission is
        // invisible downstream -- the same shape as this file's six other
        // silent relaxations.
        crate::config_registry::note_crossed(
            "crates/axeyum-solver/src/nia_linearize.rs::POW2_TABLE_MAX_EXP",
            u64::try_from(hi).unwrap_or(u64::MAX),
            u64::try_from(POW2_TABLE_MAX_EXP).unwrap_or(u64::MAX),
        );
    }
    if lo <= hi && hi - lo >= POW2_TABLE_MAX_CASES {
        crate::config_registry::note_crossed(
            "crates/axeyum-solver/src/nia_linearize.rs::POW2_TABLE_MAX_CASES",
            u64::try_from(hi - lo).unwrap_or(u64::MAX),
            u64::try_from(POW2_TABLE_MAX_CASES).unwrap_or(u64::MAX),
        );
    }
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
    if triples.len() > MAX_MCCORMICK_PRODUCTS {
        // Distinguished from the empty case deliberately: both return `(0, 0)`,
        // and only one of them is a bound declining to do work it could have
        // done. Recorded before the shared return, not after it.
        crate::config_registry::note_crossed(
            "crates/axeyum-solver/src/nia_linearize.rs::MAX_MCCORMICK_PRODUCTS",
            triples.len() as u64,
            MAX_MCCORMICK_PRODUCTS as u64,
        );
    }
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
        let narrow = narrow_factor(a, b, a_bounds, b_bounds);
        // Only a product that WOULD have been split counts as a crossing: the
        // budget being spent is not a loss unless something wanted it. Recorded
        // here because the `&&` below simply falls through to the envelope, so
        // a forgone exact split is otherwise indistinguishable from a product
        // that never had a narrow factor.
        if split_products >= MAX_SMALL_DOMAIN_PRODUCTS && narrow.is_some() {
            crate::config_registry::note_crossed(
                "crates/axeyum-solver/src/nia_linearize.rs::MAX_SMALL_DOMAIN_PRODUCTS",
                split_products as u64,
                MAX_SMALL_DOMAIN_PRODUCTS as u64,
            );
        }
        if split_products < MAX_SMALL_DOMAIN_PRODUCTS
            && let Some((narrow, other, lo, hi)) = narrow
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

/// How much wall clock the incremental-linearization loop gets, and how it is
/// divided between the rounds inside it.
///
/// # Why this is an object and not two constants
///
/// The 2026-09-08 span-log sweep asked whether the `QF_NIA` division's "one
/// round" files were running one enormous round or failing to iterate, and the
/// answer needed an A/B on two independent knobs. Two constants cannot be A/B'd
/// without a rebuild; one named policy with an [`NiaRefinementPolicy::OFF`] arm
/// can, and `AXEYUM_NIA_REFINEMENT` selects it in one binary.
///
/// **`OFF` reproduces the committed behaviour exactly**, so a difference
/// measured against it is caused by the arm and not by the plumbing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NiaRefinementPolicy {
    /// Denominator of the caller's REMAINING budget the loop may use, on a
    /// query whose entailed bounds produced `McCormick` envelopes or exact
    /// splits. `3` is the committed value; `1` gives the loop everything left.
    ///
    /// Never raises the slice above the caller's own timeout — this divides an
    /// existing budget and never invents one.
    pub slice_denominator: u32,
    /// Denominator of the loop's REMAINING slice that any single round may use.
    ///
    /// `1` (the committed value) hands round 0 the entire slice, so a round that
    /// cannot decide ends the loop having learned nothing: measured 2026-09-08
    /// on `bench-results/parity-lists/QF_NIA.txt`, the loop's first round is
    /// also its last on a large share of the division. A denominator above 1
    /// bounds one round so a later round can still run — which only helps when
    /// the round that timed out would have produced a spurious model to cut off,
    /// and the arm exists so that "would it" is measured rather than argued.
    pub round_denominator: u32,
    /// Floor on any single round, so a large `round_denominator` on a small
    /// slice cannot hand a round a budget too short to reach the solver at all.
    pub round_floor_ms: u64,
}

impl NiaRefinementPolicy {
    /// The committed behaviour: a third of the remaining budget for the loop,
    /// all of it available to any one round.
    ///
    /// This is the arm every measurement is compared against, so it must stay
    /// byte-for-byte what the tree did before the policy existed.
    pub const OFF: Self = Self {
        slice_denominator: NIA_MCCORMICK_BUDGET_SHARE,
        round_denominator: 1,
        round_floor_ms: 0,
    };

    /// Whether this policy is the committed one, so a caller can assert an
    /// experiment actually selected an arm rather than silently running `OFF`.
    #[must_use]
    pub const fn is_off(self) -> bool {
        self.slice_denominator == Self::OFF.slice_denominator
            && self.round_denominator == Self::OFF.round_denominator
            && self.round_floor_ms == Self::OFF.round_floor_ms
    }

    /// The loop's slice out of `remaining`, given whether the entailed-bound
    /// pass emitted anything.
    ///
    /// Without envelopes the slice is [`NIA_SLICE_MS`] regardless of policy:
    /// that arm is the pre-ladder hang guard, not a search budget, and moving
    /// it is a different decision from moving this one.
    fn slice(
        self,
        remaining: Option<std::time::Duration>,
        has_envelopes: bool,
    ) -> std::time::Duration {
        let base = std::time::Duration::from_millis(NIA_SLICE_MS);
        let slice = match (has_envelopes, remaining) {
            (true, Some(total)) => base.max(total / self.slice_denominator.max(1)),
            _ => base,
        };
        remaining.map_or(slice, |t| t.min(slice))
    }

    /// One round's budget out of the slice still left.
    fn round(self, slice_left: std::time::Duration) -> std::time::Duration {
        if self.round_denominator <= 1 {
            return slice_left;
        }
        let share = slice_left / self.round_denominator;
        let floor = std::time::Duration::from_millis(self.round_floor_ms);
        share.max(floor).min(slice_left)
    }
}

/// Everything [`solve_with_refinement`] needs that is not a term: the policy in
/// force and whether this query has entailed-bound structure at all.
///
/// One struct rather than two parameters because the loop already takes four
/// term-shaped arguments and a config, and the two travel together at the only
/// call site — they are decided by the same pass over the products.
#[derive(Debug, Clone, Copy)]
struct RefinementSetup {
    /// See [`NiaRefinementPolicy`].
    policy: NiaRefinementPolicy,
    /// Whether the entailed-bound pass emitted anything. Without it a spurious
    /// model ends the loop instead of being cut off, because there is no
    /// structure for a tangent lemma to bite on and the loop would be a pure
    /// budget tax.
    refine: bool,
    /// ADR-2136's order/monotonicity pass. Read from the lever ONCE, at the
    /// call site, and carried here rather than consulted inside the loop: the
    /// lever is a process-lifetime `OnceLock` (determinism is a public API
    /// promise), so a test that wanted to exercise the armed arm could not
    /// otherwise reach it, and an arm no test can reach is an arm no test
    /// guards.
    order_lemmas: bool,
}

/// The refinement policy in force, read once from `AXEYUM_NIA_REFINEMENT`.
///
/// Format: `slice/rounds` or `slice/rounds/floor_ms`, e.g. `1/4` (whole
/// remaining budget, four rounds' worth per round) or `3/1` (the default).
/// Anything unparseable is [`NiaRefinementPolicy::OFF`] — a malformed sweep
/// variable must not silently become a third arm.
///
/// Read once into a `OnceLock`: determinism is a public API promise, so the
/// policy cannot change between two solves in one process.
/// `scripts/parity-run.sh` records any `AXEYUM_*` lever it sees, so a swept
/// number can never be mistaken for a default-configuration one.
fn refinement_policy() -> NiaRefinementPolicy {
    use std::sync::OnceLock;
    static POLICY: OnceLock<NiaRefinementPolicy> = OnceLock::new();
    *POLICY.get_or_init(|| {
        let Ok(raw) = std::env::var("AXEYUM_NIA_REFINEMENT") else {
            return NiaRefinementPolicy::OFF;
        };
        parse_refinement_policy(raw.trim()).unwrap_or(NiaRefinementPolicy::OFF)
    })
}

/// See [`refinement_policy`]. Separated so the parse is testable without an
/// environment variable and without the `OnceLock`'s one-shot behaviour.
fn parse_refinement_policy(raw: &str) -> Option<NiaRefinementPolicy> {
    let mut parts = raw.split('/');
    let slice_denominator = parts.next()?.parse::<u32>().ok()?;
    let round_denominator = parts.next()?.parse::<u32>().ok()?;
    let round_floor_ms = match parts.next() {
        None => 0,
        Some(f) => f.parse::<u64>().ok()?,
    };
    if parts.next().is_some() || slice_denominator == 0 || round_denominator == 0 {
        return None;
    }
    Some(NiaRefinementPolicy {
        slice_denominator,
        round_denominator,
        round_floor_ms,
    })
}

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
    // ADR-2136's arm is read ONCE here and threaded down, so the only thing
    // that separates the shipped route from the armed one is this argument.
    check_with_nia_armed(
        arena,
        assertions,
        config,
        why,
        nia_order_lemmas_enabled() == 1,
    )
}

/// [`check_with_nia`] with ADR-2136's order/monotonicity arm passed explicitly.
///
/// Split out because the lever is a process-lifetime `OnceLock` — determinism
/// is a public API promise, so it cannot be toggled between two solves in one
/// process, and a test of the armed arm would otherwise have no way in.
fn check_with_nia_armed(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    why: &mut Option<DeclineReason>,
    order_lemmas: bool,
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
    // The zero-divisor congruence mode (ADR-1730) needs no guard on this route:
    // its `unsat` transfers in every mode, and its `sat` is already gated by
    // `replay_sat` against the ORIGINAL assertions, which a model that violates
    // `div`/`mod` functionality cannot pass.
    let lin = axeyum_rewrite::eliminate_int_divmod(arena, &base)
        .map_err(err)?
        .into_assertions();
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
            "[nia] products={} mccormick={} splits={} relaxed={} timeout={:?} policy={}",
            rewritten_triples.len(),
            mccormick,
            splits,
            relaxed.len(),
            config.timeout,
            // Printed, not assumed: an A/B whose lever failed to parse is
            // `OFF`, and a sweep that cannot see that reports an arm it never
            // ran. `is_off` is the only thing that distinguishes them.
            if refinement_policy().is_off() {
                "off".to_owned()
            } else {
                format!(
                    "{}/{}/{}",
                    refinement_policy().slice_denominator,
                    refinement_policy().round_denominator,
                    refinement_policy().round_floor_ms
                )
            }
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
    let setup = RefinementSetup {
        policy: refinement_policy(),
        // The "this query has entailed-bound structure" signal: without it the
        // loop is a pure budget tax (see `RefinementSetup::refine`).
        //
        // ADR-2136 adds the second disjunct, and it is the difference between
        // the armed arm running and the armed arm being unreachable. `refine`
        // gates the loop on the entailed-bound passes having produced
        // something, and both of those need a factor with a two-sided constant
        // bound. The sizing census measured that this population has
        // essentially none: `unbounded_products` equals `products` at every
        // quantile over the 116 undecided rows, so `mccormick + splits` is 0
        // and the loop does ONE round on exactly the files this lane is aimed
        // at. The order and monotonicity lemmas need no static bound at all --
        // that is ADR-2112 E1's second design claim -- so on an armed run a
        // product is itself structure for a lemma to bite on.
        refine: mccormick + splits > 0 || (order_lemmas && !rewritten_triples.is_empty()),
        // ADR-2136, SHIPPED DISARMED (the caller reads the lever).
        order_lemmas,
    };
    let capped = config
        .clone()
        .with_timeout(setup.policy.slice(config.timeout, setup.refine));
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
        setup,
        why,
    )
}

/// One round's relaxation solve, timed as this loop's round-opening half.
///
/// The exact counterpart of the other two lazy loops' propositional skeleton
/// solve: it is what every round runs, and it is where the round count lives.
/// The clock is read only when counting is armed.
fn timed_relaxation_solve(
    arena: &mut TermArena,
    relaxed: &[TermId],
    round_config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let started = crate::lazy_smt_counters::enabled().then(std::time::Instant::now);
    let outcome = check_with_lia_dpll(arena, relaxed, round_config);
    if let Some(started) = started {
        let stage_outcome = match &outcome {
            Ok(CheckResult::Sat(_)) => RoundOutcome::Sat,
            Ok(CheckResult::Unsat) => RoundOutcome::Unsat,
            Ok(CheckResult::Unknown(_)) | Err(_) => RoundOutcome::Unknown,
        };
        crate::lazy_smt_counters::record_skeleton(
            LazySmtLoop::Nia,
            started.elapsed(),
            stage_outcome,
        );
    }
    outcome
}

/// The ground-evaluator replay, timed as this loop's theory half: it is what
/// decides whether the round's model is real, and its outcome is the round's
/// verdict on the cube.
fn timed_replay(arena: &TermArena, assertions: &[TermId], model: &Model) -> Option<CheckResult> {
    let started = crate::lazy_smt_counters::enabled().then(std::time::Instant::now);
    let replayed = replay_sat(arena, assertions, model);
    if let Some(started) = started {
        crate::lazy_smt_counters::record_theory(
            started.elapsed(),
            if replayed.is_some() {
                RoundOutcome::Sat
            } else {
                // A spurious model is this loop's conflict: it is what the next
                // round's tangent lemmas cut off.
                RoundOutcome::Unsat
            },
        );
    }
    replayed
}

/// The tangent-plane refinement, timed as this loop's blocking-clause half.
///
/// Each lemma rules out a region of the relaxation the round has just shown to
/// be spurious, so it is counted through the same field as the other loops'
/// blocking clauses — "how fast is the learned set growing" then reads the same
/// way on all three.
///
/// # Errors
///
/// Propagates term-construction failures.
fn timed_refine(
    arena: &mut TermArena,
    triples: &[(TermId, TermId, TermId)],
    order_index: Option<&BTreeMap<TermId, Vec<usize>>>,
    model: &Model,
    emitted: &mut BTreeSet<TermId>,
    relaxed: &mut Vec<TermId>,
) -> Result<usize, SolverError> {
    let started = crate::lazy_smt_counters::enabled().then(std::time::Instant::now);
    let mut added = refine_with_tangents(arena, triples, model, emitted, relaxed)?;
    // ADR-2136, SHIPPED DISARMED: `order_index` is `None` unless the lever is
    // armed, so with it off this call does not happen and the round is byte
    // for byte the round it is today. The order/monotonicity lemmas run AFTER
    // the tangents rather than instead of them — they are an addition to the
    // portfolio, and ADR-2112 §D2's finding is that redundancy is what a
    // portfolio is for.
    if let Some(index) = order_index {
        added += refine_with_order_and_monotone(arena, triples, index, model, emitted, relaxed)?;
    }
    if let Some(started) = started {
        crate::lazy_smt_counters::record_blocking(added as u64, started.elapsed());
    }
    Ok(added)
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
    setup: RefinementSetup,
    why: &mut Option<DeclineReason>,
) -> Result<Option<CheckResult>, SolverError> {
    let RefinementSetup {
        policy,
        refine,
        order_lemmas,
    } = setup;
    // ADR-2136's shared-factor index, built once per call (the triple list is
    // fixed across rounds; only the model moves). `None` is the shipped arm.
    let order_index = order_lemmas.then(|| shared_factor_index(triples));
    let mut relaxed = base.to_vec();
    let slice_deadline = std::time::Instant::now() + capped.timeout.unwrap_or_default();
    let debug = std::env::var_os("AXEYUM_NIA_DEBUG").is_some();
    let mut emitted: BTreeSet<TermId> = relaxed.iter().copied().collect();
    let mut round = 0usize;
    // This loop had NO instrument until 2026-09-08, which is why the span-log
    // sweep that went looking for it read the `nra` loop's rounds instead and
    // reported them as this one's. `atoms` is the abstracted-product count: the
    // number of `r = a·b` facts a round can cut off, and so the bound on how
    // much a round of refinement can learn.
    crate::lazy_smt_counters::record_entry(LazySmtLoop::Nia, triples.len() as u64);
    loop {
        let remaining = slice_deadline.checked_duration_since(std::time::Instant::now());
        let Some(remaining) = remaining.filter(|d| !d.is_zero()) else {
            *why = Some(DeclineReason::Budget(Budget::NiaRelaxationSliceExpired));
            return Ok(None);
        };
        // `remaining` is the whole slice left; the policy decides how much of it
        // ONE round may spend. Under `OFF` these are the same value, which is
        // why the loop's first round is also its last whenever the relaxation
        // solve cannot decide.
        let round_config = capped.clone().with_timeout(policy.round(remaining));
        let outcome = timed_relaxation_solve(arena, &relaxed, &round_config);
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
                if let Some(sat) = timed_replay(arena, assertions, &model) {
                    return Ok(Some(sat));
                }
                if !refine {
                    *why = Some(DeclineReason::VerifierRejected(
                        VerifierRejected::NiaRelaxationReplayFailed,
                    ));
                    return Ok(None);
                }
                if round >= MAX_REFINEMENT_ROUNDS {
                    *why = Some(DeclineReason::Budget(Budget::NiaRefinementRoundCapReached));
                    return Ok(None);
                }
                let added = timed_refine(
                    arena,
                    triples,
                    order_index.as_ref(),
                    &model,
                    &mut emitted,
                    &mut relaxed,
                )?;
                if debug {
                    eprintln!("[nia] round {round}: refined with {added} tangent lemmas");
                }
                if added == 0 {
                    // Nothing new to cut off — the loop cannot make progress.
                    *why = Some(DeclineReason::VerifierRejected(
                        VerifierRejected::NiaRefinementNoNewLemma,
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
            // Forgoing the tangent lemma for this product is invisible: the
            // `continue` is the same control flow as "already faithful".
            crate::config_registry::note_crossed(
                "crates/axeyum-solver/src/nia_linearize.rs::MAX_TANGENT_ABS_VALUE",
                u64::try_from(a_val.abs().max(b_val.abs())).unwrap_or(u64::MAX),
                u64::try_from(MAX_TANGENT_ABS_VALUE).unwrap_or(u64::MAX),
            );
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

// ---------------------------------------------------------------------------
// ADR-2136: order lemmas and monotonicity lemmas, model-driven.
//
// ADR-2112 Part E measured both classes ABSENT from this file and stated the
// two design claims this code implements, with `file:line` on z3's side:
//
//   * **order** -- `nla_order_lemmas.cpp::generate_ol` (`:286-310`) emits, for
//     two monics `ac` and `bc` that SHARE the factor `c`, one of
//         c > 0 ∧ ac ≥ bc → a ≥ b        c < 0 ∧ ac ≥ bc → a ≤ b
//         c > 0 ∧ ac ≤ bc → a ≤ b        c < 0 ∧ ac ≤ bc → a ≥ b
//     selected by `order_lemma_on_ac_and_bc_and_factors` (`:322-341`) at the
//     CURRENT assignment: the sign of `val(c)` picks the hypothesis, the
//     observed relation between the two ABSTRACTION values picks the second,
//     and the lemma is emitted only when the conclusion is violated there.
//     Our linearizer abstracts every product independently (a fresh `r` per
//     product, `check_with_nia` step 3) and nothing related two abstractions
//     that share a factor.
//
//   * **monotonicity** -- `nla_monotone_lemmas.cpp::monotonicity_lemma_lt`
//     (`:80-90`) and `::monotonicity_lemma_gt` (`:61-72`) cut at the current
//     assignment with no static bound, which is the difference from
//     [`mccormick_lemmas`]: ours fires only for factors whose bounds the
//     relaxation ENTAILS, and this population has essentially none (the
//     sizing census measured `unbounded_products == products` at every
//     quantile over the 116 undecided rows).
//
// The magnitude atoms both classes are STATED on (`|x| ≤ |y|`) never become
// `abs` terms here. z3 does not build them either: `nla_basics_lemmas.cpp::
// negate_strict_sign` (`:202-216`) replaces a magnitude atom by a STRICT SIGN
// literal keyed off the current value's sign, which is sound precisely because
// the hypothesis then pins the sign as well as the magnitude. Every lemma below
// is built the same way -- plain linear atoms against integer constants read
// from the model -- so no IR magnitude term is introduced.
//
// cvc5 reaches the same two places by a different route, recorded so a later
// lane does not read "z3 only": `monomial_bounds_check.cpp:308-325` multiplies
// an asserted inequality through by a term whose model sign is known, reversing
// the relation when that sign is negative (`infer_type`, `:308`) -- the order
// lemma in inference form -- and gates emission on the inferred fact being
// FALSE at the current abstract model (`:317`), the same model-driven trigger.
// `monomial_check.cpp::checkMagnitude` (`:193`) orders monomials by the
// ABSOLUTE value of their abstract model values (`assignOrderIds(..., true)`,
// `:202`) and `compareMonomial` (`:517`) emits the magnitude comparisons: the
// monotonicity analogue. Its tangent analogue, `tangent_plane_check.cpp:37`,
// is the class we already have ([`tangent_lemmas`]).
//
// SOUNDNESS. Every lemma below is a consequence of the intended extension
// `r := a·b` alone -- it is valid in every integer model of the ORIGINAL query,
// exactly like the sign and tangent lemmas. So adding them can only shrink the
// relaxation's model space, an `unsat` still transfers, and a `sat` is still
// accepted only after [`replay_sat`] against the original assertions. The
// validity is not asserted: [`lemma_holds_at_faithful_points`] evaluates every
// emitted lemma at pseudo-random integer points with each abstraction variable
// set to the product of its own factors, under `debug_assert!`, and the schema
// tests drive every sign case through it.
// ---------------------------------------------------------------------------

/// ADR-2136's order/monotonicity lemma pass, SHIPPED DISARMED.
///
/// `0` is the shipped arm and leaves the refinement loop byte-identical;
/// `AXEYUM_NIA_ORDER_LEMMAS=1` arms it. Anything but an exact `1` is the
/// shipped arm, so a typo cannot select an arm nobody chose.
const NIA_ORDER_LEMMAS_ARMED: u32 = 0;

axeyum_ir::cap_lever! {
    /// [`NIA_ORDER_LEMMAS_ARMED`], or `AXEYUM_NIA_ORDER_LEMMAS`.
    pub(crate) fn nia_order_lemmas_enabled() -> u32 =
        "AXEYUM_NIA_ORDER_LEMMAS" or NIA_ORDER_LEMMAS_ARMED;
}

/// Largest number of shared-factor product PAIRS examined in one refinement
/// round. The sizing census measured a median of 2,249 such pairs per
/// undecided `QF_NIA` row and a maximum of 9,407,886, so the pass has to bound
/// what it LOOKS AT and not only what it emits — an emission cap alone would
/// still walk ten million pairs on the worst file.
const MAX_ORDER_PAIRS_EXAMINED_PER_ROUND: usize = 4_096;

/// Largest number of order lemmas appended in one refinement round.
const MAX_ORDER_LEMMAS_PER_ROUND: usize = 64;

/// Largest number of monotonicity lemmas appended in one refinement round.
const MAX_MONOTONE_LEMMAS_PER_ROUND: usize = 64;

/// Largest absolute model value at which either class is built, so every
/// product of two model values stays exact in `i128` (`|a·b| ≤ 2^80`). The same
/// guard [`MAX_TANGENT_ABS_VALUE`] puts on the tangent pass, for the same
/// reason.
const MAX_ORDER_ABS_VALUE: i128 = 1 << 40;

/// A lemma emitted by this pass, with the abstraction triples its validity
/// depends on — carried so the debug-build checker can make those abstractions
/// FAITHFUL before it evaluates the lemma.
struct CheckedLemma {
    lemma: TermId,
    /// Indices into the refinement loop's `triples`.
    depends_on: Vec<usize>,
}

/// The **order** lemma for two abstracted products sharing the factor `c`, at
/// the current relaxation model — or `None` when the model does not violate
/// any of the four implications.
///
/// `rac` abstracts `a·c` and `rbc` abstracts `b·c`. The four cases are z3's
/// (`nla_order_lemmas.cpp:286-310`); which one is emitted is decided entirely
/// by the model, as in `order_lemma_on_ac_and_bc_and_factors` (`:322-341`):
///
/// * the sign of `c`'s value picks the hypothesis `c > 0` or `c < 0`
///   (`c = 0` emits nothing — every implication is vacuous there, and z3
///   asserts the same precondition);
/// * the relation the model exhibits between the two ABSTRACTION values picks
///   the hypothesis `ac ≥ bc` or `ac ≤ bc` (note: between the abstraction
///   variables, not between the products — the whole point is that the
///   relaxation's `r` need not equal `a·c`);
/// * those two together force the conclusion's direction, and the lemma is
///   emitted only when the model VIOLATES it.
#[allow(clippy::too_many_arguments)]
fn order_lemma_at_model(
    arena: &mut TermArena,
    c: TermId,
    a: TermId,
    b: TermId,
    rac: TermId,
    rbc: TermId,
    c_val: i128,
    a_val: i128,
    b_val: i128,
    rac_val: i128,
    rbc_val: i128,
    zero: TermId,
) -> Result<Option<TermId>, SolverError> {
    if c_val == 0 || rac_val == rbc_val {
        return Ok(None);
    }
    let c_positive = c_val > 0;
    // `c > 0 ∧ ac ≥ bc → a ≥ b` and its three siblings collapse to this: the
    // conclusion points the same way as the abstraction values when `c > 0`
    // and the opposite way when `c < 0`.
    let conclude_a_ge_b = (rac_val > rbc_val) == c_positive;
    let violated = if conclude_a_ge_b {
        a_val < b_val
    } else {
        a_val > b_val
    };
    if !violated {
        return Ok(None);
    }
    let hyp_c = if c_positive {
        arena.int_gt(c, zero).map_err(err)?
    } else {
        arena.int_lt(c, zero).map_err(err)?
    };
    let hyp_r = if rac_val > rbc_val {
        arena.int_ge(rac, rbc).map_err(err)?
    } else {
        arena.int_le(rac, rbc).map_err(err)?
    };
    let concl = if conclude_a_ge_b {
        arena.int_ge(a, b).map_err(err)?
    } else {
        arena.int_le(a, b).map_err(err)?
    };
    let hyp = arena.and(hyp_c, hyp_r).map_err(err)?;
    Ok(Some(arena.implies(hyp, concl).map_err(err)?))
}

/// The **order equality** lemma `c ≠ 0 ∧ ac = bc → a = b`, at the current
/// model — z3's `generate_ol_eq` (`nla_order_lemmas.cpp:265-284`), the case the
/// four ordered implications above cannot reach because they need the two
/// abstraction values to differ.
///
/// Returns `None` unless the model has `rac = rbc` with `a` and `b` differing,
/// which is exactly when the conclusion is violated.
#[allow(clippy::too_many_arguments)]
fn order_eq_lemma_at_model(
    arena: &mut TermArena,
    c: TermId,
    a: TermId,
    b: TermId,
    rac: TermId,
    rbc: TermId,
    c_val: i128,
    a_val: i128,
    b_val: i128,
    rac_val: i128,
    rbc_val: i128,
    zero: TermId,
) -> Result<Option<TermId>, SolverError> {
    if c_val == 0 || rac_val != rbc_val || a_val == b_val {
        return Ok(None);
    }
    // `c ≠ 0` as a disjunction rather than a negated equality: the relaxation's
    // atom vocabulary is linear comparisons, and `c < 0 ∨ c > 0` keeps it there.
    let c_neg = arena.int_lt(c, zero).map_err(err)?;
    let c_pos = arena.int_gt(c, zero).map_err(err)?;
    let c_nonzero = arena.or(c_neg, c_pos).map_err(err)?;
    let same_product = arena.eq(rac, rbc).map_err(err)?;
    let concl = arena.eq(a, b).map_err(err)?;
    let hyp = arena.and(c_nonzero, same_product).map_err(err)?;
    Ok(Some(arena.implies(hyp, concl).map_err(err)?))
}

/// The **monotonicity** lemmas for one abstracted product `r ≈ a·b` at the
/// current model — z3's `nla_monotone_lemmas.cpp`, stated on magnitudes and
/// built without a magnitude term.
///
/// With `p = a_val·b_val`, two cases, each emitted only when the model's `r`
/// has the wrong MAGNITUDE (the sign lemmas already own the quadrant):
///
/// * `|r_val| < |p|` — z3's `monotonicity_lemma_lt` (`:80-90`). Hypotheses pin
///   each factor at or beyond its own value ON ITS OWN SIDE of zero
///   (`a ≤ a_val` when `a_val < 0`, `a ≥ a_val` when `a_val > 0`), which fixes
///   both the sign and a magnitude floor, so the product's sign is `sign(p)`
///   and its magnitude is at least `|p|`:
///   `H_a ∧ H_b → (r ≤ p)` when `p < 0`, `(r ≥ p)` when `p > 0`.
/// * `|r_val| > |p|` — z3's `monotonicity_lemma_gt` (`:61-72`). Hypotheses trap
///   each factor in the closed interval between `0` and its own value — this is
///   where the second, SIGN-pinning literal comes from (`a ≤ 0` when
///   `a_val < 0`) and it is not decoration: without it the hypothesis admits a
///   factor of the opposite sign and unbounded magnitude, and the conclusion
///   is false. That gives `|r| ≤ |p|` with `sign(r) ∈ {0, sign(p)}`:
///   `H_a ∧ H_b → (r ≤ p)` when `p > 0`, `(r ≥ p)` when `p < 0`.
///
/// A zero factor value emits nothing: `sign_lemmas` already gives `a = 0 → r = 0`,
/// and z3 likewise routes a zero through `mon_has_zero` before it reaches here.
fn monotone_lemmas_at_model(
    arena: &mut TermArena,
    a: TermId,
    b: TermId,
    r: TermId,
    a_val: i128,
    b_val: i128,
    r_val: i128,
    zero: TermId,
) -> Result<Vec<TermId>, SolverError> {
    if a_val == 0 || b_val == 0 {
        return Ok(Vec::new());
    }
    // Exact: both guarded by `MAX_ORDER_ABS_VALUE` at the call site.
    let p = a_val * b_val;
    let a_const = arena.int_const(a_val);
    let b_const = arena.int_const(b_val);
    let p_const = arena.int_const(p);

    let mut out = Vec::new();
    if r_val.abs() < p.abs() {
        // `|r|` is too SMALL: force it out to at least `|p|`.
        let hyp_a = if a_val < 0 {
            arena.int_le(a, a_const).map_err(err)?
        } else {
            arena.int_ge(a, a_const).map_err(err)?
        };
        let hyp_b = if b_val < 0 {
            arena.int_le(b, b_const).map_err(err)?
        } else {
            arena.int_ge(b, b_const).map_err(err)?
        };
        let concl = if p < 0 {
            arena.int_le(r, p_const).map_err(err)?
        } else {
            arena.int_ge(r, p_const).map_err(err)?
        };
        let hyp = arena.and(hyp_a, hyp_b).map_err(err)?;
        out.push(arena.implies(hyp, concl).map_err(err)?);
    } else if r_val.abs() > p.abs() {
        // `|r|` is too LARGE: trap each factor between zero and its own value.
        let hyp_a = monotone_interval_hypothesis(arena, a, a_const, a_val, zero)?;
        let hyp_b = monotone_interval_hypothesis(arena, b, b_const, b_val, zero)?;
        let concl = if p > 0 {
            arena.int_le(r, p_const).map_err(err)?
        } else {
            arena.int_ge(r, p_const).map_err(err)?
        };
        let hyp = arena.and(hyp_a, hyp_b).map_err(err)?;
        out.push(arena.implies(hyp, concl).map_err(err)?);
    }
    Ok(out)
}

/// `v ≤ x ≤ 0` when `v < 0`, `0 ≤ x ≤ v` when `v > 0` — the interval between
/// zero and the factor's own model value, both halves.
///
/// The half that pins the SIGN (`x ≤ 0`, `0 ≤ x`) is the one z3 adds as a
/// second literal in `monotonicity_lemma_gt` (`nla_monotone_lemmas.cpp:66-68`).
/// Dropping it leaves a hypothesis that a factor of the opposite sign
/// satisfies, and the conclusion does not hold there — see
/// `monotone_gt_without_the_sign_pin_is_refutable`.
fn monotone_interval_hypothesis(
    arena: &mut TermArena,
    x: TermId,
    x_const: TermId,
    x_val: i128,
    zero: TermId,
) -> Result<TermId, SolverError> {
    let (near, far) = if x_val < 0 {
        (
            arena.int_le(x, zero).map_err(err)?,
            arena.int_ge(x, x_const).map_err(err)?,
        )
    } else {
        (
            arena.int_ge(x, zero).map_err(err)?,
            arena.int_le(x, x_const).map_err(err)?,
        )
    };
    arena.and(near, far).map_err(err)
}

/// `factor term -> indices of the triples it is an operand of`, in a
/// deterministic order (`BTreeMap` keys, ascending triple index).
///
/// Built once per `check_with_nia` call rather than per round: the triple list
/// does not change across rounds, only the model does.
fn shared_factor_index(triples: &[(TermId, TermId, TermId)]) -> BTreeMap<TermId, Vec<usize>> {
    let mut index: BTreeMap<TermId, Vec<usize>> = BTreeMap::new();
    for (i, &(a, b, _)) in triples.iter().enumerate() {
        index.entry(a).or_default().push(i);
        if b != a {
            index.entry(b).or_default().push(i);
        }
    }
    // A factor in exactly one product has no pair to couple with.
    index.retain(|_, ids| ids.len() >= 2);
    index
}

/// The operand of `triple` that is NOT `c`. For a square (`c·c`) that is `c`
/// itself, which is correct: `ac` with `a = c` is still `a·c`.
fn other_operand(triple: (TermId, TermId, TermId), c: TermId) -> TermId {
    let (a, b, _) = triple;
    if a == c { b } else { a }
}

/// Evaluates `lemma` at `points` pseudo-random integer assignments in which
/// every abstraction variable is made FAITHFUL (`r := a·b`), and reports the
/// first point at which it is false.
///
/// This is the soundness argument executed rather than asserted. A lemma from
/// this pass is claimed valid in every integer model of the original query;
/// the only models it has to hold at are those where each `r` really is the
/// product of its factors, so the checker constructs exactly those.
///
/// Deterministic: a fixed-seed LCG, and the symbol order comes from
/// [`collect_symbols`]'s `BTreeSet`. Determinism is a public promise and a
/// checker that samples differently per run would make a `debug_assert!`
/// failure unreproducible.
///
/// Returns `Ok(())` when no counterexample was found in `points` samples, and
/// `Err(description)` naming the falsifying assignment otherwise. A point at
/// which the lemma does not ground-evaluate to a boolean is SKIPPED and
/// counted; if every point is skipped the result is `Err`, because a checker
/// that silently examined nothing is worse than no checker.
fn lemma_holds_at_faithful_points(
    arena: &TermArena,
    lemma: TermId,
    triples: &[(TermId, TermId, TermId)],
    depends_on: &[usize],
    points: usize,
) -> Result<(), String> {
    use axeyum_ir::Assignment;

    // The abstraction variables in play, and the factors they abstract.
    let mut abstractions: Vec<(SymbolId, TermId, TermId)> = Vec::new();
    for &i in depends_on {
        let (a, b, r) = triples[i];
        if let TermNode::Symbol(sym) = arena.node(r) {
            abstractions.push((*sym, a, b));
        }
    }
    let abstract_syms: BTreeSet<SymbolId> = abstractions.iter().map(|&(s, _, _)| s).collect();

    // Everything the lemma and its factors mention, minus the abstractions.
    let mut roots = vec![lemma];
    for &(_, a, b) in &abstractions {
        roots.push(a);
        roots.push(b);
    }
    let free: Vec<SymbolId> = collect_symbols(arena, &roots)
        .into_iter()
        .filter(|s| !abstract_syms.contains(s))
        .collect();

    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = move || {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        // Small magnitudes: the interesting failures are sign-case failures,
        // and a wide range only makes a counterexample harder to read.
        i128::from((state >> 33) as u32 % 17) - 8
    };

    let mut examined = 0usize;
    for _ in 0..points {
        let mut assignment = Assignment::default();
        for &s in &free {
            assignment.set(s, Value::Int(next()));
        }
        // Abstractions may nest (`(a·b)·c`), so assign to a fixpoint rather
        // than in list order.
        let mut pending: Vec<&(SymbolId, TermId, TermId)> = abstractions.iter().collect();
        loop {
            let before = pending.len();
            pending.retain(|&&(s, a, b)| {
                let (Some(av), Some(bv)) = (
                    int_value(arena, a, &assignment),
                    int_value(arena, b, &assignment),
                ) else {
                    return true;
                };
                let Some(p) = av.checked_mul(bv) else {
                    return true;
                };
                assignment.set(s, Value::Int(p));
                false
            });
            if pending.len() == before {
                break;
            }
        }
        if !pending.is_empty() {
            continue; // this point could not be made faithful
        }
        match eval(arena, lemma, &assignment) {
            Ok(Value::Bool(true)) => examined += 1,
            Ok(Value::Bool(false)) => {
                return Err(format!(
                    "lemma {lemma:?} is FALSE at a faithful integer point: {assignment:?}"
                ));
            }
            _ => {}
        }
    }
    if examined == 0 {
        return Err(format!(
            "lemma {lemma:?} could not be evaluated at ANY of {points} faithful points \
             — the check examined nothing, which is not evidence that it holds"
        ));
    }
    Ok(())
}

/// Number of random points [`lemma_holds_at_faithful_points`] tries under
/// `debug_assert!`. Small enough that a debug-build solve stays usable and
/// large enough that a sign-case error, which is wrong on roughly half of all
/// points, is found with overwhelming probability.
#[cfg(debug_assertions)]
const LEMMA_CHECK_POINTS: usize = 24;

/// Builds this round's order and monotonicity lemmas at the spurious model, for
/// the products the model gets WRONG.
///
/// Emission order is deterministic: monotonicity walks `triples` in index
/// order, then order lemmas walk the shared-factor index in `BTreeMap` key
/// order and, within a factor, in ascending triple-index pairs. Both are
/// capped; the order pass caps what it EXAMINES as well as what it emits,
/// because the sizing census found a file with 9,407,886 shared-factor pairs.
fn order_and_monotone_lemmas(
    arena: &mut TermArena,
    triples: &[(TermId, TermId, TermId)],
    index: &BTreeMap<TermId, Vec<usize>>,
    model: &Model,
) -> Result<Vec<CheckedLemma>, SolverError> {
    let assignment = model.to_assignment();
    let zero = arena.int_const(0);
    let mut out: Vec<CheckedLemma> = Vec::new();

    // Model values, once per triple. `None` for a triple the model does not
    // ground-evaluate or whose magnitudes leave the exact-`i128` band.
    let values: Vec<Option<(i128, i128, i128)>> = triples
        .iter()
        .map(|&(a, b, r)| {
            let (Some(av), Some(bv), Some(rv)) = (
                int_value(arena, a, &assignment),
                int_value(arena, b, &assignment),
                int_value(arena, r, &assignment),
            ) else {
                return None;
            };
            if av.abs() > MAX_ORDER_ABS_VALUE
                || bv.abs() > MAX_ORDER_ABS_VALUE
                || rv.abs() > MAX_ORDER_ABS_VALUE
            {
                crate::config_registry::note_crossed(
                    "crates/axeyum-solver/src/nia_linearize.rs::MAX_ORDER_ABS_VALUE",
                    u64::try_from(av.abs().max(bv.abs()).max(rv.abs())).unwrap_or(u64::MAX),
                    u64::try_from(MAX_ORDER_ABS_VALUE).unwrap_or(u64::MAX),
                );
                return None;
            }
            Some((av, bv, rv))
        })
        .collect();

    // --- monotonicity: one product at a time, at the current assignment.
    let mut monotone = 0usize;
    for (i, &(a, b, r)) in triples.iter().enumerate() {
        if monotone >= MAX_MONOTONE_LEMMAS_PER_ROUND {
            break;
        }
        let Some((av, bv, rv)) = values[i] else {
            continue;
        };
        if av * bv == rv {
            continue; // already faithful — nothing to cut off
        }
        for lemma in monotone_lemmas_at_model(arena, a, b, r, av, bv, rv, zero)? {
            out.push(CheckedLemma {
                lemma,
                depends_on: vec![i],
            });
            monotone += 1;
        }
    }

    // --- order: two products sharing a factor.
    let mut examined = 0usize;
    let mut emitted = 0usize;
    'factors: for (&c, ids) in index {
        for (n, &i) in ids.iter().enumerate() {
            for &j in &ids[n + 1..] {
                if examined >= MAX_ORDER_PAIRS_EXAMINED_PER_ROUND
                    || emitted >= MAX_ORDER_LEMMAS_PER_ROUND
                {
                    break 'factors;
                }
                examined += 1;
                let (Some((ai, bi, ri)), Some((aj, bj, rj))) = (values[i], values[j]) else {
                    continue;
                };
                let (a, b) = (other_operand(triples[i], c), other_operand(triples[j], c));
                if a == b {
                    continue; // the lemma would relate a term to itself
                }
                // `c`'s own value: it is one of the two operands of triple `i`.
                let c_val = if triples[i].0 == c { ai } else { bi };
                let a_val = if triples[i].0 == c { bi } else { ai };
                let b_val = if triples[j].0 == c { bj } else { aj };
                let (rac, rbc) = (triples[i].2, triples[j].2);
                let built = if ri == rj {
                    order_eq_lemma_at_model(
                        arena, c, a, b, rac, rbc, c_val, a_val, b_val, ri, rj, zero,
                    )?
                } else {
                    order_lemma_at_model(
                        arena, c, a, b, rac, rbc, c_val, a_val, b_val, ri, rj, zero,
                    )?
                };
                if let Some(lemma) = built {
                    out.push(CheckedLemma {
                        lemma,
                        depends_on: vec![i, j],
                    });
                    emitted += 1;
                }
            }
        }
    }

    // Every lemma this pass emits claims to be valid in every integer model of
    // the original query. In a debug build, CHECK that rather than assert it.
    #[cfg(debug_assertions)]
    for cl in &out {
        if let Err(why) = lemma_holds_at_faithful_points(
            arena,
            cl.lemma,
            triples,
            &cl.depends_on,
            LEMMA_CHECK_POINTS,
        ) {
            debug_assert!(false, "ADR-2136 emitted an INVALID lemma: {why}");
        }
    }

    Ok(out)
}

/// Appends this round's order and monotonicity lemmas, skipping any already
/// present. Returns how many genuinely new lemmas were appended.
fn refine_with_order_and_monotone(
    arena: &mut TermArena,
    triples: &[(TermId, TermId, TermId)],
    index: &BTreeMap<TermId, Vec<usize>>,
    model: &Model,
    emitted: &mut BTreeSet<TermId>,
    relaxed: &mut Vec<TermId>,
) -> Result<usize, SolverError> {
    let built = order_and_monotone_lemmas(arena, triples, index, model)?;
    let considered = built.len();
    let mut added = 0usize;
    for cl in built {
        if emitted.insert(cl.lemma) {
            relaxed.push(cl.lemma);
            added += 1;
        }
    }
    // Printed, not assumed. An A/B arm that reaches this code and emits NOTHING
    // is indistinguishable in every verdict column from an arm that was never
    // armed, and that is the shape that left a lever "measured at zero" when it
    // had simply not been wired (ADR-2112 proved its own floor reached by a
    // parse panic rather than by a null result).
    if std::env::var_os("AXEYUM_NIA_DEBUG").is_some() {
        eprintln!("[nia] order/monotone: built={considered} new={added}");
    }
    #[cfg(test)]
    LEMMAS_BUILT.with(|n| n.set(n.get() + considered));
    Ok(added)
}

#[cfg(test)]
thread_local! {
    /// How many order/monotonicity lemmas this thread's solves have BUILT.
    ///
    /// Exists so an end-to-end fixture can assert it reached this pass at all.
    /// The first draft of `a_negative_shared_factor_must_not_refute_this_satisfiable_system`
    /// passed while the relaxation's very first model replayed successfully --
    /// no refinement round ran, no lemma was ever built, and the test was green
    /// for a reason that had nothing to do with its subject. A fixture that
    /// cannot tell "the lemma was right" from "the lemma was never emitted" is
    /// not a soundness-negative fixture.
    static LEMMAS_BUILT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
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
    //
    // Roadmap 2.11: the replay above ran against `model.to_assignment()` and this
    // rebuilt a model carrying symbol entries ONLY — dropping functions,
    // `real_div_zero`, `uninterpreted_cardinalities` and the quantified sat
    // certificates. Narrowing through `retain_symbols` keeps every component the
    // replay saw, and every component added to `Model` in future.
    let originals = collect_symbols(arena, assertions);
    let mut clean = model.clone();
    clean.retain_symbols(|sym| originals.contains(&sym));
    Some(CheckResult::Sat(clean))
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Assignment;
    use std::time::Duration;

    /// The `OFF` arm must reproduce the committed slice EXACTLY, so an A/B
    /// difference is caused by the arm and not by the plumbing that introduced
    /// the arm.
    ///
    /// The expectation is the pre-policy expression, written out, not a call
    /// back into `NiaRefinementPolicy::slice` — a test that computes its
    /// expectation the way the subject does cannot fail.
    #[test]
    fn the_off_arm_reproduces_the_committed_slice_and_round_budget() {
        assert!(NiaRefinementPolicy::OFF.is_off());
        for total_ms in [0_u64, 1, 599, 600, 1_800, 24_000, 600_000] {
            for has_envelopes in [false, true] {
                let total = Duration::from_millis(total_ms);
                let base = Duration::from_millis(NIA_SLICE_MS);
                let want_slice = if has_envelopes {
                    base.max(total / NIA_MCCORMICK_BUDGET_SHARE)
                } else {
                    base
                };
                let want = total.min(want_slice);
                assert_eq!(
                    NiaRefinementPolicy::OFF.slice(Some(total), has_envelopes),
                    want,
                    "OFF must reproduce the committed slice at {total_ms} ms, \
                     envelopes={has_envelopes}"
                );
                // Under OFF a round may spend the WHOLE remaining slice, which
                // is why the loop's first round is also its last whenever the
                // relaxation solve cannot decide inside it.
                assert_eq!(NiaRefinementPolicy::OFF.round(want), want);
            }
        }
        // No caller budget: the pre-ladder hang guard, unchanged.
        assert_eq!(
            NiaRefinementPolicy::OFF.slice(None, true),
            Duration::from_millis(NIA_SLICE_MS)
        );
    }

    /// The arm must actually differ from `OFF`, in both knobs, or an A/B run
    /// with it selected would measure nothing and report agreement.
    #[test]
    fn a_selected_arm_moves_the_slice_and_bounds_one_round_below_it() {
        let whole = NiaRefinementPolicy {
            slice_denominator: 1,
            round_denominator: 4,
            round_floor_ms: 250,
        };
        assert!(!whole.is_off());
        let total = Duration::from_secs(24);
        assert_eq!(
            whole.slice(Some(total), true),
            total,
            "slice_denominator=1 must hand the loop the whole remaining budget"
        );
        assert_eq!(
            NiaRefinementPolicy::OFF.slice(Some(total), true),
            Duration::from_secs(8),
            "and OFF must not, or the two arms are the same experiment"
        );
        assert_eq!(whole.round(total), Duration::from_secs(6));
        // The floor is what stops a large denominator on a small slice from
        // handing a round a budget too short to reach the solver at all.
        assert_eq!(
            whole.round(Duration::from_millis(400)),
            Duration::from_millis(250)
        );
        // ...and it never exceeds what is left.
        assert_eq!(
            whole.round(Duration::from_millis(100)),
            Duration::from_millis(100)
        );
    }

    /// A malformed sweep variable must be `OFF`, never a silent third arm: a
    /// run whose lever did not parse has to be indistinguishable from a default
    /// run, or a sweep reports an arm it never ran.
    #[test]
    fn a_malformed_policy_string_is_off_and_not_a_third_arm() {
        for bad in [
            "", "3", "3/", "/1", "a/b", "3/1/x", "3/1/2/4", "0/1", "3/0", "-3/1", "3 / 1",
        ] {
            assert_eq!(
                parse_refinement_policy(bad),
                None,
                "{bad:?} must not parse into an arm"
            );
        }
        assert_eq!(
            parse_refinement_policy("3/1"),
            Some(NiaRefinementPolicy::OFF),
            "the committed shape must round-trip to OFF"
        );
        assert_eq!(
            parse_refinement_policy("1/4/250"),
            Some(NiaRefinementPolicy {
                slice_denominator: 1,
                round_denominator: 4,
                round_floor_ms: 250,
            })
        );
    }

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

    /// The three per-candidate relaxation bounds must be attributable.
    ///
    /// Each of them forgoes a lemma through control flow that is
    /// indistinguishable from "there was nothing to emit": a dropped endpoint
    /// and an absent endpoint are both `None`, and a too-wide factor and a
    /// factor with no interval are both a `None` window. Recording the crossing
    /// is the only thing that tells them apart, and these drive the real
    /// functions rather than `note_crossed`.
    #[test]
    fn crossing_a_relaxation_bound_is_recorded_with_its_numbers() {
        assert!(
            crate::config_registry::crossings().is_empty(),
            "this thread must start with nothing recorded"
        );
        let _ = clamp_to_mccormick_bound(Some(MCCORMICK_MAX_ABS_BOUND + 1));
        assert!(
            crate::config_registry::crossings().is_empty(),
            "recording must be opt-in: a crossing outside a guard recorded anyway"
        );

        let magnitude = {
            let _g = crate::config_registry::ConfigTraceGuard::enable();
            assert_eq!(
                clamp_to_mccormick_bound(Some(MCCORMICK_MAX_ABS_BOUND + 1)),
                None
            );
            crate::config_registry::crossings()
        };
        assert_eq!(
            magnitude,
            vec![(
                "crates/axeyum-solver/src/nia_linearize.rs::MCCORMICK_MAX_ABS_BOUND",
                u64::try_from(MCCORMICK_MAX_ABS_BOUND + 1).unwrap(),
                u64::try_from(MCCORMICK_MAX_ABS_BOUND).unwrap(),
            )]
        );

        let (mut arena, ..) = triple();
        let a = arena.int_var("wa").unwrap();
        let b = arena.int_var("wb").unwrap();
        let width = {
            let _g = crate::config_registry::ConfigTraceGuard::enable();
            let wide = (Some(0_i128), Some(MAX_SMALL_DOMAIN_WIDTH + 1));
            assert_eq!(narrow_factor(a, b, wide, wide), None);
            crate::config_registry::crossings()
        };
        assert_eq!(
            width,
            vec![(
                "crates/axeyum-solver/src/nia_linearize.rs::MAX_SMALL_DOMAIN_WIDTH",
                u64::try_from(MAX_SMALL_DOMAIN_WIDTH + 1).unwrap(),
                u64::try_from(MAX_SMALL_DOMAIN_WIDTH).unwrap(),
            )]
        );

        // The non-crossing cases, each in a FRESH guard and each asserted
        // EMPTY. Checked inside the guard that had already recorded the key,
        // these were vacuous: `note_crossed` keeps only the first crossing per
        // key, so a wrongly recorded second call cannot grow the set.
        let in_bound = {
            let _g = crate::config_registry::ConfigTraceGuard::enable();
            assert_eq!(
                clamp_to_mccormick_bound(Some(MCCORMICK_MAX_ABS_BOUND)),
                Some(MCCORMICK_MAX_ABS_BOUND)
            );
            assert_eq!(clamp_to_mccormick_bound(None), None);
            crate::config_registry::crossings()
        };
        assert!(
            in_bound.is_empty(),
            "an endpoint inside the bound, or an absent one, is not a crossing; got {in_bound:?}"
        );
        let unbounded = {
            let _g = crate::config_registry::ConfigTraceGuard::enable();
            assert_eq!(narrow_factor(a, b, (None, None), (None, None)), None);
            crate::config_registry::crossings()
        };
        assert!(
            unbounded.is_empty(),
            "a factor with no entailed interval is not a crossing; got {unbounded:?}"
        );

        // `MAX_MCCORMICK_PRODUCTS` shares its `(0, 0)` return with the empty
        // case, which is exactly why the crossing has to be recorded before it.
        let triples = vec![(a, b, arena.int_var("wr").unwrap()); MAX_MCCORMICK_PRODUCTS + 1];
        let mut relaxed: Vec<TermId> = Vec::new();
        let products = {
            let _g = crate::config_registry::ConfigTraceGuard::enable();
            assert_eq!(
                add_entailed_bound_lemmas(&mut arena, &triples, &mut relaxed).unwrap(),
                (0, 0)
            );
            crate::config_registry::crossings()
        };
        // The empty case gets its OWN guard. Sharing the one above made this
        // negative VACUOUS: `note_crossed` keeps only the FIRST crossing of a
        // key, so once the key is recorded the set cannot grow again whatever
        // the empty call does, and the mutation that records the empty case as
        // a crossing SURVIVED. A fresh guard is what makes the assertion able
        // to fail.
        let empty = {
            let _g = crate::config_registry::ConfigTraceGuard::enable();
            assert_eq!(
                add_entailed_bound_lemmas(&mut arena, &[], &mut relaxed).unwrap(),
                (0, 0)
            );
            crate::config_registry::crossings()
        };
        assert!(
            empty.is_empty(),
            "an EMPTY product set returns the same (0, 0) and must not be recorded as a \
             crossing; got {empty:?}"
        );
        assert_eq!(
            products,
            vec![(
                "crates/axeyum-solver/src/nia_linearize.rs::MAX_MCCORMICK_PRODUCTS",
                (MAX_MCCORMICK_PRODUCTS + 1) as u64,
                MAX_MCCORMICK_PRODUCTS as u64,
            )]
        );
    }
    // ----------------------------------------------------------------------
    // ADR-2136: order and monotonicity lemmas.
    //
    // Every lemma this pass emits is claimed VALID over the integers — true in
    // every model of the original query. These tests do not take that on the
    // doc comment's word: each schema is driven through all of its sign cases,
    // each emitted lemma is evaluated at faithful integer points by the same
    // checker the debug build runs, and the checker itself is shown able to
    // FAIL (a checker that cannot fail is worse than no checker).
    // ----------------------------------------------------------------------

    /// `a`, `b`, `c` plus the two abstractions `rac ≈ a·c` and `rbc ≈ b·c`,
    /// with the triple list the refinement loop would build.
    #[allow(clippy::type_complexity)]
    fn order_setup() -> (
        TermArena,
        [SymbolId; 5],
        [TermId; 5],
        Vec<(TermId, TermId, TermId)>,
    ) {
        let mut arena = TermArena::new();
        let sa = arena.declare("a", Sort::Int).unwrap();
        let sb = arena.declare("b", Sort::Int).unwrap();
        let sc = arena.declare("c", Sort::Int).unwrap();
        let sac = arena.declare("!nia_0", Sort::Int).unwrap();
        let sbc = arena.declare("!nia_1", Sort::Int).unwrap();
        let (a, b, c) = (arena.var(sa), arena.var(sb), arena.var(sc));
        let (rac, rbc) = (arena.var(sac), arena.var(sbc));
        // `(a·c, rac)` and `(b·c, rbc)`, in the shape `check_with_nia` builds.
        let triples = vec![(a, c, rac), (b, c, rbc)];
        (arena, [sa, sb, sc, sac, sbc], [a, b, c, rac, rbc], triples)
    }

    fn five_point(syms: [SymbolId; 5], vals: [i128; 5]) -> Assignment {
        let mut assignment = Assignment::new();
        for (s, v) in syms.into_iter().zip(vals) {
            assignment.set(s, Value::Int(v));
        }
        assignment
    }

    /// **Every sign case, and each one discriminated.**
    ///
    /// For each of the four `(sign of c, which abstraction is larger)` cases:
    /// a lemma must be emitted, it must be VALID at faithful integer points,
    /// and it must be the right one of the four. The last is checked by two
    /// points per case rather than by reading the term:
    ///
    /// * a point where the hypotheses hold and the intended conclusion is
    ///   violated — the lemma must evaluate FALSE there, which the sibling
    ///   with the opposite conclusion would not;
    /// * a point where `c` has the OTHER sign — the lemma must evaluate TRUE
    ///   there (its `c` hypothesis is unmet), which the sibling with the
    ///   opposite `c` hypothesis would not.
    ///
    /// Without those two points the test would pass on any lemma at all that
    /// happened to be valid.
    #[test]
    fn order_lemma_covers_all_four_sign_cases_and_each_is_discriminated() {
        // (c_val, rac_val, rbc_val, a_val, b_val, expects `a ≥ b`)
        let cases: [(i128, i128, i128, i128, i128, bool); 4] = [
            // c > 0, ac ≥ bc ⇒ a ≥ b, violated because the model has a < b
            (2, 7, 1, 1, 3, true),
            // c > 0, ac ≤ bc ⇒ a ≤ b, violated because the model has a > b
            (2, 1, 7, 3, 1, false),
            // c < 0, ac ≥ bc ⇒ a ≤ b, violated because the model has a > b
            (-2, 7, 1, 3, 1, false),
            // c < 0, ac ≤ bc ⇒ a ≥ b, violated because the model has a < b
            (-2, 1, 7, 1, 3, true),
        ];
        for (c_val, rac_val, rbc_val, a_val, b_val, expect_a_ge_b) in cases {
            let (mut arena, syms, [a, b, c, rac, rbc], triples) = order_setup();
            let zero = arena.int_const(0);
            let lemma = order_lemma_at_model(
                &mut arena, c, a, b, rac, rbc, c_val, a_val, b_val, rac_val, rbc_val, zero,
            )
            .unwrap()
            .unwrap_or_else(|| panic!("no order lemma at c={c_val} rac={rac_val} rbc={rbc_val}"));

            lemma_holds_at_faithful_points(&arena, lemma, &triples, &[0, 1], 400)
                .unwrap_or_else(|why| panic!("order lemma at c={c_val} is not valid: {why}"));

            // Discriminates the CONCLUSION: hypotheses met, conclusion broken.
            let (bad_a, bad_b) = if expect_a_ge_b { (1, 3) } else { (3, 1) };
            let hyp_met = five_point(syms, [bad_a, bad_b, c_val, rac_val, rbc_val]);
            assert!(
                !holds(&arena, lemma, &hyp_met),
                "c={c_val} rac={rac_val}: the lemma must be false where its own \
                 hypotheses hold and its conclusion does not — if it is true here \
                 the emitted conclusion points the wrong way"
            );

            // Discriminates the HYPOTHESIS on `c`: flip only `c`'s sign.
            let c_flipped = five_point(syms, [bad_a, bad_b, -c_val, rac_val, rbc_val]);
            assert!(
                holds(&arena, lemma, &c_flipped),
                "c={c_val} rac={rac_val}: with `c`'s sign flipped the hypothesis is \
                 unmet and the lemma must be vacuously true — if it is false here \
                 the emitted `c` hypothesis has the wrong sign"
            );
        }
    }

    /// The pass is MODEL-DRIVEN, so it must emit nothing when the model already
    /// satisfies the implication — otherwise the "cap" on emissions is the only
    /// thing standing between us and the 9,407,886 shared-factor pairs the
    /// sizing census found on one file.
    #[test]
    fn order_lemma_emits_nothing_when_the_model_already_satisfies_it() {
        let (mut arena, _syms, [a, b, c, rac, rbc], _t) = order_setup();
        let zero = arena.int_const(0);
        // c > 0, rac > rbc ⇒ a ≥ b, and the model HAS a ≥ b.
        assert!(
            order_lemma_at_model(&mut arena, c, a, b, rac, rbc, 2, 5, 1, 7, 1, zero)
                .unwrap()
                .is_none()
        );
        // c = 0: every implication is vacuous, nothing to cut.
        assert!(
            order_lemma_at_model(&mut arena, c, a, b, rac, rbc, 0, 1, 3, 7, 1, zero)
                .unwrap()
                .is_none()
        );
        // rac = rbc: the four ordered cases do not apply (the EQ lemma does).
        assert!(
            order_lemma_at_model(&mut arena, c, a, b, rac, rbc, 2, 1, 3, 4, 4, zero)
                .unwrap()
                .is_none()
        );
    }

    /// `c ≠ 0 ∧ ac = bc → a = b` — the case the four ordered implications
    /// structurally cannot reach, and the control that they cannot: the same
    /// model produces `None` from `order_lemma_at_model` above.
    #[test]
    fn the_order_equality_lemma_covers_what_the_four_cannot() {
        let (mut arena, syms, [a, b, c, rac, rbc], triples) = order_setup();
        let zero = arena.int_const(0);
        let lemma = order_eq_lemma_at_model(&mut arena, c, a, b, rac, rbc, -3, 1, 3, 4, 4, zero)
            .unwrap()
            .expect("rac = rbc with a != b and c != 0 must produce the equality lemma");
        lemma_holds_at_faithful_points(&arena, lemma, &triples, &[0, 1], 400).unwrap();

        // Hypotheses met, conclusion broken.
        assert!(!holds(&arena, lemma, &five_point(syms, [1, 3, -3, 4, 4])));
        // `c = 0` leaves the hypothesis unmet.
        assert!(holds(&arena, lemma, &five_point(syms, [1, 3, 0, 4, 4])));
        // The abstractions differing leaves the hypothesis unmet.
        assert!(holds(&arena, lemma, &five_point(syms, [1, 3, -3, 4, 5])));

        // And it emits nothing where it does not apply.
        assert!(
            order_eq_lemma_at_model(&mut arena, c, a, b, rac, rbc, -3, 2, 2, 4, 4, zero)
                .unwrap()
                .is_none(),
            "a = b in the model: the conclusion is not violated"
        );
    }

    /// **All four sign quadrants, both directions.** `monotonicity_lemma_lt`
    /// fires when the relaxation's `r` is too SMALL in magnitude and
    /// `..._gt` when it is too large; each must be valid in every quadrant of
    /// `(sign a, sign b)`.
    #[test]
    fn monotone_lemmas_are_valid_in_every_quadrant_in_both_directions() {
        for (a_val, b_val) in [(3_i128, 5_i128), (3, -5), (-3, 5), (-3, -5)] {
            let p = a_val * b_val;
            for (name, r_val) in [("lt", 0_i128), ("gt", p * 4)] {
                let (mut arena, _s, [a, b, _c, _rac, _rbc], _t) = order_setup();
                let sr = arena.declare("!nia_m", Sort::Int).unwrap();
                let r = arena.var(sr);
                let triples = vec![(a, b, r)];
                let zero = arena.int_const(0);
                let lemmas =
                    monotone_lemmas_at_model(&mut arena, a, b, r, a_val, b_val, r_val, zero)
                        .unwrap();
                assert_eq!(
                    lemmas.len(),
                    1,
                    "{name}: a={a_val} b={b_val} r={r_val} must produce exactly one lemma"
                );
                lemma_holds_at_faithful_points(&arena, lemmas[0], &triples, &[0], 400)
                    .unwrap_or_else(|why| panic!("{name} at a={a_val} b={b_val}: {why}"));
            }
        }
    }

    /// A faithful product emits nothing, and a zero factor emits nothing — the
    /// zero case is owned by `sign_lemmas` (`a = 0 → r = 0`), and z3 likewise
    /// routes a zero away from this lemma (`mon_has_zero`).
    #[test]
    fn monotone_lemmas_skip_the_faithful_and_the_zero_factor() {
        let (mut arena, _s, [a, b, _c, _rac, _rbc], _t) = order_setup();
        let sr = arena.declare("!nia_m", Sort::Int).unwrap();
        let r = arena.var(sr);
        let zero = arena.int_const(0);
        assert!(
            monotone_lemmas_at_model(&mut arena, a, b, r, 3, 5, 15, zero)
                .unwrap()
                .is_empty(),
            "r = a·b exactly: nothing to cut off"
        );
        assert!(
            monotone_lemmas_at_model(&mut arena, a, b, r, 0, 5, 99, zero)
                .unwrap()
                .is_empty(),
            "a zero factor belongs to the sign lemmas"
        );
    }

    /// **The sign-pinning literal in the `gt` variant is load-bearing.**
    ///
    /// z3 adds a SECOND literal per factor there (`nla_monotone_lemmas.cpp:66-68`)
    /// and this test is why: built without it, the hypothesis `a ≥ a_val` admits
    /// a factor of the opposite sign and unbounded magnitude, and the conclusion
    /// is false at such a point. The weakened lemma is constructed here BY HAND
    /// — the shipped builder is never asked to produce it — so this is a control
    /// on the design claim and not a test of dead code.
    #[test]
    fn monotone_gt_without_the_sign_pin_is_refutable() {
        let (mut arena, _s, [a, b, _c, _rac, _rbc], _t) = order_setup();
        let sr = arena.declare("!nia_m", Sort::Int).unwrap();
        let r = arena.var(sr);
        let triples = vec![(a, b, r)];
        let (a_val, b_val) = (-2_i128, 3_i128);
        let p = a_val * b_val; // -6

        // The WEAKENED hypothesis: the far half only, sign pin dropped.
        let a_const = arena.int_const(a_val);
        let b_const = arena.int_const(b_val);
        let p_const = arena.int_const(p);
        let weak_a = arena.int_ge(a, a_const).unwrap();
        let weak_b = arena.int_le(b, b_const).unwrap();
        let concl = arena.int_ge(r, p_const).unwrap();
        let hyp = arena.and(weak_a, weak_b).unwrap();
        let weakened = arena.implies(hyp, concl).unwrap();
        assert!(
            lemma_holds_at_faithful_points(&arena, weakened, &triples, &[0], 400).is_err(),
            "the sign-pinned half is not decoration: without it the lemma is FALSE \
             at faithful integer points"
        );

        // The shipped builder's version of the same case IS valid.
        let zero = arena.int_const(0);
        let lemmas =
            monotone_lemmas_at_model(&mut arena, a, b, r, a_val, b_val, p * 4, zero).unwrap();
        assert_eq!(lemmas.len(), 1);
        lemma_holds_at_faithful_points(&arena, lemmas[0], &triples, &[0], 400).unwrap();
    }

    /// **The validity checker must be able to fail.** Two ways it could be
    /// useless: it passes an invalid lemma, or it passes because it examined
    /// nothing. Both are asserted here, against a lemma that is plainly false
    /// (`a ≥ b` unconditionally) and against a zero-point budget.
    #[test]
    fn the_lemma_validity_checker_can_fail_and_says_which_way() {
        let (mut arena, _s, [a, b, _c, _rac, _rbc], triples) = order_setup();
        let false_lemma = arena.int_ge(a, b).unwrap();
        let err = lemma_holds_at_faithful_points(&arena, false_lemma, &triples, &[0, 1], 400)
            .expect_err("an unconditional `a ≥ b` is not valid and must be caught");
        assert!(err.contains("FALSE at a faithful integer point"), "{err}");

        let trivially_true = arena.int_ge(a, a).unwrap();
        lemma_holds_at_faithful_points(&arena, trivially_true, &triples, &[0, 1], 400)
            .expect("a valid lemma must pass");
        let vacuous = lemma_holds_at_faithful_points(&arena, trivially_true, &triples, &[0, 1], 0)
            .expect_err("examining zero points is not evidence and must be reported");
        assert!(vacuous.contains("examined nothing"), "{vacuous}");
    }

    /// The shared-factor index is what decides which pairs are examined, so its
    /// order is part of the determinism promise. It must also drop a factor
    /// that appears in only one product — there is no pair to couple.
    #[test]
    fn the_shared_factor_index_is_deterministic_and_drops_lone_factors() {
        let (mut arena, _s, [a, b, c, rac, rbc], _t) = order_setup();
        let sd = arena.declare("d", Sort::Int).unwrap();
        let se = arena.declare("!nia_2", Sort::Int).unwrap();
        let (d, rde) = (arena.var(sd), arena.var(se));
        let triples = vec![(a, c, rac), (b, c, rbc), (d, d, rde)];
        let first = shared_factor_index(&triples);
        let again = shared_factor_index(&triples);
        assert_eq!(
            first.keys().copied().collect::<Vec<_>>(),
            again.keys().copied().collect::<Vec<_>>()
        );
        assert_eq!(first.get(&c).map(Vec::len), Some(2), "c is shared by two");
        assert!(first.get(&a).is_none(), "`a` is in one product only");
        assert!(
            first.get(&d).is_none(),
            "`d·d` is ONE monomial: a lone square is not a pair, so `d` must not \
             enter the index (the same distinction the sizing census's \
             `lone-square-is-not-a-pair` control pins)"
        );
    }

    /// `other_operand` on a square must return the factor itself: `c·c` read as
    /// `a·c` has `a = c`, which is correct and not a degenerate case to skip.
    #[test]
    fn the_other_operand_of_a_square_is_the_factor_itself() {
        let (_arena, _s, [_a, _b, c, rac, _rbc], _t) = order_setup();
        assert_eq!(other_operand((c, c, rac), c), c);
    }

    /// **The soundness-negative fixture.**
    ///
    /// A SATISFIABLE system with a NEGATIVE shared factor, every model of which
    /// has `a < b`:
    ///
    /// ```text
    /// 1 ≤ a ≤ 8,  3 ≤ b ≤ 10,  −20 ≤ c ≤ −2,  a + 2 ≤ b,  a·c + b·c = −20
    /// ```
    ///
    /// witnessed at `(a, b, c) = (1, 3, −5)`. Because `c < 0` and `a < b`, this
    /// witness satisfies `c < 0 ∧ a·c ≥ b·c`, so the `c < 0` case of the order
    /// lemma applies to it and concludes `a ≤ b`. Get that sign case backwards
    /// and the lemma reads `a ≥ b`, which the witness violates -- the relaxation
    /// loses its only models and the query is refuted. **The assertion is that
    /// every lemma this pass builds is TRUE at the witness**, so a sign-case
    /// mistake shows up as a satisfiable system being cut away.
    ///
    /// **Why the pass is driven directly instead of through a solve.** Three
    /// drafts of this fixture called `check_with_nia_armed` and were green
    /// having built no lemma at all: the DPLL(T) relaxation's very first model
    /// was faithful every time (once because `a` and `b` were pinned, once
    /// because `c`'s window of 4 sent the products through
    /// `small_domain_lemmas`' exact case split, and once just because the
    /// engine picked a corner of the box). Depending on which vertex a linear
    /// engine happens to choose is not a fixture. So the spurious models are
    /// written down HERE -- one per direction of the `rac` / `rbc` relation,
    /// because a flipped sign case and the shipped code never emit at the same
    /// model -- and `built > 0` is asserted so the test cannot pass by
    /// examining nothing. The end-to-end no-refutation property is covered by
    /// `shared_factor_systems_agree_across_both_arms_and_keep_their_witness`
    /// over 48 generated systems.
    #[test]
    fn a_negative_shared_factor_must_not_cut_away_a_satisfiable_systems_models() {
        let mut arena = TermArena::new();
        let sa = arena.declare("a", Sort::Int).unwrap();
        let sb = arena.declare("b", Sort::Int).unwrap();
        let sc = arena.declare("c", Sort::Int).unwrap();
        let sac = arena.declare("!nia_0", Sort::Int).unwrap();
        let sbc = arena.declare("!nia_1", Sort::Int).unwrap();
        let (a, b, c) = (arena.var(sa), arena.var(sb), arena.var(sc));
        let (rac, rbc) = (arena.var(sac), arena.var(sbc));

        // The system, and the witness CHECKED rather than assumed -- a fixture
        // that is quietly unsat cannot fail for the reason it was written for.
        let mut assertions = Vec::new();
        for (t, lo, hi) in [(a, 1_i128, 8_i128), (b, 3, 10), (c, -20, -2)] {
            let k_lo = arena.int_const(lo);
            let k_hi = arena.int_const(hi);
            assertions.push(arena.int_ge(t, k_lo).unwrap());
            assertions.push(arena.int_le(t, k_hi).unwrap());
        }
        let two = arena.int_const(2);
        let a_plus_two = arena.int_add(a, two).unwrap();
        assertions.push(arena.int_le(a_plus_two, b).unwrap());
        let ac = arena.int_mul(a, c).unwrap();
        let bc = arena.int_mul(b, c).unwrap();
        let sum = arena.int_add(ac, bc).unwrap();
        let neg_twenty = arena.int_const(-20);
        assertions.push(arena.eq(sum, neg_twenty).unwrap());

        let (av, bv, cv) = (1_i128, 3_i128, -5_i128);
        let mut witness = Assignment::new();
        witness.set(sa, Value::Int(av));
        witness.set(sb, Value::Int(bv));
        witness.set(sc, Value::Int(cv));
        for &asrt in &assertions {
            assert!(
                holds(&arena, asrt, &witness),
                "the fixture must be satisfiable at (a,b,c) = ({av},{bv},{cv})"
            );
        }
        // The witness extended to the abstractions, which is the assignment the
        // lemmas have to survive: `rac = a·c`, `rbc = b·c`.
        witness.set(sac, Value::Int(av * cv));
        witness.set(sbc, Value::Int(bv * cv));

        let triples = vec![(a, c, rac), (b, c, rbc)];
        let index = shared_factor_index(&triples);
        assert_eq!(index.len(), 1, "`c` is the one shared factor");

        // Two SPURIOUS relaxation models, differing only in which abstraction
        // the relaxation made larger. Both keep `rac + rbc = −20`, so both are
        // models the relaxation could actually hand back.
        let spurious: [(i128, i128); 2] = [(-15, -5), (0, -20)];
        let mut built = 0usize;
        for (rac_v, rbc_v) in spurious {
            let mut model = Model::new();
            model.set(sa, Value::Int(av));
            model.set(sb, Value::Int(bv));
            model.set(sc, Value::Int(cv));
            model.set(sac, Value::Int(rac_v));
            model.set(sbc, Value::Int(rbc_v));
            let lemmas = order_and_monotone_lemmas(&mut arena, &triples, &index, &model).unwrap();
            for cl in &lemmas {
                assert!(
                    holds(&arena, cl.lemma, &witness),
                    "a lemma built at the spurious model (rac={rac_v}, rbc={rbc_v}) is \
                     FALSE at (a,b,c) = ({av},{bv},{cv}), a real model of the query -- \
                     the pass is cutting away a SATISFIABLE system's only models"
                );
                lemma_holds_at_faithful_points(&arena, cl.lemma, &triples, &cl.depends_on, 400)
                    .unwrap_or_else(|why| panic!("lemma is not valid over the integers: {why}"));
            }
            built += lemmas.len();
        }
        assert!(
            built > 0,
            "no lemma was built at EITHER spurious model, so this fixture examined \
             nothing and its green is not evidence"
        );
    }

    /// **The fuzz seed class: shared-factor monomial systems.**
    ///
    /// A family of systems `x·z`, `y·z` with a sign constraint on the shared
    /// factor `z` -- the shape where an order lemma is the decisive step -- run
    /// through BOTH arms of the lever. It is a unit test rather than an
    /// oracle-backed fuzz because the property needs no oracle: each system is
    /// generated together with a WITNESS, so neither arm may return `unsat`,
    /// and the two arms must never disagree.
    ///
    /// The generator's shape is taken from the sizing census rather than from
    /// convenience. The factors are **not** two-sidedly bounded, because on the
    /// 116 undecided `QF_NIA` rows `unbounded_products` equals `products` at
    /// every quantile -- with a bounded box the McCormick envelopes make the
    /// very first relaxation model faithful, the replay accepts it, and the
    /// pass under test never runs at all. An earlier draft of this test did
    /// exactly that and was green over 48 systems having built zero lemmas,
    /// which is why `LEMMAS_BUILT` is asserted here.
    ///
    /// `z = 0` is generated deliberately: `c ≠ 0` is the order lemma's
    /// precondition, and a generator that structurally cannot emit the
    /// degenerate shared factor is not a soundness gate on it -- the `a946f925`
    /// shape, where a differential fuzz passed because it only ever emitted
    /// variable divisors.
    #[test]
    fn shared_factor_systems_agree_across_both_arms_and_keep_their_witness() {
        let config = SolverConfig::default().with_timeout(Duration::from_millis(1_500));
        let mut state: u64 = 0xDEAD_BEEF_1234_5678;
        let mut next = move |m: i128| -> i128 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            i128::from((state >> 33) as u32).rem_euclid(2 * m + 1) - m
        };
        let mut cases = 0usize;
        let mut zero_factor_cases = 0usize;
        let mut reached_the_pass = 0usize;
        let mut gained = 0usize;
        for _ in 0..48 {
            // `x = y + d` with `d ≠ 0`, and `(x − y)·z = d·z` pinned, so the
            // system is satisfiable exactly at the generated `(yv, zv)` line
            // and `z`'s sign is asserted rather than derived.
            let yv = next(6);
            let d = {
                let raw = next(5);
                if raw == 0 { 3 } else { raw }
            };
            let zv = next(2);
            let xv = yv + d;
            if zv == 0 {
                zero_factor_cases += 1;
            }

            let mut arena = TermArena::new();
            let sx = arena.declare("x", Sort::Int).unwrap();
            let sy = arena.declare("y", Sort::Int).unwrap();
            let sz = arena.declare("z", Sort::Int).unwrap();
            let (x, y, z) = (arena.var(sx), arena.var(sy), arena.var(sz));
            let mut assertions = Vec::new();

            // x − y = d. No two-sided bound on any of x, y, z: that is the
            // point (see the doc comment).
            let d_const = arena.int_const(d);
            let diff = arena.int_sub(x, y).unwrap();
            assertions.push(arena.eq(diff, d_const).unwrap());
            // The sign constraint on the SHARED factor, one-sided.
            let zero = arena.int_const(0);
            match zv.signum() {
                1 => assertions.push(arena.int_gt(z, zero).unwrap()),
                -1 => assertions.push(arena.int_lt(z, zero).unwrap()),
                _ => assertions.push(arena.int_le(z, zero).unwrap()),
            }
            // x·z − y·z = d·z, the two monomials that share `z`.
            let xz = arena.int_mul(x, z).unwrap();
            let yz = arena.int_mul(y, z).unwrap();
            let delta = arena.int_sub(xz, yz).unwrap();
            let target = arena.int_const(d * zv);
            assertions.push(arena.eq(delta, target).unwrap());

            let mut witness = Assignment::new();
            witness.set(sx, Value::Int(xv));
            witness.set(sy, Value::Int(yv));
            witness.set(sz, Value::Int(zv));
            assert!(
                assertions.iter().all(|&t| holds(&arena, t, &witness)),
                "generated system is not satisfiable at ({xv},{yv},{zv})"
            );

            let mut verdicts = Vec::new();
            for armed in [false, true] {
                LEMMAS_BUILT.with(|n| n.set(0));
                let mut why = None;
                let mut work = arena.clone();
                let got = check_with_nia_armed(&mut work, &assertions, &config, &mut why, armed)
                    .expect("no solver error");
                assert!(
                    !matches!(got, Some(CheckResult::Unsat)),
                    "armed={armed}: ({xv},{yv},{zv}) has a witness and was refuted \
                     (why={why:?})"
                );
                let built = LEMMAS_BUILT.with(std::cell::Cell::get);
                if armed {
                    reached_the_pass += usize::from(built > 0);
                } else {
                    assert_eq!(
                        built, 0,
                        "the DISARMED arm reached the pass: the lever does not gate it"
                    );
                }
                verdicts.push(matches!(got, Some(CheckResult::Sat(_))));
            }
            // The two arms may DIFFER in how much they decide -- deciding more
            // is the whole point of the arm -- but they may never CONFLICT, and
            // the shipped arm may never lose a decision it had. `unsat` is
            // already refused above on every system, so the only conflict left
            // to rule out is the armed arm dropping a `sat` the shipped arm
            // found.
            assert!(
                verdicts[1] || !verdicts[0],
                "({xv},{yv},{zv}): the shipped arm decided `sat` and the armed arm \
                 did not -- the lemma pass cost a decision"
            );
            gained += usize::from(verdicts[1] && !verdicts[0]);
            cases += 1;
        }
        assert_eq!(cases, 48, "the generator must run every case");
        assert!(
            zero_factor_cases > 0,
            "the seed class must emit the DEGENERATE shared factor `z = 0` -- a \
             generator that structurally cannot produce it is not a soundness \
             gate on the order lemma's `c != 0` precondition (the a946f925 shape)"
        );
        assert!(
            reached_the_pass > 0,
            "the armed arm built NO lemma on ANY of the {cases} generated systems, \
             so this test is a measurement of the shipped route and says nothing \
             about the arm it claims to fuzz"
        );
        // Not a ratchet on the corpus -- this is a generated family, and what it
        // is worth on real files is §4's A/B, not this number. It is pinned so
        // that a change which silently makes the arm inert on the shape the
        // lane exists for fails HERE, where it is cheap to see, rather than
        // showing up as a null A/B result weeks later.
        assert!(
            gained > 0,
            "the armed arm decided nothing the shipped arm did not on any of the \
             {cases} shared-factor systems"
        );
    }

    /// **The disarmed lever changes nothing.** `0` is the shipped arm and the
    /// refinement round must be the round it is today — the index is never
    /// built, so `timed_refine` cannot reach the new pass at all.
    #[test]
    fn the_disarmed_lever_is_the_shipped_arm() {
        assert_eq!(
            NIA_ORDER_LEMMAS_ARMED, 0,
            "ADR-2136 ships DISARMED until an interleaved A/B says otherwise"
        );
    }
}

/// Roadmap 2.11 — this file's narrowing site, `replay_sat`.
///
/// `replay_sat` checks the ORIGINAL assertions against `model.to_assignment()`
/// and then emitted a model carrying **symbol entries only** — dropping
/// function interpretations, `real_div_zero`, `uninterpreted_cardinalities` and
/// the quantified sat certificates. It is the widest loss of the eleven sites
/// item 2.11 lists, and the row does not mention the function drop at all.
#[cfg(test)]
mod sound2_narrowing_site_tests {
    use super::replay_sat;
    use crate::backend::CheckResult;
    use crate::model::Model;
    use axeyum_ir::{FuncValue, Rational, Sort, TermArena, Value};

    /// DIES ON: rebuilding the emitted model in `replay_sat` instead of
    /// narrowing the one the replay ran against.
    #[test]
    fn replay_sat_keeps_every_component_the_replay_saw() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).expect("declare x");
        let internal = arena
            .declare_internal("!nia_scratch", Sort::Int)
            .expect("declare internal");
        let func = arena
            .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
            .expect("declare f");
        let opaque = arena.declare_uninterpreted_sort("U");

        // One assertion, true under x = 3, mentioning only `x`.
        let three = arena.int_const(3);
        let xv = arena.var(x);
        let assertion = arena.eq(xv, three).expect("eq");

        let mut model = Model::new();
        model.set(x, Value::Int(3));
        model.set(internal, Value::Int(9));
        model.set_function(
            func,
            FuncValue::constant(vec![Sort::BitVec(8)], Sort::BitVec(8), 4).define(&[1], 2),
        );
        model.set_real_div_zero(Rational::integer(5), Rational::integer(100));
        model.set_uninterpreted_cardinality(opaque, 3);

        let Some(CheckResult::Sat(clean)) = replay_sat(&arena, &[assertion], &model) else {
            panic!("the fixture must replay true, or this test measures nothing");
        };

        assert_eq!(clean.get(internal), None, "the `!nia_` scaffolding symbol");
        assert_eq!(clean.get(x), Some(Value::Int(3)), "x");
        assert!(
            clean.function(func).is_some(),
            "the UF interpretation the replay consulted was dropped from the emitted \
             certificate (the 9b259f7c2 shape)"
        );
        assert_eq!(
            clean.real_div_zero(Rational::integer(5)),
            Some(Rational::integer(100)),
            "the division-at-zero witness was dropped (the c41dd4264 shape)"
        );
        assert_eq!(
            clean.uninterpreted_cardinality(opaque),
            Some(3),
            "the declared carrier size was dropped, and no `to_assignment` replay \
             would have told you"
        );
    }
}
