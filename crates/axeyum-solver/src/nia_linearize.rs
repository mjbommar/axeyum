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
