//! `Nat.factorization : ℕ → Nat.Multiset` — the COMPUTED prime factorization,
//! with `prod (factorization n) = n` and every element prime.
//!
//! # What this closes
//!
//! `multiset.rs` landed UNIQUENESS of prime factorization
//! (`Nat.Multiset.count_eq_of_prod_eq`) without ever naming "the"
//! factorization of anything, and `factorization.rs` landed EXISTENCE
//! (`Nat.exists_prime_factorization`) as an anonymous `(k, f)` pair inside an
//! `Exists`. Neither gives a FUNCTION. This module does:
//!
//! ```text
//! Nat.factorizationAux 0        n := Multiset.zero
//! Nat.factorizationAux (succ j) n := if n ≤ 1 then Multiset.zero
//!                                    else Multiset.singleton (minFac n)
//!                                         + factorizationAux j (n / minFac n)
//! Nat.factorization n := factorizationAux n n
//! ```
//!
//! and proves `Nat.prod_factorization : ∀ n, 0 < n → prod (factorization n) = n`
//! together with `Nat.factorization_prime : ∀ n x, 0 < count (factorization n) x
//! → prime_condition x`. With uniqueness already in hand, the three together
//! are the Fundamental Theorem of Arithmetic in computed form.
//!
//! # The fuel is `n`, and the induction carries `n ≤ fuel`
//!
//! `Nat.prodFactorizationAux : ∀ fuel n, 0 < n → n ≤ fuel →
//! prod (factorizationAux fuel n) = n`. Both hypotheses are load-bearing and
//! neither is bookkeeping:
//!
//! - `0 < n` rules out `n = 0`, where the guard `n ≤ 1` is TRUE and the answer
//!   would be `prod zero = 1 ≠ 0`. The statement is false without it.
//! - `n ≤ fuel` makes the fuel-exhaustion case VACUOUS rather than wrong:
//!   `0 < n` and `n ≤ 0` cannot both hold, so the base case is discharged by
//!   contradiction and never has to claim `prod zero = n`.
//!
//! The recursive step needs `n / minFac n ≤ j`, which is where
//! `Nat.div_lt_self` and `Nat.min_fac_two_le` (`min_fac_dvd.rs`) come in: the
//! quotient is strictly smaller because the divisor is at least `2`, and
//! `n ≤ succ j` then bounds it by `j`. It also needs `0 < n / minFac n`, which
//! comes from `minFac n * (n / minFac n) = n` (`Nat.div_mul_cancel_of_dvd`) by
//! a case split on the quotient: at `0` the product is `0`, contradicting
//! `0 < n`.
//!
//! # Guards are decided by the CASE SPLIT, not the other way round
//!
//! Every proof below splits on `n` against `2` first (`cases_lt_or_ge`) and
//! then DERIVES the guard's Boolean value in each branch
//! (`ble_eq_true_of_le` / `ble_eq_false_of_lt`), transporting the goal along
//! that one equation. Splitting on the guard instead would demand a proof in
//! the branch that cannot occur, which is exactly the branch with no
//! information in it.
//!
//! # `prod (singleton a) = a` is not free
//!
//! `Nat.Multiset.prod_singleton` needs the fold over `[0, a)` to collapse,
//! which is `Nat.prodRange_eq_one_of_below` (new here: the hypothesis has to
//! live INSIDE the induction's motive, since the bound moves), plus
//! `Nat.Multiset.count_singleton_self` and `count_singleton_of_ne`. Note
//! `pow a 1 ≡ mul (pow a 0) a ≡ mul 1 a` reduces only that far: `Nat.mul`
//! recurses on its RIGHT argument, so `mul 1 a` is STUCK for symbolic `a` and
//! the last step is `Nat.one_mul`, not reduction.
//!
//! Every helper hoists each sub-expression into its own `let` before passing it
//! to a `NatOps` method (`&mut NatDev` cannot be reborrowed twice in one call),
//! per this development's house rule.

use super::NatPrelude;
use super::finite::{select_nat_false, select_nat_true};
use super::multiset::{ms_count, ms_prod, prod_range};
use super::ops::{NatDev, NatOps, bool_true_or_false, cases_lt_or_ge, cases_zero_succ};
use super::primes::prime_condition;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::name::NameId;

/// `∀ binders, stmt`, proved by `proof`. A local copy of the same helper in
/// `multiset.rs` / `multiset_prod.rs` / `min_fac_dvd.rs`, per this
/// development's per-file-copy convention.
fn declare_forall(
    d: &mut NatDev<'_>,
    name: NameId,
    binders: &[(u64, ExprId)],
    stmt: ExprId,
    proof: ExprId,
) -> Result<(), KernelError> {
    let mut ty = stmt;
    let mut value = proof;
    for &(fv, binder_ty) in binders.iter().rev() {
        ty = d.pi_fv(fv, binder_ty, ty);
        value = d.lam_fv(fv, binder_ty, value);
    }
    d.declare_theorem(name, ty, value)
}

/// `False.rec` into `target` from a proof of `False`.
fn from_false(d: &mut NatDev<'_>, p: &NatPrelude, false_proof: ExprId, target: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `Or.rec` at a `Prop` goal.
#[allow(clippy::too_many_arguments)]
fn or_cases(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_minor: ExprId,
    right_minor: ExprId,
    proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let split_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, split_ty, goal, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        rec,
        &[left_ty, right_ty, motive, left_minor, right_minor, proof],
    )
}

/// The carrier constant `Nat.Multiset`.
fn multiset_ty(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    d.kernel().const_(p.multiset, vec![])
}

/// `Nat.Multiset.singleton a`.
fn ms_singleton(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId) -> ExprId {
    d.const_app(p.multiset_singleton, &[a])
}

/// Computational `if condition then on_true else on_false` at
/// `Nat.Multiset` — the carrier's twin of [`NatOps::bool_select_nat`].
fn bool_select_ms(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let ms = multiset_ty(d, p);
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, ms, BinderInfo::Default);
    let one = d.level_one();
    let rec = d.kernel().const_(p.logic.bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// A goal that MENTIONS a `Bool` guard, proved at the guard's known value and
/// transported back. `heq : Eq Bool guard value` and a proof of
/// `goal_at(value)` give a proof of `goal_at(guard)`.
///
/// This is the shape every proof in this module needs, because the case split
/// is on `n` (against `2`) and the guard's value is a CONSEQUENCE of that
/// split — a two-sided split on the guard itself would demand a proof in a
/// branch that cannot occur.
fn transport_bool_guard(
    d: &mut NatDev<'_>,
    guard: ExprId,
    value: ExprId,
    heq: ExprId,
    goal_at: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    proof_at_value: ExprId,
) -> ExprId {
    let motive = d.bool_eq_motive(value, goal_at);
    let back = d.bool_symm(guard, value, heq);
    d.bool_transport(value, motive, proof_at_value, guard, back)
}

/// `Lt a b ⊢ Not (Eq a b)`.
fn ne_of_lt(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let p = *p;
    let eq_ty = d.eq(a, b);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let motive = d.eq_motive(a, &|d, x| d.lt(x, b));
    let moved = d.transport(a, motive, hlt, b, h);
    let contradiction = d.lemma(p.not_succ_le_self, &[b, moved]);
    d.lam_fv(h_fv, eq_ty, contradiction)
}

/// `Nat.prodRange_eq_one_of_below : ∀ f k, (∀ i, Lt i k → Eq (f i) 1) →
/// Eq (prodRange f k) 1`.
///
/// The hypothesis lives INSIDE the induction's motive, because the bound moves:
/// at `succ j` the induction hypothesis needs the premise restricted to `j`,
/// which `le_step` supplies from the premise at `succ j`.
fn declare_prod_range_eq_one(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let below_ty = |d: &mut NatDev<'_>, bound: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let lt = d.lt(i, bound);
        let fi = d.apply(f, &[i]);
        let one = d.num(1);
        let concl = d.eq(fi, one);
        let body = d.arrow(lt, concl);
        d.pi_fv(i_fv, nat, body)
    };

    let claim = |d: &mut NatDev<'_>, bound: ExprId| -> ExprId {
        let hyp = below_ty(d, bound);
        let fold = prod_range(d, &p, f, bound);
        let one = d.num(1);
        let concl = d.eq(fold, one);
        d.arrow(hyp, concl)
    };
    let base = |d: &mut NatDev<'_>| -> ExprId {
        let zero = d.zero();
        let hyp = below_ty(d, zero);
        let h_fv = d.fresh_fvar();
        let one = d.num(1);
        let body = d.refl(one);
        d.lam_fv(h_fv, hyp, body)
    };
    let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let succ_j = d.succ(j);
        let hyp = below_ty(d, succ_j);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // Restrict the premise from `succ j` to `j`: `Lt i j` is `Le (succ i) j`,
        // and `le_step` weakens it to `Le (succ i) (succ j)`.
        let restricted = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lt_ty = d.lt(i, j);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);
            let succ_i = d.succ(i);
            let weakened = d.lemma(p.le_step, &[succ_i, j, hi]);
            let applied = d.apply(h, &[i, weakened]);
            let with_hi = d.lam_fv(hi_fv, lt_ty, applied);
            d.lam_fv(i_fv, nat, with_hi)
        };
        let below_one = d.apply(ih, &[restricted]);

        let fold_j = prod_range(d, &p, f, j);
        let fj = d.apply(f, &[j]);
        let start = d.mul(fold_j, fj);
        let one = d.num(1);
        let mid = d.mul(one, fj);
        let s1 = d.congr(fold_j, one, below_one, &|d, y| d.mul(y, fj));
        let lt_self = d.lemma(p.le_refl_thm, &[succ_j]);
        let fj_one = d.apply(h, &[j, lt_self]);
        let mid2 = d.mul(one, one);
        let s2 = d.congr(fj, one, fj_one, &|d, y| d.mul(one, y));
        let (_, proof) = d.chain(start, &[(mid, s1), (mid2, s2)]);
        // `mul 1 1` is a closed numeral and reduces to `1`.
        d.lam_fv(h_fv, hyp, proof)
    };
    let proof = d.induct(&claim, &base, &step, k);
    let stmt = claim(d, k);
    declare_forall(
        d,
        p.prod_range_eq_one_of_below,
        &[(f_fv, fn_ty), (k_fv, nat)],
        stmt,
        proof,
    )
}

/// `Nat.Multiset.count_singleton_self` and
/// `Nat.Multiset.count_singleton_of_ne`.
fn declare_count_singleton(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    // count_singleton_self : ∀ a, Eq (count (singleton a) a) 1
    d.theorem(p.multiset_count_singleton_self, 1, &|d, v| {
        let a = v[0];
        let one = d.num(1);
        let zero = d.zero();
        let single = ms_singleton(d, &p, a);
        let succ_a = d.succ(a);
        let below = d.lemma(p.le_refl_thm, &[succ_a]);
        let reads_raw = d.lemma(p.multiset_count_of_lt_bound, &[single, a, below]);
        let guard = d.beq(a, a);
        let guard_true = d.lemma(p.beq_refl, &[a]);
        let selects = select_nat_true(d, guard, one, zero, guard_true);
        let raw_at = {
            let raw = d.const_app(p.multiset_raw, &[single]);
            d.apply(raw, &[a])
        };
        let count = ms_count(d, &p, single, a);
        let proof = d.trans(count, raw_at, one, reads_raw, selects);
        let stmt = d.eq(count, one);
        (stmt, proof)
    })?;

    // count_singleton_of_ne : ∀ a x, Eq Bool (beq x a) false →
    //   Eq (count (singleton a) x) 0
    d.theorem(p.multiset_count_singleton_of_ne, 2, &|d, v| {
        let (a, x) = (v[0], v[1]);
        let one = d.num(1);
        let zero = d.zero();
        let single = ms_singleton(d, &p, a);
        let guard = d.beq(x, a);
        let false_val = d.bool_false();
        let hyp = d.bool_eq(guard, false_val);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let count = ms_count(d, &p, single, x);
        let succ_a = d.succ(a);
        let motive = |d: &mut NatDev<'_>, _y: ExprId| -> ExprId {
            let count = ms_count(d, &p, single, x);
            let zero = d.zero();
            d.eq(count, zero)
        };
        // Below the bound `count` reads `raw`, which is the `beq` selector.
        let small = |d: &mut NatDev<'_>, _y: ExprId, hlt: ExprId| -> ExprId {
            let reads_raw = d.lemma(p.multiset_count_of_lt_bound, &[single, x, hlt]);
            let selects = select_nat_false(d, guard, one, zero, h);
            let raw_at = {
                let raw = d.const_app(p.multiset_raw, &[single]);
                d.apply(raw, &[x])
            };
            let count = ms_count(d, &p, single, x);
            d.trans(count, raw_at, zero, reads_raw, selects)
        };
        // At or above it `count` truncates to `0` with no side condition.
        let big = |d: &mut NatDev<'_>, _y: ExprId, hge: ExprId| -> ExprId {
            d.lemma(p.multiset_count_eq_zero_of_bound_le, &[single, x, hge])
        };
        let body = cases_lt_or_ge(d, &p, x, succ_a, &motive, &small, &big);
        let stmt = {
            let concl = d.eq(count, zero);
            d.arrow(hyp, concl)
        };
        let proof = d.lam_fv(h_fv, hyp, body);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.Multiset.prod_singleton : ∀ a, Eq (prod (singleton a)) a`.
fn declare_prod_singleton(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.multiset_prod_singleton, 1, &|d, v| {
        let a = v[0];
        let one = d.num(1);
        let single = ms_singleton(d, &p, a);
        let counts = d.const_app(p.multiset_count, &[single]);
        let factors = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let cq = d.apply(counts, &[q]);
            let body = d.pow(q, cq);
            d.lam_fv(q_fv, nat, body)
        };

        // Every factor strictly below `a` is `1`: `beq i a` is `false` there,
        // so the count is `0` and `pow i 0 ≡ 1`.
        let below = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let lt_ty = d.lt(i, a);
            let hi_fv = d.fresh_fvar();
            let hi = d.kernel().fvar(hi_fv);
            let ne = ne_of_lt(d, &p, i, a, hi);
            let guard_false = d.lemma(p.beq_eq_false_of_ne, &[i, a, ne]);
            let vanishes = d.lemma(p.multiset_count_singleton_of_ne, &[a, i, guard_false]);
            let ci = ms_count(d, &p, single, i);
            let zero = d.zero();
            let lifted = d.congr(ci, zero, vanishes, &|d, y| d.pow(i, y));
            let to_one = d.lemma(p.pow_zero, &[i]);
            let from = d.pow(i, ci);
            let via = d.pow(i, zero);
            let one = d.num(1);
            let body = d.trans(from, via, one, lifted, to_one);
            let with_hi = d.lam_fv(hi_fv, lt_ty, body);
            d.lam_fv(i_fv, nat, with_hi)
        };
        let lower_fold = prod_range(d, &p, factors, a);
        let lower_one = d.lemma(p.prod_range_eq_one_of_below, &[factors, a, below]);

        // The top factor is `pow a 1`. `Nat.pow` recurses on its exponent, so
        // `pow a 1 ≡ mul (pow a 0) a ≡ mul 1 a` — and `Nat.mul` recurses on its
        // RIGHT argument, so `mul 1 a` is STUCK for symbolic `a`: the last step
        // is `one_mul`, not reduction.
        let ca = ms_count(d, &p, single, a);
        let count_one = d.lemma(p.multiset_count_singleton_self, &[a]);
        let top_lifted = d.congr(ca, one, count_one, &|d, y| d.pow(a, y));
        let top_from = d.pow(a, ca);
        let top_via = d.pow(a, one);
        let collapse = d.lemma(p.one_mul, &[a]);
        let top_eq = d.trans(top_from, top_via, a, top_lifted, collapse);

        let start = d.mul(lower_fold, top_from);
        let mid = d.mul(one, top_from);
        let s1 = d.congr(lower_fold, one, lower_one, &|d, y| d.mul(y, top_from));
        let mid2 = d.mul(one, a);
        let s2 = d.congr(top_from, a, top_eq, &|d, y| d.mul(one, y));
        let s3 = d.lemma(p.one_mul, &[a]);
        let (_, proof) = d.chain(start, &[(mid, s1), (mid2, s2), (a, s3)]);

        let lhs = ms_prod(d, &p, single);
        let stmt = d.eq(lhs, a);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.factorizationAux` and `Nat.factorization`.
fn declare_factorization_defs(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let ms = multiset_ty(d, &p);
    let nat_to_ms = d.arrow(nat, ms);

    // factorizationAux : Nat -> Nat -> Multiset
    {
        let zero_minor = {
            let n_fv = d.fresh_fvar();
            let empty = d.kernel().const_(p.multiset_zero, vec![]);
            d.lam_fv(n_fv, nat, empty)
        };
        let succ_minor = {
            let j_fv = d.fresh_fvar();
            let row_fv = d.fresh_fvar();
            let row = d.kernel().fvar(row_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);

            let one = d.num(1);
            let guard = d.ble(n, one);
            let empty = d.kernel().const_(p.multiset_zero, vec![]);
            let mf = d.const_app(p.min_fac, &[n]);
            let head = ms_singleton(d, &p, mf);
            let quotient = d.div(n, mf);
            let tail = d.apply(row, &[quotient]);
            let joined = d.const_app(p.multiset_add, &[head, tail]);
            let body = bool_select_ms(d, &p, guard, empty, joined);

            let with_n = d.lam_fv(n_fv, nat, body);
            let with_row = d.lam_fv(row_fv, nat_to_ms, with_n);
            d.lam_fv(j_fv, nat, with_row)
        };
        let motive = d.kernel().lam(anon, nat, nat_to_ms, BinderInfo::Default);
        let rec = d.kernel().const_(p.rec, vec![one_level]);
        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);
        let row = d.apply(rec, &[motive, zero_minor, succ_minor, fuel]);
        let value = d.lam_fv(fuel_fv, nat, row);
        let ty = d.arrow(nat, nat_to_ms);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.factorization_aux,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    // factorization n := factorizationAux n n
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.const_app(p.factorization_aux, &[n, n]);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, ms);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.factorization,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(7),
        })?;
    }

    Ok(())
}

/// `Nat.factorizationAux fuel n`.
fn fact_aux(d: &mut NatDev<'_>, p: &NatPrelude, fuel: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.factorization_aux, &[fuel, n])
}

/// `Nat.prodFactorizationAux` and `Nat.prod_factorization`.
fn declare_prod_factorization(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let stmt_at = |d: &mut NatDev<'_>, fuel: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let zero = d.zero();
        let pos = d.lt(zero, n);
        let bounded = d.le(n, fuel);
        let built = fact_aux(d, &p, fuel, n);
        let folded = ms_prod(d, &p, built);
        let concl = d.eq(folded, n);
        let inner = d.arrow(bounded, concl);
        let body = d.arrow(pos, inner);
        d.pi_fv(n_fv, nat, body)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        // `0 < n` and `n ≤ 0` cannot both hold, so this case is VACUOUS -- it
        // never has to claim `prod zero = n`.
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let zero = d.zero();
        let pos_ty = d.lt(zero, n);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let bounded_ty = d.le(n, zero);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);

        let one = d.num(1);
        let one_le_zero = d.lemma(p.le_trans, &[one, n, zero, hp, hb]);
        let contradiction = d.lemma(p.not_succ_le_zero, &[zero, one_le_zero]);
        let built = fact_aux(d, &p, zero, n);
        let folded = ms_prod(d, &p, built);
        let goal = d.eq(folded, n);
        let body = from_false(d, &p, contradiction, goal);
        let with_hb = d.lam_fv(hb_fv, bounded_ty, body);
        let with_hp = d.lam_fv(hp_fv, pos_ty, with_hb);
        d.lam_fv(n_fv, nat, with_hp)
    };

    let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let succ_j = d.succ(j);
        let pos_ty = d.lt(zero, n);
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let bounded_ty = d.le(n, succ_j);
        let hb_fv = d.fresh_fvar();
        let hb = d.kernel().fvar(hb_fv);

        let guard = d.ble(n, one);
        let empty = d.kernel().const_(p.multiset_zero, vec![]);
        let mf = d.const_app(p.min_fac, &[n]);
        let head = ms_singleton(d, &p, mf);
        let quotient = d.div(n, mf);
        let tail = fact_aux(d, &p, j, quotient);
        let joined = d.const_app(p.multiset_add, &[head, tail]);

        let goal_at = |d: &mut NatDev<'_>, b: ExprId| -> ExprId {
            let selected = bool_select_ms(d, &p, b, empty, joined);
            let folded = ms_prod(d, &p, selected);
            d.eq(folded, n)
        };

        let motive = |d: &mut NatDev<'_>, _y: ExprId| -> ExprId {
            let selected = bool_select_ms(d, &p, guard, empty, joined);
            let folded = ms_prod(d, &p, selected);
            d.eq(folded, n)
        };

        // `n < 2`: with `0 < n` this forces `n = 1`, the guard is `true`, and
        // `prod Multiset.zero ≡ 1`.
        let small = |d: &mut NatDev<'_>, _y: ExprId, hlt: ExprId| -> ExprId {
            let one = d.num(1);
            let n_le_one = d.lemma(p.le_of_succ_le_succ, &[n, one, hlt]);
            let guard_true = d.lemma(p.ble_eq_true_of_le, &[n, one, n_le_one]);
            let n_eq_one = d.lemma(p.le_antisymm, &[n, one, n_le_one, hp]);
            let one_eq_n = d.symm(n, one, n_eq_one);
            let true_val = d.bool_true();
            transport_bool_guard(d, guard, true_val, guard_true, &goal_at, one_eq_n)
        };

        // `2 ≤ n`: the guard is `false`, and the recursive call is on the
        // strictly smaller `n / minFac n`.
        let big = |d: &mut NatDev<'_>, _y: ExprId, h2n: ExprId| -> ExprId {
            let one = d.num(1);
            let two = d.num(2);
            let guard_false = d.lemma(p.ble_eq_false_of_lt, &[n, one, h2n]);

            let mf_two_le = d.lemma(p.min_fac_two_le, &[n, h2n]);
            let one_le_two = d.lemma(p.le_succ, &[one]);
            let mf_pos = d.lemma(p.le_trans, &[one, two, mf, one_le_two, mf_two_le]);
            let mf_dvd = d.lemma(p.min_fac_dvd, &[n, h2n]);
            let cancel = d.lemma(p.div_mul_cancel_of_dvd, &[mf, n, mf_pos, mf_dvd]);

            // `0 < n / minFac n`: at `0` the product `minFac n * 0` is `0`,
            // which contradicts `0 < n`.
            let q_pos = {
                let q_motive = |d: &mut NatDev<'_>, y: ExprId| -> ExprId {
                    let product = d.mul(mf, y);
                    let premise = d.eq(product, n);
                    let zero = d.zero();
                    let concl = d.lt(zero, y);
                    d.arrow(premise, concl)
                };
                let at_zero = |d: &mut NatDev<'_>| -> ExprId {
                    let zero = d.zero();
                    let product = d.mul(mf, zero);
                    let premise = d.eq(product, n);
                    let he_fv = d.fresh_fvar();
                    let he = d.kernel().fvar(he_fv);
                    // `mul mf zero ≡ zero`, so `he : Eq zero n`.
                    let back = d.symm(product, n, he);
                    let m = d.eq_motive(n, &|d, y| {
                        let zero = d.zero();
                        d.lt(zero, y)
                    });
                    let bad = d.transport(n, m, hp, product, back);
                    let contradiction = d.lemma(p.not_succ_le_zero, &[zero, bad]);
                    let goal = {
                        let zero = d.zero();
                        d.lt(zero, zero)
                    };
                    let body = from_false(d, &p, contradiction, goal);
                    d.lam_fv(he_fv, premise, body)
                };
                let at_succ = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
                    let succ_k = d.succ(k);
                    let product = d.mul(mf, succ_k);
                    let premise = d.eq(product, n);
                    let he_fv = d.fresh_fvar();
                    let positive = d.zero_lt_succ(k);
                    d.lam_fv(he_fv, premise, positive)
                };
                let decided = cases_zero_succ(d, quotient, &q_motive, &at_zero, &at_succ);
                d.apply(decided, &[cancel])
            };

            let q_lt_n = d.lemma(p.div_lt_self, &[n, mf, hp, mf_two_le]);
            let succ_q = d.succ(quotient);
            let succ_j_local = d.succ(j);
            let succ_q_le = d.lemma(p.le_trans, &[succ_q, n, succ_j_local, q_lt_n, hb]);
            let q_le_j = d.lemma(p.le_of_succ_le_succ, &[quotient, j, succ_q_le]);
            let ih_at = d.apply(ih, &[quotient, q_pos, q_le_j]);

            let folded_joined = ms_prod(d, &p, joined);
            let head_prod = ms_prod(d, &p, head);
            let tail_prod = ms_prod(d, &p, tail);
            let split = d.lemma(p.multiset_prod_add, &[head, tail]);
            let after_split = d.mul(head_prod, tail_prod);
            let head_eq = d.lemma(p.multiset_prod_singleton, &[mf]);
            let after_head = d.mul(mf, tail_prod);
            let s2 = d.congr(head_prod, mf, head_eq, &|d, y| d.mul(y, tail_prod));
            let after_tail = d.mul(mf, quotient);
            let s3 = d.congr(tail_prod, quotient, ih_at, &|d, y| d.mul(mf, y));
            let (_, proof_at_false) = d.chain(
                folded_joined,
                &[
                    (after_split, split),
                    (after_head, s2),
                    (after_tail, s3),
                    (n, cancel),
                ],
            );
            let false_val = d.bool_false();
            transport_bool_guard(d, guard, false_val, guard_false, &goal_at, proof_at_false)
        };

        let body = cases_lt_or_ge(d, &p, n, two, &motive, &small, &big);
        let with_hb = d.lam_fv(hb_fv, bounded_ty, body);
        let with_hp = d.lam_fv(hp_fv, pos_ty, with_hb);
        d.lam_fv(n_fv, nat, with_hp)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof = d.induct(&stmt_at, &base, &step, fuel);
    let stmt = stmt_at(d, fuel);
    declare_forall(d, p.prod_factorization_aux, &[(fuel_fv, nat)], stmt, proof)?;

    // prod_factorization : ∀ n, Lt 0 n → Eq (prod (factorization n)) n
    d.theorem(p.prod_factorization, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let pos_ty = d.lt(zero, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let refl_le = d.lemma(p.le_refl_thm, &[n]);
        let body = d.lemma(p.prod_factorization_aux, &[n, n, h, refl_le]);
        let built = d.const_app(p.factorization, &[n]);
        let folded = ms_prod(d, &p, built);
        let concl = d.eq(folded, n);
        let stmt = d.arrow(pos_ty, concl);
        let proof = d.lam_fv(h_fv, pos_ty, body);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.factorizationAuxPrime` and `Nat.factorization_prime`.
fn declare_factorization_prime(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let stmt_at = |d: &mut NatDev<'_>, fuel: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let built = fact_aux(d, &p, fuel, n);
        let c = ms_count(d, &p, built, x);
        let zero = d.zero();
        let present = d.lt(zero, c);
        let prime = prime_condition(d, &p, x);
        let body = d.arrow(present, prime);
        let with_x = d.pi_fv(x_fv, nat, body);
        d.pi_fv(n_fv, nat, with_x)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        // `factorizationAux zero n ≡ Multiset.zero`, whose bound is `0`, so the
        // count is `0` and the premise is absurd.
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let zero = d.zero();
        let built = fact_aux(d, &p, zero, n);
        let c = ms_count(d, &p, built, x);
        let present = d.lt(zero, c);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let empty = d.kernel().const_(p.multiset_zero, vec![]);
        let above = d.lemma(p.zero_le, &[x]);
        let vanishes = d.lemma(p.multiset_count_eq_zero_of_bound_le, &[empty, x, above]);
        let m = d.eq_motive(c, &|d, y| {
            let zero = d.zero();
            d.lt(zero, y)
        });
        let bad = d.transport(c, m, h, zero, vanishes);
        let contradiction = d.lemma(p.not_succ_le_zero, &[zero, bad]);
        let prime = prime_condition(d, &p, x);
        let body = from_false(d, &p, contradiction, prime);
        let with_h = d.lam_fv(h_fv, present, body);
        let with_x = d.lam_fv(x_fv, nat, with_h);
        d.lam_fv(n_fv, nat, with_x)
    };

    let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);

        let guard = d.ble(n, one);
        let empty = d.kernel().const_(p.multiset_zero, vec![]);
        let mf = d.const_app(p.min_fac, &[n]);
        let head = ms_singleton(d, &p, mf);
        let quotient = d.div(n, mf);
        let tail = fact_aux(d, &p, j, quotient);
        let joined = d.const_app(p.multiset_add, &[head, tail]);

        // The GOAL is the whole implication, so the guard transport carries the
        // premise with it and each branch binds its own hypothesis.
        let goal_at = |d: &mut NatDev<'_>, b: ExprId| -> ExprId {
            let selected = bool_select_ms(d, &p, b, empty, joined);
            let c = ms_count(d, &p, selected, x);
            let zero = d.zero();
            let present = d.lt(zero, c);
            let prime = prime_condition(d, &p, x);
            d.arrow(present, prime)
        };
        let motive = |d: &mut NatDev<'_>, _y: ExprId| -> ExprId { goal_at(d, guard) };

        let small = |d: &mut NatDev<'_>, _y: ExprId, hlt: ExprId| -> ExprId {
            let one = d.num(1);
            let n_le_one = d.lemma(p.le_of_succ_le_succ, &[n, one, hlt]);
            let guard_true = d.lemma(p.ble_eq_true_of_le, &[n, one, n_le_one]);
            let at_true = {
                let c = ms_count(d, &p, empty, x);
                let zero = d.zero();
                let present = d.lt(zero, c);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let above = d.lemma(p.zero_le, &[x]);
                let vanishes = d.lemma(p.multiset_count_eq_zero_of_bound_le, &[empty, x, above]);
                let m = d.eq_motive(c, &|d, y| {
                    let zero = d.zero();
                    d.lt(zero, y)
                });
                let bad = d.transport(c, m, h, zero, vanishes);
                let contradiction = d.lemma(p.not_succ_le_zero, &[zero, bad]);
                let prime = prime_condition(d, &p, x);
                let body = from_false(d, &p, contradiction, prime);
                d.lam_fv(h_fv, present, body)
            };
            let true_val = d.bool_true();
            transport_bool_guard(d, guard, true_val, guard_true, &goal_at, at_true)
        };

        let big = |d: &mut NatDev<'_>, _y: ExprId, h2n: ExprId| -> ExprId {
            let one = d.num(1);
            let guard_false = d.lemma(p.ble_eq_false_of_lt, &[n, one, h2n]);
            let at_false = {
                let c = ms_count(d, &p, joined, x);
                let zero = d.zero();
                let present = d.lt(zero, c);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let prime = prime_condition(d, &p, x);

                let head_count = ms_count(d, &p, head, x);
                let tail_count = ms_count(d, &p, tail, x);
                let sum = d.add(head_count, tail_count);
                let splits = d.lemma(p.multiset_count_add, &[head, tail, x]);

                let guard_x = d.beq(x, mf);
                let true_val = d.bool_true();
                let false_val = d.bool_false();
                let left_ty = d.bool_eq(guard_x, true_val);
                let right_ty = d.bool_eq(guard_x, false_val);

                // `x = minFac n`: primality transports along that equation.
                let left_minor = {
                    let g_fv = d.fresh_fvar();
                    let g = d.kernel().fvar(g_fv);
                    let x_eq = d.lemma(p.eq_of_beq_eq_true, &[x, mf, g]);
                    let mf_prime = d.lemma(p.min_fac_prime, &[n, h2n]);
                    let back = d.symm(x, mf, x_eq);
                    let m = d.eq_motive(mf, &|d, y| prime_condition(d, &p, y));
                    let moved = d.transport(mf, m, mf_prime, x, back);
                    d.lam_fv(g_fv, left_ty, moved)
                };
                // `x ≠ minFac n`: the head contributes `0`, so the whole count
                // is the tail's and the induction hypothesis applies.
                let right_minor = {
                    let g_fv = d.fresh_fvar();
                    let g = d.kernel().fvar(g_fv);
                    let head_zero = d.lemma(p.multiset_count_singleton_of_ne, &[mf, x, g]);
                    let zero = d.zero();
                    let zero_plus = d.add(zero, tail_count);
                    let to_zero =
                        d.congr(head_count, zero, head_zero, &|d, y| d.add(y, tail_count));
                    let collapse = d.lemma(p.zero_add, &[tail_count]);
                    let (_, count_eq) = d.chain(
                        c,
                        &[(sum, splits), (zero_plus, to_zero), (tail_count, collapse)],
                    );
                    let m = d.eq_motive(c, &|d, y| {
                        let zero = d.zero();
                        d.lt(zero, y)
                    });
                    let tail_present = d.transport(c, m, h, tail_count, count_eq);
                    let recursed = d.apply(ih, &[quotient, x, tail_present]);
                    d.lam_fv(g_fv, right_ty, recursed)
                };

                let split = bool_true_or_false(d, &p, guard_x);
                let body = or_cases(
                    d,
                    &p,
                    left_ty,
                    right_ty,
                    prime,
                    left_minor,
                    right_minor,
                    split,
                );
                d.lam_fv(h_fv, present, body)
            };
            let false_val = d.bool_false();
            transport_bool_guard(d, guard, false_val, guard_false, &goal_at, at_false)
        };

        let body = cases_lt_or_ge(d, &p, n, two, &motive, &small, &big);
        let _ = zero;
        let with_x = d.lam_fv(x_fv, nat, body);
        d.lam_fv(n_fv, nat, with_x)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof = d.induct(&stmt_at, &base, &step, fuel);
    let stmt = stmt_at(d, fuel);
    declare_forall(d, p.factorization_aux_prime, &[(fuel_fv, nat)], stmt, proof)?;

    // factorization_prime : ∀ n x, Lt 0 (count (factorization n) x) →
    //   prime_condition x
    d.theorem(p.factorization_prime, 2, &|d, v| {
        let (n, x) = (v[0], v[1]);
        let built = d.const_app(p.factorization, &[n]);
        let c = ms_count(d, &p, built, x);
        let zero = d.zero();
        let present = d.lt(zero, c);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.lemma(p.factorization_aux_prime, &[n, n, x, h]);
        let prime = prime_condition(d, &p, x);
        let stmt = d.arrow(present, prime);
        let proof = d.lam_fv(h_fv, present, body);
        (stmt, proof)
    })?;

    Ok(())
}

/// The computed factorization: `Nat.prodRange_eq_one_of_below`, the two
/// `Nat.Multiset.count_singleton` laws, `Nat.Multiset.prod_singleton`,
/// `Nat.factorizationAux`/`Nat.factorization`, and the two correctness
/// theorems.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_factorization_multiset_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_prod_range_eq_one(d, p)?;
    declare_count_singleton(d, p)?;
    declare_prod_singleton(d, p)?;
    declare_factorization_defs(d, p)?;
    declare_prod_factorization(d, p)?;
    declare_factorization_prime(d, p)?;
    Ok(())
}
