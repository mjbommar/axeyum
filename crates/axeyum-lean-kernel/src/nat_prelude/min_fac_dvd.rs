//! `Nat.minFac` DIVIDES, is at least `2`, and is PRIME.
//!
//! # Why these were missing
//!
//! `min_fac.rs` built `Nat.minFac` and proved its MINIMALITY
//! (`Nat.min_fac_minimal_of_two_le`: nothing between `2` and `minFac n`
//! divides `n`), which is what `Nat.coprime_of_lt_min_fac` needed. Minimality
//! alone says nothing about `minFac n` itself — a `minFac` that returned a
//! non-divisor satisfies it vacuously — so the three facts a trial-division
//! factorization actually consumes were all absent:
//!
//! - `Nat.min_fac_dvd : ∀ n, 2 ≤ n → minFac n ∣ n`
//! - `Nat.min_fac_two_le : ∀ n, 2 ≤ n → 2 ≤ minFac n`
//! - `Nat.min_fac_prime : ∀ n, 2 ≤ n → prime_condition (minFac n)`
//!
//! # The two fuel inductions
//!
//! Both generalize the candidate INSIDE the induction, as
//! `min_fac.rs`'s `min_fac_aux_minimal_stmt` does, and both state the candidate
//! as `succ cp` rather than as a bare variable. That is not cosmetic:
//! `Nat.div_mod_exec` requires its divisor expressed as a SUCCESSOR, and a bare
//! `candidate` fvar is stuck. `min_fac.rs`'s minimality proof pays for this
//! with an explicit `pos_implies_succ_pred` unfold plus a transport back;
//! quantifying over the predecessor from the start costs nothing and removes
//! both steps.
//!
//! - `Nat.minFacAuxTwoLe : ∀ fuel n cp, 2 ≤ succ cp → 2 ≤ minFacAux fuel n
//!   (succ cp)`. The fuel-exhaustion row returns the candidate unchanged, so
//!   the base case IS the hypothesis; the successor row returns either the
//!   candidate (again the hypothesis) or the recursive call at
//!   `succ (succ cp)`, where the induction hypothesis applies.
//! - `Nat.minFacAuxDvd : ∀ fuel n cp, add (succ cp) fuel = n → minFacAux fuel n
//!   (succ cp) ∣ n`. **The `add (succ cp) fuel = n` premise is what makes the
//!   fuel-exhaustion row correct**, and it is `min_fac.rs`'s module-doc
//!   reasoning turned into a hypothesis: the fuel counts down in lockstep with
//!   the candidate counting up, so `fuel = 0` coincides with `candidate = n`,
//!   and `n ∣ n`. Without the premise the statement is FALSE —
//!   `minFacAux 0 6 4 = 4` and `4 ∤ 6`.
//!
//! The successor row splits on the guard `beq (mod n (succ cp)) 0` through
//! `bool_true_or_false` plus `select_nat_true`/`select_nat_false` rather than a
//! dependent `Bool.rec`: the guard's two values give two EQUATIONS about the
//! selector, and the goal transports along each. On the `true` side
//! `div_mod_remainder_eq_zero_iff_dvd`'s FORWARD direction turns the zero
//! remainder into the divisibility (the mirror of `min_fac.rs`'s
//! `not_divides_of_remainder_nonzero`, which uses the reverse); on the `false`
//! side the induction hypothesis applies at the next candidate, after
//! `succ_add` moves the successor from the fuel onto the candidate.
//!
//! # Primality needs no new induction
//!
//! `2 ≤ minFac n` is the lower half directly. For the divisor half, take
//! `c ∣ minFac n`; then `c ∣ n` by transitivity and `c ≤ minFac n` by
//! `le_of_dvd`. Split `c` against `2`: below it `c` is `0` or `1`, and `c = 0`
//! would force `minFac n = 0` against `2 ≤ minFac n`; at or above it,
//! `c < minFac n` is refuted by `min_fac_minimal_of_two_le`, so
//! `minFac n ≤ c` and `le_antisymm` closes.
//!
//! Every helper hoists each sub-expression into its own `let` before passing it
//! to a `NatOps` method (`&mut NatDev` cannot be reborrowed twice in one call),
//! per this development's house rule.

use super::NatPrelude;
use super::finite::{select_nat_false, select_nat_true};
use super::helpers::{iff_forward, transport_dvd_left, transport_dvd_right};
use super::ops::{NatDev, NatOps, bool_true_or_false, cases_lt_bound_absurd, cases_lt_or_ge};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::name::NameId;

/// `∀ binders, stmt`, proved by `proof`. A local copy of the same helper in
/// `multiset.rs` / `multiset_prod.rs`, per this development's per-file-copy
/// convention.
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

/// A goal shaped `motive(bool_select_nat cond on_true on_false)`, from branch
/// closures that each receive the guard's own equation.
///
/// `bool_true_or_false` splits the guard into `cond = true` / `cond = false`,
/// and `select_nat_true`/`select_nat_false` turn each into an equation about
/// the selector, which the goal transports along. Deliberately not a dependent
/// `Bool.rec`: each branch proves a statement about `on_true`/`on_false` and
/// never mentions the scrutinee, so nothing needs the motive to vary with it —
/// but the `true` branch DOES need the equation itself (that is where the zero
/// remainder comes from), which is why the branches are closures.
#[allow(clippy::too_many_arguments)]
fn cases_bool_select_nat(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    cond: ExprId,
    on_true: ExprId,
    on_false: ExprId,
    motive: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    proof_true: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
    proof_false: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let selector = d.bool_select_nat(cond, on_true, on_false);
    let goal = motive(d, selector);
    let true_val = d.bool_true();
    let false_val = d.bool_false();
    let left_ty = d.bool_eq(cond, true_val);
    let right_ty = d.bool_eq(cond, false_val);

    let left_minor = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let inner = proof_true(d, h);
        let selects = select_nat_true(d, cond, on_true, on_false, h);
        let back = d.symm(selector, on_true, selects);
        let m = d.eq_motive(on_true, motive);
        let body = d.transport(on_true, m, inner, selector, back);
        d.lam_fv(h_fv, left_ty, body)
    };
    let right_minor = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let inner = proof_false(d, h);
        let selects = select_nat_false(d, cond, on_true, on_false, h);
        let back = d.symm(selector, on_false, selects);
        let m = d.eq_motive(on_false, motive);
        let body = d.transport(on_false, m, inner, selector, back);
        d.lam_fv(h_fv, right_ty, body)
    };

    let split = bool_true_or_false(d, p, cond);
    or_cases(
        d,
        p,
        left_ty,
        right_ty,
        goal,
        left_minor,
        right_minor,
        split,
    )
}

/// `Nat.minFacAux fuel n candidate`.
fn min_fac_aux(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    fuel: ExprId,
    n: ExprId,
    candidate: ExprId,
) -> ExprId {
    d.const_app(p.min_fac_aux, &[fuel, n, candidate])
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

/// `Not (Eq a b) ⊢ Not (Eq b a)`.
fn ne_symm(d: &mut NatDev<'_>, a: ExprId, b: ExprId, hne: ExprId) -> ExprId {
    let eq_ba = d.eq(b, a);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let flipped = d.symm(b, a, h);
    let bad = d.apply(hne, &[flipped]);
    d.lam_fv(h_fv, eq_ba, bad)
}

/// `Nat.minFacAuxTwoLe : ∀ fuel n cp, Le 2 (succ cp) →
/// Le 2 (minFacAux fuel n (succ cp))`.
fn declare_min_fac_aux_two_le(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let stmt_at = |d: &mut NatDev<'_>, fuel: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let cp_fv = d.fresh_fvar();
        let cp = d.kernel().fvar(cp_fv);
        let two = d.num(2);
        let candidate = d.succ(cp);
        let hyp = d.le(two, candidate);
        let searched = min_fac_aux(d, &p, fuel, n, candidate);
        let concl = d.le(two, searched);
        let body = d.arrow(hyp, concl);
        let with_cp = d.pi_fv(cp_fv, nat, body);
        d.pi_fv(n_fv, nat, with_cp)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        // `minFacAux zero n candidate ≡ candidate`: the hypothesis is the whole
        // answer.
        let n_fv = d.fresh_fvar();
        let cp_fv = d.fresh_fvar();
        let cp = d.kernel().fvar(cp_fv);
        let two = d.num(2);
        let candidate = d.succ(cp);
        let hyp = d.le(two, candidate);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let with_h = d.lam_fv(h_fv, hyp, h);
        let with_cp = d.lam_fv(cp_fv, nat, with_h);
        d.lam_fv(n_fv, nat, with_cp)
    };

    let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let cp_fv = d.fresh_fvar();
        let cp = d.kernel().fvar(cp_fv);
        let two = d.num(2);
        let candidate = d.succ(cp);
        let hyp = d.le(two, candidate);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let zero = d.zero();
        let remainder = d.modulo(n, candidate);
        let guard = d.beq(remainder, zero);
        let next = d.succ(candidate);
        let recursed = min_fac_aux(d, &p, j, n, next);

        let le_next = d.lemma(p.le_succ, &[candidate]);
        let two_le_next = d.lemma(p.le_trans, &[two, candidate, next, h, le_next]);
        let ih_at = d.apply(ih, &[n, candidate, two_le_next]);

        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let two = d.num(2);
            d.le(two, x)
        };
        let body = cases_bool_select_nat(
            d,
            &p,
            guard,
            candidate,
            recursed,
            &motive,
            &|_d, _g| h,
            &|_d, _g| ih_at,
        );
        let with_h = d.lam_fv(h_fv, hyp, body);
        let with_cp = d.lam_fv(cp_fv, nat, with_h);
        d.lam_fv(n_fv, nat, with_cp)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof = d.induct(&stmt_at, &base, &step, fuel);
    let stmt = stmt_at(d, fuel);
    declare_forall(d, p.min_fac_aux_two_le, &[(fuel_fv, nat)], stmt, proof)
}

/// `Nat.minFacAuxDvd : ∀ fuel n cp, Eq (add (succ cp) fuel) n →
/// dvd (minFacAux fuel n (succ cp)) n`.
fn declare_min_fac_aux_dvd(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let stmt_at = |d: &mut NatDev<'_>, fuel: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let cp_fv = d.fresh_fvar();
        let cp = d.kernel().fvar(cp_fv);
        let candidate = d.succ(cp);
        let reached = d.add(candidate, fuel);
        let hyp = d.eq(reached, n);
        let searched = min_fac_aux(d, &p, fuel, n, candidate);
        let concl = d.dvd(searched, n);
        let body = d.arrow(hyp, concl);
        let with_cp = d.pi_fv(cp_fv, nat, body);
        d.pi_fv(n_fv, nat, with_cp)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        // `add candidate zero ≡ candidate`, so the premise says `candidate = n`,
        // and `minFacAux zero n candidate ≡ candidate`.
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let cp_fv = d.fresh_fvar();
        let cp = d.kernel().fvar(cp_fv);
        let candidate = d.succ(cp);
        let zero = d.zero();
        let reached = d.add(candidate, zero);
        let hyp = d.eq(reached, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let refl_dvd = d.lemma(p.dvd_refl, &[candidate]);
        let moved = transport_dvd_right(d, candidate, candidate, n, h, refl_dvd);
        let with_h = d.lam_fv(h_fv, hyp, moved);
        let with_cp = d.lam_fv(cp_fv, nat, with_h);
        d.lam_fv(n_fv, nat, with_cp)
    };

    let step = |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let cp_fv = d.fresh_fvar();
        let cp = d.kernel().fvar(cp_fv);
        let candidate = d.succ(cp);
        let succ_j = d.succ(j);
        let reached = d.add(candidate, succ_j);
        let hyp = d.eq(reached, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let zero = d.zero();
        let remainder = d.modulo(n, candidate);
        let guard = d.beq(remainder, zero);
        let next = d.succ(candidate);
        let recursed = min_fac_aux(d, &p, j, n, next);

        // The premise moves from `candidate + succ j = n` to
        // `succ candidate + j = n` — the same value, since `Nat.add` recurses on
        // its RIGHT argument (`add c (succ j) ≡ succ (add c j)`) and `succ_add`
        // re-associates the successor onto the candidate.
        let shifted = {
            let moved = d.lemma(p.succ_add, &[candidate, j]);
            let lhs = d.add(next, j);
            let inner = d.add(candidate, j);
            let mid = d.succ(inner);
            d.trans(lhs, mid, n, moved, h)
        };
        let ih_at = d.apply(ih, &[n, candidate, shifted]);

        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId { d.dvd(x, n) };
        let true_branch = |d: &mut NatDev<'_>, g: ExprId| -> ExprId {
            let quotient = d.div(n, candidate);
            let exec = d.lemma(p.div_mod_exec, &[cp, n]);
            let spec = d.lemma(
                p.div_mod_remainder_eq_zero_iff_dvd,
                &[candidate, n, quotient, remainder, exec],
            );
            let remainder_zero_ty = d.eq(remainder, zero);
            let divides_ty = d.dvd(candidate, n);
            let forward = iff_forward(d, remainder_zero_ty, divides_ty, spec);
            let remainder_zero = d.lemma(p.eq_of_beq_eq_true, &[remainder, zero, g]);
            d.apply(forward, &[remainder_zero])
        };
        let body = cases_bool_select_nat(
            d,
            &p,
            guard,
            candidate,
            recursed,
            &motive,
            &true_branch,
            &|_d, _g| ih_at,
        );
        let with_h = d.lam_fv(h_fv, hyp, body);
        let with_cp = d.lam_fv(cp_fv, nat, with_h);
        d.lam_fv(n_fv, nat, with_cp)
    };

    let fuel_fv = d.fresh_fvar();
    let fuel = d.kernel().fvar(fuel_fv);
    let proof = d.induct(&stmt_at, &base, &step, fuel);
    let stmt = stmt_at(d, fuel);
    declare_forall(d, p.min_fac_aux_dvd, &[(fuel_fv, nat)], stmt, proof)
}

/// `minFac n`'s two boundary `bool_select_nat` wrappers unwound down to
/// `minFacAux (sub n 2) n 2`, given `2 ≤ n`. Returns the unwound term and the
/// equation `minFac n = minFacAux (sub n 2) n 2`'s left-to-right form
/// (`Eq (minFac n) searched`). Mirrors the same step inside `min_fac.rs`'s
/// `declare_min_fac_minimal_of_two_le`, which is module-private there.
fn unfold_min_fac(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId, h2n: ExprId) -> (ExprId, ExprId) {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let two = d.num(2);

    let zero_lt_two = d.zero_lt_succ(one);
    let zero_lt_n = d.lemma(p.lt_of_lt_of_le, &[zero, two, n, zero_lt_two, h2n]);
    let zero_ne_n = ne_of_lt(d, &p, zero, n, zero_lt_n);
    let n_ne_zero = ne_symm(d, zero, n, zero_ne_n);
    let is_zero_false = d.lemma(p.beq_eq_false_of_ne, &[n, zero, n_ne_zero]);
    // `Le 2 n` IS `Lt 1 n` by defeq (`succ one ≡ two`).
    let one_ne_n = ne_of_lt(d, &p, one, n, h2n);
    let n_ne_one = ne_symm(d, one, n, one_ne_n);
    let is_one_false = d.lemma(p.beq_eq_false_of_ne, &[n, one, n_ne_one]);

    let fuel = d.sub(n, two);
    let searched = min_fac_aux(d, &p, fuel, n, two);
    let is_zero = d.beq(n, zero);
    let is_one = d.beq(n, one);
    let else_branch = d.bool_select_nat(is_one, one, searched);
    let full_body = d.bool_select_nat(is_zero, two, else_branch);
    let outer = select_nat_false(d, is_zero, two, else_branch, is_zero_false);
    let inner = select_nat_false(d, is_one, one, searched, is_one_false);
    let unfold_eq = d.trans(full_body, else_branch, searched, outer, inner);
    (searched, unfold_eq)
}

/// `dvd zero x ⊢ Eq x zero`. `Nat.dvd a n` is `∃ q, n = a * q`, so at `a = 0`
/// the witness gives `x = 0 * q`, and `zero_mul` collapses the right side.
fn zero_dvd_eq_zero(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId, proof: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one_level = d.level_one();
    let anon = d.anon_name();
    let zero = d.zero();
    let goal = d.eq(x, zero);
    let predicate = d.dvd_predicate(zero, x);
    let dvd_ty = d.dvd(zero, x);
    let motive = d.kernel().lam(anon, dvd_ty, goal, BinderInfo::Default);
    let minor = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let product = d.mul(zero, q);
        let eq_ty = d.eq(x, product);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let collapse = d.lemma(p.zero_mul, &[q]);
        let body = d.trans(x, product, zero, e, collapse);
        let with_e = d.lam_fv(e_fv, eq_ty, body);
        d.lam_fv(q_fv, nat, with_e)
    };
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one_level]);
    d.apply(rec, &[nat, predicate, motive, minor, proof])
}

/// `Nat.min_fac_two_le` and `Nat.min_fac_dvd`.
fn declare_min_fac_facts(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    // min_fac_two_le : ∀ n, Le 2 n → Le 2 (minFac n)
    d.theorem(p.min_fac_two_le, 1, &|d, v| {
        let n = v[0];
        let two = d.num(2);
        let one = d.num(1);
        let hyp = d.le(two, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let (searched, unfold_eq) = unfold_min_fac(d, &p, n, h);
        let fuel = d.sub(n, two);
        // The starting candidate is the literal `2 = succ 1`, so `cp := 1`.
        let two_le_two = d.lemma(p.le_refl_thm, &[two]);
        let at_fuel = d.lemma(p.min_fac_aux_two_le, &[fuel, n, one, two_le_two]);
        let min_fac_n = d.const_app(p.min_fac, &[n]);
        let back = d.symm(min_fac_n, searched, unfold_eq);
        let motive = d.eq_motive(searched, &|d, x| {
            let two = d.num(2);
            d.le(two, x)
        });
        let moved = d.transport(searched, motive, at_fuel, min_fac_n, back);
        let concl = d.le(two, min_fac_n);
        let stmt = d.arrow(hyp, concl);
        let proof = d.lam_fv(h_fv, hyp, moved);
        (stmt, proof)
    })?;

    // min_fac_dvd : ∀ n, Le 2 n → dvd (minFac n) n
    d.theorem(p.min_fac_dvd, 1, &|d, v| {
        let n = v[0];
        let two = d.num(2);
        let one = d.num(1);
        let hyp = d.le(two, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let (searched, unfold_eq) = unfold_min_fac(d, &p, n, h);
        let fuel = d.sub(n, two);
        let cancel = d.lemma(p.add_sub_cancel_of_le, &[two, n, h]);
        let at_fuel = d.lemma(p.min_fac_aux_dvd, &[fuel, n, one, cancel]);
        let min_fac_n = d.const_app(p.min_fac, &[n]);
        let back = d.symm(min_fac_n, searched, unfold_eq);
        let moved = transport_dvd_left(d, searched, min_fac_n, back, n, at_fuel);
        let concl = d.dvd(min_fac_n, n);
        let stmt = d.arrow(hyp, concl);
        let proof = d.lam_fv(h_fv, hyp, moved);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.min_fac_prime : ∀ n, Le 2 n → prime_condition (minFac n)`.
fn declare_min_fac_prime(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    d.theorem(p.min_fac_prime, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let hyp = d.le(two, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let min_fac_n = d.const_app(p.min_fac, &[n]);
        let lower = d.le(two, min_fac_n);
        let lower_proof = d.lemma(p.min_fac_two_le, &[n, h]);
        let dvd_n = d.lemma(p.min_fac_dvd, &[n, h]);

        let divisors_ty = {
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let hd = d.dvd(c, min_fac_n);
            let triv = d.eq(c, one);
            let whole = d.eq(c, min_fac_n);
            let disj = d.const_app(p.logic.or, &[triv, whole]);
            let body = d.arrow(hd, disj);
            d.pi_fv(c_fv, nat, body)
        };
        let divisors_proof = {
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let hd_ty = d.dvd(c, min_fac_n);
            let hd_fv = d.fresh_fvar();
            let hd = d.kernel().fvar(hd_fv);

            let one_le_two = d.lemma(p.le_succ, &[one]);
            let one_le_mf = d.lemma(p.le_trans, &[one, two, min_fac_n, one_le_two, lower_proof]);
            let c_le_mf = d.lemma(p.le_of_dvd, &[c, min_fac_n, one_le_mf, hd]);
            let c_dvd_n = d.lemma(p.dvd_trans, &[c, min_fac_n, n, hd, dvd_n]);

            let motive = |d: &mut NatDev<'_>, _x: ExprId| -> ExprId {
                let triv = d.eq(c, one);
                let whole = d.eq(c, min_fac_n);
                d.const_app(p.logic.or, &[triv, whole])
            };
            // `c < 2`: `c` is `0` or `1`. `c = 0` forces `minFac n = 0`
            // (`dvd 0 x` unfolds to `∃ q, x = 0 * q`), contradicting
            // `2 ≤ minFac n`; `c = 1` is the left disjunct.
            let small = |d: &mut NatDev<'_>, _x: ExprId, hlt: ExprId| -> ExprId {
                let goal_here = motive(d, c);
                let at_zero = |d: &mut NatDev<'_>, eq_c0: ExprId| -> ExprId {
                    let zero = d.zero();
                    let moved = transport_dvd_left(d, c, zero, eq_c0, min_fac_n, hd);
                    let mf_zero = zero_dvd_eq_zero(d, &p, min_fac_n, moved);
                    let m = d.eq_motive(min_fac_n, &|d, x| {
                        let two = d.num(2);
                        d.le(two, x)
                    });
                    let two_le_zero = d.transport(min_fac_n, m, lower_proof, zero, mf_zero);
                    let one = d.num(1);
                    let contradiction = d.lemma(p.not_succ_le_zero, &[one, two_le_zero]);
                    let goal = motive(d, c);
                    from_false(d, &p, contradiction, goal)
                };
                let at_one = |d: &mut NatDev<'_>, eq_c1: ExprId| -> ExprId {
                    let one = d.num(1);
                    let triv = d.eq(c, one);
                    let whole = d.eq(c, min_fac_n);
                    d.const_app(p.logic.or_inl, &[triv, whole, eq_c1])
                };
                let _ = zero;
                cases_lt_bound_absurd(d, &p, c, 2, hlt, goal_here, &[&at_zero, &at_one])
            };
            // `2 ≤ c`: minimality forbids `c < minFac n`, so `minFac n ≤ c` and
            // `lt_or_eq_of_le` leaves only `c = minFac n`.
            let big = |d: &mut NatDev<'_>, _x: ExprId, hge: ExprId| -> ExprId {
                let minimal = d.lemma(p.min_fac_minimal_of_two_le, &[n, h]);
                let lt_ty = d.lt(c, min_fac_n);
                let split = d.lemma(p.lt_or_eq_of_le, &[c, min_fac_n, c_le_mf]);
                let eq_ty = d.eq(c, min_fac_n);
                let goal_here = motive(d, c);
                let left = {
                    let hl_fv = d.fresh_fvar();
                    let hl = d.kernel().fvar(hl_fv);
                    let bad = d.apply(minimal, &[c, hge, hl, c_dvd_n]);
                    let body = from_false(d, &p, bad, goal_here);
                    d.lam_fv(hl_fv, lt_ty, body)
                };
                let right = {
                    let he_fv = d.fresh_fvar();
                    let he = d.kernel().fvar(he_fv);
                    let one = d.num(1);
                    let triv = d.eq(c, one);
                    let whole = d.eq(c, min_fac_n);
                    let injected = d.const_app(p.logic.or_inr, &[triv, whole, he]);
                    d.lam_fv(he_fv, eq_ty, injected)
                };
                or_cases(d, &p, lt_ty, eq_ty, goal_here, left, right, split)
            };
            let body = cases_lt_or_ge(d, &p, c, two, &motive, &small, &big);
            let with_hd = d.lam_fv(hd_fv, hd_ty, body);
            d.lam_fv(c_fv, nat, with_hd)
        };

        let prime = d.const_app(p.logic.and, &[lower, divisors_ty]);
        let intro = d.const_app(
            p.logic.and_intro,
            &[lower, divisors_ty, lower_proof, divisors_proof],
        );
        let stmt = d.arrow(hyp, prime);
        let proof = d.lam_fv(h_fv, hyp, intro);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.minFacAuxTwoLe`, `Nat.minFacAuxDvd`, `Nat.min_fac_two_le`,
/// `Nat.min_fac_dvd` and `Nat.min_fac_prime`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_min_fac_dvd_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_min_fac_aux_two_le(d, p)?;
    declare_min_fac_aux_dvd(d, p)?;
    declare_min_fac_facts(d, p)?;
    declare_min_fac_prime(d, p)?;
    Ok(())
}
