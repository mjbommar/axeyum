//! `Nat.minFac`: the least prime factor of `n`, by fuel-recursive linear
//! search over candidate divisors — see [`declare_min_fac_all`]'s doc comment
//! for the fuel-exhaustion choice, and the module-level note on why this is
//! NOT Mathlib's `def` even though the two compute identical values.
//!
//! ## Why this is not Mathlib's `minFac`, and why the mirror stays open
//!
//! Mathlib's `Nat.minFac n := if 2 ∣ n then 2 else minFacAux n 3`, where
//! `minFacAux` searches only ODD candidates starting at `3`, by
//! **well-founded recursion** on the strictly-decreasing measure
//! `sqrt n + 2 - k`, and terminates EARLY the moment `k * k > n` (returning
//! `n` itself, having proved `n` prime without checking any further
//! candidate). None of that is expressible as a *structural* `Nat.rec` — the
//! decrease is via `sqrt`, not a constructor predecessor — so building it
//! verbatim would need `WellFounded.fix`, which in this kernel is fine
//! (`lt_well_founded`, `ops.rs`) but is a materially different construction
//! from what is built here.
//!
//! What is built here instead is the simplest sound alternative: fuel
//! structural recursion (the same device `Nat.div`/`Nat.mod`/`Nat.log` use)
//! that tests EVERY candidate `2, 3, 4, …` in turn via `beq (mod n d) 0`,
//! exactly as `primes.rs`'s existing `least_divisor_search` decides
//! divisibility, with no even/odd skip and no early sqrt-bound exit. This
//! computes the identical VALUE as Mathlib's `minFac` for every `n` (both are
//! "the least divisor `≥ 2` of `n`, with `minFac 0 = 2` and `minFac 1 = 1` as
//! the same boundary conventions"), but by construction, not by algorithm:
//! the two are extensionally equal, not the same `def`.
//!
//! Per the established criterion (see `CLAUDE.md`'s "WHEN IS FLIPPING AN
//! `ml430` MIRROR HONEST" gotcha): flipping `F:ml430-nat-coprime-of-lt-minfac`
//! would require Mathlib's `minFac` and this one to be THE SAME definition,
//! not merely agree pointwise. They are not — this is the `Nat.multichoose`
//! case, not the `Nat.descFactorial_of_lt` case — so that mirror stays
//! `open`. A theorem about coprimality relative to THIS `minFac` would need
//! its own `F:nat-*` fact, not attempted in this lane (the minimality
//! property this `minFac` would need — `∀ d, 2 ≤ d → d ∣ n → minFac n ≤ d`
//! — is a further, separately-sized proof).
//!
//! ## The fuel-exhaustion base case
//!
//! `minFacAux` is called as `minFacAux (n - 2) n 2`: fuel `n - 2` and a
//! starting candidate `2` walk the candidate up to `n` in lockstep with the
//! fuel counting down to `0`, so fuel exhaustion (`fuel = 0`) coincides
//! EXACTLY with `candidate = n` — never earlier. So the base case "return the
//! candidate unchanged" is correct: it is only ever reached once every
//! candidate `2, …, n-1` has failed to divide `n`, and `n` trivially divides
//! itself, so returning `n` there is what continuing the search would have
//! found anyway (a prime `n`'s own least divisor `≥ 2` is itself).
//!
//! This is the boundary the module brief warns about: `minFac 0 = 2` and
//! `minFac 1 = 1` are handled by an outer case split BEFORE the fuel search
//! ever runs (`n - 2` truncates to `0` for `n < 2`, which would make the
//! search degenerate rather than wrong, but the two values are genuinely
//! different conventions, not a search result, so they get their own
//! branches).
//!
//! Any divisor found first, scanning upward from `2`, is automatically PRIME:
//! if the first divisor `d` found were composite, `d` would itself have a
//! divisor `2 ≤ e < d`, and `e ∣ d ∣ n` means `e` would have been found
//! first. So "first divisor found" and "smallest prime divisor" coincide for
//! this search, and `minFac 12 = 2` / `minFac 15 = 3` is exactly the
//! evaluation test (`min_fac.rs`'s own test module) discriminating a correct
//! search from one that returns the wrong candidate.

use super::NatPrelude;
use super::finite::{ne_of_lt, ne_symm, pos_implies_succ_pred};
use super::helpers::iff_reverse;
use super::ops::{NatDev, NatOps};
use super::primes::min_condition;
use super::steps::absurd;
use super::steps::or_cases;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

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

/// `Nat.minFacAux` (structural fuel recursion, see the module doc) and
/// `Nat.minFac` (the two boundary cases plus the search).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_min_fac_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let level_one = d.level_one();
    let nat_to_nat = d.arrow(nat, nat);
    let nat_to_nat_to_nat = d.arrow(nat, nat_to_nat);

    // --- Nat.minFacAux : Nat -> Nat -> Nat -> Nat ---------------------------
    //
    // minFacAux zero n candidate        := candidate
    // minFacAux (succ f) n candidate    :=
    //   if beq (mod n candidate) 0 then candidate else minFacAux f n (succ candidate)
    {
        // fuel = zero: exhausted -- see the module doc for why returning the
        // candidate unchanged is correct here (it has already reached n).
        let zero_minor = {
            let n_fv = d.fresh_fvar();
            let candidate_fv = d.fresh_fvar();
            let candidate_var = d.kernel().fvar(candidate_fv);
            let with_candidate = d.lam_fv(candidate_fv, nat, candidate_var);
            d.lam_fv(n_fv, nat, with_candidate)
        };

        // fuel = succ f.
        let succ_minor = {
            let predecessor_fv = d.fresh_fvar();
            let row_fv = d.fresh_fvar();
            let row = d.kernel().fvar(row_fv);
            let n_fv = d.fresh_fvar();
            let n_var = d.kernel().fvar(n_fv);
            let candidate_fv = d.fresh_fvar();
            let candidate_var = d.kernel().fvar(candidate_fv);

            let remainder = d.modulo(n_var, candidate_var);
            let zero = d.zero();
            let is_divisor = d.beq(remainder, zero);
            let next_candidate = d.succ(candidate_var);
            let recurse = d.apply(row, &[n_var, next_candidate]);
            let body = d.bool_select_nat(is_divisor, candidate_var, recurse);

            let with_candidate = d.lam_fv(candidate_fv, nat, body);
            let with_n = d.lam_fv(n_fv, nat, with_candidate);
            let with_row = d.lam_fv(row_fv, nat_to_nat_to_nat, with_n);
            d.lam_fv(predecessor_fv, nat, with_row)
        };

        let motive = d
            .kernel()
            .lam(anon, nat, nat_to_nat_to_nat, BinderInfo::Default);
        let rec = d.kernel().const_(p.rec, vec![level_one]);
        let fuel_fv = d.fresh_fvar();
        let fuel_var = d.kernel().fvar(fuel_fv);
        let row = d.apply(rec, &[motive, zero_minor, succ_minor, fuel_var]);
        let value_term = d.lam_fv(fuel_fv, nat, row);

        let ty = d.arrow(nat, nat_to_nat_to_nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.min_fac_aux,
            uparams: vec![],
            ty,
            value: value_term,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // --- Nat.minFac n := if n=0 then 2 else if n=1 then 1 else
    //                     minFacAux (n-2) n 2 -------------------------------
    {
        let n_fv = d.fresh_fvar();
        let n_var = d.kernel().fvar(n_fv);
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);

        let is_zero = d.beq(n_var, zero);
        let is_one = d.beq(n_var, one);
        let fuel = d.sub(n_var, two);
        let searched = min_fac_aux(d, &p, fuel, n_var, two);
        let else_branch = d.bool_select_nat(is_one, one, searched);
        let body = d.bool_select_nat(is_zero, two, else_branch);

        let value_term = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, nat);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.min_fac,
            uparams: vec![],
            ty,
            value: value_term,
            hint: ReducibilityHint::Regular(5),
        })?;
    }

    Ok(())
}

// ============================================================================
// `minFacAuxMinimal`, `min_fac_minimal_of_two_le`, `coprime_of_lt_min_fac`.
//
// A NEW local development, not a flip of `F:ml430-nat-coprime-of-lt-minfac`
// (see the module doc above): this `minFac` is not Mathlib's `def`, so a
// theorem stated over Mathlib's `minFac` is a different proposition. What
// follows proves the analogous statement over THIS `minFac`, as its own
// `Nat.coprime_of_lt_min_fac`.
// ============================================================================

/// Given `divisor = succ divisor_pred` and a proof that
/// `beq (mod n divisor) zero = false`, produce `Not (dvd divisor n)`. Mirrors
/// the divisibility-refutation half of `primes.rs`'s `least_divisor_search`
/// succ case (`div_mod_exec` + `div_mod_remainder_eq_zero_iff_dvd` +
/// `iff_reverse`, then a `Bool` contradiction from `beq_eq_true_of_eq` against
/// the assumed `false`), generalized to an arbitrary divisor built from its
/// predecessor rather than only `succ j` inside an ordinary bound induction.
fn not_divides_of_remainder_nonzero(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    divisor_pred: ExprId,
    n: ExprId,
    condition_false: ExprId,
) -> ExprId {
    let p = *p;
    let divisor = d.succ(divisor_pred);
    let remainder = d.modulo(n, divisor);
    let quotient = d.div(n, divisor);
    let zero = d.zero();
    let exec = d.lemma(p.div_mod_exec, &[divisor_pred, n]);
    let spec = d.lemma(
        p.div_mod_remainder_eq_zero_iff_dvd,
        &[divisor, n, quotient, remainder, exec],
    );
    let remainder_zero_ty = d.eq(remainder, zero);
    let divides_ty = d.dvd(divisor, n);
    let reverse = iff_reverse(d, remainder_zero_ty, divides_ty, spec);

    let assumed_fv = d.fresh_fvar();
    let assumed = d.kernel().fvar(assumed_fv);
    let remainder_zero = d.apply(reverse, &[assumed]);
    let true_value = d.bool_true();
    let holds = d.lemma(p.beq_eq_true_of_eq, &[remainder, zero, remainder_zero]);
    let condition = d.beq(remainder, zero);
    let false_value = d.bool_false();
    let flipped = d.bool_symm(condition, false_value, condition_false);
    let impossible = d.bool_trans(false_value, condition, true_value, flipped, holds);
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let body = d.false_true_elim(false_ty, impossible);
    d.lam_fv(assumed_fv, divides_ty, body)
}

/// Congruence of `bool_select_nat`'s first argument: `h : Eq Bool cond value
/// ⊢ Eq Nat (bool_select_nat cond on_true on_false) (bool_select_nat value
/// on_true on_false)`. Mirrors [`NatOps::congr`](super::ops::NatOps::congr)
/// (`Eq Nat a b ⊢ Eq Nat (f a) (f b)`) with the equality's carrier `Bool`
/// instead of `Nat`, using `bool_eq_motive`/`bool_transport` in place of
/// `eq_motive`/`transport`. When `value` is a Bool LITERAL, the right-hand
/// side reduces (`ι`) to `on_true`/`on_false` directly, so callers use the
/// result at that reduced type without any further step.
fn bool_select_congr(
    d: &mut NatDev<'_>,
    cond: ExprId,
    value: ExprId,
    h: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let f_cond = d.bool_select_nat(cond, on_true, on_false);
    let motive = d.bool_eq_motive(cond, &|d, x| {
        let fx = d.bool_select_nat(x, on_true, on_false);
        d.eq(f_cond, fx)
    });
    let refl_case = d.refl(f_cond);
    d.bool_transport(cond, motive, refl_case, value, h)
}

/// The fuel-generalized statement at `fuel`: `∀ n candidate, Le 2 candidate →
/// Eq (add candidate fuel) n → min_condition(n, candidate) →
/// min_condition(n, minFacAux fuel n candidate)`. See the module doc's new
/// section for the overall shape; `candidate` and `n` are generalized inside
/// the induction on `fuel` exactly as `fibonacci.rs`'s `fib_aux_add_two_gen`
/// generalizes its own accumulator seed.
fn min_fac_aux_minimal_stmt(d: &mut NatDev<'_>, p: &NatPrelude, fuel: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let two = d.num(2);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let candidate_fv = d.fresh_fvar();
    let candidate = d.kernel().fvar(candidate_fv);
    let ge2_ty = d.le(two, candidate);
    let sum = d.add(candidate, fuel);
    let eqn_ty = d.eq(sum, n);
    let mc_ty = min_condition(d, &p, n, candidate);
    let searched = min_fac_aux(d, &p, fuel, n, candidate);
    let concl = min_condition(d, &p, n, searched);
    let inner = d.arrow(mc_ty, concl);
    let inner2 = d.arrow(eqn_ty, inner);
    let body = d.arrow(ge2_ty, inner2);
    let with_candidate = d.pi_fv(candidate_fv, nat, body);
    d.pi_fv(n_fv, nat, with_candidate)
}

/// Base case (`fuel = zero`): `minFacAux zero n candidate` reduces (`ι`) to
/// `candidate` unchanged, so the goal collapses to exactly the given
/// `min_condition(n, candidate)` hypothesis — no other hypothesis is used.
fn min_fac_aux_minimal_base(d: &mut NatDev<'_>, p: &NatPrelude) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let two = d.num(2);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let candidate_fv = d.fresh_fvar();
    let candidate = d.kernel().fvar(candidate_fv);
    let ge2_ty = d.le(two, candidate);
    let ge2_fv = d.fresh_fvar();
    let zero = d.zero();
    let sum = d.add(candidate, zero);
    let eqn_ty = d.eq(sum, n);
    let eqn_fv = d.fresh_fvar();
    let mc_ty = min_condition(d, &p, n, candidate);
    let mc_fv = d.fresh_fvar();
    let mc = d.kernel().fvar(mc_fv);
    let with_mc = d.lam_fv(mc_fv, mc_ty, mc);
    let with_eqn = d.lam_fv(eqn_fv, eqn_ty, with_mc);
    let with_ge2 = d.lam_fv(ge2_fv, ge2_ty, with_eqn);
    let with_candidate = d.lam_fv(candidate_fv, nat, with_ge2);
    d.lam_fv(n_fv, nat, with_candidate)
}

/// `min_condition(n, succ spc)`, built from `min_condition(n, spc)` and
/// `Not (dvd spc n)`: split `e < succ spc` (i.e. `e ≤ spc`) into `e < spc`
/// (hand off to `mc_spc`) or `e = spc` (transport `not_divides_spc` along the
/// equation), mirroring `primes.rs`'s `least_divisor_search` "extend" step.
fn min_condition_of_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    n: ExprId,
    spc: ExprId,
    mc_spc: ExprId,
    not_divides_spc: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let two = d.num(2);
    let ssp = d.succ(spc);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let ge_ty = d.le(two, e);
    let ge_fv = d.fresh_fvar();
    let ge = d.kernel().fvar(ge_fv);
    let lt_ty = d.lt(e, ssp);
    let lt_fv = d.fresh_fvar();
    let lt = d.kernel().fvar(lt_fv);

    let le_e_spc = d.lemma(p.le_of_succ_le_succ, &[e, spc, lt]);
    let split = d.lemma(p.lt_or_eq_of_le, &[e, spc, le_e_spc]);
    let strict_ty = d.lt(e, spc);
    let equal_ty = d.eq(e, spc);
    let goal = {
        let dv = d.dvd(e, n);
        d.const_app(p.logic.not, &[dv])
    };

    let lt_branch = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.apply(mc_spc, &[e, ge, h]);
        d.lam_fv(h_fv, strict_ty, body)
    };
    let eq_branch = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let reversed = d.symm(e, spc, h);
        let motive = d.eq_motive(spc, &|d, x| {
            let dv = d.dvd(x, n);
            d.const_app(p.logic.not, &[dv])
        });
        let body = d.transport(spc, motive, not_divides_spc, e, reversed);
        d.lam_fv(h_fv, equal_ty, body)
    };
    let body = or_cases(d, strict_ty, equal_ty, goal, lt_branch, eq_branch, split);
    let with_lt = d.lam_fv(lt_fv, lt_ty, body);
    let with_ge = d.lam_fv(ge_fv, ge_ty, with_lt);
    d.lam_fv(e_fv, nat, with_ge)
}

/// Succ case (`fuel = succ j`, given `ih : min_fac_aux_minimal_stmt(j)`).
/// See the module doc's new section: unfold `candidate` to `succ (pred
/// candidate)` (needed because `div_mod_exec` requires a positive divisor
/// expressed as a successor), prove the goal for that `spc := succ (pred
/// candidate)` by a `Bool.rec` case split on `beq (mod n spc) zero`
/// (mirroring `primes.rs`'s dependent-motive `Bool.rec` construction), then
/// transport back along `Eq candidate spc`.
fn min_fac_aux_minimal_step(d: &mut NatDev<'_>, p: &NatPrelude, j: ExprId, ih: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let two = d.num(2);
    let one = d.num(1);
    let zero = d.zero();
    let sj = d.succ(j);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let candidate_fv = d.fresh_fvar();
    let candidate = d.kernel().fvar(candidate_fv);
    let ge2_ty = d.le(two, candidate);
    let ge2_fv = d.fresh_fvar();
    let ge2 = d.kernel().fvar(ge2_fv);
    let candidate_plus_sj = d.add(candidate, sj);
    let eqn_ty = d.eq(candidate_plus_sj, n);
    let eqn_fv = d.fresh_fvar();
    let eqn = d.kernel().fvar(eqn_fv);
    let mc_ty = min_condition(d, &p, n, candidate);
    let mc_fv = d.fresh_fvar();
    let mc = d.kernel().fvar(mc_fv);

    // `candidate = succ (pred candidate)`, from `2 ≤ candidate`.
    let zero_lt_two = d.zero_lt_succ(one);
    let candidate_pos = d.lemma(p.lt_of_lt_of_le, &[zero, two, candidate, zero_lt_two, ge2]);
    let succ_pred_fn = pos_implies_succ_pred(d, &p, candidate);
    let eq_candidate_spc = d.apply(succ_pred_fn, &[candidate_pos]);
    let pc = d.pred(candidate);
    let spc = d.succ(pc);

    // Transport the three hypotheses from `candidate` to `spc`.
    let ge2_spc = {
        let motive = d.eq_motive(candidate, &|d, x| d.le(two, x));
        d.transport(candidate, motive, ge2, spc, eq_candidate_spc)
    };
    let eqn_spc = {
        let motive = d.eq_motive(candidate, &|d, x| {
            let x_plus_sj = d.add(x, sj);
            d.eq(x_plus_sj, n)
        });
        d.transport(candidate, motive, eqn, spc, eq_candidate_spc)
    };
    let mc_spc = {
        let motive = d.eq_motive(candidate, &|d, x| min_condition(d, &p, n, x));
        d.transport(candidate, motive, mc, spc, eq_candidate_spc)
    };

    // Build the goal for `spc` (call it `t`), then transport back.
    let remainder = d.modulo(n, spc);
    let condition_c = d.beq(remainder, zero);
    let ssp = d.succ(spc);
    let recurse = min_fac_aux(d, &p, j, n, ssp);

    let minimality_at = |d: &mut NatDev<'_>, selector: ExprId| -> ExprId {
        let selected = d.bool_select_nat(selector, spc, recurse);
        min_condition(d, &p, n, selected)
    };

    let divides_branch = {
        let h_fv = d.fresh_fvar();
        let true_value = d.bool_true();
        let eq_ty = d.bool_eq(condition_c, true_value);
        d.lam_fv(h_fv, eq_ty, mc_spc)
    };
    let refutes_branch = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let false_value = d.bool_false();
        let eq_ty = d.bool_eq(condition_c, false_value);

        let not_divides_spc = not_divides_of_remainder_nonzero(d, &p, pc, n, h);
        let le2_ssp = d.lemma(p.le_succ_of_le, &[two, spc, ge2_spc]);
        let succ_add_spc_j = d.lemma(p.succ_add, &[spc, j]);
        let combined = {
            let a = d.add(ssp, j);
            let spc_plus_j = d.add(spc, j);
            let b = d.succ(spc_plus_j);
            d.trans(a, b, n, succ_add_spc_j, eqn_spc)
        };
        let mc_ssp = min_condition_of_succ(d, &p, n, spc, mc_spc, not_divides_spc);
        let ih_applied = d.apply(ih, &[n, ssp, le2_ssp, combined, mc_ssp]);
        d.lam_fv(h_fv, eq_ty, ih_applied)
    };

    let bool_ty = d.bool_ty();
    let motive_sel = {
        let selector_fv = d.fresh_fvar();
        let selector = d.kernel().fvar(selector_fv);
        let eqn_sel = d.bool_eq(condition_c, selector);
        let body = minimality_at(d, selector);
        let arrowed = d.arrow(eqn_sel, body);
        d.lam_fv(selector_fv, bool_ty, arrowed)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    let selected = d.apply(
        bool_rec,
        &[motive_sel, refutes_branch, divides_branch, condition_c],
    );
    let reflexivity = d.bool_refl(condition_c);
    let t = d.apply(selected, &[reflexivity]);

    // Transport `t : min_condition(n, minFacAux sj n spc)` back along
    // `Eq spc candidate` to get `min_condition(n, minFacAux sj n candidate)`.
    let eq_spc_candidate = d.symm(candidate, spc, eq_candidate_spc);
    let motive_final = d.eq_motive(spc, &|d, x| {
        let searched = min_fac_aux(d, &p, sj, n, x);
        min_condition(d, &p, n, searched)
    });
    let result = d.transport(spc, motive_final, t, candidate, eq_spc_candidate);

    let with_mc = d.lam_fv(mc_fv, mc_ty, result);
    let with_eqn = d.lam_fv(eqn_fv, eqn_ty, with_mc);
    let with_ge2 = d.lam_fv(ge2_fv, ge2_ty, with_eqn);
    let with_candidate = d.lam_fv(candidate_fv, nat, with_ge2);
    d.lam_fv(n_fv, nat, with_candidate)
}

/// `Nat.minFacAuxMinimal`. See the module doc's new section and
/// [`min_fac_aux_minimal_stmt`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_min_fac_aux_minimal(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.min_fac_aux_minimal, 1, &|d, v| {
        let fuel = v[0];
        let stmt = min_fac_aux_minimal_stmt(d, &p, fuel);
        let base = |d: &mut NatDev<'_>| min_fac_aux_minimal_base(d, &p);
        let step =
            |d: &mut NatDev<'_>, j: ExprId, ih: ExprId| min_fac_aux_minimal_step(d, &p, j, ih);
        let proof = d.induct(
            &|d: &mut NatDev<'_>, f: ExprId| min_fac_aux_minimal_stmt(d, &p, f),
            &base,
            &step,
            fuel,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.min_fac_minimal_of_two_le : ∀ n, Le 2 n → ∀ e, Le 2 e → Lt e (minFac
/// n) → Not (dvd e n)`. Unwinds `minFac n`'s two boundary `bool_select_nat`
/// wrappers (both `false`, since `2 ≤ n` rules out `n = 0` and `n = 1`) down
/// to `minFacAux (sub n 2) n 2`, then applies
/// [`declare_min_fac_aux_minimal`]'s theorem at that fuel/candidate pair,
/// with the vacuous `min_condition(n, 2)` (nothing is both `≥ 2` and `< 2`).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_min_fac_minimal_of_two_le(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.min_fac_minimal_of_two_le, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let one = d.num(1);
        let two = d.num(2);
        let h2n_ty = d.le(two, n);
        let h2n_fv = d.fresh_fvar();
        let h2n = d.kernel().fvar(h2n_fv);

        // `n ≠ 0` and `n ≠ 1` from `2 ≤ n`.
        let zero_lt_two = d.zero_lt_succ(one);
        let zero_lt_n = d.lemma(p.lt_of_lt_of_le, &[zero, two, n, zero_lt_two, h2n]);
        let zero_ne_n = ne_of_lt(d, &p, zero, n, zero_lt_n);
        let n_ne_zero = ne_symm(d, zero, n, zero_ne_n);
        let is_zero_false = d.lemma(p.beq_eq_false_of_ne, &[n, zero, n_ne_zero]);
        let one_lt_n = h2n; // `Le 2 n` is `Lt 1 n` by defeq (`succ one = two`).
        let one_ne_n = ne_of_lt(d, &p, one, n, one_lt_n);
        let n_ne_one = ne_symm(d, one, n, one_ne_n);
        let is_one_false = d.lemma(p.beq_eq_false_of_ne, &[n, one, n_ne_one]);

        // Unwind `minFac n` to `minFacAux (sub n 2) n 2`.
        let fuel = d.sub(n, two);
        let searched = min_fac_aux(d, &p, fuel, n, two);
        let is_zero = d.beq(n, zero);
        let is_one = d.beq(n, one);
        let else_branch = d.bool_select_nat(is_one, one, searched);
        let full_body = d.bool_select_nat(is_zero, two, else_branch);
        let false_value = d.bool_false();
        let outer = bool_select_congr(d, is_zero, false_value, is_zero_false, two, else_branch);
        let inner = bool_select_congr(d, is_one, false_value, is_one_false, one, searched);
        let unfold_eq = d.trans(full_body, else_branch, searched, outer, inner);

        // `min_condition(n, 2)`: vacuous, nothing is both `≥ 2` and `< 2`.
        let vacuous = {
            let nat = d.nat_ty();
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let ge_ty = d.le(two, e);
            let ge_fv = d.fresh_fvar();
            let ge = d.kernel().fvar(ge_fv);
            let lt_ty = d.lt(e, two);
            let lt_fv = d.fresh_fvar();
            let lt = d.kernel().fvar(lt_fv);
            let e_le_1 = d.lemma(p.le_of_succ_le_succ, &[e, one, lt]);
            let two_le_1 = d.lemma(p.le_trans, &[two, e, one, ge, e_le_1]);
            let contradiction = d.lemma(p.not_succ_le_self, &[one, two_le_1]);
            let goal = {
                let dv = d.dvd(e, n);
                d.const_app(p.logic.not, &[dv])
            };
            let body = absurd(d, goal, contradiction);
            let with_lt = d.lam_fv(lt_fv, lt_ty, body);
            let with_ge = d.lam_fv(ge_fv, ge_ty, with_lt);
            d.lam_fv(e_fv, nat, with_ge)
        };

        let ge2_2 = d.lemma(p.le_refl, &[two]);
        let cancel = d.lemma(p.add_sub_cancel_of_le, &[two, n, h2n]);
        let minimal_at_fuel = d.lemma(
            p.min_fac_aux_minimal,
            &[fuel, n, two, ge2_2, cancel, vacuous],
        );

        let min_fac_n = d.const_app(p.min_fac, &[n]);
        let rev = d.symm(min_fac_n, searched, unfold_eq);
        let motive = d.eq_motive(searched, &|d, x| min_condition(d, &p, n, x));
        let transported = d.transport(searched, motive, minimal_at_fuel, min_fac_n, rev);

        let concl_ty = transported_ty_placeholder(d, &p, n);
        let stmt = d.arrow(h2n_ty, concl_ty);
        let proof = d.lam_fv(h2n_fv, h2n_ty, transported);
        (stmt, proof)
    })?;
    Ok(())
}

/// The conclusion type `min_condition(n, minFac n)` — factored out so the
/// STATEMENT half of [`declare_min_fac_minimal_of_two_le`] matches the PROOF
/// half without duplicating the construction.
fn transported_ty_placeholder(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let p = *p;
    let min_fac_n = d.const_app(p.min_fac, &[n]);
    min_condition(d, &p, n, min_fac_n)
}

/// `Nat.coprime_of_lt_min_fac : ∀ n m, Not (Eq m zero) → Lt m (minFac n) →
/// Eq (gcd n m) one`. See the module doc's new section: case split on `n`
/// (`< 2` via [`super::ops::cases_lt_bound`], `≥ 2` via
/// [`super::ops::cases_lt_or_ge`]); the `n ≥ 2` branch is the interesting
/// one, deriving a contradiction from `gcd n m ≥ 2` via
/// [`declare_min_fac_minimal_of_two_le`].
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_of_lt_min_fac(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.coprime_of_lt_min_fac, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let one = d.num(1);
        let two = d.num(2);

        let motive = |d: &mut NatDev<'_>, x: ExprId| -> ExprId {
            let zero = d.zero();
            let eq_m0 = d.eq(m, zero);
            let ne_ty = d.const_app(p.logic.not, &[eq_m0]);
            let min_fac_x = d.const_app(p.min_fac, &[x]);
            let lt_ty = d.lt(m, min_fac_x);
            let g = d.gcd(x, m);
            let one = d.num(1);
            let concl = d.eq(g, one);
            let inner = d.arrow(lt_ty, concl);
            d.arrow(ne_ty, inner)
        };
        let stmt = motive(d, n);

        // `n = 0`: `minFac 0 = 2`; `Lt m 2` and `m ≠ 0` force `m = 1`, and
        // `gcd 0 1 = 1` directly.
        let branch0 = {
            let ne_fv = d.fresh_fvar();
            let ne = d.kernel().fvar(ne_fv);
            let zero = d.zero();
            let ne_ty = {
                let eq_m0 = d.eq(m, zero);
                d.const_app(p.logic.not, &[eq_m0])
            };
            let min_fac_0 = d.const_app(p.min_fac, &[zero]);
            let lt_ty = d.lt(m, min_fac_0);
            let lt_fv = d.fresh_fvar();
            let lt = d.kernel().fvar(lt_fv);

            // `Lt m (minFac 0)` is defeq `Lt m 2 = Le (succ m) (succ one)`.
            let le_m_1 = d.lemma(p.le_of_succ_le_succ, &[m, one, lt]);
            let split = d.lemma(p.lt_or_eq_of_le, &[m, one, le_m_1]);
            let lt_m1_ty = d.lt(m, one);
            let eq_m1_ty = d.eq(m, one);
            let goal = {
                let g = d.gcd(zero, m);
                d.eq(g, one)
            };

            // `Lt m 1`: forces `m = 0`, contradicting `ne`.
            let lt_branch_m = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let le_m_0 = d.lemma(p.le_of_succ_le_succ, &[m, zero, h]);
                let le_0_m = d.lemma(p.zero_le, &[m]);
                let m_eq_0 = d.lemma(p.le_antisymm, &[m, zero, le_m_0, le_0_m]);
                let false_proof = d.apply(ne, &[m_eq_0]);
                let body = absurd(d, goal, false_proof);
                d.lam_fv(h_fv, lt_m1_ty, body)
            };
            // `Eq m 1`: transport `gcd 0 1 = 1` along `Eq 1 m`.
            let eq_branch_m = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let base = d.lemma(p.gcd_zero_left, &[one]);
                let reversed = d.symm(m, one, h);
                let motive = d.eq_motive(one, &|d, x| {
                    let zero = d.zero();
                    let g = d.gcd(zero, x);
                    let one = d.num(1);
                    d.eq(g, one)
                });
                let body = d.transport(one, motive, base, m, reversed);
                d.lam_fv(h_fv, eq_m1_ty, body)
            };
            let body = or_cases(d, lt_m1_ty, eq_m1_ty, goal, lt_branch_m, eq_branch_m, split);
            let with_lt = d.lam_fv(lt_fv, lt_ty, body);
            d.lam_fv(ne_fv, ne_ty, with_lt)
        };

        // `n = 1`: `minFac 1 = 1`; `Lt m 1` forces `m = 0`, contradicting
        // `m ≠ 0` directly.
        let branch1 = {
            let ne_fv = d.fresh_fvar();
            let ne = d.kernel().fvar(ne_fv);
            let zero = d.zero();
            let ne_ty = {
                let eq_m0 = d.eq(m, zero);
                d.const_app(p.logic.not, &[eq_m0])
            };
            let min_fac_1 = d.const_app(p.min_fac, &[one]);
            let lt_ty = d.lt(m, min_fac_1);
            let lt_fv = d.fresh_fvar();
            let lt = d.kernel().fvar(lt_fv);

            let le_m_0 = d.lemma(p.le_of_succ_le_succ, &[m, zero, lt]);
            let le_0_m = d.lemma(p.zero_le, &[m]);
            let m_eq_0 = d.lemma(p.le_antisymm, &[m, zero, le_m_0, le_0_m]);
            let false_proof = d.apply(ne, &[m_eq_0]);
            let goal1 = {
                let g = d.gcd(one, m);
                d.eq(g, one)
            };
            let body = absurd(d, goal1, false_proof);
            let with_lt = d.lam_fv(lt_fv, lt_ty, body);
            d.lam_fv(ne_fv, ne_ty, with_lt)
        };

        // `n ≥ 2`: the real argument.
        let big = |d: &mut NatDev<'_>, x: ExprId, h2x: ExprId| -> ExprId {
            let ne_fv = d.fresh_fvar();
            let ne = d.kernel().fvar(ne_fv);
            let zero = d.zero();
            let ne_ty = {
                let eq_m0 = d.eq(m, zero);
                d.const_app(p.logic.not, &[eq_m0])
            };
            let min_fac_x = d.const_app(p.min_fac, &[x]);
            let lt_ty = d.lt(m, min_fac_x);
            let lt_fv = d.fresh_fvar();
            let lt = d.kernel().fvar(lt_fv);

            let g = d.gcd(x, m);
            let one = d.num(1);
            let goal = d.eq(g, one);

            let m_pos = d.lemma(p.zero_lt_of_ne_zero, &[m, ne]);
            let g_dvd_m = d.lemma(p.gcd_dvd_right, &[x, m]);
            let one_le_g = d.lemma(p.one_le_of_dvd_pos, &[g, m, m_pos, g_dvd_m]);
            let split = d.lemma(p.lt_or_eq_of_le, &[one, g, one_le_g]);
            let lt_1_g_ty = d.lt(one, g);
            let eq_1_g_ty = d.eq(one, g);

            let eq_branch = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let result = d.symm(one, g, h);
                d.lam_fv(h_fv, eq_1_g_ty, result)
            };
            let lt_branch = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let g_dvd_x = d.lemma(p.gcd_dvd_left, &[x, m]);
                let g_le_m = d.lemma(p.le_of_dvd, &[g, m, m_pos, g_dvd_m]);
                let g_lt_min_fac = d.lemma(p.lt_of_le_of_lt, &[g, m, min_fac_x, g_le_m, lt]);
                let not_dvd = d.lemma(p.min_fac_minimal_of_two_le, &[x, h2x, g, h, g_lt_min_fac]);
                let false_proof = d.apply(not_dvd, &[g_dvd_x]);
                let result = absurd(d, goal, false_proof);
                d.lam_fv(h_fv, lt_1_g_ty, result)
            };
            let proof_body = or_cases(d, lt_1_g_ty, eq_1_g_ty, goal, lt_branch, eq_branch, split);
            let with_lt = d.lam_fv(lt_fv, lt_ty, proof_body);
            d.lam_fv(ne_fv, ne_ty, with_lt)
        };

        let proof = super::ops::cases_lt_or_ge(
            d,
            &p,
            n,
            two,
            &motive,
            &|d, x, h_lt| {
                super::ops::cases_lt_bound(d, &p, x, 2, h_lt, &motive, &[branch0, branch1])
            },
            &big,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare every theorem in this file's second section (see the module doc).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_min_fac_minimal_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_min_fac_aux_minimal(d, p)?;
    declare_min_fac_minimal_of_two_le(d, p)?;
    declare_coprime_of_lt_min_fac(d, p)?;
    Ok(())
}
