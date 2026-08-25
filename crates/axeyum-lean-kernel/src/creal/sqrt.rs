//! **`CReal.natSqrt`**: the integer square root, by structural recursion, with
//! its defining two-sided bound — the missing computational primitive behind
//! `CReal.sqrt`.
//!
//! ## Why this file exists, and why it stops here
//!
//! `CReal.sqrt`'s only genuinely hard part is not real-analysis machinery —
//! `equiv_of_bounded`, `regular_between`, `fuse_at`
//! ([`super::product`]) and `ratSqLe`/`ratSqSandwich`
//! ([`super::mul_self_zero`]) already give the CReal-level estimate template
//! (see that module's docs: the sandwich lemma turns a rational bound on a
//! *square* directly into a `CReal.Within`, with no division and no case split
//! on which of two reals is bigger). What is missing is a **rational square
//! root approximation with a proven error bound**, and nothing in the trusted
//! library computes one: `RatPrelude` has no `sqrt`/`pow`-inverse, and the one
//! natural place to build it — `Nat`'s own integer square root — does not
//! exist in `nat_prelude` either.
//!
//! Building that primitive needs a genuine **decidable, data-level** search
//! (unlike every real-order fact in this module, which is `Prop`-valued and
//! cannot select data — see [`CReal.inv`](super::CRealPrelude::inv)'s own
//! docs on exactly this restriction). The tool that makes it possible without
//! any new axiom is [`NatOps::ble`](crate::nat_prelude::NatOps::ble) (`Bool`,
//! not `Prop`, so `Bool.rec` may select a `Nat` freely) together with
//! [`NatOps::bool_select_nat`](crate::nat_prelude::NatOps::bool_select_nat)
//! (already built, and already used by `Nat.div`/`Nat.mod`'s own executable
//! state — [`nat_prelude::division`](crate::nat_prelude) — which is the
//! template this file follows).
//!
//! **This slice stays at the `Nat` level on purpose.** Lifting `natSqrt` to a
//! rational approximant of a `CReal` sample needs a decidable comparison for
//! `Rat`/`Int` (built from `Nat.ble` by a constructor case split on `Int`,
//! itself unproblematic since `Int.rec` eliminates into any `Sort` — `Int` is
//! a `Type`, not a `Prop`) and then the sampling-index schedule that
//! compensates for `sqrt` **not** being Lipschitz at `0` (its modulus of
//! continuity is itself a square root: `|sqrt a − sqrt b| ≤ sqrt |a−b|`,
//! provable from `ratSqSandwich` applied to `sqrt a − sqrt b` without ever
//! dividing by `sqrt a + sqrt b`, which is what makes `0 ≤ x` — not
//! `PosBound x k` — the honest hypothesis for `CReal.sqrt`, unlike
//! `CReal.inv`: nothing here needs to *decide* how close to zero `x` is,
//! only to *sample deeper* as the target precision tightens). That remaining
//! climb is real-analysis-sized on its own (`CReal.mul`'s `product.rs` is
//! 2400+ lines; `mul_self_zero.rs`, reusing most of that, still took a
//! four-lane chain — its own commit message says so) and is exactly the
//! obstruction named in this slice's report, not solved by it.

use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{den, normalize, num, one_le_succ, rat_ty, rzero};

use super::{CRealPrelude, DERIVED_HEIGHT, and_intro, creal_ty, sample};

/// `And left right`, as a `Prop`. Generic over what `left`/`right` are —
/// unlike [`super::equiv`]/[`super::within`], this file's statements are
/// plain `Nat` facts, so there is no `CReal`-specific packaging to reuse.
fn and_ty(d: &mut IntDev<'_>, p: CRealPrelude, left: ExprId, right: ExprId) -> ExprId {
    d.const_app(p.rat.int.logic.and, &[left, right])
}

/// `False.rec (fun _ => target) false_proof : target`.
///
/// A local copy of the identical private helper in `nat_prelude::fermat`,
/// `nat_prelude::totient`, `nat_prelude::order_more`, and
/// `nat_prelude::binomial` (each of those, in turn, a copy of the others) —
/// adapted here to `IntDev` since this module builds over `IntDev`, not
/// `NatDev`. Trivial enough (one `False.rec` application) that a fifth copy
/// costs nothing next to threading a `NatDev`-specific dependency through the
/// `creal` module boundary.
#[allow(dead_code)] // staged for declare_kregular_sqrt_approx (Step A/B, not yet landed)
fn ex_falso(d: &mut IntDev<'_>, p: CRealPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let nat = p.rat.int.nat;
    let false_ty = d.kernel().const_(nat.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(nat.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `h : Lt zero n ⊢ Eq n (succ (pred n))` — i.e. `1 ≤ n → n = succ (pred n)`
/// (`Nat.lt zero n` is definitionally `Nat.le (succ zero) n = Nat.le 1 n`).
///
/// A local copy of `nat_prelude::finite::pos_implies_succ_pred` (itself
/// duplicated in `fermat.rs` and `totient.rs` — this is the fourth copy, and
/// per that helper's own doc comment, promoting it to a declared `Nat`
/// theorem reachable outside `nat_prelude` is the right long-term fix, not
/// attempted here). By induction on `n`: the base case is impossible via
/// `not_lt_zero`; the successor case is `refl`, since `pred (succ m)` reduces
/// to `m` definitionally. `n` may be any `Nat`-typed expression, not just a
/// bound variable — `Nat.rec` does not require its target to reduce.
#[allow(dead_code)] // staged for declare_kregular_sqrt_approx (Step A/B, not yet landed)
fn one_le_implies_succ_pred(d: &mut IntDev<'_>, p: CRealPrelude, n: ExprId) -> ExprId {
    let nat = p.rat.int.nat;
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let zero = d.zero();
        let hyp = d.lt(zero, x);
        let px = d.pred(x);
        let spx = d.succ(px);
        let concl = d.eq(x, spx);
        d.arrow(hyp, concl)
    };
    d.induct(
        &motive,
        &|d: &mut IntDev<'_>| {
            let zero = d.zero();
            let hyp_ty = d.lt(zero, zero);
            let hyp_fv = d.fresh_fvar();
            let hyp = d.kernel().fvar(hyp_fv);
            let pz = d.pred(zero);
            let spz = d.succ(pz);
            let target_ty = d.eq(zero, spz);
            let not_lt = d.lemma(nat.not_lt_zero, &[zero]);
            let false_proof = d.apply(not_lt, &[hyp]);
            let body = ex_falso(d, p, target_ty, false_proof);
            d.lam_fv(hyp_fv, hyp_ty, body)
        },
        &|d: &mut IntDev<'_>, m: ExprId, _ih: ExprId| {
            let sm = d.succ(m);
            let zero = d.zero();
            let hyp_ty = d.lt(zero, sm);
            let hyp_fv = d.fresh_fvar();
            let _hyp = d.kernel().fvar(hyp_fv);
            let body = d.refl(sm);
            d.lam_fv(hyp_fv, hyp_ty, body)
        },
        n,
    )
}

/// Step A's Nat-level floor bracket (`docs/mathematics-2026-08/diary-creal-sqrt.md`):
/// given a positive denominator `b` (`b_pos : Le one b`, e.g. `Rat.den_pos`)
/// and a dividend `scaled`, writing `k := Nat.div scaled b` and
/// `s := CReal.natSqrt k`, returns `s` together with
///
/// - `lower : Le (b*(s*s)) scaled`
/// - `upper : Lt scaled (b*((succ s)*(succ s)))`
///
/// **Derivation.** `one_le_implies_succ_pred` turns `b_pos` (`Lt zero b`,
/// definitionally `Le one b`) into `b = succ (pred b)`; rewriting
/// `Nat.div_mod_exec (pred b) scaled` along that equality (in both the
/// divisor position and inside the `div`/`mod` it names) gives `divMod b
/// scaled k (Nat.mod scaled b)` with `k` and `Nat.mod scaled b` matching the
/// `div`/`modulo` built directly from `b` — the rewrite target is chosen to
/// land exactly there so no further massaging is needed. `Nat.div_mod_bounds`
/// then gives `b*k ≤ scaled < b*(succ k)`. `natSqrtLe`/`natSqrtLt` give `s*s ≤
/// k < (succ s)*(succ s)` i.e. `succ k ≤ (succ s)*(succ s)`; `mul_le_mul_left`
/// scales both by `b` (`b*(s*s) ≤ b*k` and `b*(succ k) ≤ b*((succ
/// s)*(succ s))`), and `le_trans`/`lt_of_lt_of_le` compose each with the
/// `div_mod_bounds` half on the same side.
#[allow(dead_code)] // staged for declare_kregular_sqrt_approx (Step A/B/C, not yet landed)
fn nat_floor_bracket(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    b: ExprId,
    b_pos: ExprId,
    scaled: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let nat = p.rat.int.nat;

    // b = succ (pred b).
    let succ_pred_fn = one_le_implies_succ_pred(d, p, b);
    let b_eq_succ_pred = d.apply(succ_pred_fn, &[b_pos]);
    let pred_b = d.pred(b);
    let sp = d.succ(pred_b);
    let sp_eq_b = d.symm(b, sp, b_eq_succ_pred);

    // The executable witness, stated at the successor-shaped divisor `sp`.
    let exec = d.lemma(nat.div_mod_exec, &[pred_b, scaled]);
    // exec : divMod sp scaled (Nat.div scaled sp) (Nat.mod scaled sp)

    // Rewrite `sp` to `b` throughout, via `sp_eq_b : Eq sp b`.
    let motive = d.eq_motive(sp, &|d, x| {
        let q = NatOps::div(d, scaled, x);
        let r = NatOps::modulo(d, scaled, x);
        d.div_mod(x, scaled, q, r)
    });
    let relation = d.transport(sp, motive, exec, b, sp_eq_b);
    // relation : divMod b scaled (Nat.div scaled b) (Nat.mod scaled b)

    let k = NatOps::div(d, scaled, b);
    let r = NatOps::modulo(d, scaled, b);
    let bounds = d.lemma(nat.div_mod_bounds, &[b, scaled, k, r]);
    let bounds = d.apply(bounds, &[relation]);
    // bounds : And (Le (b*k) scaled) (Lt scaled (b*(succ k)))
    let bk = d.mul(b, k);
    let lower_ty = d.le(bk, scaled);
    let succ_k = d.succ(k);
    let b_succ_k = d.mul(b, succ_k);
    let upper_ty = d.lt(scaled, b_succ_k);
    let bounds_lower = d.and_left(lower_ty, upper_ty, bounds);
    let bounds_upper = d.and_right(lower_ty, upper_ty, bounds);

    let s = d.const_app(p.nat_sqrt, &[k]);
    let ss = d.mul(s, s);
    // s*s <= k
    let sqrt_le = d.lemma(p.nat_sqrt_le, &[k]);
    // k < (succ s)*(succ s), i.e. succ k <= (succ s)*(succ s)
    let sqrt_lt = d.lemma(p.nat_sqrt_lt, &[k]);
    let succ_s = d.succ(s);
    let succ_s_sq = d.mul(succ_s, succ_s);

    // b*(s*s) <= b*k <= scaled.
    let b_ss = d.mul(b, ss);
    let scale_lower = d.lemma(nat.mul_le_mul_left, &[b, ss, k, sqrt_le]);
    let lower = d.lemma(nat.le_trans, &[b_ss, bk, scaled, scale_lower, bounds_lower]);

    // scaled < b*(succ k) <= b*((succ s)*(succ s)).
    let b_succ_s_sq = d.mul(b, succ_s_sq);
    let scale_upper = d.lemma(nat.mul_le_mul_left, &[b, succ_k, succ_s_sq, sqrt_lt]);
    let upper = d.lemma(
        nat.lt_of_lt_of_le,
        &[scaled, b_succ_k, b_succ_s_sq, bounds_upper, scale_upper],
    );

    (s, lower, upper)
}

/// From `h : Eq Bool b Bool.false`, derive `Not (Eq Bool b Bool.true)`.
///
/// `b`'s two possible values are mutually exclusive
/// ([`NatOps::false_true_elim`](crate::nat_prelude::NatOps::false_true_elim)
/// is the existing `Bool.false ≠ Bool.true` discriminator); this is the
/// one-line bridge from "`b` computed to `false`" to "`b` did not compute to
/// `true`", needed to reach [`RatPrelude`](crate::RatPrelude)'s Nat-level
/// `not_le_of_not_ble_eq_true` from the *other* branch of a
/// [`NatOps::bool_select_nat`] discriminant.
fn not_bool_eq_true_of_false(d: &mut IntDev<'_>, b: ExprId, h_false: ExprId) -> ExprId {
    let false_ = d.bool_false();
    let true_ = d.bool_true();
    let sym = d.bool_symm(b, false_, h_false);
    let h2_ty = d.bool_eq(b, true_);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let contra = d.bool_trans(false_, b, true_, sym, h2);
    let false_name = d.prelude().logic.false_;
    let false_ty = d.kernel().const_(false_name, vec![]);
    let body = d.false_true_elim(false_ty, contra);
    d.lam_fv(h2_fv, h2_ty, body)
}

/// `Nat.le (Nat.succ (Nat.mul a a)) (Nat.mul (Nat.succ a) (Nat.succ a))` —
/// `(a+1)² ≥ a²+1`, the one algebraic fact the successor case of
/// [`declare_nat_sqrt_spec`] needs to grow the upper bound.
///
/// `(a+1)·(a+1) = ((a·a)+a)+(a+1)` (`succ_mul` then `mul_succ`, folded by one
/// `congr`); `succ(a·a) = (a·a)+1 ≤ (a·a)+(a+1)` (`1 ≤ a+1` is
/// `le_succ_succ` at `zero_le a`, scaled by `add_le_add_left`); and
/// `(a·a)+(a+1) ≤ ((a·a)+a)+(a+1)` is `le_add_right` scaled by
/// `add_le_add_right`. `le_trans` composes the two, and the whole thing is
/// rewritten back along the opening identity.
fn sq_step_bound(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    let nat = p.rat.int.nat;
    let pa = d.mul(a, a);
    let succ_a = d.succ(a);

    // (a+1)*(a+1) = ((a*a)+a)+(a+1).
    let a_succ_a = d.mul(a, succ_a);
    let pa_plus_a = d.add(pa, a);
    let step_succ_mul = d.const_app(nat.succ_mul, &[a, succ_a]);
    let step_mul_succ = d.const_app(nat.mul_succ, &[a, a]);
    let lhs0 = d.mul(succ_a, succ_a);
    let mid0 = d.add(a_succ_a, succ_a);
    let rhs0 = d.add(pa_plus_a, succ_a);
    let congr1 = d.congr(a_succ_a, pa_plus_a, step_mul_succ, &|d, t| d.add(t, succ_a));
    let (_, whole_eq) = d.chain(lhs0, &[(mid0, step_succ_mul), (rhs0, congr1)]);

    // succ(a*a) <= (a*a) + (a+1), via (a*a)+1 = succ(a*a) and 1 <= a+1.
    let zero = d.zero();
    let one = d.succ(zero);
    let zero_le_a = d.const_app(nat.zero_le, &[a]);
    let one_le_succ_a = d.const_app(nat.le_succ_succ, &[zero, a, zero_le_a]);
    let pa_one = d.add(pa, one);
    let pa_succ_a = d.add(pa, succ_a);
    let add_le_1 = d.const_app(nat.add_le_add_left, &[pa, one, succ_a, one_le_succ_a]);
    let add_succ_pa = d.const_app(nat.add_succ, &[pa, zero]);
    let pa_zero = d.add(pa, zero);
    let add_zero_pa = d.const_app(nat.add_zero, &[pa]);
    let congr2 = d.congr(pa_zero, pa, add_zero_pa, &|d, t| d.succ(t));
    let succ_pa_zero = d.succ(pa_zero);
    let succ_pa = d.succ(pa);
    let (_, pa_one_eq_succ_pa) = d.chain(pa_one, &[(succ_pa_zero, add_succ_pa), (succ_pa, congr2)]);
    let add_le_1_at_succ_pa = {
        let motive = d.eq_motive(pa_one, &|d, t| d.le(t, pa_succ_a));
        d.transport(pa_one, motive, add_le_1, succ_pa, pa_one_eq_succ_pa)
    };
    // add_le_1_at_succ_pa : Le (succ pa) pa_succ_a

    // (a*a)+(a+1) <= ((a*a)+a)+(a+1), via (a*a) <= (a*a)+a.
    let le_add_right_pa_a = d.const_app(nat.le_add_right, &[pa, a]);
    let add_le_2 = d.const_app(
        nat.add_le_add_right,
        &[succ_a, pa, pa_plus_a, le_add_right_pa_a],
    );
    // add_le_2 : Le pa_succ_a rhs0

    let combined = d.const_app(
        nat.le_trans,
        &[succ_pa, pa_succ_a, rhs0, add_le_1_at_succ_pa, add_le_2],
    );
    // combined : Le (succ pa) rhs0

    let whole_eq_rev = d.symm(lhs0, rhs0, whole_eq);
    let motive2 = d.eq_motive(rhs0, &|d, t| d.le(succ_pa, t));
    d.transport(rhs0, motive2, combined, lhs0, whole_eq_rev)
}

/// `CReal.natSqrt : Nat -> Nat`, by structural recursion:
///
/// ```text
/// natSqrt 0        = 0
/// natSqrt (succ j) = let c := succ (natSqrt j)
///                     if Nat.ble (c*c) (succ j) then c else natSqrt j
/// ```
///
/// The single running candidate (rather than `Nat.choose`'s two-argument row,
/// or `Nat.div`/`Nat.mod`'s shared quotient/remainder state) is enough here:
/// unlike division, there is nothing to reset, only ever to grow by at most
/// one per step.
fn declare_nat_sqrt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
    let base = d.zero();
    let step = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let candidate = d.succ(ih);
        let succ_j = d.succ(j);
        let sq = d.mul(candidate, candidate);
        let cond = d.ble(sq, succ_j);
        let selected = d.bool_select_nat(cond, candidate, ih);
        let with_ih = d.lam_fv(ih_fv, nat, selected);
        d.lam_fv(j_fv, nat, with_ih)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec = d.kernel().const_(p.rat.int.nat.rec, vec![one]);
    let body = d.apply(rec, &[motive, base, step, n]);
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);
    // Strictly greater delta height than `Nat.mul`/`Nat.ble` (both height 1).
    d.kernel().add_declaration(Declaration::Definition {
        name: p.nat_sqrt,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(2),
    })
}

/// `CReal.natSqrtSpec : ∀ n,
///   And (Nat.le (natSqrt n * natSqrt n) n)
///       (Nat.lt n (succ (natSqrt n) * succ (natSqrt n)))`.
///
/// By induction on `n`, proving both halves together (the successor case
/// needs the upper-bound IH to grow the lower bound and vice versa). The
/// step case's discriminant is exactly `natSqrt`'s own `Nat.ble` test; the
/// standard `Bool.rec`-applied-to-the-discriminant-itself trick (as in
/// `nat_prelude::division`'s executable spec proof) recovers each branch as
/// a hypothesis without a separate "cases on this Bool" lemma.
fn declare_nat_sqrt_spec(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let nat = p.rat.int.nat;

    let spec = |d: &mut IntDev<'_>, n: ExprId| -> ExprId {
        let s = d.const_app(p.nat_sqrt, &[n]);
        let ss = d.mul(s, s);
        let left = d.le(ss, n);
        let s1 = d.succ(s);
        let s1s1 = d.mul(s1, s1);
        let right = d.lt(n, s1s1);
        and_ty(d, p, left, right)
    };

    d.theorem(p.nat_sqrt_spec, 1, &|d, v| {
        let n = v[0];
        let stmt = spec(d, n);
        let proof = d.induct(
            &spec,
            &|d| {
                let zero = d.zero();
                let sqrt0 = d.const_app(p.nat_sqrt, &[zero]);
                let ss0 = d.mul(sqrt0, sqrt0);
                let left_ty = d.le(ss0, zero);
                let left_proof = d.const_app(nat.le_refl, &[zero]);
                let succ_sqrt0 = d.succ(sqrt0);
                let rhs = d.mul(succ_sqrt0, succ_sqrt0);
                let right_ty = d.lt(zero, rhs);
                let right_proof = d.zero_lt_succ(sqrt0);
                and_intro(d, p, left_ty, right_ty, left_proof, right_proof)
            },
            &|d, j, ih| {
                let s = d.const_app(p.nat_sqrt, &[j]);
                let ss = d.mul(s, s);
                let left_ih_ty = d.le(ss, j);
                let succ_s = d.succ(s);
                let s1s1 = d.mul(succ_s, succ_s);
                let right_ih_ty = d.lt(j, s1s1);
                let ih_left = d.and_left(left_ih_ty, right_ih_ty, ih);
                let ih_right = d.and_right(left_ih_ty, right_ih_ty, ih);

                let succ_j = d.succ(j);
                let condition = d.ble(s1s1, succ_j);
                let bool_ty = d.bool_ty();

                let target_for = |d: &mut IntDev<'_>, selector: ExprId| -> ExprId {
                    let next = d.bool_select_nat(selector, succ_s, s);
                    let next_sq = d.mul(next, next);
                    let l = d.le(next_sq, succ_j);
                    let succ_next = d.succ(next);
                    let r_rhs = d.mul(succ_next, succ_next);
                    let r = d.lt(succ_j, r_rhs);
                    and_ty(d, p, l, r)
                };
                let branch_for = |d: &mut IntDev<'_>, selector: ExprId| -> ExprId {
                    let eqty = d.bool_eq(condition, selector);
                    let tgt = target_for(d, selector);
                    d.arrow(eqty, tgt)
                };

                let false_ = d.bool_false();
                let false_minor = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let h_ty = d.bool_eq(condition, false_);
                    let left_proof = d.const_app(nat.le_step, &[ss, j, ih_left]);
                    let not_true = not_bool_eq_true_of_false(d, condition, h);
                    let not_le =
                        d.const_app(nat.not_le_of_not_ble_eq_true, &[s1s1, succ_j, not_true]);
                    let right_proof = d.const_app(nat.lt_of_not_le, &[s1s1, succ_j, not_le]);
                    let left_ty = d.le(ss, succ_j);
                    let right_ty = d.lt(succ_j, s1s1);
                    let body = and_intro(d, p, left_ty, right_ty, left_proof, right_proof);
                    d.lam_fv(h_fv, h_ty, body)
                };

                let true_ = d.bool_true();
                let true_minor = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let h_ty = d.bool_eq(condition, true_);
                    let left_proof = d.const_app(nat.le_of_ble_eq_true, &[s1s1, succ_j, h]);

                    let succ_succ_j = d.succ(succ_j);
                    let succ_s1s1 = d.succ(s1s1);
                    let step1 = d.const_app(nat.le_succ_succ, &[succ_j, s1s1, ih_right]);
                    let bound2 = sq_step_bound(d, p, succ_s);
                    let succ_s1 = d.succ(succ_s);
                    let target_rhs = d.mul(succ_s1, succ_s1);
                    let right_proof = d.const_app(
                        nat.le_trans,
                        &[succ_succ_j, succ_s1s1, target_rhs, step1, bound2],
                    );

                    let left_ty = d.le(s1s1, succ_j);
                    let right_ty = d.lt(succ_j, target_rhs);
                    let body = and_intro(d, p, left_ty, right_ty, left_proof, right_proof);
                    d.lam_fv(h_fv, h_ty, body)
                };

                let motive = {
                    let selector_fv = d.fresh_fvar();
                    let selector = d.kernel().fvar(selector_fv);
                    let body = branch_for(d, selector);
                    d.lam_fv(selector_fv, bool_ty, body)
                };
                let level_zero = d.kernel().level_zero();
                let bool_rec = d
                    .kernel()
                    .const_(p.rat.int.logic.bool_rec, vec![level_zero]);
                let selected = d.apply(bool_rec, &[motive, false_minor, true_minor, condition]);
                let refl_cond = d.bool_refl(condition);
                d.apply(selected, &[refl_cond])
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `CReal.natSqrtLe : ∀ n, Nat.le (natSqrt n * natSqrt n) n` — the lower
/// projection of [`declare_nat_sqrt_spec`].
fn declare_nat_sqrt_le(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    d.theorem(p.nat_sqrt_le, 1, &|d, v| {
        let n = v[0];
        let s = d.const_app(p.nat_sqrt, &[n]);
        let ss = d.mul(s, s);
        let left = d.le(ss, n);
        let s1 = d.succ(s);
        let s1s1 = d.mul(s1, s1);
        let right = d.lt(n, s1s1);
        let spec_const = d.kernel().const_(p.nat_sqrt_spec, vec![]);
        let full = d.apply(spec_const, &[n]);
        let proof = d.and_left(left, right, full);
        (left, proof)
    })?;
    Ok(())
}

/// `CReal.natSqrtLt : ∀ n, Nat.lt n (succ (natSqrt n) * succ (natSqrt n))` —
/// the upper projection of [`declare_nat_sqrt_spec`].
fn declare_nat_sqrt_lt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    d.theorem(p.nat_sqrt_lt, 1, &|d, v| {
        let n = v[0];
        let s = d.const_app(p.nat_sqrt, &[n]);
        let ss = d.mul(s, s);
        let left = d.le(ss, n);
        let s1 = d.succ(s);
        let s1s1 = d.mul(s1, s1);
        let right = d.lt(n, s1s1);
        let spec_const = d.kernel().const_(p.nat_sqrt_spec, vec![]);
        let full = d.apply(spec_const, &[n]);
        let proof = d.and_right(left, right, full);
        (right, proof)
    })?;
    Ok(())
}

/// `CReal.sqrtApprox : CReal → Nat → Rat` — the rational approximant
/// `CReal.sqrt` will be built from.
///
/// ```text
/// sqrtApprox x n :=
///   let d := n + 1                                -- Nat
///   let j := d * d                                 -- Nat, the sample index
///   let q := Rat.max (CReal.seq x j) Rat.zero        -- Rat, clamped >= 0
///   let a := Int.natAbs (Rat.num q)                   -- Nat
///   let b := Rat.den q                                 -- Nat, >= 1
///   let k := Nat.div (a * j) b                          -- Nat
///   let s := CReal.natSqrt k                             -- Nat
///   Rat.normalize (Int.ofNat s) d (one_le_succ n)          -- Rat, "= s/d"
/// ```
///
/// **Why this shape.** Sampling `x` at `j = (n+1)²` rather than `n` puts `q`
/// within `Rat.natDivSucc 1 j = 1/((n+1)²+1)` of `x` — finer than the
/// `1/(n+1)²` the non-Lipschitz-at-0 modulus of `√` needs (module docs above)
/// — with **no `Nat` subtraction**. Clamping with `Rat.max q Rat.zero` needs
/// no case split on `x`'s sign (`Rat.max` dispatches on the representation,
/// [`super::lattice`]) and the hypothesis `0 ≤ x` is not consumed here at
/// all — matching the recorded signature decision that `sqrt`'s hypothesis
/// is needed only *inside proofs*, never as data driving the construction.
/// Reusing `j = d*d` as **both** the sample index and the fixed-point scale
/// (rather than an independent precision parameter) is what keeps this a
/// bare `Nat.rec`-free definition with no side proof obligation: `a*j` and
/// `b` are both already-computed naturals, and `Nat.div` is total.
///
/// **What this declaration does NOT establish.** `s/d` is within `O(1/d)` of
/// `√x` — from `natSqrtSpec` (`s² ≤ k < (s+1)²`, so `s/d ≤ √(k/j) < (s+1)/d`
/// since `j = d²`), plus the `Nat.div` floor error on `k` vs `a*j/b` (also
/// `O(1/d)` after dividing by `d`, via the same "`√` moves a gap of `ε` to a
/// gap of `√ε`" fact `ratSqLe`/`ratSqSandwich` already prove at the rational
/// level), plus `q`'s `O(1/d²)` distance from `x` contributing another
/// `O(1/d)` through that same non-Lipschitz modulus — but turning that into
/// the *exact* Bishop bound `CReal.Regular` demands (`|s(m)/d(m) - s(n)/d(n)|
/// ≤ 1/(m+1) + 1/(n+1)`, no free constant) is a genuine rational-inequality
/// argument that has not been built. See the module docs' closing paragraph
/// and this slice's final report for exactly what is missing.
pub(super) fn declare_sqrt_approx(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let rat_carrier = rat_ty(d);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let dd = d.succ(n);
    let j = NatOps::mul(d, dd, dd);
    let sample_q = sample(d, p, x, j);
    let zero_rat = rzero(d, p.rat);
    let q_pos = d.const_app(p.rat.max, &[sample_q, zero_rat]);
    let numerator = num(d, q_pos);
    let a = d.const_app(p.rat.int.nat_abs, &[numerator]);
    let b = den(d, q_pos);
    let scaled = NatOps::mul(d, a, j);
    let k = NatOps::div(d, scaled, b);
    let s = d.const_app(p.nat_sqrt, &[k]);
    let s_int = d.of_nat(s);
    let pos = one_le_succ(d, n);
    let body = normalize(d, s_int, dd, pos);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(x_fv, carrier, with_n)
    };
    let ty = {
        let inner = d.arrow(nat, rat_carrier);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.sqrt_approx,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DERIVED_HEIGHT + 43),
    })
}

/// Admit `CReal.natSqrt`, `CReal.natSqrtSpec`, `CReal.natSqrtLe`,
/// `CReal.natSqrtLt`, `CReal.sqrtApprox`.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_sqrt(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_nat_sqrt(d, p)?;
    declare_nat_sqrt_spec(d, p)?;
    declare_nat_sqrt_le(d, p)?;
    declare_nat_sqrt_lt(d, p)?;
    declare_sqrt_approx(d, p)
}

#[cfg(test)]
mod bridging_smoke_tests {
    use super::*;
    use crate::int_prelude::ops::IntDev;

    /// Smoke-checks [`one_le_implies_succ_pred`] (the local copy of bridging
    /// piece 1 from the sqrt route's "what is left" list) by wrapping it in
    /// a declared theorem and letting the kernel accept or reject it —
    /// building the Rust closures is not evidence the *term* is well-typed,
    /// only `Kernel::add_declaration`'s trusted checker is.
    #[test]
    fn one_le_implies_succ_pred_type_checks() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let nat = d.nat_ty();
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let zero = d.zero();
        let hyp = d.lt(zero, n);
        let pn = d.pred(n);
        let spn = d.succ(pn);
        let concl = d.eq(n, spn);
        let inner_ty = d.arrow(hyp, concl);

        let body = one_le_implies_succ_pred(&mut d, p, n);

        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.pi_fv(n_fv, nat, inner_ty);

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "sqrtSmokeOneLeImpliesSuccPred");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "one_le_implies_succ_pred must kernel-check: {:?}",
            result.err()
        );
    }

    /// Smoke-checks [`nat_floor_bracket`] (Step A's Nat-level core) at
    /// symbolic `b`/`scaled`, with the hypothesis stated the way
    /// [`crate::rat_prelude::ops::den_pos`] actually delivers it (`Le one
    /// b`, not `Lt zero b`) — the real call site (`sqrtApprox`'s `den q`)
    /// supplies exactly that shape, and `one_le_implies_succ_pred` expects
    /// `Lt zero b`; this checks the kernel accepts the unfolding without an
    /// explicit conversion step.
    #[test]
    fn nat_floor_bracket_type_checks() {
        let mut kernel = crate::Kernel::new();
        let p = crate::build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        let mut d = IntDev::new(&mut kernel, p.rat.int);

        let nat = d.nat_ty();
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let scaled_fv = d.fresh_fvar();
        let scaled = d.kernel().fvar(scaled_fv);

        let zero = d.zero();
        let one = d.succ(zero);
        let bpos_ty = d.le(one, b);
        let bpos_fv = d.fresh_fvar();
        let bpos = d.kernel().fvar(bpos_fv);

        let (s, lower, upper) = nat_floor_bracket(&mut d, p, b, bpos, scaled);

        let ss = d.mul(s, s);
        let b_ss = d.mul(b, ss);
        let lower_ty = d.le(b_ss, scaled);

        let succ_s = d.succ(s);
        let succ_s_sq = d.mul(succ_s, succ_s);
        let b_succ_s_sq = d.mul(b, succ_s_sq);
        let upper_ty = d.lt(scaled, b_succ_s_sq);

        let body = and_intro(&mut d, p, lower_ty, upper_ty, lower, upper);
        let concl_ty = and_ty(&mut d, p, lower_ty, upper_ty);

        let with_bpos_value = d.lam_fv(bpos_fv, bpos_ty, body);
        let with_bpos_ty = d.arrow(bpos_ty, concl_ty);
        let with_scaled_value = d.lam_fv(scaled_fv, nat, with_bpos_value);
        let with_scaled_ty = d.pi_fv(scaled_fv, nat, with_bpos_ty);
        let value = d.lam_fv(b_fv, nat, with_scaled_value);
        let ty = d.pi_fv(b_fv, nat, with_scaled_ty);

        let anon = d.kernel().anon();
        let name = d.kernel().name_str(anon, "sqrtSmokeNatFloorBracket");
        let result = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            result.is_ok(),
            "nat_floor_bracket must kernel-check: {:?}",
            result.err()
        );
    }
}
