//! `Nat.countRange_reversal_even` — a general, `totient`-INDEPENDENT
//! evenness lemma: if a `Bool`-valued predicate `h` over `[0,L)` is invariant
//! under the reflection `j <-> pred L - j` and never `true` at a fixed point
//! of that reflection, then `countRange h L` is even.
//!
//! This is the one genuinely new piece
//! `docs/plan/status/295-totient-even.md` identified for `Nat.totient_even`
//! (the reflection `k <-> n-k` over residues coprime to `n` has no fixed
//! point once `n > 2`, since a fixed point forces `n = 2*k` and `gcd k n = k
//! = 1`). It is declared here, independent of `gcd`/`totient`, because
//! nothing in its statement or proof mentions either — the plan's own
//! instruction is to land it in its reusable form rather than specialising
//! it inline.
//!
//! ## Statement
//!
//! ```text
//! Nat.countRange_reversal_even :
//!   ∀ (L : Nat) (h : Nat -> Bool),
//!     (∀ j, Lt j L -> Eq Bool (h (sub (pred L) j)) (h j)) ->
//!     (∀ j, Lt j L -> Eq Bool (h j) true -> Not (Eq Nat j (sub (pred L) j))) ->
//!     Even (countRange h L)
//! ```
//!
//! `L` is bound OUTERMOST (not `h` first, as the plan's prose sketch has it)
//! purely so the statement's own recursion variable is the
//! `WellFounded.fix`-eliminated one directly — an equivalent, just
//! differently curried, proposition.
//!
//! ## Proof route
//!
//! Well-founded (strong) induction on `L` via `lt_well_founded`/
//! `WellFounded.fix` — the same primitive `gcd`/`bezout_witnesses`/
//! `base_induction` already use — with motive `P(L) := ∀ h, hyp1(h,L) ->
//! hyp2(h,L) -> Even (countRange h L)`.
//!
//! The recursion is split via `Nat.zero_or_succ` (an actual EQUATION `L =
//! succ pred`, needed twice), NOT via `Nat.rec`/`cases_zero_succ`: the
//! latter only produces a term of the right overall TYPE without a usable
//! proposition relating the case-split value back to the original
//! induction target, and the recursive case here needs exactly that
//! relation (`Lt w L`) to invoke the induction hypothesis.
//!
//! - `L = 0`: `countRange h 0` is defeq `0` (the `Nat.rec` base case), and
//!   `0` is `Even` by the trivial witness `0`.
//! - `L = 1`: `hyp2` at `j = 0` (the only index, its own fixed point) forces
//!   `h 0 = false` (deciding `h 0` via `bool_true_or_false` and refuting the
//!   `true` branch), so `countRange h 1` defeq-reduces to `countRange h 0 =
//!   0`.
//! - `L = succ (succ w)`: peel BOTH ends in one step. `countRange_split(h,
//!   1, sw)` (`sw := succ w`, `add 1 sw` bridged to `sw`'s successor by
//!   `succ_add`/`zero_add`, exactly `coprime_succ_self`'s own device) peels
//!   index `0`; the resulting `countRange (shift1 h) sw` (`shift1 h k := h
//!   (add 1 k)`) peels its OWN top index (`w`, defeq structural recursion at
//!   the literal `succ w`), landing on original index `sw = L - 1`. `hyp1`
//!   at `j = 0` gives `h sw = h 0` directly (no case split on the VALUE
//!   needed — the two boundary contributions are literally equal terms
//!   after this rewrite, so their sum is trivially even via
//!   `Even (add k k)`, for either `k = 0` or `k = 1`). The middle term
//!   `countRange (shift1 h) w` is handed to the induction hypothesis at `w`
//!   (`w < L`, from `L = succ (succ w)`), after re-deriving `hyp1`/`hyp2`
//!   for `shift1 h` at `w` — the index correspondence is `sub (pred L)
//!   (succ j) = succ (sub (pred w) j)` for `j < w`, via `succ_sub_succ` and
//!   `succ_sub_of_le` (NOT the generic-looking-but-wrong `succ_sub_succ`
//!   twice; `succ_sub_of_le`'s `Le` side condition is exactly `j <= pred w`,
//!   derived from `j < w`).
//!
//! ## What was traced but turned out unnecessary
//!
//! `docs/plan/status/295-totient-even.md` sketches the front-peel via a
//! `shift`-by-`add m k` (matching `totient.rs`'s private `shifted_pred`) and
//! separately worried about "picking the right induction principle". Both
//! concerns were real but resolved cheaply: `shifted_pred`'s `add`-based
//! shape needs exactly one extra `succ_add`/`zero_add` bridge per use
//! (already a named local device, [`shift1_bridge`]) rather than a second
//! function definition, and the "right induction principle" is
//! `Nat.zero_or_succ` twice (an existing theorem) rather than a new
//! recursor — `WellFounded.fix` alone gives the STRONG induction step; it
//! does not, by itself, let that step's body relate a case-split value back
//! to the step's own target, which is what `zero_or_succ`'s equation
//! supplies.

use super::NatPrelude;
use super::ops::{NatDev, NatOps, bool_true_or_false};
use super::parity::even_predicate;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Local copies of shared devices (this prelude's own per-file convention).
// ============================================================================

/// `False.rec (fun _ => target) false_proof : target`.
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `h : Eq Bool a b ⊢ Eq Nat (f a) (f b)`, for `f : Bool -> Nat` — local
/// copy of `totient.rs`'s/`totient_lemmas.rs`'s `bool_congr_nat`.
fn bool_congr_nat(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.eq(fa, fx)
    });
    let refl_case = d.refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// `h : Eq Nat a b ⊢ Eq Bool (f a) (f b)`, for `f : Nat -> Bool` — local
/// copy of `totient.rs`'s `nat_congr_bool`.
fn nat_congr_bool(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.bool_eq(fa, fx)
    });
    let refl_case = d.bool_refl(fa);
    d.transport(a, motive, refl_case, b, h)
}

/// `countRange(d, p, f, n)` — local copy of `totient.rs`'s private helper.
fn count_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
}

/// `fun k => f (add one k)` — the `countRange_split`-shaped shift by one
/// index, matching `totient.rs`'s private `shifted_pred(f, one)` exactly
/// (a fresh local copy, per this prelude's convention).
fn shifted_by_one(d: &mut NatDev<'_>, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let one = d.num(1);
    let one_k = d.add(one, k);
    let fk = d.apply(f, &[one_k]);
    d.lam_fv(k_fv, nat, fk)
}

/// `(a+b)+(c+d) = (a+c)+(b+d)`, returned as `(target, proof)`.
///
/// Retired to `crate::ring::nat` (docs/plan/status/460-ring-tactic-1.md): a
/// pure ring-rearrangement chain, now searched for and emitted rather than
/// hand-assembled — one of eight verbatim-duplicated hand proofs of this
/// exact identity across `nat_prelude` (`binomial.rs`, `div_mod_lemmas.rs`,
/// `finite_set.rs`, `fibonacci.rs`, `subset_sum.rs`, `rec_agreement.rs`,
/// `eisenstein_lemma.rs`).
fn add_add_add_comm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    dd: ExprId,
) -> (ExprId, ExprId) {
    let ac = d.add(a, c);
    let bd = d.add(b, dd);
    let target = d.add(ac, bd);
    // Generic-then-apply (`prove_eq_at`): a caller may pass compound
    // arguments outside the ring fragment; `prove_eq` on the literal terms
    // would (correctly) decline `NonRing` on those.
    let proof = crate::ring::nat::prove_eq_at(d, p, &[a, b, c, dd], &|d, v| {
        let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
        let ab = d.add(a, b);
        let cd = d.add(c, dd);
        let lhs = d.add(ab, cd);
        let ac = d.add(a, c);
        let bd = d.add(b, dd);
        let rhs = d.add(ac, bd);
        (lhs, rhs)
    })
    .unwrap_or_else(|err| panic!("ring declined add_add_add_comm: {err:?}"));
    (target, proof)
}

/// `Eq (add one n) (succ n)`, returned as `(succ n, proof)`: `succ_add(zero,
/// n)` then congr `zero_add(n)` through `succ` — exactly
/// `totient_lemmas.rs`'s `declare_coprime_succ_self` inline device.
fn one_add_eq_succ(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> (ExprId, ExprId) {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let sum = d.add(one, n);
    let sn = d.succ(n);
    let add_zero_n = d.add(zero, n);
    let succ_add_step = d.lemma(p.succ_add, &[zero, n]);
    let zero_add_n = d.lemma(p.zero_add, &[n]);
    let congr_succ = d.congr(add_zero_n, n, zero_add_n, &|d, x| d.succ(x));
    let succ_add_zero_n = d.succ(add_zero_n);
    let (_e, proof) = d.chain(sum, &[(succ_add_zero_n, succ_add_step), (sn, congr_succ)]);
    (sn, proof)
}

/// `Eq Bool (shift1 h) x)) (h (succ x))`, where `shift1 h := shifted_by_one
/// d h` — bridges the `add`-shaped shift `countRange_split` produces to the
/// `succ`-shaped indexing the reflection arithmetic below is stated in,
/// via [`one_add_eq_succ`] congr'd through `h`.
fn shift1_bridge(d: &mut NatDev<'_>, p: &NatPrelude, h: ExprId, x: ExprId) -> ExprId {
    let one = d.num(1);
    let add1x = d.add(one, x);
    let (succ_x, proof) = one_add_eq_succ(d, p, x);
    nat_congr_bool(d, add1x, succ_x, proof, &|d, y| d.apply(h, &[y]))
}

/// `Even (add k k)`, via `Exists.intro k (Eq.refl (add k k))`.
fn even_witness(d: &mut NatDev<'_>, p: &NatPrelude, k: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let kk = d.add(k, k);
    let pred = even_predicate(d, kk);
    let one_lvl = d.level_one();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one_lvl]);
    let refl_kk = d.refl(kk);
    d.apply(intro, &[nat, pred, k, refl_kk])
}

/// `Even x -> Even y -> Even (add x y)`: eliminate both witnesses (`x =
/// kx+kx`, `y = ky+ky`), then `(kx+kx)+(ky+ky) = (kx+ky)+(kx+ky)` via
/// [`add_add_add_comm`], giving witness `add kx ky`.
fn even_add(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    ex: ExprId,
    y: ExprId,
    ey: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one_lvl = d.level_one();
    let anon = d.anon_name();
    let sum_xy = d.add(x, y);
    let goal = d.const_app(p.even, &[sum_xy]);

    let pred_x = even_predicate(d, x);
    let exists_c = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
    let ex_ty = d.apply(exists_c, &[nat, pred_x]);
    let motive_outer = d.kernel().lam(anon, ex_ty, goal, BinderInfo::Default);

    let minor_outer = {
        let kx_fv = d.fresh_fvar();
        let kx = d.kernel().fvar(kx_fv);
        let kxkx = d.add(kx, kx);
        let eqx_ty = d.eq(x, kxkx);
        let eqx_fv = d.fresh_fvar();
        let eqx = d.kernel().fvar(eqx_fv);

        let pred_y = even_predicate(d, y);
        let exists_c2 = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
        let ey_ty = d.apply(exists_c2, &[nat, pred_y]);
        let motive_inner = d.kernel().lam(anon, ey_ty, goal, BinderInfo::Default);

        let ky_fv = d.fresh_fvar();
        let ky = d.kernel().fvar(ky_fv);
        let kyky = d.add(ky, ky);
        let eqy_ty = d.eq(y, kyky);
        let eqy_fv = d.fresh_fvar();
        let eqy = d.kernel().fvar(eqy_fv);

        let minor_inner = {
            let add_kxkx_y = d.add(kxkx, y);
            let cong_x = d.congr(x, kxkx, eqx, &|d, t| d.add(t, y));
            let sum_kk = d.add(kxkx, kyky);
            let cong_y = d.congr(y, kyky, eqy, &|d, t| d.add(kxkx, t));

            let (four_target, four_proof) = add_add_add_comm(d, &p, kx, kx, ky, ky);
            let (_e, chained) = d.chain(
                sum_xy,
                &[
                    (add_kxkx_y, cong_x),
                    (sum_kk, cong_y),
                    (four_target, four_proof),
                ],
            );

            let witness = d.add(kx, ky);
            let pred_sum = even_predicate(d, sum_xy);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one_lvl]);
            d.apply(intro, &[nat, pred_sum, witness, chained])
        };
        let with_eqy = d.lam_fv(eqy_fv, eqy_ty, minor_inner);
        let with_ky = d.lam_fv(ky_fv, nat, with_eqy);
        let exists_rec_inner = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
        let body = d.apply(exists_rec_inner, &[nat, pred_y, motive_inner, with_ky, ey]);
        let with_eqx = d.lam_fv(eqx_fv, eqx_ty, body);
        d.lam_fv(kx_fv, nat, with_eqx)
    };
    let exists_rec_outer = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
    d.apply(
        exists_rec_outer,
        &[nat, pred_x, motive_outer, minor_outer, ex],
    )
}

/// `Eq (countRange f (succ k)) (countRange f k)`, given `h_false : Eq Bool
/// (f k) false` — the `false`-branch analogue of the already-declared
/// `Nat.countRange_succ_of_true`, kept as a local (non-declared) helper
/// since only this file's base case needs it.
fn count_range_succ_false(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    f: ExprId,
    k: ExprId,
    h_false: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let zero = d.zero();
    let fk = d.apply(f, &[k]);
    let false_v = d.bool_false();
    let cr_f_k = count_range(d, &p, f, k);
    let sel_congr = bool_congr_nat(d, fk, false_v, h_false, &|d, x| {
        let one_inner = d.num(1);
        let zero_inner = d.zero();
        d.bool_select_nat(x, one_inner, zero_inner)
    });
    let sel_fk = d.bool_select_nat(fk, one, zero);
    let sel_false = d.bool_select_nat(false_v, one, zero);
    d.congr(sel_fk, sel_false, sel_congr, &|d, x| d.add(cr_f_k, x))
}

// ============================================================================
// The statement, and its two hypothesis shapes.
// ============================================================================

/// `Pi j, Lt j l -> Eq Bool (h (sub (pred l) j)) (h j)`.
fn hyp1_ty_for(d: &mut NatDev<'_>, h: ExprId, l: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let lt_j_l = d.lt(j, l);
    let pred_l = d.pred(l);
    let sub_val = d.sub(pred_l, j);
    let h_sub = d.apply(h, &[sub_val]);
    let h_j = d.apply(h, &[j]);
    let eq_ty = d.bool_eq(h_sub, h_j);
    let body = d.arrow(lt_j_l, eq_ty);
    d.pi_fv(j_fv, nat, body)
}

/// `Pi j, Lt j l -> Eq Bool (h j) true -> Not (Eq Nat j (sub (pred l) j))`.
fn hyp2_ty_for(d: &mut NatDev<'_>, p: &NatPrelude, h: ExprId, l: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let lt_j_l = d.lt(j, l);
    let pred_l = d.pred(l);
    let sub_val = d.sub(pred_l, j);
    let h_j = d.apply(h, &[j]);
    let true_v = d.bool_true();
    let heq_true_ty = d.bool_eq(h_j, true_v);
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let eq_j_sub = d.eq(j, sub_val);
    let not_ty = d.arrow(eq_j_sub, false_ty);
    let inner = d.arrow(heq_true_ty, not_ty);
    let body = d.arrow(lt_j_l, inner);
    d.pi_fv(j_fv, nat, body)
}

/// `Pi h, hyp1(h,l) -> hyp2(h,l) -> Even (countRange h l)` — `P(l)` for the
/// `WellFounded.fix` motive.
fn statement_at(d: &mut NatDev<'_>, p: &NatPrelude, pred_ty: ExprId, l: ExprId) -> ExprId {
    let p = *p;
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let hyp1 = hyp1_ty_for(d, h, l);
    let hyp2 = hyp2_ty_for(d, &p, h, l);
    let cr = count_range(d, &p, h, l);
    let even_l = d.const_app(p.even, &[cr]);
    let inner = d.arrow(hyp2, even_l);
    let body = d.arrow(hyp1, inner);
    d.pi_fv(h_fv, pred_ty, body)
}

// ============================================================================
// Base cases.
// ============================================================================

/// `statement_at(0)`: `countRange h 0` is defeq `0`, `Even 0` via witness
/// `0`.
fn base_case_zero(d: &mut NatDev<'_>, p: &NatPrelude, pred_ty: ExprId) -> ExprId {
    let p = *p;
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let zero = d.zero();
    let hyp1 = hyp1_ty_for(d, h, zero);
    let hyp2 = hyp2_ty_for(d, &p, h, zero);
    let ev = even_witness(d, &p, zero);
    let h1_fv = d.fresh_fvar();
    let h2_fv = d.fresh_fvar();
    let with_h2 = d.lam_fv(h2_fv, hyp2, ev);
    let with_h1 = d.lam_fv(h1_fv, hyp1, with_h2);
    d.lam_fv(h_fv, pred_ty, with_h1)
}

/// `statement_at(1)`: `hyp2` at `j=0` (its own fixed point) forces `h 0 =
/// false`, so `countRange h 1` reduces to `countRange h 0 = 0`.
fn base_case_one(d: &mut NatDev<'_>, p: &NatPrelude, pred_ty: ExprId) -> ExprId {
    let p = *p;
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let zero = d.zero();
    let one_n = d.succ(zero);
    let hyp1 = hyp1_ty_for(d, h, one_n);
    let hyp2 = hyp2_ty_for(d, &p, h, one_n);
    let h1_fv = d.fresh_fvar();
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let h0 = d.apply(h, &[zero]);
    let true_v = d.bool_true();
    let false_v = d.bool_false();
    let eq_true_ty = d.bool_eq(h0, true_v);
    let eq_false_ty = d.bool_eq(h0, false_v);
    let dichot = bool_true_or_false(d, &p, h0);

    let cr1 = count_range(d, &p, h, one_n);
    let goal = d.const_app(p.even, &[cr1]);
    let lt01 = d.lemma(p.lt_succ_self, &[zero]);

    let on_true = {
        let ht_fv = d.fresh_fvar();
        let ht = d.kernel().fvar(ht_fv);
        let h2_at0 = d.apply(h2, &[zero, lt01, ht]);
        let refl0 = d.refl(zero);
        let false_val = d.apply(h2_at0, &[refl0]);
        let body = ex_falso(d, &p, goal, false_val);
        d.lam_fv(ht_fv, eq_true_ty, body)
    };
    let on_false = {
        let hf_fv = d.fresh_fvar();
        let hf = d.kernel().fvar(hf_fv);
        let eqn = count_range_succ_false(d, &p, h, zero, hf);
        let cr0 = count_range(d, &p, h, zero);
        let ev0 = even_witness(d, &p, zero);
        let motive = d.eq_motive(cr0, &|d, x| d.const_app(p.even, &[x]));
        let symm_eqn = d.symm(cr1, cr0, eqn);
        let result = d.transport(cr0, motive, ev0, cr1, symm_eqn);
        d.lam_fv(hf_fv, eq_false_ty, result)
    };
    let body = d.const_app(
        p.logic.or_elim,
        &[eq_true_ty, eq_false_ty, goal, dichot, on_true, on_false],
    );
    let with_h2 = d.lam_fv(h2_fv, hyp2, body);
    let with_h1 = d.lam_fv(h1_fv, hyp1, with_h2);
    d.lam_fv(h_fv, pred_ty, with_h1)
}

// ============================================================================
// The recursive case, `L = succ (succ w)`.
// ============================================================================

/// Order-theoretic + index-arithmetic facts shared by [`build_hyp1_prime`]
/// and [`build_hyp2_prime`], for a fixed `j < w` (`sw := succ w`, `v := succ
/// sw` implicit): `(Lt (succ j) v, sub (pred w) j, succ (sub (pred w) j),
/// sub sw (succ j), idx_eq : Eq (sub sw (succ j)) (succ (sub (pred w) j)))`.
fn per_j_bundle(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    w: ExprId,
    sw: ExprId,
    j: ExprId,
    hlt: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId) {
    let p = *p;
    let zero = d.zero();
    let one = d.num(1);
    let succ_j = d.succ(j);

    let le_w_sw = d.lemma(p.le_succ, &[w]);
    let le_succj_sw = d.lemma(p.le_trans, &[succ_j, w, sw, hlt, le_w_sw]);
    let lt_succj_v = d.lemma(p.succ_le_succ, &[succ_j, sw, le_succj_sw]);

    let zero_le_j = d.lemma(p.zero_le, &[j]);
    let le_one_succj = d.lemma(p.succ_le_succ, &[zero, j, zero_le_j]);
    let pos_w = d.lemma(p.le_trans, &[one, succ_j, w, le_one_succj, hlt]);
    let pred_w = d.pred(w);
    let eq_w_fn = d.lemma(p.succ_pred_of_pos, &[w]);
    let eq_w = d.apply(eq_w_fn, &[pos_w]);
    let succ_pred_w = d.succ(pred_w);

    let motive_le = d.eq_motive(w, &|d, x| d.le(succ_j, x));
    let le_succj_succpredw = d.transport(w, motive_le, hlt, succ_pred_w, eq_w);
    let le_j_predw = d.lemma(p.le_of_succ_le_succ, &[j, pred_w, le_succj_succpredw]);

    let succ_sub_le_fact = d.lemma(p.succ_sub_of_le, &[pred_w, j, le_j_predw]);
    let sub_predw_j = d.sub(pred_w, j);
    let succ_sub_predw_j = d.succ(sub_predw_j);
    let motive_subw = d.eq_motive(succ_pred_w, &|d, x| {
        let s = d.sub(x, j);
        d.eq(s, succ_sub_predw_j)
    });
    let symm_eq_w = d.symm(w, succ_pred_w, eq_w);
    let sub_w_j_eq = d.transport(succ_pred_w, motive_subw, succ_sub_le_fact, w, symm_eq_w);

    let succ_sub_succ_fact = d.lemma(p.succ_sub_succ, &[w, j]);
    let sub_sw_succj = d.sub(sw, succ_j);
    let sub_w_j = d.sub(w, j);
    let (_e, idx_eq) = d.chain(
        sub_sw_succj,
        &[
            (sub_w_j, succ_sub_succ_fact),
            (succ_sub_predw_j, sub_w_j_eq),
        ],
    );

    (
        lt_succj_v,
        sub_predw_j,
        succ_sub_predw_j,
        sub_sw_succj,
        idx_eq,
    )
}

/// `hyp1(shift1 h, w)`, built from `hyp1(h, v)` (`h1`) plus the index
/// correspondence.
fn build_hyp1_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    h: ExprId,
    h1: ExprId,
    shift1: ExprId,
    w: ExprId,
    sw: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);
    let lt_j_w_ty = d.lt(j, w);

    let (lt_succj_v, sub_predw_j, succ_sub_predw_j, sub_sw_succj, idx_eq) =
        per_j_bundle(d, &p, w, sw, j, hlt);

    let succ_j = d.succ(j);
    let h1_at_succj = d.apply(h1, &[succ_j, lt_succj_v]);

    let congr_idx_bool = nat_congr_bool(d, sub_sw_succj, succ_sub_predw_j, idx_eq, &|d, y| {
        d.apply(h, &[y])
    });

    let h_sub_sw_succj = d.apply(h, &[sub_sw_succj]);
    let h_succ_sub_predw_j = d.apply(h, &[succ_sub_predw_j]);
    let h_succ_j = d.apply(h, &[succ_j]);

    let symm_congr = d.bool_symm(h_sub_sw_succj, h_succ_sub_predw_j, congr_idx_bool);
    let combined = d.bool_trans(
        h_succ_sub_predw_j,
        h_sub_sw_succj,
        h_succ_j,
        symm_congr,
        h1_at_succj,
    );

    let bridge_a = shift1_bridge(d, &p, h, sub_predw_j);
    let bridge_b = shift1_bridge(d, &p, h, j);

    let shift1_sub = d.apply(shift1, &[sub_predw_j]);
    let shift1_j = d.apply(shift1, &[j]);

    let step1 = d.bool_trans(shift1_sub, h_succ_sub_predw_j, h_succ_j, bridge_a, combined);
    let symm_bridge_b = d.bool_symm(shift1_j, h_succ_j, bridge_b);
    let final_result = d.bool_trans(shift1_sub, h_succ_j, shift1_j, step1, symm_bridge_b);

    let body = d.lam_fv(hlt_fv, lt_j_w_ty, final_result);
    d.lam_fv(j_fv, nat, body)
}

/// `hyp2(shift1 h, w)`, built from `hyp2(h, v)` (`h2`) plus the index
/// correspondence.
fn build_hyp2_prime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    h: ExprId,
    h2: ExprId,
    shift1: ExprId,
    w: ExprId,
    sw: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);
    let lt_j_w_ty = d.lt(j, w);

    let (lt_succj_v, sub_predw_j, succ_sub_predw_j, sub_sw_succj, idx_eq) =
        per_j_bundle(d, &p, w, sw, j, hlt);

    let shift1_j = d.apply(shift1, &[j]);
    let true_v = d.bool_true();
    let htrue_ty = d.bool_eq(shift1_j, true_v);
    let htrue_fv = d.fresh_fvar();
    let htrue = d.kernel().fvar(htrue_fv);

    let eq_j_sub_ty = d.eq(j, sub_predw_j);

    let succ_j = d.succ(j);
    let h_succ_j = d.apply(h, &[succ_j]);
    let bridge_b = shift1_bridge(d, &p, h, j);
    let symm_bridge_b = d.bool_symm(shift1_j, h_succ_j, bridge_b);
    let h_succj_eq_true = d.bool_trans(h_succ_j, shift1_j, true_v, symm_bridge_b, htrue);

    let h2_at_succj = d.apply(h2, &[succ_j, lt_succj_v, h_succj_eq_true]);

    let inner = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let congr_succ = d.congr(j, sub_predw_j, heq, &|d, x| d.succ(x));
        let symm_idx_eq = d.symm(sub_sw_succj, succ_sub_predw_j, idx_eq);
        let (_e, final_eq) = d.chain(
            succ_j,
            &[(succ_sub_predw_j, congr_succ), (sub_sw_succj, symm_idx_eq)],
        );
        let false_val = d.apply(h2_at_succj, &[final_eq]);
        d.lam_fv(heq_fv, eq_j_sub_ty, false_val)
    };

    let with_htrue = d.lam_fv(htrue_fv, htrue_ty, inner);
    let with_hlt = d.lam_fv(hlt_fv, lt_j_w_ty, with_htrue);
    d.lam_fv(j_fv, nat, with_hlt)
}

/// `statement_at(succ (succ w))`, given `ih : Pi y, Lt y (succ (succ w)) ->
/// statement_at(y)` and `lt_w_v : Lt w (succ (succ w))`. See the module doc
/// for the route.
fn succ_succ_case(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred_ty: ExprId,
    w: ExprId,
    ih: ExprId,
    lt_w_v: ExprId,
) -> ExprId {
    let p = *p;
    let sw = d.succ(w);
    let v = d.succ(sw);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let hyp1_ty = hyp1_ty_for(d, h, v);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let hyp2_ty = hyp2_ty_for(d, &p, h, v);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let zero = d.zero();
    let one = d.num(1);

    // `h sw = h 0`, from hyp1 at j = 0.
    let lt_0_v = d.lemma(p.zero_lt_succ, &[sw]);
    let h_sw_eq_h0 = d.apply(h1, &[zero, lt_0_v]);

    // Master equation: `countRange h v = add sel0 (add rest sel_sw)`.
    let shift1 = shifted_by_one(d, h);
    let (one_add_sw, one_add_sw_proof) = one_add_eq_succ(d, &p, sw);
    let add1sw = d.add(one, sw);
    let split_eq = d.lemma(p.count_range_split, &[h, one, sw]);
    let cr_h_1 = count_range(d, &p, h, one);
    let cr_shift1_sw = count_range(d, &p, shift1, sw);
    let cr_h_add1sw = count_range(d, &p, h, add1sw);
    let rhs_split = d.add(cr_h_1, cr_shift1_sw);
    let cr_h_v = count_range(d, &p, h, v);
    let congr_lhs = d.congr(add1sw, one_add_sw, one_add_sw_proof, &|d, x| {
        let p2 = p;
        count_range(d, &p2, h, x)
    });
    let symm_congr_lhs = d.symm(cr_h_add1sw, cr_h_v, congr_lhs);
    let (_e1, split_a) = d.chain(
        cr_h_v,
        &[(cr_h_add1sw, symm_congr_lhs), (rhs_split, split_eq)],
    );

    let h0 = d.apply(h, &[zero]);
    let sel0 = d.bool_select_nat(h0, one, zero);
    let eq_b = d.lemma(p.zero_add, &[sel0]);

    let (one_add_w, one_add_w_proof) = one_add_eq_succ(d, &p, w);
    let add1w = d.add(one, w);
    let shift1_w = d.apply(shift1, &[w]);
    let h_sw_val = d.apply(h, &[sw]);
    let congr_shift1w = nat_congr_bool(d, add1w, one_add_w, one_add_w_proof, &|d, x| {
        d.apply(h, &[x])
    });
    let sel_shift1w = d.bool_select_nat(shift1_w, one, zero);
    let sel_sw = d.bool_select_nat(h_sw_val, one, zero);
    let sel_congr_c = bool_congr_nat(d, shift1_w, h_sw_val, congr_shift1w, &|d, x| {
        let one_i = d.num(1);
        let zero_i = d.zero();
        d.bool_select_nat(x, one_i, zero_i)
    });
    let cr_shift1_w = count_range(d, &p, shift1, w);
    let eq_c = d.congr(sel_shift1w, sel_sw, sel_congr_c, &|d, x| {
        d.add(cr_shift1_w, x)
    });

    let congr_b = d.congr(cr_h_1, sel0, eq_b, &|d, x| d.add(x, cr_shift1_sw));
    let mid1 = d.add(sel0, cr_shift1_sw);
    let inner_c_rhs = d.add(cr_shift1_w, sel_sw);
    let congr_c2 = d.congr(cr_shift1_sw, inner_c_rhs, eq_c, &|d, x| d.add(sel0, x));
    let mid2 = d.add(sel0, inner_c_rhs);

    let (_e2, master_eq) = d.chain(
        cr_h_v,
        &[(rhs_split, split_a), (mid1, congr_b), (mid2, congr_c2)],
    );

    // Rewrite `sel_sw -> sel0` using `h_sw_eq_h0`, then reassociate to
    // `add (add sel0 sel0) rest`.
    let sel_eq = bool_congr_nat(d, h_sw_val, h0, h_sw_eq_h0, &|d, x| {
        let one_i = d.num(1);
        let zero_i = d.zero();
        d.bool_select_nat(x, one_i, zero_i)
    });
    let rest = cr_shift1_w;
    let inner_after = d.add(rest, sel0);
    let congr_sel = d.congr(sel_sw, sel0, sel_eq, &|d, x| d.add(rest, x));
    let mid3 = d.add(sel0, inner_after);
    let congr_step1 = d.congr(inner_c_rhs, inner_after, congr_sel, &|d, x| d.add(sel0, x));

    let comm1 = d.lemma(p.add_comm, &[rest, sel0]);
    let sel0_rest = d.add(sel0, rest);
    let mid4 = d.add(sel0, sel0_rest);
    let congr_step2 = d.congr(inner_after, sel0_rest, comm1, &|d, x| d.add(sel0, x));

    let assoc1 = d.lemma(p.add_assoc, &[sel0, sel0, rest]);
    let sel0sel0 = d.add(sel0, sel0);
    let target_expr = d.add(sel0sel0, rest);
    let symm_assoc1 = d.symm(target_expr, mid4, assoc1);

    let (_e3, final_eq) = d.chain(
        cr_h_v,
        &[
            (mid2, master_eq),
            (mid3, congr_step1),
            (mid4, congr_step2),
            (target_expr, symm_assoc1),
        ],
    );

    // `Even rest` via the induction hypothesis, `Even (add sel0 sel0)`
    // trivially, then `even_add`.
    let hyp1_prime = build_hyp1_prime(d, &p, h, h1, shift1, w, sw);
    let hyp2_prime = build_hyp2_prime(d, &p, h, h2, shift1, w, sw);
    let ih_at_w = d.apply(ih, &[w, lt_w_v]);
    let even_rest = d.apply(ih_at_w, &[shift1, hyp1_prime, hyp2_prime]);
    let even_bb = even_witness(d, &p, sel0);
    let even_target = even_add(d, &p, sel0sel0, even_bb, rest, even_rest);

    let motive_final = d.eq_motive(target_expr, &|d, x| d.const_app(p.even, &[x]));
    let symm_final_eq = d.symm(cr_h_v, target_expr, final_eq);
    let result = d.transport(
        target_expr,
        motive_final,
        even_target,
        cr_h_v,
        symm_final_eq,
    );

    let with_h2 = d.lam_fv(h2_fv, hyp2_ty, result);
    let with_h1 = d.lam_fv(h1_fv, hyp1_ty, with_h2);
    d.lam_fv(h_fv, pred_ty, with_h1)
}

/// `WellFounded.fix`'s `step`: given `capital_v` and `ih : Pi y, Lt y
/// capital_v -> statement_at(y)`, produce `statement_at(capital_v)`. Splits
/// `capital_v` via `Nat.zero_or_succ` (twice) rather than
/// `Nat.rec`/`cases_zero_succ`, so the recursive case has an actual
/// equation relating its bound `w` back to `capital_v` for `ih`'s `Lt`
/// hypothesis — see the module doc.
fn recursive_step(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred_ty: ExprId,
    capital_v: ExprId,
    ih: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one_lvl = d.level_one();
    let zero = d.zero();

    let goal_v = statement_at(d, &p, pred_ty, capital_v);
    let disj = d.lemma(p.zero_or_succ, &[capital_v]);
    let eq_v0_ty = d.eq(capital_v, zero);

    let pred_pred_ty = {
        let pr_fv = d.fresh_fvar();
        let pr = d.kernel().fvar(pr_fv);
        let spr = d.succ(pr);
        let body = d.eq(capital_v, spr);
        d.lam_fv(pr_fv, nat, body)
    };
    let exists_c = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
    let ex_ty = d.apply(exists_c, &[nat, pred_pred_ty]);

    let case_zero = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let proof0 = base_case_zero(d, &p, pred_ty);
        let motive_v = d.eq_motive(zero, &|d, x| statement_at(d, &p, pred_ty, x));
        let symm_heq = d.symm(capital_v, zero, heq);
        let result = d.transport(zero, motive_v, proof0, capital_v, symm_heq);
        d.lam_fv(heq_fv, eq_v0_ty, result)
    };

    let case_succ = {
        let hex_fv = d.fresh_fvar();
        let hex = d.kernel().fvar(hex_fv);
        let anon = d.anon_name();
        let motive_ex = d.kernel().lam(anon, ex_ty, goal_v, BinderInfo::Default);

        let minor = {
            let pr_fv = d.fresh_fvar();
            let pr = d.kernel().fvar(pr_fv);
            let s_pr = d.succ(pr);
            let heq1_ty = d.eq(capital_v, s_pr);
            let heq1_fv = d.fresh_fvar();
            let heq1 = d.kernel().fvar(heq1_fv);

            let disj2 = d.lemma(p.zero_or_succ, &[pr]);
            let eq_pr0_ty = d.eq(pr, zero);
            let pred_pred_ty2 = {
                let w_fv = d.fresh_fvar();
                let w = d.kernel().fvar(w_fv);
                let sw = d.succ(w);
                let body = d.eq(pr, sw);
                d.lam_fv(w_fv, nat, body)
            };
            let exists_c2 = d.kernel().const_(p.logic.exists_, vec![one_lvl]);
            let ex_ty2 = d.apply(exists_c2, &[nat, pred_pred_ty2]);

            let sub_case_zero = {
                let heq2_fv = d.fresh_fvar();
                let heq2 = d.kernel().fvar(heq2_fv);
                let proof1 = base_case_one(d, &p, pred_ty);
                let s_zero = d.succ(zero);
                let congr_s = d.congr(pr, zero, heq2, &|d, x| d.succ(x));
                let motive_sv = d.eq_motive(s_zero, &|d, x| statement_at(d, &p, pred_ty, x));
                let symm_congr_s = d.symm(s_pr, s_zero, congr_s);
                let proof_at_spr = d.transport(s_zero, motive_sv, proof1, s_pr, symm_congr_s);
                let motive_v2 = d.eq_motive(s_pr, &|d, x| statement_at(d, &p, pred_ty, x));
                let symm_heq1 = d.symm(capital_v, s_pr, heq1);
                let result = d.transport(s_pr, motive_v2, proof_at_spr, capital_v, symm_heq1);
                d.lam_fv(heq2_fv, eq_pr0_ty, result)
            };

            let sub_case_succ = {
                let hex2_fv = d.fresh_fvar();
                let hex2 = d.kernel().fvar(hex2_fv);
                let anon2 = d.anon_name();
                let motive_ex2 = d.kernel().lam(anon2, ex_ty2, goal_v, BinderInfo::Default);

                let minor2 = {
                    let w_fv = d.fresh_fvar();
                    let w = d.kernel().fvar(w_fv);
                    let sw = d.succ(w);
                    let heq3_ty = d.eq(pr, sw);
                    let heq3_fv = d.fresh_fvar();
                    let heq3 = d.kernel().fvar(heq3_fv);

                    let lt_w_sw = d.lemma(p.lt_succ_self, &[w]);
                    let le_sw_ssw = d.lemma(p.le_succ, &[sw]);
                    let succ_w = d.succ(w);
                    let ssw = d.succ(sw);
                    let le_succw_ssw = d.lemma(p.le_trans, &[succ_w, sw, ssw, lt_w_sw, le_sw_ssw]);

                    let congr_v = d.congr(pr, sw, heq3, &|d, x| d.succ(x));
                    let s_sw = d.succ(sw);
                    let (_e2, v_eq_ssw) = d.chain(capital_v, &[(s_pr, heq1), (s_sw, congr_v)]);
                    let motive_lt = d.eq_motive(s_sw, &|d, x| d.lt(w, x));
                    let symm_v_eq_ssw = d.symm(capital_v, s_sw, v_eq_ssw);
                    let lt_w_v =
                        d.transport(s_sw, motive_lt, le_succw_ssw, capital_v, symm_v_eq_ssw);

                    let proof_ss = succ_succ_case(d, &p, pred_ty, w, ih, lt_w_v);
                    let motive_v3 = d.eq_motive(s_sw, &|d, x| statement_at(d, &p, pred_ty, x));
                    let result = d.transport(s_sw, motive_v3, proof_ss, capital_v, symm_v_eq_ssw);

                    let with_heq3 = d.lam_fv(heq3_fv, heq3_ty, result);
                    d.lam_fv(w_fv, nat, with_heq3)
                };
                let exists_rec2 = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
                let body2 = d.apply(exists_rec2, &[nat, pred_pred_ty2, motive_ex2, minor2, hex2]);
                d.lam_fv(hex2_fv, ex_ty2, body2)
            };

            let body_pr = d.const_app(
                p.logic.or_elim,
                &[
                    eq_pr0_ty,
                    ex_ty2,
                    goal_v,
                    disj2,
                    sub_case_zero,
                    sub_case_succ,
                ],
            );
            let with_heq1 = d.lam_fv(heq1_fv, heq1_ty, body_pr);
            d.lam_fv(pr_fv, nat, with_heq1)
        };
        let exists_rec_outer = d.kernel().const_(p.logic.exists_rec, vec![one_lvl]);
        let body_outer = d.apply(
            exists_rec_outer,
            &[nat, pred_pred_ty, motive_ex, minor, hex],
        );
        d.lam_fv(hex_fv, ex_ty, body_outer)
    };

    d.const_app(
        p.logic.or_elim,
        &[eq_v0_ty, ex_ty, goal_v, disj, case_zero, case_succ],
    )
}

/// `Nat.countRange_reversal_even`. See the module doc for the statement and
/// the route.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_count_range_reversal_even(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pred_ty = d.arrow(nat, bool_ty);

    let l_fv = d.fresh_fvar();
    let l = d.kernel().fvar(l_fv);
    let ty_body = statement_at(d, &p, pred_ty, l);
    let ty = d.pi_fv(l_fv, nat, ty_body);

    let one_level = d.level_one();
    let zero_level = d.kernel().level_zero();
    let relation = d.kernel().const_(p.lt, vec![]);
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);
    let fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one_level, zero_level]);

    let motive_lam = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let body = statement_at(d, &p, pred_ty, x);
        d.lam_fv(x_fv, nat, body)
    };

    let step = {
        let v_fv = d.fresh_fvar();
        let v_var = d.kernel().fvar(v_fv);
        let ih_fv = d.fresh_fvar();
        let ih_var = d.kernel().fvar(ih_fv);
        let ih_ty = {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let lt_y_v = d.lt(y, v_var);
            let py = statement_at(d, &p, pred_ty, y);
            let body = d.arrow(lt_y_v, py);
            d.pi_fv(y_fv, nat, body)
        };
        let body = recursive_step(d, &p, pred_ty, v_var, ih_var);
        let with_ih = d.lam_fv(ih_fv, ih_ty, body);
        d.lam_fv(v_fv, nat, with_ih)
    };

    let proof_of_p_l = d.apply(fix, &[nat, relation, motive_lam, well_founded, step, l]);
    let value = d.lam_fv(l_fv, nat, proof_of_p_l);

    d.declare_theorem(p.count_range_reversal_even, ty, value)
}
