//! `Nat.totient_mul_of_coprime` — Euler's totient is multiplicative on
//! coprime arguments, and the two CRT self-map facts it needs.
//!
//! ```text
//! Nat.totient_mul_of_coprime :
//!   ∀ m n, Eq (gcd m n) 1 →
//!     Eq (totient (mul m n)) (mul (totient m) (totient n))
//! ```
//!
//! ## The map, and where coprimality actually enters
//!
//! Everything runs over the **residue-pairing self-map** of `[0, n*m)`
//!
//! ```text
//! g x := add (mul n (mod x m)) (mod x n)
//! ```
//!
//! written with `n` on the LEFT of the product and `mod x n` as the offset so
//! that `Nat.div_mod_block` reads it back with no `mul_comm` in the way, and
//! so that the bound `mul n m` is literally the shape
//! `Nat.countRange_product` factors (`n` is the block WIDTH, `m` the block
//! COUNT).
//!
//! With `R a := beq (gcd a m) 1` (`totient m`'s own predicate),
//! `S b := beq (gcd b n) 1` (`totient n`'s), `V y := band (R (div y n))
//! (S (mod y n))` and `P x := beq (gcd x (m*n)) 1` (`totient (m*n)`'s), the
//! chain is
//!
//! ```text
//! countRange P (mul m n)                        -- totient (m*n), by δ
//!   = countRange P (mul n m)                    -- mul_comm, on the BOUND only
//!   = countRange (V ∘ g) (mul n m)              -- countRange_congr, pointwise
//!   = countRange V (mul n m)                    -- countRange_permute, SYMM
//!   = mul (countRange S n) (countRange R m)     -- countRange_product
//!   = mul (totient m) (totient n)               -- mul_comm
//! ```
//!
//! **Three of those four steps are coprimality-INDEPENDENT and exactly one is
//! not**, which is the whole reason this file states them separately. Measured
//! before any of it was written, by
//! `scripts/tests/check-totient-mul-coprime-numerics.py` (20 checks, each with
//! a control asserted to genuinely fail), over every pair `1 ≤ m,n ≤ 9`:
//!
//! - `MapsInto g (mul n m)` holds at all 81 pairs, including all 26
//!   non-coprime ones. It needs only `0 < m` and `0 < n`, so
//!   [`declare_crt_self_map_maps_into`] carries **no hypothesis at all** —
//!   both arguments are taken as PREDECESSORS and the positivity is
//!   syntactic.
//! - the pointwise identity `P x = V (g x)` holds for all `x < 60` at all 81
//!   pairs, so the *unconditional* `Nat.countRange_congr` is the right tool
//!   and the coprimality hypothesis must not be smuggled into it.
//! - the Fubini factorization `countRange V (n*m) = totient n * totient m`
//!   holds at all 26 non-coprime pairs too — this is precisely the claim
//!   `docs/plan/status/301`'s traced plan got RIGHT.
//! - `InjectiveOn g (mul n m)` holds at **0 of those 26** (smallest collision
//!   `m = n = 2`, where `g 0 = g 2 = 0`), and the permute step fails at 26 of
//!   26. So the entire hypothesis is carried by
//!   [`declare_crt_self_map_injective_on`], and by nothing else.
//!
//! What `301` got wrong was attributing the Fubini step's independence to the
//! TOTIENT identity, which fails at 26 of 26 non-coprime pairs (smallest
//! counterexample `m = n = 2`: `totient 4 = 2` against `1 * 1`).
//!
//! ## Why predecessors, and why no new `Definition`
//!
//! Both self-map theorems are stated at `succ mp` / `succ np` rather than at
//! `m` / `n` with `Lt 0 m` / `Lt 0 n` hypotheses. Three things need the
//! successor form *syntactically* and would otherwise need a case split at
//! each use: `Nat.mul_succ_add_lt_of_le_of_lt` (the entire `MapsInto` proof,
//! one lemma), `Nat.div_mod_exec` (which takes the divisor's PREDECESSOR),
//! and the bound `mul (succ np) (succ mp)`, which is defeq
//! `succ (add (mul (succ np) mp) np)` by two ι-steps — so `div_mod_exec`
//! applies at the *product* modulus with no arithmetic lemma at all. The main
//! theorem splits both arguments once, at the top, and everything below sees
//! literal successors.
//!
//! `g`, `R`, `S` and `V` are bare lambdas, not `Declaration::Definition`s.
//! The kernel cannot tell a definition it is wrong (it only type-checks), so
//! each one added would owe an evaluation test; none is needed here, because
//! `R` and `S` are built by the same recipe as `totient`'s own predicate and
//! are therefore defeq to it on the nose, and `g`/`V` are consumed only
//! through lemmas that state what they mean.
//!
//! ## The `Bool` bridge
//!
//! `Nat.coprime_mul_iff` is a `Prop`-level `Iff`; `countRange` wants a `Bool`
//! equality. [`coprime_bool_bridge`] closes that gap by deciding both factors
//! with `bool_true_or_false` and refuting the impossible branches through
//! `beq_eq_true_of_eq` + `false_true_elim` — three branches, no excluded
//! middle. `band` is a local `Bool.rec` selector (this prelude exposes no
//! `Bool`-valued `and`; `finite_set.rs`'s `bool_select_bool` is private), and
//! it is deliberately strict in its FIRST argument so that
//! `band false _ ≡ false` and `band true b ≡ b` both hold by ι-reduction —
//! which is exactly what discharges `countRange_product`'s two per-block
//! hypotheses with no lemma.

use super::NatPrelude;
use super::helpers::{and_left, and_right, iff_forward, iff_reverse};
use super::ops::{NatDev, NatOps, bool_true_or_false, cases_zero_succ};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// Local term builders.
// ============================================================================

/// `countRange f n`.
fn count_range(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.count_range, &[f, n])
}

/// `Bool.rec (fun _ => Bool) false b a` — computational `a && b`, strict in
/// `a`. `band false _` and `band true b` both ι-reduce, which is what makes
/// `countRange_product`'s two per-block hypotheses close by reduction.
fn band(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, bool_ty, BinderInfo::Default);
    let one = d.level_one();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![one]);
    let false_ = d.bool_false();
    d.apply(bool_rec, &[motive, false_, b, a])
}

/// `h : Eq Nat a b ⊢ Eq Bool (f a) (f b)` — the `Bool`-codomain congruence
/// [`NatOps::congr`] does not provide (it is hardcoded to a `Nat` codomain).
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

/// `h : Eq Bool a b ⊢ Eq Bool (f a) (f b)` — the `Bool`-domain,
/// `Bool`-codomain congruence, for rewriting inside [`band`].
fn bool_congr_bool(
    d: &mut NatDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut NatDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = d.bool_eq_motive(a, &|d, x| {
        let fx = f(d, x);
        d.bool_eq(fa, fx)
    });
    let refl_case = d.bool_refl(fa);
    d.bool_transport(a, motive, refl_case, b, h)
}

/// Non-dependent `Or.rec` into a goal.
#[allow(clippy::too_many_arguments)]
fn or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    left_ty: ExprId,
    right_ty: ExprId,
    goal: ExprId,
    left_case: ExprId,
    right_case: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// `fun k => beq (gcd k modulus) 1` — built by exactly the recipe
/// `totient.rs`'s private `totient_predicate` uses, so `countRange` of it at
/// `modulus` is defeq `totient modulus` on the nose.
fn coprime_pred(d: &mut NatDev<'_>, modulus: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let g = d.gcd(k, modulus);
    let one = d.num(1);
    let body = d.beq(g, one);
    d.lam_fv(k_fv, nat, body)
}

/// The raw (β-reduced) `g x` for `m = succ mp`, `n = succ np`:
/// `add (mul n (mod x m)) (mod x n)`.
fn crt_image(d: &mut NatDev<'_>, mp: ExprId, np: ExprId, x: ExprId) -> ExprId {
    let m = d.succ(mp);
    let n = d.succ(np);
    let mx = d.modulo(x, m);
    let nx = d.modulo(x, n);
    let prod = d.mul(n, mx);
    d.add(prod, nx)
}

/// `fun x => add (mul n (mod x m)) (mod x n)`, the CRT self-map of
/// `[0, mul n m)`.
fn crt_self_map(d: &mut NatDev<'_>, mp: ExprId, np: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let body = crt_image(d, mp, np, x);
    d.lam_fv(x_fv, nat, body)
}

/// `fun y => band (beq (gcd (div y n) m) 1) (beq (gcd (mod y n) n) 1)` — the
/// block-factoring predicate `countRange_product` consumes.
fn block_pred(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let one = d.num(1);
    let q = d.div(y, n);
    let r = d.modulo(y, n);
    let ga = d.gcd(q, m);
    let left = d.beq(ga, one);
    let gb = d.gcd(r, n);
    let right = d.beq(gb, one);
    let body = band(d, p, left, right);
    d.lam_fv(y_fv, nat, body)
}

/// `fun k => f (g k)`.
fn compose(d: &mut NatDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let gk = d.apply(g, &[k]);
    let body = d.apply(f, &[gk]);
    d.lam_fv(k_fv, nat, body)
}

// ============================================================================
// `Nat.crtSelfMap_mapsInto`.
// ============================================================================

/// `Nat.crtSelfMap_mapsInto : ∀ mp np,
///   MapsInto (fun x => add (mul (succ np) (mod x (succ mp))) (mod x (succ np)))
///            (mul (succ np) (succ mp))`
///
/// **No hypothesis.** Positivity of both moduli is syntactic in the successor
/// form, and coprimality is genuinely not needed — this holds at every
/// non-coprime pair too (check 2 of
/// `scripts/tests/check-totient-mul-coprime-numerics.py`).
///
/// One lemma of content. `Nat.mul_succ_add_lt_of_le_of_lt` is exactly the
/// "flatten a row-major `(block, offset)` index" bound
/// `Le i m → Lt j (succ n) → Lt (mul (succ n) i + j) (mul (succ n) (succ m))`;
/// `Nat.mod_lt` supplies both of its hypotheses (the first through
/// `le_of_lt_succ`), and its conclusion IS the goal after β.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_crt_self_map_maps_into(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.crt_self_map_maps_into, 2, &|d, v| {
        let (mp, np) = (v[0], v[1]);
        let nat = d.nat_ty();
        let m = d.succ(mp);
        let n = d.succ(np);
        let bound = d.mul(n, m);
        let g = crt_self_map(d, mp, np);
        let stmt = d.const_app(p.maps_into, &[g, bound]);

        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hi_ty = d.lt(i, bound);
        let hi_fv = d.fresh_fvar();

        let mod_i_m = d.modulo(i, m);
        let mod_i_n = d.modulo(i, n);
        let pos_m = d.zero_lt_succ(mp);
        let pos_n = d.zero_lt_succ(np);
        // `Lt (mod i m) (succ mp)`, weakened to `Le (mod i m) mp`.
        let lt_m = d.lemma(p.mod_lt, &[i, m, pos_m]);
        let le_m = d.lemma(p.le_of_lt_succ, &[mod_i_m, mp, lt_m]);
        // `Lt (mod i n) (succ np)` is already the second hypothesis's shape.
        let lt_n = d.lemma(p.mod_lt, &[i, n, pos_n]);

        let body = d.lemma(
            p.mul_succ_add_lt_of_le_of_lt,
            &[np, mp, mod_i_m, mod_i_n, le_m, lt_n],
        );
        let with_hi = d.lam_fv(hi_fv, hi_ty, body);
        let proof = d.lam_fv(i_fv, nat, with_hi);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// `Nat.crtSelfMap_injectiveOn` — the one obligation coprimality pays for.
// ============================================================================

/// `Nat.crtSelfMap_injectiveOn : ∀ mp np, Eq (gcd (succ mp) (succ np)) 1 →
///   InjectiveOn (fun x => add (mul (succ np) (mod x (succ mp))) (mod x (succ np)))
///               (mul (succ np) (succ mp))`
///
/// This is the ONLY place the coprimality hypothesis is used anywhere under
/// `Nat.totient_mul_of_coprime`, and the statement is sharp: `g` is injective
/// on `[0, n*m)` at every coprime pair with `1 ≤ m,n ≤ 9` and at **none** of
/// the 26 non-coprime ones (check 2 of the numerics script; smallest
/// collision `m = n = 2`, `g 0 = g 2 = 0`).
///
/// Route, from `g i = g j` with `i, j < n*m`:
///
/// 1. `Nat.div_mod_block` twice (its side condition `mod _ n < n` from
///    `Nat.mod_lt`) reads `div (g x) n = mod x m` and `mod (g x) n = mod x n`
///    back off the block form — so `g i = g j` gives `mod i m = mod j m` and
///    `mod i n = mod j n` by congruence in `div _ n` and `mod _ n`.
/// 2. `Nat.mod_eq_iff_div_mod_remainder_eq` (reverse), fed
///    `Nat.div_mod_exec`'s executable witnesses, turns each of those into a
///    `modEq`.
/// 3. `Nat.crt_unique` — the Nat-native one, `nat_prelude/crt.rs` — combines
///    them into `modEq (mul m n) i j`, transported to `mul n m` by
///    `Nat.mul_comm`.
/// 4. The same iff FORWARD at the product modulus (`div_mod_exec` applies
///    there with predecessor `add (mul n mp) np`, since
///    `mul (succ np) (succ mp)` is defeq `succ (add (mul (succ np) mp) np)`)
///    gives `mod i (n*m) = mod j (n*m)`, and `Nat.mod_eq_self_of_lt` collapses
///    both sides.
///
/// **No Bézout witness and no CRT existence over ℕ is used.**
/// `nat_prelude/crt.rs` declines existence deliberately (the classical witness
/// needs signed coefficients); injectivity never asks for it.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_crt_self_map_injective_on(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.crt_self_map_injective_on, 2, &|d, v| {
        let (mp, np) = (v[0], v[1]);
        let nat = d.nat_ty();
        let one = d.num(1);
        let m = d.succ(mp);
        let n = d.succ(np);
        let bound = d.mul(n, m);
        let g = crt_self_map(d, mp, np);

        let gcd_mn = d.gcd(m, n);
        let hgcd_ty = d.eq(gcd_mn, one);
        let hgcd_fv = d.fresh_fvar();
        let hgcd = d.kernel().fvar(hgcd_fv);

        let concl = d.const_app(p.injective_on, &[g, bound]);
        let stmt = d.arrow(hgcd_ty, concl);

        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hi_ty = d.lt(i, bound);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hj_ty = d.lt(j, bound);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);

        let gi = crt_image(d, mp, np, i);
        let gj = crt_image(d, mp, np, j);
        let heq_ty = d.eq(gi, gj);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        // --- step 1: read the two residues back off the block form ---------
        let pos_n = d.zero_lt_succ(np);
        let mi_m = d.modulo(i, m);
        let mi_n = d.modulo(i, n);
        let mj_m = d.modulo(j, m);
        let mj_n = d.modulo(j, n);
        let lt_i_n = d.lemma(p.mod_lt, &[i, n, pos_n]);
        let lt_j_n = d.lemma(p.mod_lt, &[j, n, pos_n]);
        let blk_i = d.lemma(p.div_mod_block, &[n, mi_m, mi_n, lt_i_n]);
        let blk_j = d.lemma(p.div_mod_block, &[n, mj_m, mj_n, lt_j_n]);

        let dq_i = d.div(gi, n);
        let dr_i = d.modulo(gi, n);
        let dq_j = d.div(gj, n);
        let dr_j = d.modulo(gj, n);
        let li_ty = d.eq(dq_i, mi_m);
        let ri_ty = d.eq(dr_i, mi_n);
        let lj_ty = d.eq(dq_j, mj_m);
        let rj_ty = d.eq(dr_j, mj_n);
        let e1i = and_left(d, li_ty, ri_ty, blk_i);
        let e2i = and_right(d, li_ty, ri_ty, blk_i);
        let e1j = and_left(d, lj_ty, rj_ty, blk_j);
        let e2j = and_right(d, lj_ty, rj_ty, blk_j);

        let hdiv = d.congr(gi, gj, heq, &|d, t| d.div(t, n));
        let hmod = d.congr(gi, gj, heq, &|d, t| d.modulo(t, n));

        // mod i m = div (g i) n = div (g j) n = mod j m
        let back_m = d.symm(dq_i, mi_m, e1i);
        let mid_m = d.trans(mi_m, dq_i, dq_j, back_m, hdiv);
        let eq_mod_m = d.trans(mi_m, dq_j, mj_m, mid_m, e1j);
        let back_n = d.symm(dr_i, mi_n, e2i);
        let mid_n = d.trans(mi_n, dr_i, dr_j, back_n, hmod);
        let eq_mod_n = d.trans(mi_n, dr_j, mj_n, mid_n, e2j);

        // --- step 2: residue equality -> modEq, at each modulus ------------
        let modeq_at = |d: &mut NatDev<'_>,
                        modulus: ExprId,
                        pred: ExprId,
                        ri: ExprId,
                        rj: ExprId,
                        h: ExprId| {
            let qi = d.div(i, modulus);
            let qj = d.div(j, modulus);
            let exec_i = d.lemma(p.div_mod_exec, &[pred, i]);
            let exec_j = d.lemma(p.div_mod_exec, &[pred, j]);
            let iff = d.lemma(
                p.mod_eq_iff_div_mod_remainder_eq,
                &[modulus, i, j, qi, ri, qj, rj, exec_i, exec_j],
            );
            let congruence = d.mod_eq(modulus, i, j);
            let rem_eq = d.eq(ri, rj);
            let reverse = iff_reverse(d, congruence, rem_eq, iff);
            d.apply(reverse, &[h])
        };
        let modeq_m = modeq_at(d, m, mp, mi_m, mj_m, eq_mod_m);
        let modeq_n = modeq_at(d, n, np, mi_n, mj_n, eq_mod_n);

        // --- step 3: CRT uniqueness, then to the `mul n m` modulus ---------
        let crt = d.lemma(p.crt_unique, &[m, n, i, j, hgcd, modeq_m, modeq_n]);
        let mn = d.mul(m, n);
        let comm = d.lemma(p.mul_comm, &[m, n]);
        let motive = d.eq_motive(mn, &|d, t| d.mod_eq(t, i, j));
        let crt_bound = d.transport(mn, motive, crt, bound, comm);

        // --- step 4: back to `i = j` ---------------------------------------
        // `mul (succ np) (succ mp)` is defeq `succ (add (mul (succ np) mp) np)`
        // (ι on `mul`, then ι on `add`), so `div_mod_exec` applies at the
        // product modulus with this predecessor and no arithmetic lemma.
        let bound_pred = {
            let partial = d.mul(n, mp);
            d.add(partial, np)
        };
        let qi_b = d.div(i, bound);
        let qj_b = d.div(j, bound);
        let ri_b = d.modulo(i, bound);
        let rj_b = d.modulo(j, bound);
        let exec_i_b = d.lemma(p.div_mod_exec, &[bound_pred, i]);
        let exec_j_b = d.lemma(p.div_mod_exec, &[bound_pred, j]);
        let iff_b = d.lemma(
            p.mod_eq_iff_div_mod_remainder_eq,
            &[bound, i, j, qi_b, ri_b, qj_b, rj_b, exec_i_b, exec_j_b],
        );
        let congruence_b = d.mod_eq(bound, i, j);
        let rem_eq_b = d.eq(ri_b, rj_b);
        let forward_b = iff_forward(d, congruence_b, rem_eq_b, iff_b);
        let rem_equal = d.apply(forward_b, &[crt_bound]);

        let self_i = d.lemma(p.mod_eq_self_of_lt, &[i, bound, hi]);
        let self_j = d.lemma(p.mod_eq_self_of_lt, &[j, bound, hj]);
        let up = d.symm(ri_b, i, self_i);
        let across = d.trans(i, ri_b, rj_b, up, rem_equal);
        let body = d.trans(i, rj_b, j, across, self_j);

        let with_heq = d.lam_fv(heq_fv, heq_ty, body);
        let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
        let over_j = d.lam_fv(j_fv, nat, with_hi);
        let over_i = d.lam_fv(i_fv, nat, over_j);
        let proof = d.lam_fv(hgcd_fv, hgcd_ty, over_i);
        (stmt, proof)
    })?;
    Ok(())
}

// ============================================================================
// The `Prop`-`Iff` -> `Bool`-equality bridge for the coprimality predicate.
// ============================================================================

/// `Eq Bool (beq (gcd x (mul m n)) 1)
///          (band (beq (gcd x m) 1) (beq (gcd x n) 1))`
///
/// `Nat.coprime_mul_iff` is unconditional (no `Coprime m n` anywhere), and so
/// is this: it is the pointwise half of the argument, which the numerics
/// confirm at all 26 non-coprime pairs. Three branches, decided by
/// `bool_true_or_false` on each factor; the two impossible ones are refuted
/// with `beq_eq_true_of_eq` against the branch hypothesis and eliminated
/// through `false_true_elim`. Constructive throughout — `Bool` has two
/// constructors, so this is case analysis, not excluded middle.
#[allow(clippy::too_many_lines)]
fn coprime_bool_bridge(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    m: ExprId,
    n: ExprId,
) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let true_ = d.bool_true();
    let false_ = d.bool_false();

    let mn = d.mul(m, n);
    let gx_mn = d.gcd(x, mn);
    let lhs = d.beq(gx_mn, one);
    let gx_m = d.gcd(x, m);
    let gx_n = d.gcd(x, n);
    let a = d.beq(gx_m, one);
    let b = d.beq(gx_n, one);
    let rhs = band(d, &p, a, b);
    let goal = d.bool_eq(lhs, rhs);

    let left_prop = d.eq(gx_mn, one);
    let eq_m = d.eq(gx_m, one);
    let eq_n = d.eq(gx_n, one);
    let and_prop = d.const_app(p.logic.and, &[eq_m, eq_n]);
    let iff = d.lemma(p.coprime_mul_iff, &[x, m, n]);
    let forward = iff_forward(d, left_prop, and_prop, iff);
    let reverse = iff_reverse(d, left_prop, and_prop, iff);

    // `Eq Bool lhs false`, given that ONE factor is `false`. `take_left`
    // selects which conjunct of `coprime_mul_iff`'s forward direction
    // contradicts it.
    let lhs_false = |d: &mut NatDev<'_>, take_left: bool, factor_false: ExprId| {
        let factor = if take_left { a } else { b };
        let factor_gcd = if take_left { gx_m } else { gx_n };
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let conj = d.apply(forward, &[h]);
        let projected = if take_left {
            and_left(d, eq_m, eq_n, conj)
        } else {
            and_right(d, eq_m, eq_n, conj)
        };
        let is_true = d.lemma(p.beq_eq_true_of_eq, &[factor_gcd, one, projected]);
        let flipped = d.bool_symm(factor, false_, factor_false);
        let absurd_eq = d.bool_trans(false_, factor, true_, flipped, is_true);
        let false_prop = d.kernel().const_(p.logic.false_, vec![]);
        let absurd = d.false_true_elim(false_prop, absurd_eq);
        let not_proof = d.lam_fv(h_fv, left_prop, absurd);
        d.lemma(p.beq_eq_false_of_ne, &[gx_mn, one, not_proof])
    };

    let a_true_ty = d.bool_eq(a, true_);
    let a_false_ty = d.bool_eq(a, false_);
    let b_true_ty = d.bool_eq(b, true_);
    let b_false_ty = d.bool_eq(b, false_);

    // --- branch `a = false`: `band false b` ι-reduces to `false` -----------
    let on_a_false = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let l_false = lhs_false(d, true, h);
        let collapse = bool_congr_bool(d, a, false_, h, &|d, t| band(d, &p, t, b));
        let flipped = d.bool_symm(rhs, false_, collapse);
        let body = d.bool_trans(lhs, false_, rhs, l_false, flipped);
        d.lam_fv(h_fv, a_false_ty, body)
    };

    // --- branch `a = true` -------------------------------------------------
    let on_a_true = {
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);

        let on_b_true = {
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let pm = d.lemma(p.eq_of_beq_eq_true, &[gx_m, one, ha]);
            let pn = d.lemma(p.eq_of_beq_eq_true, &[gx_n, one, hb]);
            let conj = d.const_app(p.logic.and_intro, &[eq_m, eq_n, pm, pn]);
            let coprime = d.apply(reverse, &[conj]);
            let l_true = d.lemma(p.beq_eq_true_of_eq, &[gx_mn, one, coprime]);
            // `band a b = band true b = band true true`, and the last is `true`.
            let s1 = bool_congr_bool(d, a, true_, ha, &|d, t| band(d, &p, t, b));
            let mid = band(d, &p, true_, b);
            let s2 = bool_congr_bool(d, b, true_, hb, &|d, t| band(d, &p, true_, t));
            let top = band(d, &p, true_, true_);
            let chain = d.bool_trans(rhs, mid, top, s1, s2);
            let flipped = d.bool_symm(rhs, top, chain);
            let body = d.bool_trans(lhs, true_, rhs, l_true, flipped);
            d.lam_fv(hb_fv, b_true_ty, body)
        };
        let on_b_false = {
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);
            let l_false = lhs_false(d, false, hb);
            let s1 = bool_congr_bool(d, a, true_, ha, &|d, t| band(d, &p, t, b));
            let mid = band(d, &p, true_, b);
            let s2 = bool_congr_bool(d, b, false_, hb, &|d, t| band(d, &p, true_, t));
            let bottom = band(d, &p, true_, false_);
            let chain = d.bool_trans(rhs, mid, bottom, s1, s2);
            let flipped = d.bool_symm(rhs, bottom, chain);
            let body = d.bool_trans(lhs, false_, rhs, l_false, flipped);
            d.lam_fv(hb_fv, b_false_ty, body)
        };

        let decided_b = bool_true_or_false(d, &p, b);
        let body = or_elim(
            d, &p, b_true_ty, b_false_ty, goal, on_b_true, on_b_false, decided_b,
        );
        d.lam_fv(ha_fv, a_true_ty, body)
    };

    let decided_a = bool_true_or_false(d, &p, a);
    or_elim(
        d, &p, a_true_ty, a_false_ty, goal, on_a_true, on_a_false, decided_a,
    )
}

// ============================================================================
// `Nat.totient_mul_of_coprime`.
// ============================================================================

/// `∀ x, Eq Bool (P x) (V (g x))` — the pointwise identity
/// `Nat.countRange_congr` consumes. Unconditional: no coprimality hypothesis
/// appears anywhere in it, and the numerics confirm it at all 26 non-coprime
/// pairs for every `x < 60`.
fn pointwise_identity(d: &mut NatDev<'_>, p: &NatPrelude, mp: ExprId, np: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.num(1);
    let m = d.succ(mp);
    let n = d.succ(np);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let mx = d.modulo(x, m);
    let nx = d.modulo(x, n);
    let gx = crt_image(d, mp, np, x);

    let pos_n = d.zero_lt_succ(np);
    let lt_x_n = d.lemma(p.mod_lt, &[x, n, pos_n]);
    let blk = d.lemma(p.div_mod_block, &[n, mx, nx, lt_x_n]);
    let dq = d.div(gx, n);
    let dr = d.modulo(gx, n);
    let l_ty = d.eq(dq, mx);
    let r_ty = d.eq(dr, nx);
    let e1 = and_left(d, l_ty, r_ty, blk);
    let e2 = and_right(d, l_ty, r_ty, blk);

    // `gcd (div (g x) n) m = gcd (mod x m) m = gcd x m`, and likewise at `n`.
    let gcd_dq = d.gcd(dq, m);
    let gcd_mx = d.gcd(mx, m);
    let gcd_x_m = d.gcd(x, m);
    let c1 = d.congr(dq, mx, e1, &|d, t| d.gcd(t, m));
    let g1 = d.lemma(p.gcd_mod_left_eq_gcd, &[x, m]);
    let ha = d.trans(gcd_dq, gcd_mx, gcd_x_m, c1, g1);

    let gcd_dr = d.gcd(dr, n);
    let gcd_nx = d.gcd(nx, n);
    let gcd_x_n = d.gcd(x, n);
    let c2 = d.congr(dr, nx, e2, &|d, t| d.gcd(t, n));
    let g2 = d.lemma(p.gcd_mod_left_eq_gcd, &[x, n]);
    let hb = d.trans(gcd_dr, gcd_nx, gcd_x_n, c2, g2);

    let a_raw = d.beq(gcd_dq, one);
    let b_raw = d.beq(gcd_dr, one);
    let a_fin = d.beq(gcd_x_m, one);
    let b_fin = d.beq(gcd_x_n, one);
    let start = band(d, &p, a_raw, b_raw);
    let mid = band(d, &p, a_fin, b_raw);
    let end = band(d, &p, a_fin, b_fin);
    let s1 = nat_congr_bool(d, gcd_dq, gcd_x_m, ha, &|d, t| {
        let bt = d.beq(t, one);
        band(d, &p, bt, b_raw)
    });
    let s2 = nat_congr_bool(d, gcd_dr, gcd_x_n, hb, &|d, t| {
        let bt = d.beq(t, one);
        band(d, &p, a_fin, bt)
    });
    let rewritten = d.bool_trans(start, mid, end, s1, s2);

    let core = coprime_bool_bridge(d, &p, x, m, n);
    let mn = d.mul(m, n);
    let gx_mn = d.gcd(x, mn);
    let px = d.beq(gx_mn, one);
    let flipped = d.bool_symm(start, end, rewritten);
    let body = d.bool_trans(px, end, start, core, flipped);
    d.lam_fv(x_fv, nat, body)
}

/// One of `countRange_product`'s two per-block hypotheses, at
/// `V y := band (R (div y n)) (S (mod y n))`.
///
/// `pinned` is the `Bool` the hypothesis fixes `R a` to. Both branches are
/// the same proof: `Nat.div_mod_block` rewrites `V (n*a + b)` into
/// `band (R a) (S b)`, and then `band pinned (S b)` ι-reduces — to `S b` at
/// `true`, to `false` at `false`. That is why `band` is strict in its FIRST
/// argument; nothing else discharges these two.
fn block_hypothesis(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    mp: ExprId,
    np: ExprId,
    pinned: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.num(1);
    let m = d.succ(mp);
    let n = d.succ(np);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let hb_ty = d.lt(b, n);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);

    let gcd_a_m = d.gcd(a, m);
    let r_a = d.beq(gcd_a_m, one);
    let gcd_b_n = d.gcd(b, n);
    let s_b = d.beq(gcd_b_n, one);
    let hr_ty = d.bool_eq(r_a, pinned);
    let hr_fv = d.fresh_fvar();
    let hr = d.kernel().fvar(hr_fv);

    let na = d.mul(n, a);
    let idx = d.add(na, b);
    let blk = d.lemma(p.div_mod_block, &[n, a, b, hb]);
    let dq = d.div(idx, n);
    let dr = d.modulo(idx, n);
    let l_ty = d.eq(dq, a);
    let r_ty = d.eq(dr, b);
    let e1 = and_left(d, l_ty, r_ty, blk);
    let e2 = and_right(d, l_ty, r_ty, blk);

    let gcd_dq = d.gcd(dq, m);
    let gcd_dr = d.gcd(dr, n);
    let a_raw = d.beq(gcd_dq, one);
    let b_raw = d.beq(gcd_dr, one);
    let start = band(d, &p, a_raw, b_raw);
    let mid = band(d, &p, r_a, b_raw);
    let end = band(d, &p, r_a, s_b);
    let s1 = nat_congr_bool(d, dq, a, e1, &|d, t| {
        let g = d.gcd(t, m);
        let bt = d.beq(g, one);
        band(d, &p, bt, b_raw)
    });
    let s2 = nat_congr_bool(d, dr, b, e2, &|d, t| {
        let g = d.gcd(t, n);
        let bt = d.beq(g, one);
        band(d, &p, r_a, bt)
    });
    let rewritten = d.bool_trans(start, mid, end, s1, s2);

    let collapsed = band(d, &p, pinned, s_b);
    let step = bool_congr_bool(d, r_a, pinned, hr, &|d, t| band(d, &p, t, s_b));
    let body = d.bool_trans(start, end, collapsed, rewritten, step);

    let with_hr = d.lam_fv(hr_fv, hr_ty, body);
    let with_hb = d.lam_fv(hb_fv, hb_ty, with_hr);
    let over_b = d.lam_fv(b_fv, nat, with_hb);
    d.lam_fv(a_fv, nat, over_b)
}

/// `Eq (totient (mul m n)) (mul (totient m) (totient n))`.
fn goal(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId) -> ExprId {
    let mn = d.mul(m, n);
    let lhs = d.const_app(p.totient, &[mn]);
    let tm = d.const_app(p.totient, &[m]);
    let tn = d.const_app(p.totient, &[n]);
    let rhs = d.mul(tm, tn);
    d.eq(lhs, rhs)
}

/// The whole chain, at `m = succ mp` and `n = succ np`, under
/// `hgcd : Eq (gcd (succ mp) (succ np)) 1`.
fn positive_case(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    mp: ExprId,
    np: ExprId,
    hgcd: ExprId,
) -> ExprId {
    let p = *p;
    let m = d.succ(mp);
    let n = d.succ(np);
    let mn = d.mul(m, n);
    let bound = d.mul(n, m);

    let pred_p = coprime_pred(d, mn);
    let v = block_pred(d, &p, m, n);
    let g = crt_self_map(d, mp, np);
    let vg = compose(d, v, g);
    let r = coprime_pred(d, m);
    let s = coprime_pred(d, n);

    // `countRange P (mul m n)` IS `totient (mul m n)` by δ.
    let start = count_range(d, &p, pred_p, mn);

    // (b) rewrite the BOUND only; `P` keeps naming `mul m n` and that is fine.
    let comm = d.lemma(p.mul_comm, &[m, n]);
    let step_b = d.congr(mn, bound, comm, &|d, t| count_range(d, &p, pred_p, t));
    let after_b = count_range(d, &p, pred_p, bound);

    // (c) pointwise, unconditional.
    let pointwise = pointwise_identity(d, &p, mp, np);
    let step_c = d.lemma(p.count_range_congr, &[pred_p, vg, bound, pointwise]);
    let after_c = count_range(d, &p, vg, bound);

    // (d) the permutation, SYMM -- this is the one step needing coprimality.
    let injective = d.lemma(p.crt_self_map_injective_on, &[mp, np, hgcd]);
    let maps_into = d.lemma(p.crt_self_map_maps_into, &[mp, np]);
    let permute = d.lemma(p.count_range_permute, &[v, g, bound, injective, maps_into]);
    let after_d = count_range(d, &p, v, bound);
    let step_d = d.symm(after_d, after_c, permute);

    // (e) the Fubini factorization, unconditional.
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let h_true = block_hypothesis(d, &p, mp, np, true_);
    let h_false = block_hypothesis(d, &p, mp, np, false_);
    let step_e = d.lemma(p.count_range_product, &[v, r, s, n, m, h_true, h_false]);
    let cs = count_range(d, &p, s, n);
    let cr = count_range(d, &p, r, m);
    let after_e = d.mul(cs, cr);

    // (f) `countRange S n` IS `totient n` and `countRange R m` IS `totient m`,
    //     both by δ, so this last `mul_comm` lands exactly on the goal.
    let step_f = d.lemma(p.mul_comm, &[cs, cr]);
    let after_f = d.mul(cr, cs);

    let (_last, whole) = d.chain(
        start,
        &[
            (after_b, step_b),
            (after_c, step_c),
            (after_d, step_d),
            (after_e, step_e),
            (after_f, step_f),
        ],
    );
    whole
}

/// `Nat.totient_mul_of_coprime : ∀ m n, Eq (gcd m n) 1 →
///   Eq (totient (mul m n)) (mul (totient m) (totient n))`
///
/// See the module doc for the chain and for which of its steps needs the
/// hypothesis (exactly one: the permutation along the CRT self-map).
///
/// Both arguments are split once at the top. `n = 0` is `Eq.refl zero`:
/// `Nat.mul` recurses on its RIGHT argument so `mul m 0` ι-reduces, and
/// `totient 0` is `countRange _ 0`, which is `zero`; the right-hand side
/// collapses the same way. `m = 0` is the one that is NOT free —
/// `mul 0 n` does not reduce for symbolic `n` — and needs `Nat.zero_mul`
/// twice, once inside `totient` and once outside.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// type-check.
pub(super) fn declare_totient_mul_of_coprime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.totient_mul_of_coprime, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let one = d.num(1);
        let gcd_mn = d.gcd(m, n);
        let hyp_ty = d.eq(gcd_mn, one);
        let target = goal(d, &p, m, n);
        let stmt = d.arrow(hyp_ty, target);

        let outer_motive = |d: &mut NatDev<'_>, x: ExprId| {
            let g = d.gcd(m, x);
            let o = d.num(1);
            let h = d.eq(g, o);
            let t = goal(d, &p, m, x);
            d.arrow(h, t)
        };

        let proof = cases_zero_succ(
            d,
            n,
            &outer_motive,
            // n = 0: `mul m 0`, `totient 0` and `mul _ 0` all ι-reduce to zero.
            &|d| {
                let zero = d.zero();
                let g = d.gcd(m, zero);
                let o = d.num(1);
                let h_ty = d.eq(g, o);
                let h_fv = d.fresh_fvar();
                let body = d.refl(zero);
                d.lam_fv(h_fv, h_ty, body)
            },
            &|d, np| {
                let n_inner = d.succ(np);
                let inner_motive = |d: &mut NatDev<'_>, y: ExprId| {
                    let g = d.gcd(y, n_inner);
                    let o = d.num(1);
                    let h = d.eq(g, o);
                    let t = goal(d, &p, y, n_inner);
                    d.arrow(h, t)
                };
                cases_zero_succ(
                    d,
                    m,
                    &inner_motive,
                    // m = 0: `mul 0 n` needs `zero_mul`; so does `mul 0 (totient n)`.
                    &|d| {
                        let zero = d.zero();
                        let g = d.gcd(zero, n_inner);
                        let o = d.num(1);
                        let h_ty = d.eq(g, o);
                        let h_fv = d.fresh_fvar();
                        let zm = d.lemma(p.zero_mul, &[n_inner]);
                        let zero_n = d.mul(zero, n_inner);
                        let tot_zn = d.const_app(p.totient, &[zero_n]);
                        let tot_zero = d.const_app(p.totient, &[zero]);
                        let step1 = d.congr(zero_n, zero, zm, &|d, t| d.const_app(p.totient, &[t]));
                        let tot_n = d.const_app(p.totient, &[n_inner]);
                        let zm2 = d.lemma(p.zero_mul, &[tot_n]);
                        let prod = d.mul(zero, tot_n);
                        let step2 = d.symm(prod, zero, zm2);
                        let body = d.trans(tot_zn, tot_zero, prod, step1, step2);
                        d.lam_fv(h_fv, h_ty, body)
                    },
                    &|d, mp| {
                        let m_inner = d.succ(mp);
                        let g = d.gcd(m_inner, n_inner);
                        let o = d.num(1);
                        let h_ty = d.eq(g, o);
                        let h_fv = d.fresh_fvar();
                        let h = d.kernel().fvar(h_fv);
                        let body = positive_case(d, &p, mp, np, h);
                        d.lam_fv(h_fv, h_ty, body)
                    },
                )
            },
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// Declare the two CRT self-map facts and then
/// [`declare_totient_mul_of_coprime`], which consumes both.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_totient_mul_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_crt_self_map_maps_into(d, p)?;
    declare_crt_self_map_injective_on(d, p)?;
    declare_totient_mul_of_coprime(d, p)?;
    Ok(())
}
