//! Ten `ml430` addition mirrors that are not already covered by
//! [`super::algebra::declare_additive_theorems`]: `add_add_add_comm`, the
//! notation bridge `add_eq`, the two "solve for the other summand"
//! biconditionals `add_eq_left`/`add_eq_right`, the `Iff` form of
//! `add_eq_zero`, and the `add_eq_{one,two,three}_iff` family.
//!
//! `Nat.add_assoc` and `Nat.add_comm` (`declare_additive_theorems`) and the
//! mp-only `Nat.add_eq_zero` (`declare_add_no_zero_summands`) already exist
//! under those exact names with types matching the corresponding Mathlib
//! lemmas verbatim, so those three facts close by evidence pointing at the
//! existing declarations rather than by anything in this file. This file adds
//! `add_eq_zero_iff` — Mathlib's current (post-2025-10-26-deprecation) name
//! for the `Iff` — as a NEW declaration rather than widening `add_eq_zero`,
//! because that name is already taken by the weaker arrow-only theorem and a
//! prelude can never redeclare a name (see `nat_prelude.rs`'s cross-prelude
//! collision gotcha in `CLAUDE.md`).
//!
//! The `add_eq_{one,two,three}_iff` group shares one generic helper,
//! [`declare_add_eq_lit_iff`], parameterized only by the small literal `k`:
//!
//! - `mp` (`add m n = k → disjunction`) bounds `m ≤ k` via `le_add_right` +
//!   `Eq` transport, then walks `lt_or_eq_of_le`/`le_of_lt_succ` down from
//!   `k` to `0` (the same bounded-case-split idiom `choose.rs`/`min_fac.rs`/
//!   `desc_factorial.rs` use elsewhere in this prelude). Each `Eq` leaf
//!   recovers the matching `n` via `add_left_cancel` and is placed into the
//!   right-associated `Or` chain at position `i` by `place_in_or`; the `Lt`
//!   leaf at bound `0` is a contradiction via `not_lt_zero`.
//! - `mpr` (`disjunction → add m n = k`) walks the SAME `Or` shape via a
//!   private `or_elim`, and at each atom substitutes both conjuncts by
//!   `congr` and closes the resulting concrete arithmetic identity by
//!   `Eq.refl` (small numerals fully reduce by defeq).
//!
//! `or_elim`/`absurd` are private per-file copies of the non-dependent
//! `Or.rec`/`False.rec` wrappers `fibonacci.rs`/`rec_agreement.rs`/
//! `choose.rs` each already carry (see their doc comments for why this
//! follows the existing per-file-copy convention rather than a new shared
//! one).

use super::NatPrelude;
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps};
use super::steps::absurd;
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// Non-dependent `Or.rec` (private copy; see the module doc for why).
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
    let p = *p;
    let anon = d.anon_name();
    let or_ty = d.const_app(p.logic.or, &[left_ty, right_ty]);
    let motive = d.kernel().lam(anon, or_ty, goal, BinderInfo::Default);
    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
    d.apply(
        or_rec,
        &[left_ty, right_ty, motive, left_case, right_case, or_proof],
    )
}

/// `(a+b)+(c+d) = (a+c)+(b+d)`, via `add_assoc` twice, `add_comm` once —
/// see `div_mod_lemmas.rs`'s per-file copy of the same shape for the fully
/// annotated version this mirrors; this prelude never exposed it publicly
/// before (`nat_prelude.rs` doc: "this prelude has no `add_add_add_comm`").
pub(super) fn declare_add_add_add_comm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_add_add_comm, 4, &|d, v| {
        let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
        let cd = d.add(c, dd);
        let bd = d.add(b, dd);
        let ab = d.add(a, b);
        let start = d.add(ab, cd);

        // start = a + (b + (c+d))
        let bcd = d.add(b, cd);
        let s1 = d.add(a, bcd);
        let h1 = d.lemma(p.add_assoc, &[a, b, cd]);

        // b+(c+d) -> (b+c)+d
        let bc = d.add(b, c);
        let bc_d = d.add(bc, dd);
        let s2 = d.add(a, bc_d);
        let h_bcd = d.lemma(p.add_assoc, &[b, c, dd]); // (b+c)+d = b+(c+d)
        let h2_inner = d.symm(bc_d, bcd, h_bcd); // b+(c+d) = (b+c)+d
        let h2 = d.congr(bcd, bc_d, h2_inner, &|d, t| d.add(a, t));

        // (b+c) -> (c+b)
        let cb = d.add(c, b);
        let cb_d = d.add(cb, dd);
        let s3 = d.add(a, cb_d);
        let h_comm = d.lemma(p.add_comm, &[b, c]); // b+c = c+b
        let h3 = d.congr(bc, cb, h_comm, &|d, t| {
            let t_d = d.add(t, dd);
            d.add(a, t_d)
        });

        // a + ((c+b)+d) -> (a+c) + (b+d)
        let ac = d.add(a, c);
        let target = d.add(ac, bd);
        let h4 = d.lemma(p.add_assoc, &[c, b, dd]); // (c+b)+d = c+(b+d)
        let cbd = d.add(c, bd);
        let s4 = d.add(a, cbd);
        let h4c = d.congr(cb_d, cbd, h4, &|d, t| d.add(a, t));
        let h5 = d.lemma(p.add_assoc, &[a, c, bd]); // (a+c)+(b+d) = a+(c+(b+d))
        let h5_rev = d.symm(target, s4, h5);

        let (_end, proof) = d.chain(
            start,
            &[(s1, h1), (s2, h2), (s3, h3), (s4, h4c), (target, h5_rev)],
        );
        let stmt = d.eq(start, target);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.add_eq : ∀ x y, add x y = add x y` — this prelude has one `add`
/// function and no separate `+` notation over it, so Mathlib's
/// `Nat.add x y = x + y` bridge is the identity function applied to itself,
/// closed by `Eq.refl`.
pub(super) fn declare_add_eq(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_eq, 2, &|d, v| {
        let (x, y) = (v[0], v[1]);
        let axy = d.add(x, y);
        let stmt = d.eq(axy, axy);
        let proof = d.refl(axy);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.add_eq_left : ∀ a b, add a b = a ↔ b = 0`.
pub(super) fn declare_add_eq_left(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_eq_left, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ab = d.add(a, b);
        let zero = d.zero();
        let lhs_ty = d.eq(ab, a);
        let rhs_ty = d.eq(b, zero);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

        // mp : (a+b=a) -> b=0
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let a0 = d.add(a, zero);
            let add_zero_a = d.lemma(p.add_zero, &[a]); // Eq (add a 0) a
            let a_eq_a0 = d.symm(a0, a, add_zero_a); // Eq a (add a 0)
            let ab_eq_a0 = d.trans(ab, a, a0, h, a_eq_a0); // Eq (add a b) (add a 0)
            let body = d.lemma(p.add_left_cancel, &[a, b, zero, ab_eq_a0]); // Eq b 0
            d.lam_fv(h_fv, lhs_ty, body)
        };

        // mpr : b=0 -> a+b=a
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let a0 = d.add(a, zero);
            let congr_h = d.congr(b, zero, h, &|d, t| d.add(a, t)); // Eq (add a b) (add a 0)
            let add_zero_a = d.lemma(p.add_zero, &[a]); // Eq (add a 0) a
            let body = d.trans(ab, a0, a, congr_h, add_zero_a); // Eq (add a b) a
            d.lam_fv(h_fv, rhs_ty, body)
        };

        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.add_eq_right : ∀ a b, add a b = b ↔ a = 0`.
pub(super) fn declare_add_eq_right(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_eq_right, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let ab = d.add(a, b);
        let zero = d.zero();
        let lhs_ty = d.eq(ab, b);
        let rhs_ty = d.eq(a, zero);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

        // mp : (a+b=b) -> a=0
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let zb = d.add(zero, b);
            let zero_add_b = d.lemma(p.zero_add, &[b]); // Eq (add 0 b) b
            let b_eq_zb = d.symm(zb, b, zero_add_b); // Eq b (add 0 b)
            let ab_eq_zb = d.trans(ab, b, zb, h, b_eq_zb); // Eq (add a b) (add 0 b)
            let body = d.lemma(p.add_right_cancel, &[a, zero, b, ab_eq_zb]); // Eq a 0
            d.lam_fv(h_fv, lhs_ty, body)
        };

        // mpr : a=0 -> a+b=b
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let zb = d.add(zero, b);
            let congr_h = d.congr(a, zero, h, &|d, t| d.add(t, b)); // Eq (add a b) (add 0 b)
            let zero_add_b = d.lemma(p.zero_add, &[b]); // Eq (add 0 b) b
            let body = d.trans(ab, zb, b, congr_h, zero_add_b); // Eq (add a b) b
            d.lam_fv(h_fv, rhs_ty, body)
        };

        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.add_eq_zero_iff : ∀ m n, add m n = 0 ↔ m = 0 ∧ n = 0` — the `Iff`
/// Mathlib states; `p.add_eq_zero` (already declared for a bitwise consumer)
/// is only the mp arrow, reused directly here rather than re-derived.
pub(super) fn declare_add_eq_zero_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.add_eq_zero_iff, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let mn = d.add(m, n);
        let zero = d.zero();
        let lhs_ty = d.eq(mn, zero);
        let m0 = d.eq(m, zero);
        let n0 = d.eq(n, zero);
        let rhs_ty = d.const_app(p.logic.and, &[m0, n0]);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);

        // mp : reuse the already-declared arrow directly.
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.lemma(p.add_eq_zero, &[m, n, h]);
            d.lam_fv(h_fv, lhs_ty, body)
        };

        // mpr : And(m=0,n=0) -> add m n = 0
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hm = and_left(d, m0, n0, h);
            let hn = and_right(d, m0, n0, h);
            let zn = d.add(zero, n);
            let zz = d.add(zero, zero);
            let step1 = d.congr(m, zero, hm, &|d, t| d.add(t, n)); // Eq (add m n) (add 0 n)
            let step2 = d.congr(n, zero, hn, &|d, t| d.add(zero, t)); // Eq (add 0 n) (add 0 0)
            let zero_add_zero = d.lemma(p.zero_add, &[zero]); // Eq (add 0 0) 0
            let (_end, body) = d.chain(mn, &[(zn, step1), (zz, step2), (zero, zero_add_zero)]);
            d.lam_fv(h_fv, rhs_ty, body)
        };

        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// The `atom` conjunction for disjunct `i` of `add_eq_lit_iff`:
/// `And (Eq m (num i)) (Eq n (num (k-i)))`.
fn add_eq_atom(d: &mut NatDev<'_>, p: &NatPrelude, m: ExprId, n: ExprId, i: u32, k: u32) -> ExprId {
    let p = *p;
    let i_lit = d.num(i);
    let ki_lit = d.num(k - i);
    let mi = d.eq(m, i_lit);
    let nk = d.eq(n, ki_lit);
    d.const_app(p.logic.and, &[mi, nk])
}

/// `Or(atoms[start], Or(atoms[start+1], … atoms[last]))`, right-associated
/// (matching Lean's `∨`), the disjunction shape all three `add_eq_*_iff`
/// facts state.
fn suffix_or_type(d: &mut NatDev<'_>, p: &NatPrelude, atoms: &[ExprId], start: usize) -> ExprId {
    let p = *p;
    if start + 1 == atoms.len() {
        atoms[start]
    } else {
        let rest = suffix_or_type(d, &p, atoms, start + 1);
        d.const_app(p.logic.or, &[atoms[start], rest])
    }
}

/// Embed a proof of `atoms[i]` into the full right-associated `Or` chain
/// over `atoms`, via `i` applications of `or_inr` (to skip past the earlier
/// disjuncts) followed by one `or_inl` (unless `i` is the last disjunct, in
/// which case no wrapping is needed at all).
fn place_in_or(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    atoms: &[ExprId],
    i: usize,
    atom_proof: ExprId,
) -> ExprId {
    let p = *p;
    let last = atoms.len() - 1;
    let mut proof = if i == last {
        atom_proof
    } else {
        let suffix = suffix_or_type(d, &p, atoms, i + 1);
        d.const_app(p.logic.or_inl, &[atoms[i], suffix, atom_proof])
    };
    for j in (0..i).rev() {
        let suffix = suffix_or_type(d, &p, atoms, j + 1);
        proof = d.const_app(p.logic.or_inr, &[atoms[j], suffix, proof]);
    }
    proof
}

/// The recursive `mp` step: given `Le m bound_lit` (`bound_val` in Rust),
/// `h : Eq (add m n) k_lit`, and the full `atoms`/`disj_ty`, produce a proof
/// of `disj_ty` by `lt_or_eq_of_le` at `bound_val`, recursing down through
/// `le_of_lt_succ` on the `Lt` branch and closing the `Eq` branch directly.
#[allow(clippy::too_many_arguments)]
fn add_eq_lit_mp_bound(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    h: ExprId,
    k: u32,
    k_lit: ExprId,
    bound_val: u32,
    bound_lit: ExprId,
    le_proof: ExprId,
    atoms: &[ExprId],
    disj_ty: ExprId,
) -> ExprId {
    let p = *p;
    let lt_ty = d.lt(m, bound_lit);
    let eq_ty = d.eq(m, bound_lit);
    let split = d.lemma(p.lt_or_eq_of_le, &[m, bound_lit, le_proof]);

    // Eq branch: m = bound_lit -> derive n = num(k-bound_val), place atom.
    let eq_branch = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let n_val = k - bound_val;
        let n_lit = d.num(n_val);

        // Eq (add bound_lit n) k_lit, from h and heq.
        let mn = d.add(m, n);
        let step1 = d.congr(m, bound_lit, heq, &|d, t| d.add(t, n)); // Eq (add m n) (add bound_lit n)
        let bn = d.add(bound_lit, n);
        let step1_symm = d.symm(mn, bn, step1);
        let combined = d.trans(bn, mn, k_lit, step1_symm, h);

        // Eq (add bound_lit n_lit) k_lit, by defeq (small concrete arithmetic):
        // `d.refl(bnl)` infers `Eq bnl bnl`, accepted here at `Eq bnl k_lit`
        // because `bnl` and `k_lit` reduce to the same normal form.
        let bnl = d.add(bound_lit, n_lit);
        let known_leg = d.refl(bnl);
        let known_leg_symm = d.symm(bnl, k_lit, known_leg);

        let proof_eq = d.trans(bn, k_lit, bnl, combined, known_leg_symm);
        let n_eq = d.lemma(p.add_left_cancel, &[bound_lit, n, n_lit, proof_eq]); // Eq n n_lit

        let n_eq_ty = d.eq(n, n_lit);
        let atom_proof = d.const_app(p.logic.and_intro, &[eq_ty, n_eq_ty, heq, n_eq]);
        let placed = place_in_or(d, &p, atoms, bound_val as usize, atom_proof);
        d.lam_fv(heq_fv, eq_ty, placed)
    };

    // Lt branch: m < bound_lit -> either contradiction (bound_val == 0) or
    // recurse one bound lower.
    let lt_branch = {
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);
        if bound_val == 0 {
            let contra = d.lemma(p.not_lt_zero, &[m, hlt]); // False
            let result = absurd(d, disj_ty, contra);
            d.lam_fv(hlt_fv, lt_ty, result)
        } else {
            let new_bound_val = bound_val - 1;
            let new_bound_lit = d.num(new_bound_val);
            let new_le = d.lemma(p.le_of_lt_succ, &[m, new_bound_lit, hlt]); // Le m new_bound_lit
            let sub_proof = add_eq_lit_mp_bound(
                d,
                &p,
                m,
                n,
                h,
                k,
                k_lit,
                new_bound_val,
                new_bound_lit,
                new_le,
                atoms,
                disj_ty,
            );
            d.lam_fv(hlt_fv, lt_ty, sub_proof)
        }
    };

    or_elim(d, &p, lt_ty, eq_ty, disj_ty, lt_branch, eq_branch, split)
}

/// `Eq (add m n) k_lit` given `hm : Eq m (num i)`, `hn : Eq n (num (k-i))`.
#[allow(clippy::too_many_arguments)]
fn add_eq_lit_close(
    d: &mut NatDev<'_>,
    m: ExprId,
    n: ExprId,
    k: u32,
    k_lit: ExprId,
    i: u32,
    hm: ExprId,
    hn: ExprId,
) -> ExprId {
    let mn = d.add(m, n);
    let mi = d.num(i);
    let nk = d.num(k - i);
    let step1 = d.congr(m, mi, hm, &|d, t| d.add(t, n)); // Eq (add m n) (add i n)
    let ikn = d.add(mi, n);
    let step2 = d.congr(n, nk, hn, &|d, t| d.add(mi, t)); // Eq (add i n) (add i (k-i))
    let ikk = d.add(mi, nk);
    let known = d.refl(ikk); // Eq (add i (k-i)) (add i (k-i)), used at type Eq ikk k_lit (defeq)
    let (_end, proof) = d.chain(mn, &[(ikn, step1), (ikk, step2), (k_lit, known)]);
    proof
}

/// Shared helper for `add_eq_one_iff`/`add_eq_two_iff`/`add_eq_three_iff`:
/// `Iff (Eq (add m n) (num k)) (Or_{i=0}^{k} (And (Eq m i) (Eq n (k-i))))`.
///
/// See the module doc for the `mp`/`mpr` construction outline.
fn declare_add_eq_lit_iff(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    name: crate::NameId,
    k: u32,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(name, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let k_lit = d.num(k);
        let mn_sum = d.add(m, n);
        let lhs_ty = d.eq(mn_sum, k_lit);
        let atoms: Vec<ExprId> = (0..=k).map(|i| add_eq_atom(d, &p, m, n, i, k)).collect();
        let disj_ty = suffix_or_type(d, &p, &atoms, 0);
        let stmt = d.const_app(p.logic.iff, &[lhs_ty, disj_ty]);

        // mp
        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let sum = d.add(m, n);
            let le_m_sum = d.lemma(p.le_add_right, &[m, n]); // Le m (add m n)
            let motive = d.eq_motive(sum, &|d, x| d.le(m, x));
            let le_m_k = d.transport(sum, motive, le_m_sum, k_lit, h); // Le m k_lit
            let body =
                add_eq_lit_mp_bound(d, &p, m, n, h, k, k_lit, k, k_lit, le_m_k, &atoms, disj_ty);
            d.lam_fv(h_fv, lhs_ty, body)
        };

        // mpr: build directly by recursing over `atoms`, consuming the
        // top-level Or proof at each nesting level via `or_elim`.
        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = add_eq_lit_mpr_top(d, &p, m, n, k, k_lit, &atoms, lhs_ty, h);
            d.lam_fv(h_fv, disj_ty, body)
        };

        let proof = d.const_app(p.logic.iff_intro, &[lhs_ty, disj_ty, mp, mpr]);
        (stmt, proof)
    })?;
    Ok(())
}

/// `mpr`, consuming the ACTUAL top-level disjunction proof `or_proof`
/// directly (unlike [`add_eq_lit_mpr`], which built a function abstracted
/// over it — kept only as a documented alternative shape and unused).
#[allow(clippy::too_many_arguments)]
fn add_eq_lit_mpr_top(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    k: u32,
    k_lit: ExprId,
    atoms: &[ExprId],
    goal: ExprId,
    or_proof: ExprId,
) -> ExprId {
    let p = *p;
    add_eq_lit_mpr_at(d, &p, m, n, k, k_lit, atoms, goal, 0, or_proof)
}

#[allow(clippy::too_many_arguments, clippy::cast_possible_truncation)]
fn add_eq_lit_mpr_at(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    m: ExprId,
    n: ExprId,
    k: u32,
    k_lit: ExprId,
    atoms: &[ExprId],
    goal: ExprId,
    idx: usize,
    or_proof: ExprId,
) -> ExprId {
    let p = *p;
    let i = idx as u32;
    let i_lit = d.num(i);
    let ki_lit = d.num(k - i);
    let mi = d.eq(m, i_lit);
    let nk = d.eq(n, ki_lit);
    let this_atom = atoms[idx];

    let close_atom = |d: &mut NatDev<'_>, h: ExprId| -> ExprId {
        let hm = and_left(d, mi, nk, h);
        let hn = and_right(d, mi, nk, h);
        add_eq_lit_close(d, m, n, k, k_lit, i, hm, hn)
    };

    if idx + 1 == atoms.len() {
        close_atom(d, or_proof)
    } else {
        let suffix = suffix_or_type(d, &p, atoms, idx + 1);
        let left_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = close_atom(d, h);
            d.lam_fv(h_fv, this_atom, body)
        };
        let right_case = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = add_eq_lit_mpr_at(d, &p, m, n, k, k_lit, atoms, goal, idx + 1, h);
            d.lam_fv(h_fv, suffix, body)
        };
        or_elim(
            d, &p, this_atom, suffix, goal, left_case, right_case, or_proof,
        )
    }
}

/// Registers all eight new declarations this file adds (`add_add_add_comm`,
/// `add_eq`, `add_eq_left`, `add_eq_right`, `add_eq_zero_iff`, and the
/// `add_eq_{one,two,three}_iff` family). Must run after
/// `declare_additive_theorems` (`add_comm`/`add_assoc`/`add_zero`/`zero_add`/
/// `add_left_cancel`/`add_right_cancel`), `declare_add_no_zero_summands`
/// (`add_eq_zero`), `declare_order` (`le_add_right`/`lt_or_eq_of_le`),
/// `declare_no_confusion` (`not_lt_zero`), and `declare_order_extra`
/// (`le_of_lt_succ`) — all already run by the time `nat_prelude.rs` calls
/// this, right after `declare_order_more`.
pub(super) fn declare_add_basics(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_add_add_add_comm(d, p)?;
    declare_add_eq(d, p)?;
    declare_add_eq_left(d, p)?;
    declare_add_eq_right(d, p)?;
    declare_add_eq_zero_iff(d, p)?;
    declare_add_eq_lit_iff(d, p, p.add_eq_one_iff, 1)?;
    declare_add_eq_lit_iff(d, p, p.add_eq_two_iff, 2)?;
    declare_add_eq_lit_iff(d, p, p.add_eq_three_iff, 3)?;
    Ok(())
}
