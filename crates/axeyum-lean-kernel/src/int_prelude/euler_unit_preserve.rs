//! `Int.euler_unit_coprime_iff` — the full predicate-preservation step
//! Euler's theorem needs, closing item 2 of `euler_theorem.rs`'s "what does
//! NOT land here" list (`docs/plan/status/374-euler-theorem.md` has the same
//! handoff in full).
//!
//! `Int.euler_unit_coprime` (`euler_totient.rs`) proves only the forward
//! half: `Coprime a n → Coprime k n → Coprime (emod (a*k) n) n`. Feeding
//! that into `Int.prodRangeIf_permute`'s `preserve` hypothesis
//! (`∀ i, i < n → Eq Bool (pred (σ i)) (pred i)`) needs the hypothesis to
//! hold at EVERY `i < n`, not only the coprime ones — so the non-coprime
//! case (`pred (σ i) = false = pred i`) needs the converse: if the IMAGE
//! `emod (a*k) n` is coprime to `n`, so was `k`.
//!
//! ## The route: apply the forward lemma a second time, at `a`'s inverse
//!
//! `Int.modEq_inverse_exists` (`gcd.rs`) gives `a'` with `ModEq n (a*a') one`
//! from `Coprime a n`. Commuting that (`Int.mul_comm`) gives `ModEq n (a'*a)
//! one`, and `euler_totient.rs`'s own private Bézout-extraction step (now
//! `pub(super)`, [`super::euler_totient::coprime_of_modeq_inverse`]) turns
//! *that* into `Coprime a' n` — the same derivation `Int.euler_unit_coprime`
//! itself already uses internally, applied here to `a`'s inverse rather than
//! to `a`.
//!
//! With `a'` coprime to `n`, `Int.euler_unit_coprime` applied at `(n, a', r)`
//! (`r := emod (a*k) n`, given coprime to `n` by the hypothesis) gives
//! `Coprime (emod (a'*r) n) n`. The rest of the proof is pure ring/`ModEq`
//! bookkeeping to identify `emod (a'*r) n` with `k` itself:
//!
//! ```text
//! a'*r  ≡ a'*(a*k)      [n]   (emod_modeq_self + mod_eq_mul_left)
//!       = (a'*a)*k             (mul_assoc)
//!       ≡ one*k          [n]   (h_apa: ModEq n (a'*a) one, mod_eq_mul_right)
//!       = k                    (one_mul)
//! ```
//!
//! chained by `Int.ModEq.trans` into one `ModEq n (a'*r) k` — which, by
//! `ModEq`'s own `Regular`-reducibility definition, unfolds directly to
//! `Eq Int (emod (a'*r) n) (emod k n)` (the same reliance on kernel-level
//! unfolding `declare_euler_unit_injective`'s own doc comment spells out).
//! Rewriting `Coprime (emod (a'*r) n) n` along that equality gives
//! `Coprime (emod k n) n`, and the caller's own bound hypotheses (`0 ≤ k`,
//! `k < n` — always available at the point this lemma is used, since it
//! feeds a `∀ i, i < n → …` hypothesis) let
//! [`super::wilson::emod_eq_self_of_in_range`] finish: `emod k n = k`.
//!
//! No new induction is needed anywhere in this file — every step is a
//! `ModEq`/ring rewrite of already-proved lemmas, applied twice rather than
//! once.
//!
//! ## What this does NOT close
//!
//! This is item 2 alone. Items 1 (bridging these `Int`-sorted bounded
//! hypotheses to the `Nat → Nat` self-map `Int.prodRangeIf_permute`
//! quantifies over) and 3 (the final product/power assembly) are untouched —
//! see `euler_theorem.rs`'s module doc and
//! `docs/plan/status/euler-theorem-spine.md` for the precise remaining gap.

use super::euler::int_exists_elim;
use super::euler_totient::coprime_of_modeq_inverse;
use super::modeq::imodeq;
use super::ops::IntDev;
use super::wilson::{emod_eq_self_of_in_range, emod_modeq_self};
use crate::KernelError;
use crate::nat_prelude::NatOps;

/// Declare `Int.euler_unit_coprime_iff :
/// ∀ n a k, 0 < n → 0 ≤ k → k < n → Coprime a n →
///   (Coprime k n ↔ Coprime (emod (a*k) n) n)`.
///
/// The full predicate-preservation step: `Int.euler_unit_coprime` gives the
/// forward (`mp`) direction directly; the backward (`mpr`) direction is the
/// second-inverse-application argument in the module doc.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection if the constructed term
/// does not check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_euler_unit_coprime_iff(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    d.int_theorem(p.euler_unit_coprime_iff, 3, &|d, v| {
        let (n, a, k) = (v[0], v[1], v[2]);
        let p = d.int();
        let int_ty = d.int_ty();
        let zero = d.izero();
        let one_i = d.ione();

        let pos_ty = d.ilt(zero, n);
        let k0_ty = d.ile(zero, k);
        let klt_ty = d.ilt(k, n);
        let cop_a_ty = d.const_app(p.coprime, &[a, n]);

        let ak = d.imul(a, k);
        let r = d.iemod(ak, n);
        let cop_k_ty = d.const_app(p.coprime, &[k, n]);
        let cop_r_ty = d.const_app(p.coprime, &[r, n]);
        let stmt_iff = d.const_app(p.logic.iff, &[cop_k_ty, cop_r_ty]);

        let stmt = {
            let inner = d.arrow(cop_a_ty, stmt_iff);
            let with_klt = d.arrow(klt_ty, inner);
            let with_k0 = d.arrow(k0_ty, with_klt);
            d.arrow(pos_ty, with_k0)
        };

        let h_pos_fv = d.fresh_fvar();
        let h_pos = d.kernel().fvar(h_pos_fv);
        let h_k0_fv = d.fresh_fvar();
        let h_k0 = d.kernel().fvar(h_k0_fv);
        let h_klt_fv = d.fresh_fvar();
        let h_klt = d.kernel().fvar(h_klt_fv);
        let h_cop_a_fv = d.fresh_fvar();
        let h_cop_a = d.kernel().fvar(h_cop_a_fv);

        // --- mp : Coprime k n -> Coprime r n --- (Int.euler_unit_coprime,
        // directly).
        let mp = {
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let body = d.lemma(p.euler_unit_coprime, &[n, a, k, h_pos, h_cop_a, hk]);
            d.lam_fv(hk_fv, cop_k_ty, body)
        };

        // --- mpr : Coprime r n -> Coprime k n --- the converse, via a's
        // own modular inverse (module doc).
        let mpr = {
            let hr_fv = d.fresh_fvar();
            let hr = d.kernel().fvar(hr_fv);

            let ex_a = d.lemma(p.mod_eq_inverse_exists, &[n, a, h_pos, h_cop_a]);
            // ex_a : Exists (fun a' => ModEq n (a*a') one).

            let outer_pred = {
                let ap_fv = d.fresh_fvar();
                let ap = d.kernel().fvar(ap_fv);
                let aap = d.imul(a, ap);
                let body = imodeq(d, n, aap, one_i);
                d.lam_fv(ap_fv, int_ty, body)
            };
            let outer_minor = {
                let ap_fv = d.fresh_fvar();
                let ap = d.kernel().fvar(ap_fv);
                let aap = d.imul(a, ap);
                let haap_ty = imodeq(d, n, aap, one_i);
                let haap_fv = d.fresh_fvar();
                let haap = d.kernel().fvar(haap_fv);

                // h_apa : ModEq n (a'*a) one -- commute a*a' to a'*a.
                let apa = d.imul(ap, a);
                let comm_eq = d.const_app(p.mul_comm, &[a, ap]); // a*a' = a'*a
                let h_apa =
                    d.int_eq_rewrite(aap, apa, comm_eq, haap, &|d, t| imodeq(d, n, t, one_i));

                // Coprime a' n -- the same Bezout extraction `euler_unit_coprime`
                // itself uses, applied at a's inverse.
                let cop_ap = coprime_of_modeq_inverse(d, n, ap, a, h_pos, h_apa);

                // Coprime (emod (a'*r) n) n -- Int.euler_unit_coprime at (a', r).
                let apr_goal = d.lemma(p.euler_unit_coprime, &[n, ap, r, h_pos, cop_ap, hr]);

                // a'*r ~[n] a'*(a*k):  emod_modeq_self + mod_eq_mul_left.
                let em = emod_modeq_self(d, ak, n, h_pos); // ModEq n ak r
                let em_symm = d.lemma(p.mod_eq_symm, &[n, ak, r, em]); // ModEq n r ak
                let step_a = d.lemma(p.mod_eq_mul_left, &[n, r, ak, ap, h_pos, em_symm]);
                // step_a : ModEq n (a'*r) (a'*(a*k))

                // a'*(a*k) = (a'*a)*k -- mul_assoc, reversed.
                let apak = d.imul(ap, ak);
                let apa_k = d.imul(apa, k);
                let assoc_eq = d.const_app(p.mul_assoc, &[ap, a, k]); // (a'*a)*k = a'*(a*k)
                let assoc_eq_symm = d.isymm(apa_k, apak, assoc_eq); // a'*(a*k) = (a'*a)*k

                let apr = d.imul(ap, r);
                let step_b = d.int_eq_rewrite(apak, apa_k, assoc_eq_symm, step_a, &|d, t| {
                    imodeq(d, n, apr, t)
                });
                // step_b : ModEq n (a'*r) ((a'*a)*k)

                // (a'*a)*k ~[n] one*k -- h_apa, mod_eq_mul_right.
                let step_c = d.lemma(p.mod_eq_mul_right, &[n, apa, one_i, k, h_pos, h_apa]);
                // step_c : ModEq n ((a'*a)*k) (one*k)

                // one*k = k -- one_mul.
                let one_k = d.imul(one_i, k);
                let one_mul_eq = d.const_app(p.one_mul, &[k]);
                let step_d =
                    d.int_eq_rewrite(one_k, k, one_mul_eq, step_c, &|d, t| imodeq(d, n, apa_k, t));
                // step_d : ModEq n ((a'*a)*k) k

                let h_final = d.lemma(p.mod_eq_trans, &[n, apr, apa_k, k, step_b, step_d]);
                // h_final : ModEq n (a'*r) k, i.e. Eq Int (emod apr n) (emod k n).

                let apr_emod = d.iemod(apr, n);
                let k_emod = d.iemod(k, n);
                let cop_k_emod = d.int_eq_rewrite(apr_emod, k_emod, h_final, apr_goal, &|d, t| {
                    d.const_app(p.coprime, &[t, n])
                });
                // cop_k_emod : Coprime (emod k n) n

                let ek_eq_k = emod_eq_self_of_in_range(d, k, n, h_pos, h_k0, h_klt); // Eq (emod k n) k
                let cop_k_final = d.int_eq_rewrite(k_emod, k, ek_eq_k, cop_k_emod, &|d, t| {
                    d.const_app(p.coprime, &[t, n])
                });
                // cop_k_final : Coprime k n

                let with_haap = d.lam_fv(haap_fv, haap_ty, cop_k_final);
                d.lam_fv(ap_fv, int_ty, with_haap)
            };
            let elim = int_exists_elim(d, outer_pred, cop_k_ty, ex_a, outer_minor);
            d.lam_fv(hr_fv, cop_r_ty, elim)
        };

        let proof_body = d.const_app(p.logic.iff_intro, &[cop_k_ty, cop_r_ty, mp, mpr]);

        let with_cop_a = d.lam_fv(h_cop_a_fv, cop_a_ty, proof_body);
        let with_klt = d.lam_fv(h_klt_fv, klt_ty, with_cop_a);
        let with_k0 = d.lam_fv(h_k0_fv, k0_ty, with_klt);
        let proof = d.lam_fv(h_pos_fv, pos_ty, with_k0);
        (stmt, proof)
    })?;
    Ok(())
}
