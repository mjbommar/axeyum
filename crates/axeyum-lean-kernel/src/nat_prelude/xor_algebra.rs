//! `Nat.eq_of_testBit_eq` — the general "same bits imply the same number"
//! extensionality lemma, built toward piece 4 of the 4 pieces
//! `docs/plan/status/260-nat-lt-xor-cases.md` named as blocking
//! `F:ml430-nat-lt-xor-cases-c43a1e85` (`Nat.xor_assoc`,
//! `Nat.xor_xor_cancel_left`/`_right`, `Nat.xor_ne_zero_iff`). See
//! `docs/plan/status/263-nat-testbit-xor.md` for piece 1 (`Nat.testBit_xor`,
//! landed) and `docs/plan/status/264-nat-xor-algebra.md` for this lane's
//! handoff, including why the three `xor` algebra targets themselves are
//! NOT landed in this file (time-boxed out; the remaining shape is
//! documented there, not sketched here as unverified code).
//!
//! # The intended route: `testBit_xor` + extensionality, not fuel induction
//!
//! `docs/plan/status/260-…`'s own land_assoc-transport warning is moot for
//! this route: `xor_assoc`/`xor_xor_cancel_left`/`xor_ne_zero_iff` do not
//! need any zero-propagation lemma at all if built THIS way. `Nat.testBit_xor`
//! (piece 1) reduces a statement about `xor` VALUES to a statement about
//! individual BITS, where `xor_bit` is a two-`Bool`-valued combine,
//! exhaustively case-splittable (`Bool.rec`, at most 2-3 levels deep — see
//! the handoff doc for the truth-table sizing). Once every bit of two
//! `xor`-built values is shown to agree, THIS file's
//! [`declare_eq_of_test_bit_eq`] — "same bits imply the same number" — turns
//! that back into a value-level equation. Neither `land_assoc`'s
//! zero-propagation lemma nor any fuel-level case analysis on `bitwiseAux`
//! is needed for any of the three targets, on this route.
//!
//! # `Nat.eq_of_testBit_eq` --- the extensionality lemma (LANDED)
//!
//! ```text
//! Nat.eq_of_testBit_eq : ∀ m n, (∀ i, Eq (testBit m i) (testBit n i)) → Eq m n
//! ```
//!
//! Not previously in this prelude: `binary.rs`'s `Nat.zero_of_testBit_eq_zero`
//! is the ONE-SIDED case ("all bits zero ⟹ the number is zero"), not the
//! general two-value form. Proved by an induction on a FUEL `k` bounding `m`
//! (the same "generalize over an outer bound, induct on the fuel" device
//! `rec_agreement.rs`'s fuel-irrelevance lemmas and `testbit_bitwise.rs`'s
//! own bridge use), with motive
//!
//! ```text
//! P(k) := ∀ n, ∀ m, Le m k → (∀ i, testBit m i = testBit n i) → Eq m n
//! ```
//!
//! - **Base** (`k = 0`): `Le m 0` forces `m = 0` (`le_antisymm` against
//!   `zero_le`); the bit hypothesis at `m := 0` then forces every bit of `n`
//!   to be `0` too (via `test_bit_of_zero` and `zero_of_test_bit_eq_zero`),
//!   so `n = 0 = m`. This same derivation --- [`zero_forces_eq`] --- closes
//!   BOTH the outer base case and the inner `m = 0` sub-case of the step
//!   below, parameterized over a proof `Eq x 0` rather than over `x` being
//!   literally the numeral `0`.
//! - **Step** (`k = succ pk`): case-splits on `m` (`cases_zero_succ`), folding
//!   the `Le`/bit hypotheses into the PER-CASE motive rather than
//!   pre-introducing them (`cases_zero_succ`'s own documented device for a
//!   hypothesis a caller wants specialized per branch). At `m = succ pm`:
//!   the bit-0 hypothesis gives `mod (succ pm) 2 = mod n 2` (`testBit _ 0` is
//!   `refl`-defeq to `mod _ 2`); the bit-`(succ j)` hypotheses, for every
//!   `j`, give `∀ j, testBit (half (succ pm)) j = testBit (half n) j`
//!   (`testBit _ (succ j)` is `refl`-defeq to `testBit (_ / 2) j`), which is
//!   exactly the IH's hypothesis at `(half (succ pm), half n)`, bounded via
//!   `half_le_predecessor_of_succ` (`rec_agreement.rs`). The IH gives
//!   `half (succ pm) = half n`; combined with the bit-0 equation and the
//!   `n = 2*(n/2) + n%2` reconstruction (`div_mod_exec`/`and_left`, the same
//!   identity `testbit_bitwise.rs`'s `div_two_mul_add_of_lt` is built from
//!   the OTHER half of) on both sides, this gives `succ pm = n`.
//!
//! Instantiating the fuel bound at `k := m` itself (`le_refl`) turns
//! `P(m)` directly into the public two-argument statement.
//!
//! # What this file does NOT reach (documented, not sketched)
//!
//! None of `Nat.xor_assoc`, `Nat.xor_xor_cancel_left`/`_right`,
//! `Nat.xor_ne_zero_iff` are declared in this file — see
//! `docs/plan/status/264-nat-xor-algebra.md` for the exact remaining shape
//! of each, including the `xor_bit` Boolean-algebra lemmas
//! (`xor_bit`'s value depends on its arguments ONLY through whether each
//! equals `1`, so associativity/self-cancellation hold for ALL `x, y, z :
//! Nat`, not merely bits in `{0, 1}`, via a `Bool.rec` case split at most
//! 2-3 levels deep) that would combine with [`declare_eq_of_test_bit_eq`]
//! and `Nat.testBit_xor` to close them.
//!
//! # Codomain / mirror check
//!
//! No `ml430` fact for any of `xor_assoc`/`xor_xor_cancel_left`/
//! `xor_ne_zero_iff` was found in the ledger (`artifacts/facts/` has no
//! `F-ml430-nat-xor-*` file). `Nat.xor`, `Nat.testBit`, `Le`, `Eq` all match
//! Mathlib's codomains for these specific statements (no `Bool`-valued
//! `testBit` involved, unlike the six sibling mirrors the `testBit`
//! codomain mismatch blocked), so whichever of them land will be new local
//! facts (`F:nat-xor-assoc`, `F:nat-xor-xor-cancel-left`, …), not `ml430`
//! mirrors of anything pre-registered. `Nat.eq_of_testBit_eq` ITSELF has no
//! `ml430` mirror either (no such general extensionality statement appears
//! in `Mathlib/Data/Nat/Bitwise.lean` at the pinned commit under this or a
//! related name) and is registered as its own new local fact.

use super::NatPrelude;
use super::helpers::and_left;
use super::ops::{NatDev, NatOps, cases_zero_succ};
use super::rec_agreement::half_le_predecessor_of_succ;
use crate::KernelError;
use crate::expr::ExprId;

// ============================================================================
// `Nat.eq_of_testBit_eq` -- same bits imply the same number.
// ============================================================================

/// `Eq x zero ⊢ (∀ i, Eq (testBit x i) (testBit n i)) → Eq x n`. Shared by
/// the outer base case (`x := m`, `hx0` from `le_antisymm`) and the step
/// case's `m = 0` sub-case (`x := zero` literally, `hx0 := refl`).
///
/// Proof: `hx0` transports the bit hypothesis to `∀ i, testBit zero i =
/// testBit n i`; `test_bit_of_zero` gives `testBit zero i = 0`, so every bit
/// of `n` is `0`, and `zero_of_test_bit_eq_zero` closes `n = 0`; `x = 0 = n`
/// by `trans`.
fn zero_forces_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    x: ExprId,
    n: ExprId,
    hx0: ExprId,
    bits_hyp: ExprId,
) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let zero = d.zero();

    let n_bits_zero = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let tb_x_i = d.const_app(p.test_bit, &[x, i]);
        let tb_n_i = d.const_app(p.test_bit, &[n, i]);
        let h_i = d.apply(bits_hyp, &[i]); // Eq tb_x_i tb_n_i
        let tb_zero_i = d.const_app(p.test_bit, &[zero, i]);
        let congr_x0 = d.congr(x, zero, hx0, &|d, y| {
            let ii = i;
            d.const_app(p.test_bit, &[y, ii])
        });
        let tb0_eq_zero = d.lemma(p.test_bit_of_zero, &[i]);
        let tb_x_eq_zero = d.trans(tb_x_i, tb_zero_i, zero, congr_x0, tb0_eq_zero);
        let tb_n_eq_tbx = d.symm(tb_x_i, tb_n_i, h_i);
        let tb_n_eq_zero = d.trans(tb_n_i, tb_x_i, zero, tb_n_eq_tbx, tb_x_eq_zero);
        d.lam_fv(i_fv, nat, tb_n_eq_zero)
    };
    let n_eq_zero = d.lemma(p.zero_of_test_bit_eq_zero, &[n, n_bits_zero]);
    let zero_eq_n = d.symm(n, zero, n_eq_zero);
    d.trans(x, zero, n, hx0, zero_eq_n)
}

/// `Eq x (add (mul two (div x two)) (mod x two))` for any `x` --- the
/// Euclidean reconstruction identity, the equation half of
/// `div_mod_exec`'s `And`. `and_left` on the same `divMod` witness
/// `testbit_bitwise.rs`'s `div_two_mul_add_of_lt` takes its bound half from.
fn reconstruct_div_mod(d: &mut NatDev<'_>, p: &NatPrelude, x: ExprId) -> ExprId {
    let p = *p;
    let one = d.num(1);
    let two = d.num(2);
    let dx = d.div(x, two);
    let rx = d.modulo(x, two);
    let two_dx = d.mul(two, dx);
    let sum = d.add(two_dx, rx);
    let eq_ty = d.eq(x, sum);
    let bound_ty = d.lt(rx, two);
    let h_exec = d.lemma(p.div_mod_exec, &[one, x]);
    and_left(d, eq_ty, bound_ty, h_exec)
}

/// `Nat.eq_of_testBit_eq : ∀ n, ∀ m, (∀ i, Eq (testBit m i) (testBit n i))
/// → Eq m n` --- see the module doc for the fuel induction shape. (Argument
/// order `n` then `m` to keep the induction's own motive, built with `n`
/// captured before the `m`-split, syntactically simple; the PUBLIC-facing
/// order in the theorem's own binders is `m` then `n`, matching every other
/// use site in this file, wired at the very end.)
fn declare_eq_of_test_bit_eq(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let bits_ty_at = |d: &mut NatDev<'_>, mm: ExprId, n: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let tb_m = d.const_app(p.test_bit, &[mm, i]);
        let tb_n = d.const_app(p.test_bit, &[n, i]);
        let body = d.eq(tb_m, tb_n);
        d.pi_fv(i_fv, nat, body)
    };

    // motive(k) := ∀ n, ∀ m, Le m k → bits(m, n) → Eq m n
    let motive = |d: &mut NatDev<'_>, k: ExprId| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let le_ty = d.le(m, k);
        let bt = bits_ty_at(d, m, n);
        let eqmn = d.eq(m, n);
        let arrow_bt = d.arrow(bt, eqmn);
        let inner = d.arrow(le_ty, arrow_bt);
        let over_m = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(n_fv, nat, over_m)
    };

    let base = |d: &mut NatDev<'_>| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let zero = d.zero();
        let le_ty = d.le(m, zero);
        let le_fv = d.fresh_fvar();
        let le_hyp = d.kernel().fvar(le_fv);
        let bt = bits_ty_at(d, m, n);
        let bits_fv = d.fresh_fvar();
        let bits_hyp = d.kernel().fvar(bits_fv);

        let zero_le_m = d.lemma(p.zero_le, &[m]);
        let m_eq_zero = d.lemma(p.le_antisymm, &[m, zero, le_hyp, zero_le_m]);
        let eq_final = zero_forces_eq(d, &p, m, n, m_eq_zero, bits_hyp);

        let with_bits = d.lam_fv(bits_fv, bt, eq_final);
        let with_le = d.lam_fv(le_fv, le_ty, with_bits);
        let with_m = d.lam_fv(m_fv, nat, with_le);
        d.lam_fv(n_fv, nat, with_m)
    };

    let step = |d: &mut NatDev<'_>, pk: ExprId, ih: ExprId| -> ExprId {
        // ih : ∀ n, ∀ m, Le m pk → bits(m, n) → Eq m n
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let succ_pk = d.succ(pk);

        let motive_m = |d: &mut NatDev<'_>, mm: ExprId| -> ExprId {
            let le_ty = d.le(mm, succ_pk);
            let bt = bits_ty_at(d, mm, n);
            let eqmn = d.eq(mm, n);
            let arrow_bt = d.arrow(bt, eqmn);
            d.arrow(le_ty, arrow_bt)
        };

        let at_zero = |d: &mut NatDev<'_>| -> ExprId {
            let zero = d.zero();
            let le_ty0 = d.le(zero, succ_pk);
            let le_fv = d.fresh_fvar();
            let _le_hyp = d.kernel().fvar(le_fv);
            let bt0 = bits_ty_at(d, zero, n);
            let bits_fv = d.fresh_fvar();
            let bits_hyp = d.kernel().fvar(bits_fv);
            let hx0 = d.refl(zero);
            let eq_final = zero_forces_eq(d, &p, zero, n, hx0, bits_hyp);
            let wb = d.lam_fv(bits_fv, bt0, eq_final);
            d.lam_fv(le_fv, le_ty0, wb)
        };

        let at_succ = |d: &mut NatDev<'_>, pm: ExprId| -> ExprId {
            let m_succ = d.succ(pm);
            let le_ty_s = d.le(m_succ, succ_pk);
            let le_fv = d.fresh_fvar();
            let le_hyp = d.kernel().fvar(le_fv);
            let bt_s = bits_ty_at(d, m_succ, n);
            let bits_fv = d.fresh_fvar();
            let bits_hyp = d.kernel().fvar(bits_fv);

            let two = d.num(2);
            let half_m = d.div(m_succ, two);
            let half_n = d.div(n, two);

            let half_bits = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let succ_j = d.succ(j);
                let h = d.apply(bits_hyp, &[succ_j]);
                let nat_ty = d.nat_ty();
                d.lam_fv(j_fv, nat_ty, h)
            };

            let half_le_pk = half_le_predecessor_of_succ(d, &p, pm, pk, le_hyp);

            let ih_at = d.apply(ih, &[half_n]);
            let ih_at = d.apply(ih_at, &[half_m]);
            let ih_at = d.apply(ih_at, &[half_le_pk]);
            let half_eq = d.apply(ih_at, &[half_bits]);

            let zero_i = d.zero();
            let low_bit_eq = d.apply(bits_hyp, &[zero_i]);

            let m_mod = d.modulo(m_succ, two);
            let n_mod = d.modulo(n, two);
            let two_half_m = d.mul(two, half_m);
            let two_half_n = d.mul(two, half_n);
            let mid_m = d.add(two_half_m, m_mod);
            let mid_shared = d.add(two_half_n, m_mod);
            let mid_n = d.add(two_half_n, n_mod);

            let step1 = d.congr(half_m, half_n, half_eq, &|d, x| {
                let two = d.num(2);
                let t = d.mul(two, x);
                let mm = m_mod;
                d.add(t, mm)
            });
            let step2 = d.congr(m_mod, n_mod, low_bit_eq, &|d, x| {
                let hn = half_n;
                let two = d.num(2);
                let t = d.mul(two, hn);
                d.add(t, x)
            });
            let combined = d.trans(mid_m, mid_shared, mid_n, step1, step2);

            let recon_m = reconstruct_div_mod(d, &p, m_succ);
            let recon_n = reconstruct_div_mod(d, &p, n);
            let recon_n_symm = d.symm(n, mid_n, recon_n);
            let (_, eq_final) = d.chain(
                m_succ,
                &[(mid_m, recon_m), (mid_n, combined), (n, recon_n_symm)],
            );

            let wb = d.lam_fv(bits_fv, bt_s, eq_final);
            d.lam_fv(le_fv, le_ty_s, wb)
        };

        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let case_proof = cases_zero_succ(d, m, &motive_m, &at_zero, &at_succ);
        let with_m = d.lam_fv(m_fv, nat, case_proof);
        d.lam_fv(n_fv, nat, with_m)
    };

    // Public theorem, order (m, n): instantiate the fuel at k := m via
    // le_refl, then apply at (n' := n, m' := m).
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let bits_fv = d.fresh_fvar();
    let bits_hyp = d.kernel().fvar(bits_fv);

    let proof_fn = d.induct(&motive, &base, &step, m);
    let le_refl_m = d.lemma(p.le_refl, &[m]);
    let inst = d.apply(proof_fn, &[n]);
    let inst = d.apply(inst, &[m]);
    let inst = d.apply(inst, &[le_refl_m]);
    let final_proof = d.apply(inst, &[bits_hyp]);

    let bits_ty_outer = bits_ty_at(d, m, n);
    let eqmn = d.eq(m, n);
    let value = {
        let wb = d.lam_fv(bits_fv, bits_ty_outer, final_proof);
        let wn = d.lam_fv(n_fv, nat, wb);
        d.lam_fv(m_fv, nat, wn)
    };
    let ty = {
        let arrow1 = d.arrow(bits_ty_outer, eqmn);
        let over_n = d.pi_fv(n_fv, nat, arrow1);
        d.pi_fv(m_fv, nat, over_n)
    };
    d.declare_theorem(p.eq_of_test_bit_eq, ty, value)
}

/// Everything this module declares. See the module doc for what's NOT
/// declared here (`Nat.xor_assoc` and siblings).
pub(super) fn declare_xor_algebra_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_eq_of_test_bit_eq(d, p)?;
    Ok(())
}
