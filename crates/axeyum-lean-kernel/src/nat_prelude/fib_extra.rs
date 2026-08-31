//! Three more `Nat.fib` `ml430` mirrors: `fib_one`, `fib_two` and
//! `fib_lt_fib_succ`. A NEW module rather than an addition to `fibonacci.rs`
//! (already a dense 1,600-line file owning `fib`'s definition, its recurrence
//! and its whole monotonicity ladder), following the precedent
//! `size_extra.rs` set for `Nat.size`.
//!
//! # Why these three are honest mirrors
//!
//! Mathlib's `Nat.fib` at the pinned commit
//! `c5ea00351c28e24afc9f0f84379aa41082b1188f`
//! (`Mathlib/Data/Nat/Fib/Basic.lean:57`) is
//!
//! ```text
//! def fib (n : ℕ) : ℕ := ((fun p : ℕ × ℕ => (p.snd, p.fst + p.snd))^[n] (0, 1)).fst
//! ```
//!
//! — an ACCUMULATOR-PAIR iteration seeded at `(0, 1)`, chosen (its own doc
//! comment says so) for performance "when compared to the naive recursive
//! implementation". Ours is `Nat.fib n := fibAux n 0 1` with
//! `fibAux (succ i) a b ≡ fibAux i b (add a b)`: the SAME accumulator
//! iteration from the SAME seed, curried across two argument slots because
//! this kernel has no tuple type. Same function, same algorithm, different
//! representation of the pair.
//!
//! That matters for the mirror-flip criterion, and it corrects ADR-0840's
//! point 4, which asserted Mathlib's `fib` is a "two-step `Nat.rec`/
//! well-founded recurrence" — it is not; that ADR cited only OUR module doc
//! for that half, where its other three points cite the pinned source. The
//! divergence-registry screen agrees: `Nat.fib` is not a registered
//! divergence, only `Nat.fastFib` (whose `binaryRec` chain genuinely is).
//!
//! `fib_zero`, `fib_one` and `fib_two` are proved `rfl` in Mathlib
//! (`Basic.lean:61-69`), so they are definitional on Mathlib's side exactly as
//! they are here — the Stirling precedent verbatim.
//!
//! # The proofs
//!
//! * `fib_one : fib 1 = 1` — `fib 1 ≡ fibAux 1 0 1 ≡ fibAux 0 1 (add 0 1) ≡
//!   add 0 1 ≡ 1`, pure `δ`/`ι`. `Eq.refl`.
//! * `fib_two : fib 2 = 1` — `fib 2 ≡ fibAux 2 0 1 ≡ fibAux 1 1 (add 0 1) ≡
//!   fibAux 0 (add 0 1) (add 1 (add 0 1)) ≡ add 0 1 ≡ 1`. Also `Eq.refl`.
//!   Note `Nat.add` recurses on its RIGHT argument, so `add 0 1` reduces
//!   (`succ (add 0 0) ≡ succ 0`) while a symbolic left operand would not
//!   matter here: both operands are literals.
//! * `fib_lt_fib_succ : ∀ n, Le 2 n → Lt (fib n) (fib (succ n))` — one
//!   application of the already-proved [`NatPrelude::fib_lt_fib`]
//!   (`2 ≤ m → (fib m < fib n ↔ m < n)`) at `(n, succ n)`, whose reverse
//!   direction consumes [`NatPrelude::lt_succ_self`]. No induction.
//!
//! Magnitudes formed here are `0`, `1` and `2`, so the unary-numeral cost
//! this prelude pays elsewhere is irrelevant.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;

/// `Nat.fib_one : Eq (fib 1) 1` — `refl`, per the module doc.
pub(super) fn declare_fib_one(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.fib_one, 0, &|d, _v| {
        let one = d.num(1);
        let lhs = d.const_app(p.fib, &[one]);
        (d.eq(lhs, one), d.refl(one))
    })?;
    Ok(())
}

/// `Nat.fib_two : Eq (fib 2) 1` — `refl`, per the module doc.
pub(super) fn declare_fib_two(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.fib_two, 0, &|d, _v| {
        let one = d.num(1);
        let two = d.num(2);
        let lhs = d.const_app(p.fib, &[two]);
        (d.eq(lhs, one), d.refl(one))
    })?;
    Ok(())
}

/// `Nat.fib_lt_fib_succ : ∀ n, Le 2 n → Lt (fib n) (fib (succ n))`.
pub(super) fn declare_fib_lt_fib_succ(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.fib_lt_fib_succ, 1, &|d, v| {
        let n = v[0];
        let two = d.num(2);
        let hyp_ty = d.le(two, n);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);

        let sn = d.succ(n);
        // `fib_lt_fib n (succ n) hyp : Iff (Lt (fib n) (fib (succ n))) (Lt n (succ n))`
        let iff_proof = d.lemma(p.fib_lt_fib, &[n, sn, hyp]);
        let fib_n = d.const_app(p.fib, &[n]);
        let fib_sn = d.const_app(p.fib, &[sn]);
        let lhs_ty = d.lt(fib_n, fib_sn);
        let rhs_ty = d.lt(n, sn);
        let lt_n_sn = d.lemma(p.lt_succ_self, &[n]);
        let result = d.lemma(p.logic.iff_mpr, &[lhs_ty, rhs_ty, iff_proof, lt_n_sn]);

        let stmt = d.arrow(hyp_ty, lhs_ty);
        let body = d.lam_fv(hyp_fv, hyp_ty, result);
        (stmt, body)
    })?;
    Ok(())
}

/// Declare every theorem in this module.
pub(super) fn declare_fib_extra_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_fib_one(d, p)?;
    declare_fib_two(d, p)?;
    declare_fib_lt_fib_succ(d, p)?;
    Ok(())
}
