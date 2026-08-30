//! `Nat.even_div` (lane `parity-finish`, 2026-08-30):
//! `∀ m n, Iff (Even (div m n)) (Eq (div (mod m (mul 2 n)) n) 0)` --
//! `F:ml430-nat-even-div-395c6b5e`.
//!
//! ## Why this is short, contrary to the handoff
//!
//! The prior lane (`nat-parity-div`) sized this as needing a NEW
//! `Nat.div_mod_scale`-shaped identity built from `div_mod_exec`/
//! `div_mod_unique` at divisor `2*n`, after checking `division.rs`/
//! `div_mod_lemmas.rs`/`mod_mul_lemmas.rs`. `mod_mul_lemmas.rs`'s
//! `Nat.mod_mul_right_div_self : ∀ m n k, Eq (div (mod m (mul n k)) n) (mod
//! (div m n) k)` -- UNCONDITIONAL, no positivity hypothesis on `n` or `k` --
//! is EXACTLY this identity at `k := 2`: `m % (n*2) / n = (m/n) % 2`. That
//! turns the whole statement into `Even q ↔ q % 2 = 0` for `q := m/n`,
//! which is `Nat.even_iff_mod_two_eq_zero(q)` verbatim, after bridging
//! `n*2`/`2*n` by `Nat.mul_comm` and transporting the `Iff` along the
//! resulting `Eq` via `Eq.rec` directly (`NatOps::transport`/`eq_motive`,
//! used here as a general-purpose `Iff`-congruence tool rather than for
//! arithmetic rewriting, which is what makes this short -- no new
//! arithmetic lemma, no case split on `n`, no fuel-style bespoke
//! `div_mod_scale` construction).

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;

/// `Nat.even_div : ∀ m n, Iff (Even (div m n)) (Eq (div (mod m (mul 2 n)) n)
/// 0)` -- `F:ml430-nat-even-div-395c6b5e`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_even_div(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.even_div, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let q = d.div(m, n);
        let two = d.num(2);
        let zero = d.zero();

        let two_n = d.mul(two, n);
        let mod_2n = d.modulo(m, two_n);
        let div_mod_2n_n = d.div(mod_2n, n);
        let rhs_ty = d.eq(div_mod_2n_n, zero);
        let even_q_ty = d.lemma(p.even, &[q]);
        let stmt = d.const_app(p.logic.iff, &[even_q_ty, rhs_ty]);

        // Iff (Even q) (Eq (mod q 2) 0), the shape we will transport.
        let base_iff = d.lemma(p.even_iff_mod_two_eq_zero, &[q]);
        let mod_q_2 = d.modulo(q, two);

        // mod_mul_right_div_self(m, n, 2) : Eq (div (mod m (mul n 2)) n)
        // (mod (div m n) 2) = Eq (div (mod m (mul n 2)) n) mod_q_2.
        let n_two = d.mul(n, two);
        let mod_n_two = d.modulo(m, n_two);
        let div_mod_n_two = d.div(mod_n_two, n);
        let mmr = d.lemma(p.mod_mul_right_div_self, &[m, n, two]);

        // Bridge `mul 2 n` (the fact's own order) to `mul n 2` (this
        // lemma's order) via `mul_comm`.
        let comm = d.lemma(p.mul_comm, &[two, n]);
        let congr_mod = d.congr(two_n, n_two, comm, &|d, x| d.modulo(m, x));
        let congr_div = d.congr(mod_2n, mod_n_two, congr_mod, &|d, x| d.div(x, n));

        // div_mod_2n_n = div_mod_n_two = mod_q_2.
        let lhs_eq_modq2 = d.trans(div_mod_2n_n, div_mod_n_two, mod_q_2, congr_div, mmr);
        let rev = d.symm(div_mod_2n_n, mod_q_2, lhs_eq_modq2);

        // Transport base_iff : Iff (Even q) (Eq mod_q_2 0) along
        // `rev : Eq mod_q_2 div_mod_2n_n` into
        // Iff (Even q) (Eq div_mod_2n_n 0) -- exactly `stmt`.
        let motive = d.eq_motive(mod_q_2, &|d, x| {
            let eq_x_zero = d.eq(x, zero);
            d.const_app(p.logic.iff, &[even_q_ty, eq_x_zero])
        });
        let proof = d.transport(mod_q_2, motive, base_iff, div_mod_2n_n, rev);
        (stmt, proof)
    })?;
    Ok(())
}
