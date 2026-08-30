//! `Nat.fermatNumber`: opens `Mathlib.NumberTheory.Fermat` (pinned commit
//! `c5ea0035…`, 13 rows) for the autogenesis screen —
//! `docs/research/09-decisions/adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md`.
//!
//! Mathlib (`Mathlib/NumberTheory/Fermat.lean`, read at the pinned commit):
//!
//! ```text
//! def fermatNumber (n : ℕ) : ℕ := 2 ^ (2 ^ n) + 1
//! ```
//!
//! This is exactly that definition over our own `Nat.pow`/`Nat.add` — the
//! SAME construction, not merely one that agrees with it pointwise (contrast
//! `Nat.minFac`/`Nat.nth`, whose module docs explain why those mirrors must
//! stay open) — so an `ml430` mirror flip against any `Nat.fermatNumber*`
//! fact is honest under the mirror-flip criterion in `CLAUDE.md`.
//!
//! **Declares the definition ONLY, per
//! `docs/research/09-decisions/adr-0653-…`: a lane sent to unblock a held-out
//! family declares the CONSTRUCTION and nothing else.** Every mirror-named
//! theorem proved alongside is one row subtracted from the blind population
//! the family is meant to supply, and the R9 screen refuses the whole family
//! if any lands in the first ten (alphabetically) of the pool. No
//! `Nat.fermatNumber_*` theorem is declared here; those are ordinary proof
//! work for whichever future lane draws them as facts.
//!
//! `Nat.pow` recurses on its **second** argument (the exponent) — see
//! `defs.rs::declare_arithmetic`, `pow x zero ≡ 1`, `pow x (succ j) ≡ mul (pow
//! x j) x` — so `pow 2 n` for a symbolic `n` does not reduce and this
//! definition does not attempt to. It is not itself recursive: it is a
//! constant, non-recursive function of `n` built from two calls to the
//! already-recursive `Nat.pow` and one to `Nat.add`.
//!
//! Concrete magnitudes are the hazard here, not recursion depth: every
//! numeral in this prelude is a unary `succ`-tower, and `fermatNumber` grows
//! DOUBLY exponentially in `n`. `fermat_number_evaluates_correctly`
//! (`nat_prelude_tests.rs`) stops at `n = 2` (value `17`, formed magnitude
//! `2^4 = 16`) deliberately — `n = 3` already forms `256`, and `n = 4` would
//! form `65536`, which prior measurements in this repository put well past a
//! single declaration's reasonable budget (`CLAUDE.md`'s "EVERY `Nat` NUMERAL
//! THIS PRELUDE BUILDS IS UNARY" entry: `gcd 512 1875` alone cost 25.6s).

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;

/// `Nat.fermatNumber n := add (pow 2 (pow 2 n)) 1`.
///
/// Delta height `4`: strictly greater than `Nat.pow`'s `3` (`defs.rs`), the
/// higher of its two dependencies (`Nat.add` is `1`).
pub(super) fn declare_fermat_number_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let two = d.num(2);
    let one = d.num(1);
    let inner_pow = d.pow(two, n); // 2 ^ n
    let outer_pow = d.pow(two, inner_pow); // 2 ^ (2 ^ n)
    let body = d.add(outer_pow, one); // 2 ^ (2 ^ n) + 1
    let value = d.lam_fv(n_fv, nat, body);
    let ty = d.arrow(nat, nat);

    d.kernel().add_declaration(Declaration::Definition {
        name: p.fermat_number,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(4),
    })?;

    Ok(())
}
