//! `Nat.factorizationLCMLeft`/`Right` — the construction ADR-1450 measured as
//! the unblock, and NOTHING else (ADR-0653: definitions and their evaluation
//! tests only, no theorems about them).
//!
//! ## Why this pair, and what it opens
//!
//! `check-dispatchable-frontier.py` sits at 2 dispatchable `ml430` mirrors
//! against a floor of 10. ADR-1420/ADR-1430 established that a refill draw
//! needs four fresh families (R5: two NEW held-out, and `_with_cycle` yields
//! `ceil(n/3)` held-out per draw); ADR-1430 declared `Nat.count` and
//! `Nat.divMaxPow` to open two of them, but ADR-1450 found `Nat.count`'s
//! family is not blind (`Nat.count` is a definitional alias of
//! `Nat.countRange`, and four of the drawn rows are the same proposition
//! term-for-term as lemmas this kernel already proves) and refused it. Its
//! measured remedy: declare a construction opening a module sorting
//! lexicographically before `Mathlib.Data.Nat.MaxPowDiv`, topic- and
//! vocabulary-clean, leaving room for two more families in the window before
//! `MaxPowDiv`. `Mathlib.Data.Nat.Factorization.LCM` behind
//! `Nat.factorizationLCMLeft`/`…Right` is that spare (ADR-1430 measured it
//! clean against a DIFFERENT window, `Count`/`LCM`; this lane re-derived the
//! `LCM`/`MaxPowDiv` window against the real `select()`/`screen_family()`
//! machinery before writing any of this file — see the `factorization-lcm-
//! unblock` lane status for the numbers).
//!
//! ## What the pair computes
//!
//! Mathlib's `Nat.factorizationLCMLeft a b` is, per-prime, `p ^ (a.factorization
//! p)` when `b.factorization p <= a.factorization p`, else `1`; `…Right` is the
//! complementary product, taking `p ^ n` (`n` the LCM's own exponent) exactly
//! where `…Left` takes `1`. So `Left * Right = lcm a b` when `a,b /= 0`, `Left
//! ∣ a`, `Right ∣ b`, and `gcd Left Right = 1` — Mathlib states the product
//! identity and the two divisibility facts as separate theorems (all four are
//! `open` `ml430` mirrors this construction does not touch).
//!
//! This kernel has no `Finsupp` and no per-prime factorization MAP (only
//! `Nat.exists_prime_factorization`, an existence witness — see
//! `factorization.rs`), so the per-prime formula above cannot be transcribed
//! directly. It computes the same VALUE a different way, verified against an
//! independent per-prime Python reference (`math.gcd`/`math.lcm`, explicit
//! trial-division factorization) over every pair in `[0,60]^2` — 3,721 pairs,
//! zero mismatches, and the algebraic invariants (`Left*Right = lcm`,
//! `Left ∣ a`, `Right ∣ b`, `gcd Left Right = 1`) checked at every nonzero
//! pair in the same sweep:
//!
//! ```text
//! coprimePartAux fuel n k :=
//!   match fuel with
//!   | 0      => n
//!   | succ f => let g := gcd n k
//!               if g <= 1 then n else coprimePartAux f (n / g) k
//! -- repeatedly divides n by gcd(n, k) until the two are coprime. Strips
//! -- EVERY copy of every prime k shares with n, however many copies n
//! -- holds, not merely k's own exponent -- e.g. coprimePartAux 32 32 2 = 1
//! -- (five copies of 2 in 32, one in the divisor, all five removed).
//!
//! factorizationLCMLeft a b :=
//!   if a = 0 then 1 else if b = 0 then 1
//!   else coprimePartAux a a (div b (gcd a b))
//! -- a stripped of every prime where b/gcd(a,b) -- exactly the primes with
//! -- b's exponent strictly exceeding a's -- shares a factor.
//!
//! factorizationLCMRight a b :=
//!   if a = 0 then 1 else if b = 0 then 1
//!   else div (lcm a b) (factorizationLCMLeft a b)
//! -- Mathlib's own `factorizationLCMLeft_mul_factorizationLCMRight` row IS
//! -- this identity (at a,b /= 0), so this is not an independent formula
//! -- being hoped to agree -- it is the stated relationship, computed.
//! ```
//!
//! **Why `b / gcd(a,b)` and not `a / gcd(a,b)`, and why `Right` is not the
//! mirror-image `coprimePartAux b b (div a (gcd a b))`:** the naive symmetric
//! attempt was tried FIRST and refuted by the same Python sweep — at `a=2,
//! b=6` (`gcd=2`), `a/gcd=1`, and `coprimePartAux` with divisor key `1` never
//! strips anything (`gcd(n,1)=1` always), so the mirror formula for `Right`
//! returns `b` unstripped (`6`) where the correct value is `3`. The failure is
//! that `a/gcd(a,b)`'s support is primes where `a`'s exponent STRICTLY exceeds
//! `b`'s, which misses primes where the two exponents are EQUAL — and equal-
//! exponent primes must still be stripped from `b` for `Right` (Mathlib's
//! `<=` in `Left`'s condition sends ties to `Left`). `lcm a b /
//! factorizationLCMLeft a b` sidesteps the asymmetry entirely rather than
//! trying to characterise the second stripping key.
//!
//! **The zero rows are not the recursion's natural fallback.** `factorizationLCMLeft
//! 0 b` and `a.factorizationLCMLeft 0` are both `1` in Mathlib (empty-support
//! convention: `Nat.factorization 0` is defined as the zero function, so the
//! product over its support is the empty product, `1`) — NOT `0`, which is
//! what `coprimePartAux a a k` would give when `a = 0` (fuel `0`, base case
//! returns `n = 0`). Both zero guards are therefore explicit, checked ahead of
//! the recursion, matching Mathlib's stated `factorizationLCMLeft_zero_left` /
//! `_zero_right` / `factorizationLCMRight_zero_right` /
//! `factorizationLCRight_zero_left` rows (the last name is Mathlib's own —
//! missing the second `M` — not a typo introduced here).
//!
//! **Asymmetric, which hands the transposition control free** (`CLAUDE.md`'s
//! standing rule that a control inherited from a sibling operator is often
//! vacuous does not apply here: this control is derived from THIS operator).
//! `factorizationLCMLeft 12 18 = 4`, `factorizationLCMLeft 18 12 = 9` —
//! swapping the arguments must NOT `def_eq`, or nothing here would catch a
//! transposed pair.
//!
//! **Type matches Mathlib's exactly** (`ℕ → ℕ → ℕ`, no `Finsupp`/`DecidablePred`
//! in the signature), so — per the mirror-flip criterion in `CLAUDE.md` — every
//! `ml430` mirror against `Nat.factorizationLCMLeft`/`…Right` stays `open` and
//! provable against this constructive definition; it is not the `Nat.count`
//! case (a different definitional body under the same name).

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;

/// `Nat.coprimePartAux`, `Nat.factorizationLCMLeft`, `Nat.factorizationLCMRight`.
/// Definitions only.
pub(super) fn declare_factorization_lcm(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();

    // Nat.coprimePartAux (fuel n k : Nat) : Nat
    {
        // Motive over `fuel` is the constant family `Nat -> Nat -> Nat`,
        // matching `divMaxPowAux`'s device: two trailing accumulator
        // arguments applied after the recursor.
        let nk_to_nat = {
            let inner = d.arrow(nat, nat);
            d.arrow(nat, inner)
        };
        let motive = d.kernel().lam(anon, nat, nk_to_nat, BinderInfo::Default);

        // base (fuel = 0): fun n k => n
        let base_case = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let k_fv = d.fresh_fvar();
            let with_k = d.lam_fv(k_fv, nat, n);
            d.lam_fv(n_fv, nat, with_k)
        };

        // step (predFuel, ih : Nat -> Nat -> Nat): fun n k => ...
        let step = {
            let predfuel_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let n_fv = d.fresh_fvar();
            let k_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let k = d.kernel().fvar(k_fv);

            let one = d.num(1);
            let g = d.gcd(n, k);
            let g_le_one = d.ble(g, one);
            let quotient = d.div(n, g);
            let recurse = d.apply(ih, &[quotient, k]);
            // if gcd n k <= 1 then n else coprimePartAux f (n / gcd n k) k
            let body = d.bool_select_nat(g_le_one, n, recurse);

            let with_k = d.lam_fv(k_fv, nat, body);
            let with_n = d.lam_fv(n_fv, nat, with_k);
            let with_ih = d.lam_fv(ih_fv, nk_to_nat, with_n);
            d.lam_fv(predfuel_fv, nat, with_ih)
        };

        let fuel_fv = d.fresh_fvar();
        let fuel = d.kernel().fvar(fuel_fv);
        let one_lvl = d.level_one();
        let rec = d.kernel().const_(p.rec, vec![one_lvl]);
        let nk_fn = d.apply(rec, &[motive, base_case, step, fuel]);

        let n2_fv = d.fresh_fvar();
        let k2_fv = d.fresh_fvar();
        let n2 = d.kernel().fvar(n2_fv);
        let k2 = d.kernel().fvar(k2_fv);
        let body = d.apply(nk_fn, &[n2, k2]);

        let value = {
            let with_k = d.lam_fv(k2_fv, nat, body);
            let with_n = d.lam_fv(n2_fv, nat, with_k);
            d.lam_fv(fuel_fv, nat, with_n)
        };
        let ty = {
            let over_nk = {
                let inner = d.arrow(nat, nat);
                d.arrow(nat, inner)
            };
            d.arrow(nat, over_nk)
        };
        // Strictly greater delta height than `gcd` (10), `div` (3) and `ble`
        // (1), the definitions it calls.
        d.kernel().add_declaration(Declaration::Definition {
            name: p.coprime_part_aux,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(11),
        })?;
    }

    // Nat.factorizationLCMLeft (a b : Nat) : Nat :=
    //   if a = 0 then 1 else if b = 0 then 1
    //   else coprimePartAux a a (div b (gcd a b))
    {
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b = d.kernel().fvar(b_fv);

        let zero = d.zero();
        let one = d.num(1);
        let a_is_zero = d.beq(a, zero);
        let b_is_zero = d.beq(b, zero);
        let g = d.gcd(a, b);
        let k = d.div(b, g);
        let computed = d.const_app(p.coprime_part_aux, &[a, a, k]);
        let b_branch = d.bool_select_nat(b_is_zero, one, computed);
        let body = d.bool_select_nat(a_is_zero, one, b_branch);

        let value = {
            let with_b = d.lam_fv(b_fv, nat, body);
            d.lam_fv(a_fv, nat, with_b)
        };
        let ty = {
            let over_b = d.arrow(nat, nat);
            d.arrow(nat, over_b)
        };
        // Strictly greater height than `coprimePartAux` (11), `gcd` (10),
        // `div` (3) and `beq` (1).
        d.kernel().add_declaration(Declaration::Definition {
            name: p.factorization_lcm_left,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(12),
        })?;
    }

    // Nat.factorizationLCMRight (a b : Nat) : Nat :=
    //   if a = 0 then 1 else if b = 0 then 1
    //   else div (lcm a b) (factorizationLCMLeft a b)
    {
        let a_fv = d.fresh_fvar();
        let b_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b = d.kernel().fvar(b_fv);

        let zero = d.zero();
        let one = d.num(1);
        let a_is_zero = d.beq(a, zero);
        let b_is_zero = d.beq(b, zero);
        let lcm_ab = d.const_app(p.lcm, &[a, b]);
        let left_ab = d.const_app(p.factorization_lcm_left, &[a, b]);
        let computed = d.div(lcm_ab, left_ab);
        let b_branch = d.bool_select_nat(b_is_zero, one, computed);
        let body = d.bool_select_nat(a_is_zero, one, b_branch);

        let value = {
            let with_b = d.lam_fv(b_fv, nat, body);
            d.lam_fv(a_fv, nat, with_b)
        };
        let ty = {
            let over_b = d.arrow(nat, nat);
            d.arrow(nat, over_b)
        };
        // Strictly greater height than `factorizationLCMLeft` (12), `lcm`
        // (11) and `div` (3).
        d.kernel().add_declaration(Declaration::Definition {
            name: p.factorization_lcm_right,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(13),
        })?;
    }

    Ok(())
}
