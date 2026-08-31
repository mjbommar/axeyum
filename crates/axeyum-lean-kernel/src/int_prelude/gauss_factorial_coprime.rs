//! Gauss's-lemma connecting theorem, item 2 (ADR-1070): `gcd(m!, pp) = 1`,
//! needed to cancel `m!` from `a^m · m! ≡ (-1)^gaussNegCount · m! [pp]` in
//! the final assembly.
//!
//! Two theorems:
//!
//! - [`declare_factorial_eq_of_nat_factorial`]: `Int.factorial m = ofNat
//!   (Nat.factorial m)` — `Int.factorial` (`wilson.rs`, `prodRange` over
//!   `fun k => ofNat (succ k)`) and `Nat.factorial` (`nat_prelude`,
//!   independently declared over `Nat.mul`) are two different constructions
//!   of the same function; this bridges them by induction so the rest of
//!   this file (and item 3's cancellation step) can reason about `Nat`
//!   divisibility/coprimality rather than re-deriving it over `Int`. The
//!   base case is `Int.factorial zero ≡ one ≡ ofNat 1 ≡ ofNat (Nat.factorial
//!   zero)`, all by defeq (`Int.one := ofNat 1`, both `factorial_zero`
//!   equations close by `Eq.refl` per their own doc comments) chained with
//!   `Nat.factorial_zero`'s content via [`IntDev::nat_eq_to_int`]. The
//!   successor step chains `Int.factorial_succ`'s defeq unfold with a
//!   congruence through the induction hypothesis and `Int.mul (ofNat _)
//!   (ofNat _) ≡ ofNat (Nat.mul _ _)` (itself defeq — `Int.mul`'s case
//!   split dispatches on the outer `Int` constructor only, so this holds for
//!   symbolic `Nat` arguments, not just literals) plus `Nat.factorial_succ`'s
//!   content.
//! - [`declare_coprime_factorial_of_lt_prime`][]: `Int.Coprime (factorial m)
//!   (ofNat pp)`, from `Nat.PrimeCond pp` and `Lt m pp` — the `Int`-typed
//!   form item 3's `Int.ModEq.cancel` needs, obtained from
//!   `nat_prelude::gauss_lemma`'s `Nat.coprime_factorial_of_lt_prime`, purely
//!   by defeq: `Int.Coprime (factorial m) (ofNat pp)` unfolds to `Eq Nat (gcd
//!   (natAbs (factorial m)) (natAbs (ofNat pp))) one`, `natAbs (ofNat pp) ≡
//!   pp` unconditionally (ι-reduction), and `natAbs (factorial m) ≡ natAbs
//!   (ofNat (Nat.factorial m)) ≡ Nat.factorial m` via the bridge lemma above
//!   composed with the same ι-reduction — so the Nat-side theorem's
//!   conclusion `Eq Nat (gcd pp (Nat.factorial m)) one` (after `gcd_comm`)
//!   IS this theorem's conclusion up to defeq, no further proof content
//!   needed.

use super::ops::IntDev;
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `Int.factorial m = ofNat (Nat.factorial m)`, by induction on `m`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_factorial_eq_of_nat_factorial(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let fact_int_x = d.const_app(p.factorial, &[x]);
        let fact_nat_x = NatOps::factorial(d, x);
        let of_nat_x = d.of_nat(fact_nat_x);
        d.ieq(fact_int_x, of_nat_x)
    };

    d.theorem(p.factorial_eq_of_nat_factorial, 1, &|d, v| {
        let m = v[0];
        let stmt_at_m = motive(d, m);

        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let one_nat = d.num(1);
                let fact_nat_zero = NatOps::factorial(d, zero);
                // Eq Nat (factorial zero) one_nat.
                let h0 = d.const_app(p.nat.factorial_zero, &[]);
                let h0_rev = d.symm(fact_nat_zero, one_nat, h0);
                // Eq Int (ofNat one_nat) (ofNat fact_nat_zero) -- and
                // `Int.factorial zero` is defeq `ofNat one_nat` (via
                // `Int.one := ofNat 1` and `factorial_zero`'s own `Eq.refl`
                // unfold), so this checks against the stated motive(zero).
                d.nat_eq_to_int(one_nat, fact_nat_zero, h0_rev, &|d, x| d.of_nat(x))
            },
            &|d, j, ih| {
                let sj = d.succ(j);
                let fact_j_int = d.const_app(p.factorial, &[j]);
                let fact_j_nat = NatOps::factorial(d, j);
                let sj_int = d.of_nat(sj);
                let of_nat_fact_j = d.of_nat(fact_j_nat);

                // step1 : Eq Int (mul fact_j_int sj_int) (mul of_nat_fact_j sj_int)
                let lhs1 = d.imul(fact_j_int, sj_int);
                let rhs1 = d.imul(of_nat_fact_j, sj_int);
                let step1 = d.icongr(fact_j_int, of_nat_fact_j, ih, &|d, t| d.imul(t, sj_int));

                // rhs1 = mul (ofNat fact_j_nat) (ofNat sj) is defeq
                // `ofNat (mul fact_j_nat sj)` (Int.mul's ofNat/ofNat case,
                // symbolic arguments included) -- no proof step needed for
                // that half.
                let mul_fact_j_sj = d.mul(fact_j_nat, sj);
                let fact_succ_nat = NatOps::factorial(d, sj);
                // Eq Nat (factorial sj) (mul fact_j_nat sj) -- Nat.factorial_succ.
                let h_succ = d.lemma(p.nat.factorial_succ, &[j]);
                let h_succ_rev = d.symm(fact_succ_nat, mul_fact_j_sj, h_succ);
                let step3 = d.nat_eq_to_int(mul_fact_j_sj, fact_succ_nat, h_succ_rev, &|d, x| {
                    d.of_nat(x)
                });

                let of_nat_fact_succ = d.of_nat(fact_succ_nat);
                // itrans bridges rhs1 (mul of_nat_fact_j sj_int) against
                // step3's LHS (ofNat mul_fact_j_sj) by defeq.
                d.itrans(lhs1, rhs1, of_nat_fact_succ, step1, step3)
            },
            m,
        );

        (stmt_at_m, proof)
    })?;
    Ok(())
}

/// `Int.Coprime (factorial m) (ofNat pp)`, from `Nat.PrimeCond pp` and `Lt m
/// pp` -- combines [`declare_factorial_eq_of_nat_factorial`] with
/// [`Nat.coprime_factorial_of_lt_prime`](super::gauss_lemma) purely by
/// defeq (`Int.Coprime`/`Int.gcd`/`Int.natAbs` all unfold transparently on
/// an `ofNat`-headed argument), after one `Nat.gcd_comm` to match
/// `coprime_factorial_of_lt_prime`'s `gcd pp (factorial m)` order to
/// `Int.Coprime`'s `gcd (natAbs _) (natAbs _) = 1` order (magnitude of the
/// factorial first, magnitude of `pp` second).
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_coprime_factorial_of_lt_prime(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.theorem(p.coprime_factorial_of_lt_prime, 2, &|d, v| {
        let (pp, m) = (v[0], v[1]);
        let prime_ty = super::wilson::prime_condition(d, pp);
        let bound_ty = d.lt(m, pp);

        let big_pp = d.of_nat(pp);
        let fact_int_m = d.const_app(p.factorial, &[m]);
        let coprime_ty = d.const_app(p.coprime, &[fact_int_m, big_pp]);

        let stmt = {
            let inner = d.arrow(bound_ty, coprime_ty);
            d.arrow(prime_ty, inner)
        };

        let prime_fv = d.fresh_fvar();
        let prime_proof = d.kernel().fvar(prime_fv);
        let bound_fv = d.fresh_fvar();
        let bound_proof = d.kernel().fvar(bound_fv);

        // Nat.coprime_factorial_of_lt_prime pp m : PrimeCond pp -> Lt m pp
        // -> Eq Nat (gcd pp (factorial m)) one.
        let nat_pf = d.lemma(p.nat.coprime_factorial_of_lt_prime, &[pp, m]);
        let nat_pf = d.apply(nat_pf, &[prime_proof, bound_proof]);
        // Eq Nat (gcd pp (factorial m)) one.

        // Flip to Eq Nat (gcd (factorial m) pp) one via gcd_comm, matching
        // Int.Coprime's `gcd (natAbs a) (natAbs b) = 1` argument order.
        let fact_nat_m = NatOps::factorial(d, m);
        let gcd_pp_fm = d.gcd(pp, fact_nat_m);
        let gcd_fm_pp = d.gcd(fact_nat_m, pp);
        let comm = d.lemma(p.nat.gcd_comm, &[pp, fact_nat_m]); // Eq (gcd pp fm) (gcd fm pp)
        let one_nat = d.num(1);
        let comm_rev = d.symm(gcd_pp_fm, gcd_fm_pp, comm); // Eq (gcd fm pp) (gcd pp fm)
        let flipped = d.trans(gcd_fm_pp, gcd_pp_fm, one_nat, comm_rev, nat_pf);
        // flipped : Eq Nat (gcd fact_nat_m pp) one.
        //
        // This is defeq the stated `coprime_ty`'s unfold: `Int.Coprime
        // fact_int_m big_pp` -> `Eq Nat (gcd (natAbs fact_int_m) (natAbs
        // big_pp)) one`, and `natAbs big_pp ≡ pp` (ι, ofNat branch) while
        // `natAbs fact_int_m ≡ fact_nat_m` needs `fact_int_m ≡ ofNat
        // fact_nat_m` -- NOT free by defeq (a real theorem,
        // `factorial_eq_of_nat_factorial`), so this proof term must route
        // through it explicitly rather than relying on the kernel's own
        // defeq check.
        let bridge = d.lemma(p.factorial_eq_of_nat_factorial, &[m]); // Eq Int fact_int_m (ofNat fact_nat_m)
        let of_nat_fm = d.of_nat(fact_nat_m);
        let motive = |d: &mut IntDev<'_>, x: ExprId| {
            let na = d.const_app(p.nat_abs, &[x]);
            let nb = d.const_app(p.nat_abs, &[big_pp]);
            let g = d.gcd(na, nb);
            d.eq(g, one_nat)
        };
        // Rewrite `flipped` (stated at `natAbs (ofNat fact_nat_m) ≡
        // fact_nat_m`, defeq) along `bridge` reversed, to move from
        // `ofNat fact_nat_m` back to `fact_int_m`.
        let bridge_rev = d.isymm(fact_int_m, of_nat_fm, bridge);
        let result = d.int_eq_rewrite(of_nat_fm, fact_int_m, bridge_rev, flipped, &motive);

        let with_bound = d.lam_fv(bound_fv, bound_ty, result);
        let proof = d.lam_fv(prime_fv, prime_ty, with_bound);
        (stmt, proof)
    })?;
    Ok(())
}
