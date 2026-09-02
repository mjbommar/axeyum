//! **ADR-1260's residue 2: the side condition.** No lattice point sits on the
//! line `p·y = q·x` inside the rectangle Eisenstein's count partitions, which
//! is exactly what makes the two STRICT half-plane predicates
//! `p·(y+1) < q·(x+1)` and `q·(x+1) < p·(y+1)` complementary and so lets
//! `Nat.countRectangle_partition` (`lattice_count.rs`, ADR-1260) be applied at
//! all.
//!
//! ## The hypothesis is coprimality, not primality
//!
//! ADR-1260 sized this as "`p ∣ q·x` with `p ∤ q` and `x < p`, i.e. Euclid's
//! lemma, which this kernel has". It has something better: `Nat.gauss_lemma`
//! (`lcm.rs`), `gcd x y = 1 → x ∣ y*z → x ∣ z` — Euclid with the primality side
//! condition already dropped. So the theorem below asks for `gcd p q = 1` and
//! never mentions `Nat.PrimeCond`.
//!
//! That is strictly more general and it is also what the consumer actually
//! holds: the law's two primes are distinct, and distinct primes are coprime.
//! Demanding `PrimeCond p` here would force every consumer to carry a primality
//! proof through a step that does not use it, and would leave the lemma
//! unusable for the (true) statement at coprime composites.
//!
//! ## Route — four lemmas, no induction and no case split
//!
//! Assume `p·y = q·x`.
//!
//! 1. `q·x = p·y` (`symm`) is a witness for `Nat.dvd p (q*x)`: `dvd a n` is
//!    `∃ k, n = a * k` (`divisibility.rs`), so the witness is `y` itself and
//!    the witness equation is the symmetrised hypothesis verbatim. No
//!    `dvd_mul`-style lemma is needed to introduce it.
//! 2. `Nat.gauss_lemma p q x` turns `gcd p q = 1` and `p ∣ q*x` into `p ∣ x`.
//! 3. `Nat.le_of_dvd p x` turns `1 ≤ x` and `p ∣ x` into `p ≤ x`. **The
//!    positivity hypothesis is load-bearing and is why `0 < x` appears**: at
//!    `x = 0` the statement is false — `p·0 = q·0` — so a version without it
//!    could not be proved and should not be attempted.
//! 4. `Nat.lt_of_lt_of_le x p x` composes `x < p` with `p ≤ x` into `x < x`,
//!    refuted by `Nat.lt_irrefl`.
//!
//! `Lt 0 x` is passed straight into `le_of_dvd`'s `Le 1 n` slot: `Nat.lt a b`
//! is `Nat.le (succ a) b` definitionally and [`NatOps::num`] builds `1` as
//! `succ zero`, so the two are the same term after δ. Nothing transports.
//!
//! ## Which side is which, and why the argument order is pinned
//!
//! The statement is `Not (Eq (mul pp y) (mul q x))` with the bound on **`x`**,
//! the index paired with `q`. That asymmetry is real: `pp·y = q·x` forces
//! `pp ∣ x`, not `pp ∣ y`, so it is `x` that must be kept below `pp`. Reading
//! the two the other way round gives a statement that is FALSE (take
//! `pp = 3`, `q = 5`, `x = 3`, `y = 5`: `3·5 = 5·3` with `y < pp` and
//! `gcd 3 5 = 1`). No evaluation test over true instances can see a
//! consistent transposition of the four binders, so the declared types are
//! pinned character for character in `eisenstein_side_tests.rs`; the false
//! instance above is what the transposition control uses.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// Declares both side-condition theorems. Must run after
/// `Nat.gauss_lemma` (`lcm.rs`), `Nat.le_of_dvd` (`primes.rs`),
/// `Nat.lt_of_lt_of_le`/`Nat.lt_irrefl` and `Nat.dvd` — all far earlier in
/// `build_nat_prelude`.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_eisenstein_side_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_mul_ne_mul_of_coprime_of_lt(d, p)?;
    declare_mul_succ_ne_mul_succ_of_coprime(d, p)?;
    Ok(())
}

/// `Nat.mul_ne_mul_of_coprime_of_lt : ∀ pp q x y, Eq (gcd pp q) 1 → Lt 0 x →
/// Lt x pp → Not (Eq (mul pp y) (mul q x))`. See the module doc.
fn declare_mul_ne_mul_of_coprime_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.mul_ne_mul_of_coprime_of_lt, 4, &|d, v| {
        let (pp, q, x, y) = (v[0], v[1], v[2], v[3]);

        let one = d.num(1);
        let zero = d.zero();
        let g = d.gcd(pp, q);
        let cop_ty = d.eq(g, one);
        let pos_ty = d.lt(zero, x);
        let bound_ty = d.lt(x, pp);

        let ppy = d.mul(pp, y);
        let qx = d.mul(q, x);
        let eq_ty = d.eq(ppy, qx);
        let not_eq_ty = d.const_app(p.logic.not, &[eq_ty]);

        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);
        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        // `q*x = pp*y` — the witness equation `Nat.dvd pp (q*x)` asks for.
        let flipped = d.symm(ppy, qx, heq);

        // `dvd pp (q*x)`, introduced at the witness `y`.
        let dvd_pred = d.dvd_predicate(pp, qx);
        let level_one = d.level_one();
        let intro = d.kernel().const_(p.logic.exists_intro, vec![level_one]);
        let nat = d.nat_ty();
        let dvd_qx = d.apply(intro, &[nat, dvd_pred, y, flipped]);

        // `pp ∣ x`, then `pp ≤ x`, then `x < x`, then `False`.
        let dvd_x = d.lemma(p.gauss_lemma, &[pp, q, x, cop, dvd_qx]);
        let le_px = d.lemma(p.le_of_dvd, &[pp, x, pos, dvd_x]);
        let lt_xx = d.lemma(p.lt_of_lt_of_le, &[x, pp, x, bound, le_px]);
        let irrefl = d.lemma(p.lt_irrefl, &[x]);
        let absurd = d.apply(irrefl, &[lt_xx]);

        let body = d.lam_fv(heq_fv, eq_ty, absurd);
        let body = d.lam_fv(bound_fv, bound_ty, body);
        let body = d.lam_fv(pos_fv, pos_ty, body);
        let proof = d.lam_fv(cop_fv, cop_ty, body);

        let stmt = d.arrow(bound_ty, not_eq_ty);
        let stmt = d.arrow(pos_ty, stmt);
        let stmt = d.arrow(cop_ty, stmt);
        (stmt, proof)
    })?;

    Ok(())
}

/// `Nat.mul_succ_ne_mul_succ_of_coprime : ∀ pp q x y, Eq (gcd pp q) 1 →
/// Lt (succ x) pp → Not (Eq (mul pp (succ y)) (mul q (succ x)))` — the form
/// the rectangle partition consumes, where both lattice coordinates are
/// `1`-based and so `succ`-shaped by construction.
///
/// Instantiating the general lemma at `(pp, q, succ x, succ y)` discharges its
/// `Lt 0 (succ x)` with [`NatOps::zero_lt_succ`]. The consumer never has to
/// produce a positivity proof, which is the whole reason this corollary exists.
fn declare_mul_succ_ne_mul_succ_of_coprime(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.mul_succ_ne_mul_succ_of_coprime, 4, &|d, v| {
        let (pp, q, x, y) = (v[0], v[1], v[2], v[3]);

        let sx = d.succ(x);
        let sy = d.succ(y);

        let one = d.num(1);
        let g = d.gcd(pp, q);
        let cop_ty = d.eq(g, one);
        let bound_ty = d.lt(sx, pp);

        let ppy = d.mul(pp, sy);
        let qx = d.mul(q, sx);
        let eq_ty = d.eq(ppy, qx);
        let not_eq_ty = d.const_app(p.logic.not, &[eq_ty]);

        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);

        let pos: ExprId = d.zero_lt_succ(x);
        let general = d.lemma(
            p.mul_ne_mul_of_coprime_of_lt,
            &[pp, q, sx, sy, cop, pos, bound],
        );

        let body = d.lam_fv(bound_fv, bound_ty, general);
        let proof = d.lam_fv(cop_fv, cop_ty, body);

        let stmt = d.arrow(bound_ty, not_eq_ty);
        let stmt = d.arrow(cop_ty, stmt);
        (stmt, proof)
    })?;

    Ok(())
}
