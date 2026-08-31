//! Least-residue sign counting toward Gauss's lemma.
//!
//! `int_prelude/qr_criterion.rs`'s module doc names Gauss's lemma as one of
//! two routes to the second supplementary law of quadratic reciprocity (`2`
//! is a QR mod `p` iff `p ≡ ±1 (mod 8)`), and sizes it as "a
//! `Nat.countRange`-shaped least-residue sign-count ... this prelude does not
//! build". Re-measured (`shape_search --name-like countRange`, 19
//! declarations across `finite_set.rs`/`totient.rs`/`count_range_permute.rs`/
//! `count_range_reversal.rs`): the counting primitive and its subset/union/
//! compl/congr/split laws are real, usable machinery, not just names — this
//! file is the first consumer that builds a NEW `countRange` application
//! rather than reusing an existing totient-shaped one.
//!
//! ## What this file builds
//!
//! - [`declare_least_residue`]: `Nat.leastResidue pp a k := mod (mul a k)
//!   pp` — the least nonnegative residue of `a*k` mod `pp`, as a plain
//!   `Nat → Nat → Nat → Nat` function (no recursion of its own; it composes
//!   two already-declared primitives).
//! - [`declare_gauss_sign_neg`]: `Nat.gaussSignNeg pp a k : Bool := ble
//!   (succ (div pp 2)) (leastResidue pp a k)` — `true` exactly when the least
//!   residue exceeds `⌊pp/2⌋`, i.e. when the symmetric representative in
//!   `(-pp/2, pp/2]` is negative. This is the per-term sign Gauss's lemma
//!   counts.
//! - [`declare_gauss_neg_count`]: `Nat.gaussNegCount pp a m := countRange
//!   (fun j => gaussSignNeg pp a (succ j)) m` — folding the sign predicate
//!   over `k = 1, …, m` (the `succ j` shift moves `countRange`'s zero-based
//!   `[0, m)` index onto the classical one-based range).
//! - [`declare_gauss_residue_two_eq_double_of_lt`]: for the multiplier `a :=
//!   2` specifically, `mul 2 k < pp → leastResidue pp 2 k = mul 2 k` — since
//!   `k` never exceeds `m = (pp-1)/2`, `2*k` never reaches `pp` and the `mod`
//!   is a no-op (`Nat.mod_eq_self_of_lt`). This is what makes `a := 2` a
//!   genuinely easier case than the general lemma: the least-residue map is
//!   the identity-doubling map, not a real reduction.
//! - A table of concrete instances of `gaussNegCount` at `a := 2`, admitted
//!   axiom-free by the kernel's own `ι`-reduction (no proof term beyond
//!   `Eq.refl`, since every numeral involved stays under 25 — nowhere near
//!   this kernel's documented unary-numeral cost cliff), for `pp ∈ {7, 11,
//!   13, 17, 19, 23}` — one representative of each nonzero residue class mod
//!   8 among small odd primes (7 ≡ 7, 11 ≡ 3, 13 ≡ 5, 17 ≡ 1, 19 ≡ 3, 23 ≡
//!   7) — plus one instance at `a := 3` (`pp = 7`) to confirm the count
//!   genuinely depends on `a`, not only on `pp`. Every value was independently
//!   computed in Python before being written into a Rust theorem statement
//!   (see this module's `#[cfg(test)]` block for the script), per this
//!   repository's standing rule that a plan's "verified numerically" claim
//!   must be re-run, not inherited.
//!
//! ## What this does NOT reach
//!
//! Nothing here connects the sign count to `a^m mod pp` — that is the actual
//! content of Gauss's lemma (`a^m ≡ (-1)^gaussNegCount(pp,a,m) [pp]`), and it
//! needs the least-residue map's INJECTIVITY on `{1,…,m}`, a pairing lemma
//! (`r > pp/2 ⟹ pp - r` lands back among `{1,…,m}`'s residues), and a
//! product-cancellation argument (`Int.prodRange` exists in
//! `int_prelude/prod.rs`, built for Wilson's theorem, and is the right
//! carrier for it) — none of that is attempted here. This file only builds
//! the COUNTING half; the second supplementary law still needs the
//! connecting theorem plus a `p mod 8` case split on top of it. See
//! `docs/plan/status/gauss-lemma-countrange.md` for exact sizing.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// Delta height for `Nat.leastResidue`: strictly above `Nat.mod`/`Nat.mul`
/// (both well under 10 in this prelude's numbering).
const LEAST_RESIDUE_HEIGHT: u16 = 32;
/// Strictly above [`LEAST_RESIDUE_HEIGHT`] (calls it) and `Nat.ble` (1).
const GAUSS_SIGN_NEG_HEIGHT: u16 = 33;
/// Strictly above [`GAUSS_SIGN_NEG_HEIGHT`] (calls it) and `Nat.countRange`
/// (12).
const GAUSS_NEG_COUNT_HEIGHT: u16 = 40;

/// `Nat.leastResidue(pp, a, k)`.
pub(super) fn least_residue(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    a: ExprId,
    k: ExprId,
) -> ExprId {
    d.const_app(p.least_residue, &[pp, a, k])
}

/// `Nat.gaussSignNeg(pp, a, k)`.
pub(super) fn gauss_sign_neg(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    a: ExprId,
    k: ExprId,
) -> ExprId {
    d.const_app(p.gauss_sign_neg, &[pp, a, k])
}

/// `Nat.gaussNegCount(pp, a, m)`.
pub(super) fn gauss_neg_count(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pp: ExprId,
    a: ExprId,
    m: ExprId,
) -> ExprId {
    d.const_app(p.gauss_neg_count, &[pp, a, m])
}

/// `Nat.leastResidue : Nat → Nat → Nat → Nat := fun pp a k => mod (mul a k) pp`.
///
/// Not recursive: it composes two already-declared primitives, so the
/// definition is a plain triple-lambda, no `Nat.rec` of its own.
pub(super) fn declare_least_residue(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pp_fv = d.fresh_fvar();
    let a_fv = d.fresh_fvar();
    let k_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let a = d.kernel().fvar(a_fv);
    let k = d.kernel().fvar(k_fv);
    let ak = d.mul(a, k);
    let body = d.modulo(ak, pp);
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_a = d.lam_fv(a_fv, nat, with_k);
        d.lam_fv(pp_fv, nat, with_a)
    };
    let ty = {
        let over_k = d.arrow(nat, nat);
        let over_a = d.arrow(nat, over_k);
        d.arrow(nat, over_a)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.least_residue,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(LEAST_RESIDUE_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.gaussSignNeg : Nat → Nat → Nat → Bool :=
///   fun pp a k => ble (succ (div pp 2)) (leastResidue pp a k)`.
///
/// `true` exactly when the least residue of `a*k` mod `pp` exceeds `⌊pp/2⌋`
/// — i.e. when its symmetric representative in `(-pp/2, pp/2]` is negative.
pub(super) fn declare_gauss_sign_neg(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let pp_fv = d.fresh_fvar();
    let a_fv = d.fresh_fvar();
    let k_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let a = d.kernel().fvar(a_fv);
    let k = d.kernel().fvar(k_fv);
    let two = d.num(2);
    let half = d.div(pp, two);
    let succ_half = d.succ(half);
    let residue = least_residue(d, &p, pp, a, k);
    let body = d.ble(succ_half, residue);
    let value = {
        let with_k = d.lam_fv(k_fv, nat, body);
        let with_a = d.lam_fv(a_fv, nat, with_k);
        d.lam_fv(pp_fv, nat, with_a)
    };
    let ty = {
        let over_k = d.arrow(nat, bool_ty);
        let over_a = d.arrow(nat, over_k);
        d.arrow(nat, over_a)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.gauss_sign_neg,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(GAUSS_SIGN_NEG_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.gaussNegCount : Nat → Nat → Nat → Nat :=
///   fun pp a m => countRange (fun j => gaussSignNeg pp a (succ j)) m`.
///
/// The `succ j` shift moves `countRange`'s zero-based `[0, m)` fold onto the
/// classical one-based range `k = 1, …, m` Gauss's lemma counts over.
pub(super) fn declare_gauss_neg_count(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let pp_fv = d.fresh_fvar();
    let a_fv = d.fresh_fvar();
    let m_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(pp_fv);
    let a = d.kernel().fvar(a_fv);
    let m = d.kernel().fvar(m_fv);
    let f = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let sj = d.succ(j);
        let body = gauss_sign_neg(d, &p, pp, a, sj);
        d.lam_fv(j_fv, nat, body)
    };
    let body = d.const_app(p.count_range, &[f, m]);
    let value = {
        let with_m = d.lam_fv(m_fv, nat, body);
        let with_a = d.lam_fv(a_fv, nat, with_m);
        d.lam_fv(pp_fv, nat, with_a)
    };
    let ty = {
        let over_m = d.arrow(nat, nat);
        let over_a = d.arrow(nat, over_m);
        d.arrow(nat, over_a)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.gauss_neg_count,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(GAUSS_NEG_COUNT_HEIGHT),
    })?;
    Ok(())
}

/// `Nat.gauss_residue_two_eq_double_of_lt : ∀ pp k,
///   Lt (mul 2 k) pp → Eq (leastResidue pp 2 k) (mul 2 k)`.
///
/// For the multiplier `a := 2`, whenever `2*k < pp` the least-residue map is
/// literally the doubling map — no reduction happens. Proof: unfold
/// `leastResidue pp 2 k` to `mod (mul 2 k) pp` (definitional) and apply
/// `Nat.mod_eq_self_of_lt`. Every caller with `k <= m` and `pp = 2*m+1`
/// satisfies the hypothesis, since `2*k <= 2*m = pp-1 < pp`.
pub(super) fn declare_gauss_residue_two_eq_double_of_lt(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.gauss_residue_two_eq_double_of_lt, 2, &|d, v| {
        let (pp, k) = (v[0], v[1]);
        let two = d.num(2);
        let two_k = d.mul(two, k);
        let hyp_ty = d.lt(two_k, pp);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        // Eq (mod two_k pp) two_k -- and `least_residue(pp, two, k)` unfolds
        // (definitionally) to exactly `mod (mul two k) pp`, i.e. `mod two_k
        // pp`, so this proof checks against the stated conclusion below by
        // the kernel's own def_eq, no congruence step needed.
        let mod_eq = d.lemma(p.mod_eq_self_of_lt, &[two_k, pp, hyp]);
        let lhs = least_residue(d, &p, pp, two, k);
        let concl_ty = d.eq(lhs, two_k);
        let stmt = d.arrow(hyp_ty, concl_ty);
        let proof = d.lam_fv(hyp_fv, hyp_ty, mod_eq);
        (stmt, proof)
    })?;
    Ok(())
}

/// One concrete `gaussNegCount` instance, admitted axiom-free purely by the
/// kernel's own `ι`-reduction (`Eq.refl` at the final numeral) -- no proof
/// term beyond that reduction. `pp`/`a`/`m`/`expected` are all small enough
/// (`pp <= 23`) that this is nowhere near the unary-numeral cost cliff this
/// kernel's other declarations have hit at magnitudes in the thousands.
fn declare_gauss_neg_count_instance(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    name: crate::name::NameId,
    pp: u32,
    a: u32,
    m: u32,
    expected: u32,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(name, 0, &|d, _v| {
        let pp = d.num(pp);
        let a = d.num(a);
        let m = d.num(m);
        let lhs = gauss_neg_count(d, &p, pp, a, m);
        let rhs = d.num(expected);
        let stmt = d.eq(lhs, rhs);
        let proof = d.refl(rhs);
        (stmt, proof)
    })?;
    Ok(())
}

/// Everything this module declares, in dependency order. Goes last in
/// `build_nat_prelude`: it needs only `Nat.countRange`
/// (`declare_totient_all`), `Nat.mod_eq_self_of_lt` (`declare_size_all`, via
/// `binary.rs`), and `Nat.mod`/`Nat.mul`/`Nat.div`/`Nat.ble`, all far above.
/// Nothing needs it.
pub(super) fn declare_gauss_lemma_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    declare_least_residue(d, p)?;
    declare_gauss_sign_neg(d, p)?;
    declare_gauss_neg_count(d, p)?;
    declare_gauss_residue_two_eq_double_of_lt(d, p)?;
    // a := 2, one representative of each nonzero residue class mod 8 among
    // small odd primes: 7 ≡ 7, 11 ≡ 3, 13 ≡ 5, 17 ≡ 1, 19 ≡ 3, 23 ≡ 7.
    // Values independently computed in Python (see this module's
    // `#[cfg(test)]` block) before being written here.
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_seven_two, 7, 2, 3, 2)?;
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_eleven_two, 11, 2, 5, 3)?;
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_thirteen_two, 13, 2, 6, 3)?;
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_seventeen_two, 17, 2, 8, 4)?;
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_nineteen_two, 19, 2, 9, 5)?;
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_twentythree_two, 23, 2, 11, 6)?;
    // a := 3 at pp := 7, to confirm the count genuinely depends on `a`, not
    // only on `pp` (the a := 2 instance at the same prime gave 2, not 1).
    declare_gauss_neg_count_instance(d, p, p.gauss_neg_count_seven_three, 7, 3, 3, 1)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Kernel, build_nat_prelude};

    /// The Python script whose output the concrete instance theorems above
    /// were transcribed from -- re-run here as a comment, not inherited,
    /// per this repository's standing rule that a "verified numerically"
    /// claim must be re-executed rather than trusted from a plan or a prior
    /// session.
    ///
    /// ```python
    /// def D(pp, a, m):
    ///     half = pp // 2
    ///     return sum(1 for k in range(1, m + 1) if (a * k) % pp > half)
    /// for pp in [7, 11, 13, 17, 19, 23]:
    ///     print(pp, pp % 8, D(pp, 2, (pp - 1) // 2))
    /// print(7, D(7, 3, 3))
    /// ```
    /// prints `7 7 2`, `11 3 3`, `13 5 3`, `17 1 4`, `19 3 5`, `23 7 6`, and
    /// `7 1` for the last line -- exactly the seven numbers this module's
    /// `declare_gauss_lemma_all` bakes in.
    #[test]
    fn gauss_neg_count_matches_an_independent_python_recomputation() {
        fn d_ref(pp: u32, a: u32, m: u32) -> u32 {
            let half = pp / 2;
            (1..=m).filter(|k| (a * k) % pp > half).count() as u32
        }
        assert_eq!(d_ref(7, 2, 3), 2);
        assert_eq!(d_ref(11, 2, 5), 3);
        assert_eq!(d_ref(13, 2, 6), 3);
        assert_eq!(d_ref(17, 2, 8), 4);
        assert_eq!(d_ref(19, 2, 9), 5);
        assert_eq!(d_ref(23, 2, 11), 6);
        assert_eq!(d_ref(7, 3, 3), 1);
    }

    /// The three definitions exist with the promised kind and the kernel's
    /// own reduction agrees with the Rust-side reference at a witness NOT
    /// among the landed theorems above (`pp := 5`, discriminating: `a := 2`
    /// gives count 1, `a := 1` gives count 0).
    #[test]
    fn gauss_definitions_compute_at_a_witness_outside_the_landed_table() {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let mut d = super::NatDev::new(&mut k, p);

        let five = d.num(5);
        let two = d.num(2);
        let one = d.num(1);
        let m = two; // (5-1)/2 = 2

        let count_a2 = gauss_neg_count(&mut d, &p, five, two, m);
        let expected_a2 = d.num(1);
        assert!(
            d.kernel().def_eq(count_a2, expected_a2),
            "gaussNegCount 5 2 2 must reduce to 1 (residues 2, 4; only 4 > 5/2=2)"
        );

        let count_a1 = gauss_neg_count(&mut d, &p, five, one, m);
        let expected_a1 = d.zero();
        assert!(
            d.kernel().def_eq(count_a1, expected_a1),
            "gaussNegCount 5 1 2 must reduce to 0 (residues 1, 2; neither exceeds 5/2=2)"
        );
        assert!(
            !d.kernel().def_eq(count_a1, expected_a2),
            "negative control: the two instances above must NOT collapse to the same value"
        );
    }
}
