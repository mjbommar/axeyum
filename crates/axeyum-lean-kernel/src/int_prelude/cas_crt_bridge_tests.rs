//! CAS → kernel bridge: **Chinese Remainder Theorem certificates**, in both
//! directions.
//!
//! `axeyum_cas::ntheory_certify::certify_crt` produces a [`CrtCertificate`] —
//! either a `Solution{solution, modulus}` with `modulus` the **least** common
//! multiple of the input moduli, or an `Inconsistent{left, right}` naming two
//! congruences that already conflict — and `check_crt_certificate` re-derives
//! it inside the CAS. ADR-0601 §2 calls that `cas-internal`. This is the
//! reconstruction route.
//!
//! # Why this family reconstructs in full, and Pratt's headline does not
//!
//! Every numeral in `F:cas-ntheory-crt-certificate`'s six systems is at most
//! `105`. Unary numerals of that size are free here, so unlike the Pratt
//! family (`super::cas_pratt_bridge_tests`, whose ledger headline is
//! `2^89 − 1` and stays out of reach) **every instance the fact claims is
//! reconstructed**, not a reachable subset. ADR-1622 records the cost
//! comparison that chose the two.
//!
//! # What is reconstructed
//!
//! Matching `check_crt_certificate`'s own guards:
//!
//! | kernel theorem | CAS guard |
//! |---|---|
//! | `Check.crt_congruence_<id>_<i>` : `ModEq (ofNat mᵢ) (ofNat x) (ofNat aᵢ)` | R3, every input congruence holds |
//! | `Check.crt_least_modulus_<id>` : `Eq Nat (lcm …) M` | R4, `M` is the LEAST common multiple |
//! | `Check.crt_canonical_<id>` : `Nat.lt x M` | R2, the solution is canonical |
//! | `Check.crt_inconsistent_<id>` : `∀ x, ModEq mₗ x aₗ → ModEq m_r x a_r → False` | R6, the conflict is genuine |
//!
//! R4 is the guard the CAS module's own doc calls out as load-bearing:
//! `residues = [(1,4),(3,6)]` with `modulus = 24` satisfies every congruence
//! and is a common multiple, and only leastness rejects it. The kernel
//! reconstruction keeps that distinction —
//! [`tests::a_merely_common_modulus_is_refused_by_the_kernel`] forges exactly
//! that certificate with this route's guards off and the kernel refuses it.
//!
//! # The inconsistency direction is a derivation, not an evaluation
//!
//! `Check.crt_inconsistent_<id>` is universally quantified over `x : Int`, so
//! no reduction can close it. The proof is
//! `Int.modEq_of_mul_left` (`ModEq (k·g) x a → ModEq g x a`, instantiated at
//! `g = gcd(mₗ, m_r)` and `k = mₗ/g`, which the kernel sees as the same
//! modulus by reduction) applied to each hypothesis, then `modEq_symm` and
//! `modEq_trans` to `ModEq g aₗ a_r`, which unfolds to
//! `emod aₗ g = emod a_r g` and reduces to a false equation between distinct
//! numerals.
//!
//! # What is NOT reconstructed
//!
//! 1. **Not the CRT theorem.** `Int.crt_exists`/`Int.crt_unique` are proved
//!    in `super::crt`; this module does not re-prove them and does not use
//!    them. It reconstructs the CAS certificate's obligations for the six
//!    concrete systems, which is what the fact claims.
//! 2. **Uniqueness of the solution is not among them.** The certificate
//!    asserts `M` is the least common multiple; that every solution is
//!    congruent to `x` modulo `M` is `Int.crt_unique`'s business and is not
//!    connected to these theorems here.
//! 3. **The moduli are not asserted to be the system's.** Each congruence
//!    theorem names its own `mᵢ` and `aᵢ`; that those are the system's is a
//!    property of the translator, checked by evaluation in [`tests`], never by
//!    the trusted gate.

use axeyum_cas::ntheory_certify::{CrtCertificate, certify_crt};

use super::ops::IntDev;
use crate::KernelError;
use crate::expr::ExprId;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

// ---------------------------------------------------------------------------
// Small term helpers — mirrors of `cas_pratt_bridge_tests`'s, kept local per
// this crate's convention for helpers of this size.
// ---------------------------------------------------------------------------

/// `Int.ofNat <unary numeral v>`.
fn inum(d: &mut IntDev<'_>, v: u32) -> ExprId {
    let n = d.num(v);
    d.of_nat(n)
}

/// `Int.ModEq n a b`.
fn modeq(d: &mut IntDev<'_>, n: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let f = d.int().mod_eq;
    d.const_app(f, &[n, a, b])
}

/// `Not (Eq Int (ofNat x) (ofNat y))` for distinct small `x`, `y`.
fn ofnat_ne(d: &mut IntDev<'_>, x: u32, y: u32) -> ExprId {
    assert!(x != y, "ofnat_ne is only for distinct numerals");
    let p = d.int();
    let xv = d.num(x);
    let yv = d.num(y);
    let xi = d.of_nat(xv);
    let yi = d.of_nat(yv);

    let h_ty = d.ieq(xi, yi);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let start = d.refl(xv);
    let moved = d.int_eq_rewrite(xi, yi, h, start, &|d, z| {
        let na = d.const_app(p.nat_abs, &[z]);
        d.eq(xv, na)
    });
    let false_b = d.bool_false();
    let hbeq = d.bool_refl(false_b);
    let body = {
        let f = d.int().nat.ne_of_beq_eq_false;
        d.const_app(f, &[xv, yv, hbeq, moved])
    };
    d.lam_fv(h_fv, h_ty, body)
}

/// `Nat.le a b` at concrete numerals, via `Nat.le_intro a b (b−a) rfl`.
fn concrete_le(d: &mut IntDev<'_>, a: u32, b: u32) -> ExprId {
    assert!(a <= b, "concrete_le is only for a <= b");
    let av = d.num(a);
    let bv = d.num(b);
    let kv = d.num(b - a);
    let refl = d.refl(bv);
    let f = d.int().nat.le_intro;
    d.const_app(f, &[av, bv, kv, refl])
}

/// Greatest common divisor, computed in Rust — the untrusted side. The kernel
/// re-derives what it is used for.
fn gcd_u32(a: u32, b: u32) -> u32 {
    if b == 0 { a } else { gcd_u32(b, a % b) }
}

// ---------------------------------------------------------------------------
// The route.
// ---------------------------------------------------------------------------

/// Which of the ROUTE's own guards run before the kernel is asked.
///
/// All of them are Rust-side conveniences; with every one off, a forged
/// certificate must still be refused by [`crate::Kernel::add_declaration`].
#[derive(Clone, Copy, Debug)]
pub(super) struct RouteGuards {
    /// Run `axeyum_cas`'s own `check_crt_certificate` first.
    pub cas_recheck: bool,
    /// Refuse a `modulus` that is not the least common multiple.
    pub leastness: bool,
    /// Refuse an `Inconsistent` witness whose named pair does not conflict.
    pub conflict: bool,
}

impl RouteGuards {
    /// Every guard on — the shipping configuration.
    pub(super) fn all() -> Self {
        Self {
            cas_recheck: true,
            leastness: true,
            conflict: true,
        }
    }

    /// Every guard off — the kernel is the only thing left to refuse.
    pub(super) fn none() -> Self {
        Self {
            cas_recheck: false,
            leastness: false,
            conflict: false,
        }
    }
}

/// `Nat.lcm` folded left over the moduli, starting at `1` (so the empty system
/// gives `1`, matching the CAS producer's own convention).
fn lcm_fold(d: &mut IntDev<'_>, moduli: &[u32]) -> ExprId {
    let lcm_name = d.int().nat.lcm;
    let mut acc = d.num(1);
    for &m in moduli {
        let mv = d.num(m);
        acc = d.const_app(lcm_name, &[acc, mv]);
    }
    acc
}

/// Reconstruct one CRT certificate into kernel theorems, returning the names
/// admitted.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` means the **kernel** refused
/// the certificate's arithmetic.
///
/// # Panics
///
/// Panics when a switched-on [`RouteGuards`] guard rejects the certificate —
/// deliberately distinguishable from the kernel refusing.
pub(super) fn reconstruct(
    d: &mut IntDev<'_>,
    id: &str,
    residues: &[(u32, u32)],
    cert: &CrtCertificate,
    guards: RouteGuards,
) -> Result<Vec<NameId>, KernelError> {
    if guards.cas_recheck {
        let wide: Vec<(i128, i128)> = residues
            .iter()
            .map(|&(a, m)| (i128::from(a), i128::from(m)))
            .collect();
        assert!(
            axeyum_cas::ntheory_certify::check_crt_certificate(&wide, cert),
            "route guard: the CAS's own checker rejects this certificate for {id}"
        );
    }
    match *cert {
        CrtCertificate::Solution { solution, modulus } => {
            let x = u32::try_from(solution).expect("a reachable solution fits in u32");
            let m = u32::try_from(modulus).expect("a reachable modulus fits in u32");
            reconstruct_solution(d, id, residues, x, m, guards)
        }
        CrtCertificate::Inconsistent { left, right } => {
            reconstruct_inconsistent(d, id, residues, left, right, guards)
        }
    }
}

fn reconstruct_solution(
    d: &mut IntDev<'_>,
    id: &str,
    residues: &[(u32, u32)],
    x: u32,
    modulus: u32,
    guards: RouteGuards,
) -> Result<Vec<NameId>, KernelError> {
    let anon = d.kernel().anon();
    let mut admitted = Vec::new();

    // R3: every input congruence holds at the claimed solution.
    for (index, &(a, m)) in residues.iter().enumerate() {
        let name = d
            .kernel()
            .name_str(anon, format!("Check.crt_congruence_{id}_{index}"));
        let m_i = inum(d, m);
        let x_i = inum(d, x);
        let a_i = inum(d, a);
        let ty = modeq(d, m_i, x_i, a_i);
        let value = {
            let lhs = d.iemod(x_i, m_i);
            d.irefl(lhs)
        };
        NatOps::declare_theorem(d, name, ty, value)?;
        admitted.push(name);
    }

    // R4: the claimed modulus is the LEAST common multiple, not merely a
    // common one. `Nat.lcm` is the kernel's own; the certificate's number is
    // checked against it by reduction.
    {
        let moduli: Vec<u32> = residues.iter().map(|&(_, m)| m).collect();
        if guards.leastness {
            let mut folded = 1u32;
            for &m in &moduli {
                folded = folded / gcd_u32(folded, m) * m;
            }
            assert_eq!(
                folded, modulus,
                "route guard: {modulus} is not the least common multiple for {id}"
            );
        }
        let name = d
            .kernel()
            .name_str(anon, format!("Check.crt_least_modulus_{id}"));
        let folded = lcm_fold(d, &moduli);
        let target = d.num(modulus);
        let ty = d.eq(folded, target);
        let value = d.refl(target);
        NatOps::declare_theorem(d, name, ty, value)?;
        admitted.push(name);
    }

    // R2: the solution is canonical, `0 ≤ x < modulus`. The lower bound is
    // structural (`x : Nat`); the strict upper bound is `Nat.le (x+1) modulus`.
    {
        let name = d
            .kernel()
            .name_str(anon, format!("Check.crt_canonical_{id}"));
        let x_nat = d.num(x);
        let m_nat = d.num(modulus);
        let ty = d.lt(x_nat, m_nat);
        assert!(
            x < modulus,
            "a canonical solution must be below its modulus, {x} was not below {modulus}"
        );
        let value = concrete_le(d, x + 1, modulus);
        NatOps::declare_theorem(d, name, ty, value)?;
        admitted.push(name);
    }

    Ok(admitted)
}

fn reconstruct_inconsistent(
    d: &mut IntDev<'_>,
    id: &str,
    residues: &[(u32, u32)],
    left: usize,
    right: usize,
    guards: RouteGuards,
) -> Result<Vec<NameId>, KernelError> {
    let anon = d.kernel().anon();
    let (a_l, m_l) = residues[left];
    let (a_r, m_r) = residues[right];
    let g = gcd_u32(m_l, m_r);
    let (u, v) = (a_l % g, a_r % g);
    if guards.conflict {
        assert_ne!(
            u, v,
            "route guard: congruences {left} and {right} do not conflict in {id}"
        );
    }

    let name = d
        .kernel()
        .name_str(anon, format!("Check.crt_inconsistent_{id}"));
    let p = d.int();
    let int_ty = d.int_ty();

    let g_i = inum(d, g);
    let a_l_i = inum(d, a_l);
    let a_r_i = inum(d, a_r);
    let m_l_i = inum(d, m_l);
    let m_r_i = inum(d, m_r);
    let k_l_i = inum(d, m_l / g);
    let k_r_i = inum(d, m_r / g);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let h_l_ty = modeq(d, m_l_i, x, a_l_i);
    let h_l_fv = d.fresh_fvar();
    let h_l = d.kernel().fvar(h_l_fv);
    let h_r_ty = modeq(d, m_r_i, x, a_r_i);
    let h_r_fv = d.fresh_fvar();
    let h_r = d.kernel().fvar(h_r_fv);

    // `ModEq (kₗ·g) x aₗ → ModEq g x aₗ`; the kernel sees `ofNat mₗ` and
    // `mul (ofNat kₗ) (ofNat g)` as the same modulus by reduction.
    let down_l = {
        let f = p.mod_eq_of_mul_left;
        d.const_app(f, &[g_i, x, a_l_i, k_l_i, h_l])
    };
    let down_r = {
        let f = p.mod_eq_of_mul_left;
        d.const_app(f, &[g_i, x, a_r_i, k_r_i, h_r])
    };
    let flipped = {
        let f = p.mod_eq_symm;
        d.const_app(f, &[g_i, x, a_l_i, down_l])
    };
    let both = {
        let f = p.mod_eq_trans;
        d.const_app(f, &[g_i, a_l_i, x, a_r_i, flipped, down_r])
    };
    // `ModEq g aₗ a_r` unfolds to `emod aₗ g = emod a_r g`, which reduces to
    // an equation between the distinct numerals `u` and `v`.
    let contradiction = if u == v {
        // With the conflict guard off and a forged pair, no refutation exists;
        // hand the kernel the certificate's own claim closed by the only term
        // available, and let it refuse.
        let false_ty = d.false_ty();
        let dummy_fv = d.fresh_fvar();
        let dummy = d.kernel().fvar(dummy_fv);
        let _ = (both, dummy);
        d.lam_fv(dummy_fv, false_ty, dummy)
    } else {
        let ne = ofnat_ne(d, u, v);
        d.kernel().app(ne, both)
    };

    let body = d.lam_fv(h_r_fv, h_r_ty, contradiction);
    let body = d.lam_fv(h_l_fv, h_l_ty, body);
    let value = d.lam_fv(x_fv, int_ty, body);

    let false_ty = d.false_ty();
    let ty = {
        let inner = d.arrow(h_r_ty, false_ty);
        let outer = d.arrow(h_l_ty, inner);
        d.pi_fv(x_fv, int_ty, outer)
    };

    NatOps::declare_theorem(d, name, ty, value)?;
    Ok(vec![name])
}

/// The six systems `F:cas-ntheory-crt-certificate` names, in its own order,
/// with the identifier used in each theorem's name.
pub(super) const SYSTEMS: &[(&str, &[(u32, u32)])] = &[
    ("coprime3", &[(2, 3), (3, 5), (2, 7)]),
    ("noncoprime", &[(1, 4), (3, 6)]),
    ("empty", &[]),
    ("trivial", &[(5, 1)]),
    ("conflict24", &[(0, 2), (1, 4)]),
    ("conflict694", &[(1, 6), (2, 9), (3, 4)]),
];

/// Fetch a CRT certificate from the CAS's own producer.
pub(super) fn certificate(residues: &[(u32, u32)]) -> CrtCertificate {
    let wide: Vec<(i128, i128)> = residues
        .iter()
        .map(|&(a, m)| (i128::from(a), i128::from(m)))
        .collect();
    certify_crt(&wide).unwrap_or_else(|| panic!("the CAS must certify {residues:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::Declaration as Decl;
    use crate::on_a_deep_stack;

    use super::super::super::{Kernel, build_int_prelude};

    fn built() -> (Kernel, crate::int_prelude::IntPrelude) {
        let mut k = Kernel::new();
        let p = build_int_prelude(&mut k).expect("Int prelude must build");
        (k, p)
    }

    /// `gcd_u32` is the greatest common divisor, checked against a
    /// straightforwardly different computation (trial division) over a dense
    /// range, in both directions.
    #[test]
    fn gcd_u32_computes_the_greatest_common_divisor() {
        let mut nontrivial = 0usize;
        for a in 1u32..40 {
            for b in 1u32..40 {
                let by_search = (1..=a.min(b)).filter(|d| a % d == 0 && b % d == 0).max();
                assert_eq!(gcd_u32(a, b), by_search.unwrap(), "gcd({a},{b})");
                if gcd_u32(a, b) > 1 {
                    nontrivial += 1;
                }
            }
        }
        assert!(
            nontrivial > 100,
            "the range must contain many non-coprime pairs, or this only \
             checks the gcd = 1 case"
        );
    }

    /// `lcm_fold` reduces to the intended numeral, and NOT to a neighbouring
    /// one — the half that makes the positive assertion mean something.
    #[test]
    fn lcm_fold_reduces_to_the_least_common_multiple() {
        let (mut k, p) = built();
        let mut d = IntDev::new(&mut k, p);
        for (moduli, expected) in [
            (vec![3u32, 5, 7], 105u32),
            (vec![4, 6], 12),
            (vec![], 1),
            (vec![1], 1),
            (vec![2, 4], 4),
        ] {
            let folded = lcm_fold(&mut d, &moduli);
            let good = d.num(expected);
            assert!(
                d.kernel().def_eq(folded, good),
                "lcm over {moduli:?} must reduce to {expected}"
            );
            // `24` is the CAS module's own recorded near-miss for `[4, 6]`: a
            // common multiple that is not the least one.
            let bad = d.num(expected * 2);
            assert!(
                !d.kernel().def_eq(folded, bad),
                "lcm over {moduli:?} must NOT reduce to {}",
                expected * 2
            );
        }
    }

    /// The reconstruction: all six systems admitted through
    /// [`crate::Kernel::add_declaration`], axiom-free.
    #[test]
    fn crt_certificates_are_kernel_reconstructed() {
        on_a_deep_stack(|| {
            let (mut k, p) = built();
            let mut d = IntDev::new(&mut k, p);
            let mut total = 0usize;
            let mut solutions = 0usize;
            let mut inconsistencies = 0usize;
            for &(id, residues) in SYSTEMS {
                let cert = certificate(residues);
                match cert {
                    CrtCertificate::Solution { .. } => solutions += 1,
                    CrtCertificate::Inconsistent { .. } => inconsistencies += 1,
                }
                let names = reconstruct(&mut d, id, residues, &cert, RouteGuards::all())
                    .unwrap_or_else(|e| panic!("the kernel must admit {id}: {e:?}"));
                assert!(!names.is_empty(), "{id} must emit at least one theorem");
                total += names.len();
                for name in names {
                    let env = d.kernel().environment();
                    let decl = env.get(name).expect("the declaration must be admitted");
                    assert!(
                        matches!(decl, Decl::Theorem { .. }),
                        "must be a Theorem, not an Axiom or an Opaque"
                    );
                    let footprint = d.kernel().axiom_footprint(name);
                    assert!(
                        footprint.is_empty(),
                        "the reconstruction must be axiom-free; footprint was {footprint:?}"
                    );
                }
            }
            // Both directions must be exercised, or the run only covers half
            // of what the fact claims.
            assert_eq!(solutions, 4, "four solvable systems");
            assert_eq!(inconsistencies, 2, "two unsolvable systems");
            assert!(
                total >= 16,
                "the route must emit at least 16 theorems, got {total}"
            );
        });
    }

    /// **The kernel is the checker, on the leastness guard.** The CAS module's
    /// own recorded near-miss — `[(1,4),(3,6)]` with `modulus = 24`, which
    /// satisfies every congruence and IS a common multiple — is refused by
    /// [`crate::Kernel::add_declaration`] with this route's guards off.
    ///
    /// The control is the same run, same guards off, with the genuine
    /// `modulus = 12`, which the kernel admits.
    #[test]
    fn a_merely_common_modulus_is_refused_by_the_kernel() {
        on_a_deep_stack(|| {
            let residues: &[(u32, u32)] = &[(1, 4), (3, 6)];

            // Control: guards off, genuine certificate — admitted.
            let (mut k, p) = built();
            let mut d = IntDev::new(&mut k, p);
            let good = certificate(residues);
            assert_eq!(
                good,
                CrtCertificate::Solution {
                    solution: 9,
                    modulus: 12
                },
                "the CAS must produce the least common multiple"
            );
            reconstruct(&mut d, "noncoprime", residues, &good, RouteGuards::none())
                .expect("guards off, the genuine certificate must still be admitted");

            // The forgery: a common multiple that is not the least one. Every
            // congruence still holds and the solution is still canonical, so
            // only the leastness theorem can reject it.
            let (mut k2, p2) = built();
            let mut d2 = IntDev::new(&mut k2, p2);
            let forged = CrtCertificate::Solution {
                solution: 9,
                modulus: 24,
            };
            let refusal = reconstruct(
                &mut d2,
                "noncoprime",
                residues,
                &forged,
                RouteGuards::none(),
            );
            assert!(
                refusal.is_err(),
                "with this route's guards OFF, the KERNEL must refuse a \
                 modulus that is merely a common multiple"
            );

            // And the route's own CAS recheck catches it too, when on.
            let (mut k3, p3) = built();
            let mut d3 = IntDev::new(&mut k3, p3);
            let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                reconstruct(&mut d3, "noncoprime", residues, &forged, RouteGuards::all())
            }));
            assert!(
                caught.is_err(),
                "the route's own guard must also reject the forgery"
            );
        });
    }

    /// **The kernel is the checker, on the conflict guard.** A fabricated
    /// `Inconsistent` witness over a pair that does NOT conflict is refused by
    /// the kernel with this route's guards off.
    #[test]
    fn a_fabricated_conflict_is_refused_by_the_kernel() {
        on_a_deep_stack(|| {
            // `[(1,6),(2,9),(3,4)]` is inconsistent, but only through the pair
            // (0, 1): `1 ≢ 2 (mod gcd(6,9) = 3)`. The pair (1, 2) does NOT
            // conflict — `2 ≡ 3 (mod gcd(9,4) = 1)` holds vacuously.
            let residues: &[(u32, u32)] = &[(1, 6), (2, 9), (3, 4)];

            let (mut k, p) = built();
            let mut d = IntDev::new(&mut k, p);
            let good = certificate(residues);
            assert_eq!(
                good,
                CrtCertificate::Inconsistent { left: 0, right: 1 },
                "the CAS must name the genuinely conflicting pair"
            );
            reconstruct(&mut d, "conflict694", residues, &good, RouteGuards::none())
                .expect("guards off, the genuine certificate must still be admitted");

            let (mut k2, p2) = built();
            let mut d2 = IntDev::new(&mut k2, p2);
            let forged = CrtCertificate::Inconsistent { left: 1, right: 2 };
            let refusal = reconstruct(
                &mut d2,
                "conflict694",
                residues,
                &forged,
                RouteGuards::none(),
            );
            assert!(
                refusal.is_err(),
                "with this route's guards OFF, the KERNEL must refuse a \
                 fabricated conflict"
            );
        });
    }
}
