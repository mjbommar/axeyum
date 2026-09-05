//! Tests for the carrier-agnostic half of [`super`]: the exact rational
//! arithmetic, the polynomial algebra, the LDLᵀ PSD decision, the
//! denominator-clearing search, and the [`DualWitness`] check.
//!
//! Nothing here builds a kernel term — that is [`super::rat`]'s own suite.
//! These are the *search* tests, and the point of separating them is that the
//! search is the untrusted half: it can be wrong without being unsound (the
//! kernel refuses), so it needs its own controls or a silent decline looks the
//! same as a correct one.

use std::collections::BTreeMap;

use super::{
    Atom, Certificate, Decline, DualWitness, Poly, Psd, Q, monomials_of_degree, search_sos,
    search_with_hypotheses,
};

fn q(n: i128, d: i128) -> Q {
    Q::new(n, d).expect("a nonzero denominator")
}

/// `x²`, `xy`, … over the given variable indices.
fn mono(p: &mut Poly, vars: &[usize], c: Q) {
    let mut copy = Poly::zero();
    let _ = copy;
    let mut term = Poly::constant(c);
    for &v in vars {
        term = term.mul(&Poly::var(v)).expect("no overflow");
    }
    *p = p.add(&term).expect("no overflow");
}

/// `x² + y² − 2xy` over `x ↦ 0`, `y ↦ 1`.
fn am_gm_two_var() -> Poly {
    let mut p = Poly::zero();
    mono(&mut p, &[0, 0], Q::integer(1));
    mono(&mut p, &[1, 1], Q::integer(1));
    mono(&mut p, &[0, 1], Q::integer(-2));
    p
}

/// `a² + b² + c² − ab − bc − ca` over `a ↦ 0`, `b ↦ 1`, `c ↦ 2`.
fn am_gm_three_var() -> Poly {
    let mut p = Poly::zero();
    for v in 0..3 {
        mono(&mut p, &[v, v], Q::integer(1));
    }
    for (i, j) in [(0, 1), (1, 2), (0, 2)] {
        mono(&mut p, &[i, j], Q::integer(-1));
    }
    p
}

// ---------------------------------------------------------------------------
// exact arithmetic
// ---------------------------------------------------------------------------

#[test]
fn rationals_normalize_and_keep_the_denominator_positive() {
    assert_eq!(q(2, 4), q(1, 2));
    assert_eq!(q(1, -2), q(-1, 2));
    assert_eq!(q(-3, -6), q(1, 2));
    assert_eq!(q(0, 5), Q::zero());
    assert!(
        Q::new(1, 0).is_none(),
        "a zero denominator is not a rational"
    );
}

#[test]
fn rational_overflow_declines_instead_of_wrapping() {
    let big = Q::integer(i128::MAX);
    assert!(
        big.add(big).is_none(),
        "an overflowing sum must be None, not a wrapped value — a wrapped \
         coefficient is a WRONG certificate the search would then believe"
    );
    assert!(big.mul(big).is_none());
}

// ---------------------------------------------------------------------------
// the PSD decision
// ---------------------------------------------------------------------------

#[test]
fn ldl_factors_a_psd_matrix_and_the_squares_reproduce_it() {
    // [[2, 1], [1, 2]] — positive definite.
    let a = vec![
        vec![Q::integer(2), Q::integer(1)],
        vec![Q::integer(1), Q::integer(2)],
    ];
    let psd = Psd::factor(&a).expect("positive definite");
    assert_eq!(psd.squares.len(), 2, "two strictly positive pivots");
    // Reproduce `a` as `Σ dᵢ ℓᵢ ℓᵢᵀ`.
    let mut rebuilt = vec![vec![Q::zero(); 2]; 2];
    for (weight, column) in &psd.squares {
        for r in 0..2 {
            for c in 0..2 {
                let entry = column[r]
                    .mul(column[c])
                    .and_then(|v| v.mul(*weight))
                    .expect("no overflow");
                rebuilt[r][c] = rebuilt[r][c].add(entry).expect("no overflow");
            }
        }
    }
    assert_eq!(rebuilt, a, "the factorization must reproduce the matrix");
}

#[test]
fn ldl_reports_a_negative_pivot_as_not_psd() {
    // [[1, 2], [2, 1]] — indefinite (determinant −3).
    let a = vec![
        vec![Q::integer(1), Q::integer(2)],
        vec![Q::integer(2), Q::integer(1)],
    ];
    assert_eq!(Psd::factor(&a), Err(Decline::NotPsd { pivot: 1 }));
    assert_eq!(Psd::is_psd(&a), Ok(false));
}

#[test]
fn ldl_reports_a_zero_pivot_beside_a_nonzero_entry_as_not_psd() {
    // [[0, 1], [1, 0]] — the case plain LDLᵀ would divide by zero on, and the
    // reason a zero pivot is checked against its own row rather than skipped.
    let a = vec![
        vec![Q::zero(), Q::integer(1)],
        vec![Q::integer(1), Q::zero()],
    ];
    assert_eq!(Psd::factor(&a), Err(Decline::NotPsd { pivot: 0 }));
}

#[test]
fn ldl_skips_a_zero_pivot_whose_row_vanishes() {
    // The singular-but-PSD shape every homogeneous form produces: the constant
    // basis row is all zero.
    let a = vec![vec![Q::zero(), Q::zero()], vec![Q::zero(), Q::integer(3)]];
    let psd = Psd::factor(&a).expect("PSD");
    assert_eq!(psd.squares.len(), 1, "the zero pivot contributes no square");
}

// ---------------------------------------------------------------------------
// the search
// ---------------------------------------------------------------------------

/// Every certificate the search returns must expand back to `scale · p`. This
/// is the search's own control; the kernel checks the same identity again.
fn assert_certificate_expands(certificate: &Certificate, p: &Poly, hypotheses: &[Poly]) {
    let expanded = certificate.expand(hypotheses).expect("no overflow");
    let target = p.scale(Q::integer(certificate.scale)).expect("no overflow");
    assert_eq!(
        expanded, target,
        "certificate expands to {expanded:?}, expected {target:?}"
    );
}

#[test]
fn two_variable_am_gm_needs_no_scale() {
    let p = am_gm_two_var();
    let certificate = search_sos(&p, 2).expect("(x−y)² is a certificate");
    assert_eq!(certificate.scale, 1, "no denominator to clear");
    assert_certificate_expands(&certificate, &p, &[]);
}

#[test]
fn three_variable_am_gm_forces_the_scale_four() {
    let p = am_gm_three_var();
    let certificate = search_sos(&p, 3).expect("4p = (2a−b−c)² + 3(b−c)²");
    assert_eq!(
        certificate.scale, 4,
        "the Gram matrix has half-integer off-diagonals, so NO unit-weight \
         integer-form decomposition exists; the scale is forced"
    );
    assert_eq!(
        certificate.summands(),
        4,
        "one copy of (2a−b−c)² and three of (b−c)²"
    );
    assert_certificate_expands(&certificate, &p, &[]);
}

#[test]
fn an_indefinite_form_is_reported_as_a_finding_not_a_decline() {
    // `x² − y²` is negative at `(0, 1)`.
    let mut p = Poly::zero();
    mono(&mut p, &[0, 0], Q::integer(1));
    mono(&mut p, &[1, 1], Q::integer(-1));
    assert!(
        matches!(search_sos(&p, 2), Err(Decline::NotPsd { .. })),
        "an indefinite quadratic form is a FINDING (the goal is false), not a \
         refusal to search"
    );
}

#[test]
fn degree_three_declines_by_degree() {
    let mut p = Poly::zero();
    mono(&mut p, &[0, 0, 0], Q::integer(1));
    assert_eq!(
        search_sos(&p, 1),
        Err(Decline::DegreeUnsupported { degree: 3 })
    );
}

#[test]
fn an_affine_square_is_found_with_its_constant() {
    // `x² − 2x + 1 = (x − 1)²`.
    let mut p = Poly::zero();
    mono(&mut p, &[0, 0], Q::integer(1));
    mono(&mut p, &[0], Q::integer(-2));
    mono(&mut p, &[], Q::integer(1));
    let certificate = search_sos(&p, 1).expect("(x−1)²");
    assert_certificate_expands(&certificate, &p, &[]);
    assert!(
        certificate
            .atoms
            .iter()
            .any(|(_, atom)| matches!(atom, Atom::Square { constant, .. } if *constant != 0)),
        "the affine basis element must carry the constant"
    );
}

#[test]
fn the_positivstellensatz_product_shape_is_found() {
    // `p = h·g + (x − y)²` with `h = x`, `g = y`: not SOS on its own (it is
    // `x² − xy + y²` … in fact PSD, so make it genuinely need the product).
    // `p = xy` is NOT a sum of squares — its Gram matrix is [[0,1/2],[1/2,0]] —
    // but `x ≥ 0`, `y ≥ 0` give it at once.
    let mut p = Poly::zero();
    mono(&mut p, &[0, 1], Q::integer(1));
    assert!(
        matches!(search_sos(&p, 2), Err(Decline::NotPsd { .. })),
        "xy is not a sum of squares"
    );
    let hypotheses = vec![Poly::var(0), Poly::var(1)];
    let certificate =
        search_with_hypotheses(&p, 2, &hypotheses).expect("x·y closes it under 0≤x, 0≤y");
    assert_certificate_expands(&certificate, &p, &hypotheses);
    assert!(
        certificate
            .atoms
            .iter()
            .any(|(_, atom)| matches!(atom, Atom::HypothesisProduct(0, 1))),
        "the certificate must use the product of the two hypotheses"
    );
}

#[test]
fn the_pure_sos_decline_survives_a_useless_hypothesis() {
    // `x² − y²` stays a finding even with an irrelevant hypothesis in scope:
    // the reported decline is the PRIMARY route's, not the last pair tried.
    let mut p = Poly::zero();
    mono(&mut p, &[0, 0], Q::integer(1));
    mono(&mut p, &[1, 1], Q::integer(-1));
    let hypotheses = vec![Poly::var(0)];
    assert!(matches!(
        search_with_hypotheses(&p, 2, &hypotheses),
        Err(Decline::NotPsd { .. })
    ));
}

// ---------------------------------------------------------------------------
// the dual side
// ---------------------------------------------------------------------------

#[test]
fn monomial_bases_have_the_expected_sizes() {
    // Degree-3 monomials in 3 variables: C(3+3-1, 3) = 10.
    assert_eq!(monomials_of_degree(3, 3).len(), 10);
    assert_eq!(monomials_of_degree(3, 0), vec![Vec::<usize>::new()]);
    assert_eq!(monomials_of_degree(2, 2).len(), 3);
}

/// The Motzkin form `x⁴y² + x²y⁴ + z⁶ − 3x²y²z²` over `x ↦ 0`, `y ↦ 1`,
/// `z ↦ 2`.
pub(crate) fn motzkin() -> Poly {
    let mut p = Poly::zero();
    mono(&mut p, &[0, 0, 0, 0, 1, 1], Q::integer(1));
    mono(&mut p, &[0, 0, 1, 1, 1, 1], Q::integer(1));
    mono(&mut p, &[2, 2, 2, 2, 2, 2], Q::integer(1));
    mono(&mut p, &[0, 0, 1, 1, 2, 2], Q::integer(-3));
    p
}

/// The dual moment functional the CAS records for the Motzkin form
/// (`axeyum_cas::sos::corpus::motzkin_psd_not_sos`), transcribed onto this
/// module's monomial indexing.
pub(crate) fn motzkin_dual() -> DualWitness {
    let entries: &[(&[usize], i128)] = &[
        (&[0, 0, 0, 0, 0, 0], 450),
        (&[1, 1, 1, 1, 1, 1], 450),
        (&[0, 0, 0, 0, 1, 1], 9),
        (&[0, 0, 1, 1, 1, 1], 9),
        (&[2, 2, 2, 2, 2, 2], 8),
        (&[0, 0, 1, 1, 2, 2], 9),
        (&[0, 0, 0, 0, 2, 2], 72),
        (&[1, 1, 1, 1, 2, 2], 72),
        (&[0, 0, 2, 2, 2, 2], 18),
        (&[1, 1, 2, 2, 2, 2], 18),
    ];
    let mut moments = BTreeMap::new();
    for (m, v) in entries {
        moments.insert((*m).to_vec(), Q::integer(*v));
    }
    DualWitness {
        half_degree: 3,
        moments,
    }
}

#[test]
fn the_motzkin_dual_witness_verifies() {
    let p = motzkin();
    let witness = motzkin_dual();
    assert_eq!(
        witness.verifies(&p, 3),
        Ok(true),
        "the moment matrix is PSD and L(Motzkin) = 26 − 27 = −1 < 0, so the \
         Motzkin form is not a sum of squares"
    );
}

#[test]
fn a_witness_that_is_nonnegative_on_the_form_does_not_verify() {
    // The same PSD moment matrix against `x⁶`, on which L is +450 > 0. A
    // witness only witnesses non-SOS-ness of a form it is NEGATIVE on, and
    // `x⁶` is obviously a square — so this is the control that the check is
    // not merely reporting "the matrix is PSD".
    let mut p = Poly::zero();
    mono(&mut p, &[0, 0, 0, 0, 0, 0], Q::integer(1));
    assert_eq!(motzkin_dual().verifies(&p, 3), Ok(false));
}

#[test]
fn a_witness_with_a_non_psd_moment_matrix_does_not_verify() {
    // Break the delicate x-block: `L(x⁶) = 450` is what makes the 3x3 block's
    // determinant exactly zero. Drop it to 1 and the block goes indefinite, so
    // the witness must be rejected even though L is still −1 on the form.
    let mut witness = motzkin_dual();
    witness
        .moments
        .insert(vec![0, 0, 0, 0, 0, 0], Q::integer(1));
    assert_eq!(
        witness.verifies(&motzkin(), 3),
        Ok(false),
        "a non-PSD moment matrix proves nothing"
    );
}
