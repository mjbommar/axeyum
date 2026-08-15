//! The committed certificate corpus.
//!
//! Three artifacts, chosen to be three different *kinds* of question rather than
//! three instances of one. Every certificate here was found by hand -- the
//! search is untrusted and, in this lane, it is a person with a pencil. What
//! matters is that [`crate::sos::check`] re-derives each one from the declared
//! system alone, in a few milliseconds, and rejects every tampering pinned in
//! `scripts/check-sos-negative-controls.sh`.
//!
//! The artifacts under `artifacts/sos-certificates/` are emitted from this
//! module (`cargo run -p axeyum-cas --release --example emit_sos_certificates`)
//! and the integration suite asserts the committed files parse back to exactly
//! these values, so a hand-edited artifact is caught by the round trip as well
//! as by the checker.

use std::collections::BTreeMap;

use axeyum_ir::Rational;

use crate::mvpoly::{Monomial, MvPoly};
use crate::sos::{
    BarrierCertificate, BarrierProblem, LyapunovCertificate, LyapunovProblem, PsdNotSosCertificate,
    PsdNotSosProblem, SosArtifact, SosSum, VectorField,
};

/// Every committed artifact, in a deterministic order.
#[must_use]
pub fn all() -> Vec<SosArtifact> {
    vec![
        damped_rotation_lyapunov(),
        energy_barrier_reachability(),
        motzkin_psd_not_sos(),
    ]
}

/// Look one artifact up by identifier.
#[must_use]
pub fn by_id(id: &str) -> Option<SosArtifact> {
    all().into_iter().find(|artifact| artifact.id() == id)
}

// ---------------------------------------------------------------------------
// 1. Global exponential stability with a certified rate
// ---------------------------------------------------------------------------

/// A cubic planar vector field whose linear part is strongly non-normal, so the
/// obvious Lyapunov candidate `|x|^2` fails, and a skewed quadratic form works.
///
/// ```text
/// x' = -x + 10y - x(x^2 + y^2)
/// y' =      -y - y(x^2 + y^2)
/// ```
///
/// The linearisation is `[[-1, 10], [0, -1]]`, which is Hurwitz but far from
/// normal: along `x = y` the energy `|x|^2` *increases*, and the certificate
/// commits the point `(1, 1)` where its Lie derivative is `+8`. Solving the
/// Lyapunov equation `A^T P + P A = -2 I` gives `V = x^2 + 10xy + 51y^2`, and
/// the cubic damping term contributes `-2|x|^2 V`, which is a product of two PSD
/// binary quadratic forms and therefore itself a sum of squares.
#[must_use]
pub fn damped_rotation_lyapunov() -> SosArtifact {
    let variables = vec!["x".to_string(), "y".to_string()];
    // x' = -x + 10y - x^3 - x y^2
    let dx = poly(&[
        (-1, 1, &[("x", 1)]),
        (10, 1, &[("y", 1)]),
        (-1, 1, &[("x", 3)]),
        (-1, 1, &[("x", 1), ("y", 2)]),
    ]);
    // y' = -y - x^2 y - y^3
    let dy = poly(&[
        (-1, 1, &[("y", 1)]),
        (-1, 1, &[("x", 2), ("y", 1)]),
        (-1, 1, &[("y", 3)]),
    ]);
    let v = poly(&[
        (1, 1, &[("x", 2)]),
        (10, 1, &[("x", 1), ("y", 1)]),
        (51, 1, &[("y", 2)]),
    ]);
    let problem = LyapunovProblem {
        id: "damped-rotation-lyapunov".to_string(),
        description: "Global exponential stability of the cubic planar field \
                      x' = -x + 10y - x(x^2+y^2), y' = -y - y(x^2+y^2), with an exactly rational \
                      certified decay rate. The naive candidate |x|^2 fails at (1,1)."
            .to_string(),
        system: VectorField {
            variables,
            field: vec![dx, dy],
        },
        v,
        lower: Rational::new(1, 2),
        upper: Rational::integer(52),
        decay: Rational::integer(2),
        naive_failure: point(&[("x", 1, 1), ("y", 1, 1)]),
    };
    let certificate = LyapunovCertificate {
        // V - (1/2)|x|^2 = (1/2)(x + 10y)^2 + (1/2) y^2
        lower_gap: sos(&[
            (1, 2, &[(1, 1, &[("x", 1)]), (10, 1, &[("y", 1)])]),
            (1, 2, &[(1, 1, &[("y", 1)])]),
        ]),
        // 52|x|^2 - V = (1/51)(51x - 5y)^2 + (26/51) y^2
        upper_gap: sos(&[
            (1, 51, &[(51, 1, &[("x", 1)]), (-5, 1, &[("y", 1)])]),
            (26, 51, &[(1, 1, &[("y", 1)])]),
        ]),
        // -V' - 2|x|^2 = 2|x|^2 V
        //             = 2(x^2+5xy)^2 + 2(xy+5y^2)^2 + 52(xy)^2 + 52(y^2)^2
        decrease: sos(&[
            (2, 1, &[(1, 1, &[("x", 2)]), (5, 1, &[("x", 1), ("y", 1)])]),
            (2, 1, &[(1, 1, &[("x", 1), ("y", 1)]), (5, 1, &[("y", 2)])]),
            (52, 1, &[(1, 1, &[("x", 1), ("y", 1)])]),
            (52, 1, &[(1, 1, &[("y", 2)])]),
        ]),
    };
    SosArtifact::Lyapunov(problem, certificate)
}

// ---------------------------------------------------------------------------
// 2. Unbounded-horizon safety
// ---------------------------------------------------------------------------

/// A nonlinearly damped oscillator that can never reach a disc five units away,
/// at any time, with no horizon bound.
///
/// ```text
/// x' = y
/// y' = -x - y^3
/// X0 = { 1 - x^2 - (y-2)^2 >= 0 }        the unit disc centred at (0, 2)
/// Xu = { 1 - (x-5)^2 - y^2 >= 0 }        the unit disc centred at (5, 0)
/// ```
///
/// The barrier `B = (1/2)(x^2 + y^2) - 6` has `B' = -y^4 <= 0`, so every
/// sublevel set is forward invariant. The initial disc is *not* centred at the
/// origin, so the level `6` is not read off the geometry: it is squeezed between
/// the maximum of the energy on `X0` (which is `9/2`, attained at `(0,3)`) and
/// its minimum on `Xu` (which is `8`), and both bounds are what the
/// Positivstellensatz multipliers pay for.
#[must_use]
pub fn energy_barrier_reachability() -> SosArtifact {
    let variables = vec!["x".to_string(), "y".to_string()];
    let dx = poly(&[(1, 1, &[("y", 1)])]);
    let dy = poly(&[(-1, 1, &[("x", 1)]), (-1, 1, &[("y", 3)])]);
    // 1 - x^2 - (y - 2)^2 = -3 - x^2 - y^2 + 4y
    let initial = poly(&[
        (-3, 1, &[]),
        (-1, 1, &[("x", 2)]),
        (-1, 1, &[("y", 2)]),
        (4, 1, &[("y", 1)]),
    ]);
    // 1 - (x - 5)^2 - y^2 = -24 + 10x - x^2 - y^2
    let unsafe_region = poly(&[
        (-24, 1, &[]),
        (10, 1, &[("x", 1)]),
        (-1, 1, &[("x", 2)]),
        (-1, 1, &[("y", 2)]),
    ]);
    let barrier = poly(&[(1, 2, &[("x", 2)]), (1, 2, &[("y", 2)]), (-6, 1, &[])]);
    let problem = BarrierProblem {
        id: "energy-barrier-reachability".to_string(),
        description: "No solution of x' = y, y' = -x - y^3 started in the unit disc at (0,2) ever \
                      reaches the unit disc at (5,0), at any time. Unbounded horizon, decided by \
                      one barrier function and two Positivstellensatz multipliers."
            .to_string(),
        system: VectorField {
            variables,
            field: vec![dx, dy],
        },
        initial: vec![initial],
        unsafe_region: vec![unsafe_region],
        barrier,
        initial_witness: point(&[("x", 0, 1), ("y", 2, 1)]),
        unsafe_witness: point(&[("x", 5, 1), ("y", 0, 1)]),
    };
    let certificate = BarrierCertificate {
        initial_multipliers: vec![sos(&[(1, 1, &[(1, 1, &[])])])],
        initial_margin: Rational::integer(1),
        // -B - 1 - g0 = (1/2)x^2 + (1/2)(y - 4)^2
        initial_gap: sos(&[
            (1, 2, &[(1, 1, &[("x", 1)])]),
            (1, 2, &[(1, 1, &[("y", 1)]), (-4, 1, &[])]),
        ]),
        unsafe_multipliers: vec![sos(&[(1, 1, &[(1, 1, &[])])])],
        unsafe_margin: Rational::integer(1),
        // B - 1 - gu = (3/2)(x - 10/3)^2 + (3/2)y^2 + 1/3
        unsafe_gap: sos(&[
            (3, 2, &[(1, 1, &[("x", 1)]), (-10, 3, &[])]),
            (3, 2, &[(1, 1, &[("y", 1)])]),
            (1, 3, &[(1, 1, &[])]),
        ]),
        // -B' = y^4
        decrease: sos(&[(1, 1, &[(1, 1, &[("y", 2)])])]),
    };
    SosArtifact::Barrier(problem, certificate)
}

// ---------------------------------------------------------------------------
// 3. Where the route stops: nonnegative but not a sum of squares
// ---------------------------------------------------------------------------

/// The Motzkin form, with both halves certified: nonnegative on the reals, and
/// **not** a sum of squares.
///
/// ```text
/// M(x, y, z) = x^4 y^2 + x^2 y^4 + z^6 - 3 x^2 y^2 z^2
/// ```
///
/// *Nonnegativity*, primal. `(x^2 + y^2 + z^2) M` is a sum of five weighted
/// squares:
///
/// ```text
/// (x^2+y^2+z^2) M = (yz(x^2 - z^2))^2 + (xz(y^2 - z^2))^2 + (x^2 y^2 - z^4)^2
///                 + (1/4)(xy(y^2 - x^2))^2 + (3/4)(xy(x^2 + y^2 - 2z^2))^2
/// ```
///
/// Since the multiplier is strictly positive off the origin and `M` is
/// homogeneous, `M >= 0` everywhere -- in every ordered field, not merely over
/// the reals.
///
/// *Non-SOS-ness*, dual. A linear functional `L` on the 28 degree-six monomials
/// whose moment matrix over the ten degree-three monomials is PSD, and with
/// `L(M) = -1 < 0`. If `M` were a sum of squares of cubic forms then
/// `L(M) = sum L(q_i^2) >= 0`. The functional is supported on ten monomials and
/// its moment matrix decomposes into three blocks plus a singleton; the blocks
/// are singular, which is what forces the values to be as delicate as they are.
///
/// The two halves together are the point of this artifact: they measure the gap
/// between "nonnegative" and "sum of squares", which is exactly the gap the SOS
/// route in this repository cannot cross. Recording that as a settled fact is
/// more honest than only recording the problems the route can do.
#[must_use]
pub fn motzkin_psd_not_sos() -> SosArtifact {
    let variables = vec!["x".to_string(), "y".to_string(), "z".to_string()];
    let form = poly(&[
        (1, 1, &[("x", 4), ("y", 2)]),
        (1, 1, &[("x", 2), ("y", 4)]),
        (1, 1, &[("z", 6)]),
        (-3, 1, &[("x", 2), ("y", 2), ("z", 2)]),
    ]);
    let multiplier = poly(&[
        (1, 1, &[("x", 2)]),
        (1, 1, &[("y", 2)]),
        (1, 1, &[("z", 2)]),
    ]);
    let problem = PsdNotSosProblem {
        id: "motzkin-psd-not-sos".to_string(),
        description: "The Motzkin form x^4y^2 + x^2y^4 + z^6 - 3x^2y^2z^2 is nonnegative on the \
                      reals but is not a sum of squares of polynomials. Certified both ways: an \
                      SOS decomposition of |x|^2 times the form, and a PSD moment functional that \
                      is negative on it."
            .to_string(),
        variables,
        form,
        multiplier,
        half_degree: 3,
    };

    let mut dual = BTreeMap::new();
    for (numerator, factors) in [
        (450_i128, &[("x", 6)][..]),
        (450, &[("y", 6)][..]),
        (9, &[("x", 4), ("y", 2)][..]),
        (9, &[("x", 2), ("y", 4)][..]),
        (8, &[("z", 6)][..]),
        (9, &[("x", 2), ("y", 2), ("z", 2)][..]),
        (72, &[("x", 4), ("z", 2)][..]),
        (72, &[("y", 4), ("z", 2)][..]),
        (18, &[("x", 2), ("z", 4)][..]),
        (18, &[("y", 2), ("z", 4)][..]),
    ] {
        dual.insert(Monomial::from_powers(factors), Rational::integer(numerator));
    }

    let certificate = PsdNotSosCertificate {
        multiplied: sos(&[
            // (y z (x^2 - z^2))^2
            (
                1,
                1,
                &[
                    (1, 1, &[("x", 2), ("y", 1), ("z", 1)]),
                    (-1, 1, &[("y", 1), ("z", 3)]),
                ],
            ),
            // (x z (y^2 - z^2))^2
            (
                1,
                1,
                &[
                    (1, 1, &[("x", 1), ("y", 2), ("z", 1)]),
                    (-1, 1, &[("x", 1), ("z", 3)]),
                ],
            ),
            // (x^2 y^2 - z^4)^2
            (1, 1, &[(1, 1, &[("x", 2), ("y", 2)]), (-1, 1, &[("z", 4)])]),
            // (1/4) (x y (y^2 - x^2))^2
            (
                1,
                4,
                &[
                    (1, 1, &[("x", 1), ("y", 3)]),
                    (-1, 1, &[("x", 3), ("y", 1)]),
                ],
            ),
            // (3/4) (x y (x^2 + y^2 - 2 z^2))^2
            (
                3,
                4,
                &[
                    (1, 1, &[("x", 3), ("y", 1)]),
                    (1, 1, &[("x", 1), ("y", 3)]),
                    (-2, 1, &[("x", 1), ("y", 1), ("z", 2)]),
                ],
            ),
        ]),
        dual,
    };
    SosArtifact::PsdNotSos(problem, certificate)
}

// ---------------------------------------------------------------------------
// small builders
// ---------------------------------------------------------------------------

type TermSpec<'a> = (i128, i128, &'a [(&'a str, u32)]);

/// Build a polynomial from `(numerator, denominator, monomial)` triples.
///
/// # Panics
///
/// Panics on a zero denominator or a coefficient outside the exact range. This
/// is corpus construction, not artifact parsing: a malformed literal here is a
/// programming error and must not be recoverable, whereas a malformed *file* is
/// reported as a message by [`crate::sos::json::from_json`].
fn poly(terms: &[TermSpec<'_>]) -> MvPoly {
    let built: Vec<(Monomial, Rational)> = terms
        .iter()
        .map(|(numerator, denominator, factors)| {
            (
                Monomial::from_powers(factors),
                Rational::checked_new(*numerator, *denominator)
                    .expect("corpus coefficient out of exact range"),
            )
        })
        .collect();
    MvPoly::from_terms(built).expect("corpus polynomial out of exact range")
}

/// Build a sum of weighted squares from `(weight numerator, weight denominator,
/// square)` triples.
///
/// # Panics
///
/// Panics on a negative weight or an out-of-range coefficient, for the same
/// reason as [`poly`].
fn sos(squares: &[(i128, i128, &[TermSpec<'_>])]) -> SosSum {
    let built: Vec<(Rational, MvPoly)> = squares
        .iter()
        .map(|(numerator, denominator, terms)| {
            (
                Rational::checked_new(*numerator, *denominator)
                    .expect("corpus weight out of exact range"),
                poly(terms),
            )
        })
        .collect();
    SosSum::new(built).expect("corpus sum of squares has a negative weight")
}

fn point(bindings: &[(&str, i128, i128)]) -> BTreeMap<String, Rational> {
    bindings
        .iter()
        .map(|(name, numerator, denominator)| {
            (
                (*name).to_string(),
                Rational::checked_new(*numerator, *denominator)
                    .expect("corpus point out of exact range"),
            )
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{all, by_id};
    use crate::sos::check;

    #[test]
    fn every_committed_artifact_checks() {
        let artifacts = all();
        assert_eq!(artifacts.len(), 3, "the corpus is three artifacts");
        for artifact in &artifacts {
            let report = check::check_artifact(artifact)
                .unwrap_or_else(|message| panic!("{} failed to check: {message}", artifact.id()));
            assert!(
                report.len() >= 5,
                "{} discharged only {} obligations",
                artifact.id(),
                report.len()
            );
        }
    }

    #[test]
    fn the_three_artifacts_are_three_different_kinds() {
        let mut kinds: Vec<&str> = all().iter().map(super::SosArtifact::kind).collect();
        kinds.sort_unstable();
        kinds.dedup();
        assert_eq!(kinds.len(), 3, "three questions of three different kinds");
    }

    #[test]
    fn the_certified_decay_rate_is_one_over_twenty_six() {
        let artifact = by_id("damped-rotation-lyapunov").expect("the artifact is in the corpus");
        let report = check::check_artifact(&artifact).expect("it checks");
        let rate = report.rate.expect("a Lyapunov artifact reports a rate");
        assert_eq!(rate.numerator(), 1);
        assert_eq!(rate.denominator(), 26);
    }

    #[test]
    fn ids_are_unique() {
        let artifacts = all();
        let mut ids: Vec<&str> = artifacts.iter().map(super::SosArtifact::id).collect();
        let total = ids.len();
        ids.sort_unstable();
        ids.dedup();
        assert_eq!(ids.len(), total);
    }
}
