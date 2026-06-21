//! Differential test pinning the fast evaluation–interpolation Sylvester
//! determinant (`sylvester_determinant`) to the reference Leibniz expansion
//! (`sylvester_determinant_leibniz`) on many small random polynomial matrices.
//!
//! This is SOUNDNESS-CRITICAL: the determinant of the Sylvester matrix IS the
//! resultant polynomial that decides 2-variable NRA verdicts. A determinant bug
//! would mis-decide sat/unsat. The two algorithms compute the SAME object by
//! different routes; they MUST agree on the exact `Rational` coefficient vector.

use axeyum_ir::Rational;
use axeyum_ir::poly::{sylvester_determinant, sylvester_determinant_leibniz};

/// A tiny deterministic xorshift PRNG (no external dep, reproducible).
struct Rng(u64);

impl Rng {
    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    /// A non-negative value reduced into `0..bound`.
    fn below(&mut self, bound: u64) -> u64 {
        self.next_u64() % bound
    }

    /// A small signed integer in `[-range, range]` (`range > 0`).
    fn small(&mut self, range: i128) -> i128 {
        let span = u64::try_from(2 * range + 1).unwrap();
        i128::from(self.below(span)) - range
    }
}

/// A random LSB-first rational polynomial of degree `< max_len` (length in
/// `0..=max_len`), small integer coefficients. May be the empty/zero polynomial.
fn rand_poly(rng: &mut Rng, max_len: usize) -> Vec<Rational> {
    let len = usize::try_from(rng.below(u64::try_from(max_len + 1).unwrap())).unwrap();
    let mut p = Vec::with_capacity(len);
    for _ in 0..len {
        // Occasionally a rational (denominator 2 or 3) to exercise the field.
        let num = rng.small(4);
        let den = match rng.below(3) {
            0 => 1,
            1 => 2,
            _ => 3,
        };
        p.push(Rational::checked_new(num, den).unwrap());
    }
    p
}

/// A random `dim × dim` matrix of small rational polynomials.
fn rand_matrix(rng: &mut Rng, dim: usize, max_len: usize) -> Vec<Vec<Vec<Rational>>> {
    (0..dim)
        .map(|_| (0..dim).map(|_| rand_poly(rng, max_len)).collect())
        .collect()
}

/// Trim trailing zero coefficients so two representations of the same polynomial
/// (different vector lengths) compare equal.
fn trim(mut p: Vec<Rational>) -> Vec<Rational> {
    while p.last().is_some_and(|c| c.is_zero()) {
        p.pop();
    }
    p
}

#[test]
fn eval_interp_determinant_matches_leibniz_on_random_matrices() {
    let mut rng = Rng(0x5eed_1234_abcd_ef01);
    let mut checked = 0usize;
    let mut agreed = 0usize;
    let mut declines = 0usize;

    // Dimensions 1..=6 (factorial-bounded reference), small-degree entries.
    for dim in 1..=6usize {
        // Many trials per dimension; fewer for the larger (slower Leibniz) dims.
        let trials = if dim <= 4 { 400 } else { 120 };
        for _ in 0..trials {
            let max_len = 1 + usize::try_from(rng.below(3)).unwrap(); // entries degree < 3
            let mat = rand_matrix(&mut rng, dim, max_len);
            let fast = sylvester_determinant(&mat);
            let slow = sylvester_determinant_leibniz(&mat);
            checked += 1;
            match (fast, slow) {
                (Some(a), Some(b)) => {
                    assert_eq!(
                        trim(a),
                        trim(b),
                        "eval-interp determinant disagreed with Leibniz on dim {dim}: {mat:?}"
                    );
                    agreed += 1;
                }
                // Overflow must be the SAME shape only loosely: if one declines we
                // skip (small coeffs here make overflow vanishingly unlikely). We
                // still record it for visibility.
                _ => declines += 1,
            }
        }
    }

    assert!(
        checked >= 1800,
        "expected a large differential sample, got {checked}"
    );
    assert_eq!(
        declines, 0,
        "small-coefficient matrices should never overflow; {declines} declined of {checked}"
    );
    // Every checked pair agreed exactly.
    assert_eq!(agreed, checked, "{agreed}/{checked} pairs agreed");
}

/// Pin a few explicit known determinants (independent hand-checks) so a uniform
/// bug in BOTH routes (which the random cross-check could miss) is still caught.
#[test]
fn eval_interp_determinant_known_values() {
    // 2×2 constant matrix [[2,3],[4,5]] ⇒ det = 2·5 − 3·4 = -2.
    let m = vec![
        vec![vec![Rational::integer(2)], vec![Rational::integer(3)]],
        vec![vec![Rational::integer(4)], vec![Rational::integer(5)]],
    ];
    assert_eq!(
        trim(sylvester_determinant(&m).unwrap()),
        vec![Rational::integer(-2)]
    );

    // 2×2 with x-polynomials: [[x, 1],[1, x]] ⇒ det = x² − 1 ⇒ [-1, 0, 1].
    let x = vec![Rational::zero(), Rational::integer(1)];
    let one = vec![Rational::integer(1)];
    let m = vec![vec![x.clone(), one.clone()], vec![one.clone(), x.clone()]];
    assert_eq!(
        trim(sylvester_determinant(&m).unwrap()),
        vec![
            Rational::integer(-1),
            Rational::zero(),
            Rational::integer(1)
        ]
    );

    // Diagonal [[x+1,0],[0,x+2]] ⇒ (x+1)(x+2) = x² + 3x + 2 ⇒ [2,3,1].
    let xp1 = vec![Rational::integer(1), Rational::integer(1)];
    let xp2 = vec![Rational::integer(2), Rational::integer(1)];
    let zero = vec![Rational::zero()];
    let m = vec![vec![xp1, zero.clone()], vec![zero, xp2]];
    assert_eq!(
        trim(sylvester_determinant(&m).unwrap()),
        vec![
            Rational::integer(2),
            Rational::integer(3),
            Rational::integer(1)
        ]
    );
}
