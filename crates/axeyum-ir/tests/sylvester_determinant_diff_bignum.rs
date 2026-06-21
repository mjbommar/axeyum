//! Differential test for the BIGNUM Sylvester determinant: the fast
//! evaluation–interpolation route (`big_determinant`) vs the reference Leibniz
//! expansion (`big_determinant_leibniz`), on many small random polynomial
//! matrices over `BigRational`. Runs only with the `bignum` feature.
//!
//! Same soundness rationale as the `i128`/`Rational` differential test: the
//! determinant IS the resultant polynomial; the two routes must agree exactly.

#![cfg(feature = "bignum")]

use axeyum_ir::poly_big::{big_determinant, big_determinant_leibniz};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Zero;

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

    fn below(&mut self, bound: u64) -> u64 {
        self.next_u64() % bound
    }

    fn small(&mut self, range: i64) -> i64 {
        let span = u64::try_from(2 * range + 1).unwrap();
        i64::try_from(self.below(span)).unwrap() - range
    }
}

fn rat(num: i64, den: i64) -> BigRational {
    BigRational::new(BigInt::from(num), BigInt::from(den))
}

fn rand_poly(rng: &mut Rng, max_len: usize) -> Vec<BigRational> {
    let len = usize::try_from(rng.below(u64::try_from(max_len + 1).unwrap())).unwrap();
    (0..len)
        .map(|_| {
            let num = rng.small(4);
            let den = match rng.below(3) {
                0 => 1,
                1 => 2,
                _ => 3,
            };
            rat(num, den)
        })
        .collect()
}

fn rand_matrix(rng: &mut Rng, dim: usize, max_len: usize) -> Vec<Vec<Vec<BigRational>>> {
    (0..dim)
        .map(|_| (0..dim).map(|_| rand_poly(rng, max_len)).collect())
        .collect()
}

fn trim(mut p: Vec<BigRational>) -> Vec<BigRational> {
    while p.last().is_some_and(BigRational::is_zero) {
        p.pop();
    }
    p
}

#[test]
fn big_eval_interp_determinant_matches_leibniz_on_random_matrices() {
    let mut rng = Rng(0x1357_9bdf_2468_ace0);
    let mut checked = 0usize;

    for dim in 1..=6usize {
        let trials = if dim <= 4 { 300 } else { 100 };
        for _ in 0..trials {
            let max_len = 1 + usize::try_from(rng.below(3)).unwrap();
            let mat = rand_matrix(&mut rng, dim, max_len);
            let fast = trim(big_determinant(&mat));
            let slow = trim(big_determinant_leibniz(&mat));
            assert_eq!(
                fast, slow,
                "bignum eval-interp determinant disagreed with Leibniz on dim {dim}: {mat:?}"
            );
            checked += 1;
        }
    }

    assert!(
        checked >= 1400,
        "expected a large differential sample, got {checked}"
    );
}

#[test]
fn big_eval_interp_determinant_known_values() {
    // [[x, 1],[1, x]] ⇒ x² − 1.
    let x = vec![rat(0, 1), rat(1, 1)];
    let one = vec![rat(1, 1)];
    let m = vec![vec![x.clone(), one.clone()], vec![one, x]];
    assert_eq!(
        trim(big_determinant(&m)),
        vec![rat(-1, 1), rat(0, 1), rat(1, 1)]
    );
}
