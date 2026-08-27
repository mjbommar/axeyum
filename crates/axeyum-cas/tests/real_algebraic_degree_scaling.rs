//! Cost-curve measurement for the `real_algebraic` module (ADR-0601): how
//! isolation, bridging, and field arithmetic scale with polynomial degree.
//!
//! `#[ignore]`d because wall-clock numbers are not a pass/fail gate (see
//! CLAUDE.md's rule against load-sensitive assertions) — run explicitly with
//! `cargo test -p axeyum-cas --test real_algebraic_degree_scaling -- --ignored --nocapture`
//! and read the printed timings. The scaling *shape* (not the absolute
//! numbers, which are host-load-sensitive) is the deliverable: this is a
//! measurement tool, not a ratchet.

use std::time::Instant;

use axeyum_cas::algebraic::real_roots;
use axeyum_cas::real_algebraic::{self, algebraic_eq};
use axeyum_ir::Rational;

fn poly_from(coeffs: &[i128]) -> Vec<Rational> {
    coeffs.iter().map(|&c| Rational::integer(c)).collect()
}

/// `x^n - 2` (LSB-first): irreducible over ℚ by Eisenstein at 2, one positive
/// real root `2^(1/n)`, exercising isolation at exactly degree `n`.
fn x_pow_n_minus_2(n: usize) -> Vec<Rational> {
    let mut coeffs = vec![0i128; n + 1];
    coeffs[0] = -2;
    coeffs[n] = 1;
    poly_from(&coeffs)
}

#[test]
#[ignore = "wall-clock measurement, not a pass/fail gate; run explicitly"]
fn isolation_and_bridging_cost_by_degree() {
    println!(
        "degree | isolate_real_roots (algebraic.rs) | bridge to RealAlgebraic (real_algebraic.rs)"
    );
    for &n in &[2usize, 3, 5, 8, 10, 12, 15, 20] {
        let p = x_pow_n_minus_2(n);

        let t0 = Instant::now();
        let roots = real_roots(&p).unwrap();
        let isolate_time = t0.elapsed();
        // x^n-2 has one real root (2^(1/n)) for odd n, and two (+-2^(1/n)) for
        // even n; either way exactly one is the positive root, sorted last
        // (ascending order).
        let expected_count = if n % 2 == 0 { 2 } else { 1 };
        assert_eq!(roots.len(), expected_count, "x^{n}-2 real-root count");
        let positive_root = roots.last().unwrap();
        assert_eq!(
            positive_root.degree(),
            n,
            "x^{n}-2 is irreducible (Eisenstein at 2)"
        );

        let t1 = Instant::now();
        let bridged = real_algebraic::from_algebraic_real(positive_root);
        let bridge_time = t1.elapsed();
        assert!(bridged.is_some(), "bridging must not decline at degree {n}");

        println!(
            "{n:>6} | {:>12.3} ms | {:>12.3} ms",
            isolate_time.as_secs_f64() * 1000.0,
            bridge_time.as_secs_f64() * 1000.0,
        );
    }
}

#[test]
#[ignore = "wall-clock measurement, not a pass/fail gate; run explicitly"]
fn field_arithmetic_cost_by_operand_degree() {
    // sqrt2 (degree 2) combined via `add`/`mul` with the degree-n root of
    // x^n-2, measuring the resultant + squarefree + Sturm-isolation cost as
    // the OTHER operand's degree grows. The resultant is generically
    // degree `2*n`, so this is where coefficient blowup would show up first.
    let sqrt2_poly = poly_from(&[-2, 0, 1]);
    let sqrt2_roots = real_roots(&sqrt2_poly).unwrap();
    let sqrt2 = real_algebraic::from_algebraic_real(&sqrt2_roots[0]).unwrap();

    println!("operand degree | add (ms) | mul (ms) | algebraic_eq self-check (ms)");
    for &n in &[2usize, 3, 5, 8, 10, 12] {
        let p = x_pow_n_minus_2(n);
        let roots = real_roots(&p).unwrap();
        let other = real_algebraic::from_algebraic_real(&roots[0]).unwrap();

        let t0 = Instant::now();
        let sum = sqrt2.add(&other);
        let add_time = t0.elapsed();

        let t1 = Instant::now();
        let product = sqrt2.mul(&other);
        let mul_time = t1.elapsed();

        // Exercise algebraic_eq on the arithmetic result against itself, the
        // cheapest nontrivial GCD call available (poly degree up to 2n),
        // measuring the equality-test cost at the resulting degree.
        let eq_time = if let Some(sum_val) = &sum {
            let t2 = Instant::now();
            let result = algebraic_eq(sum_val, sum_val);
            let elapsed = t2.elapsed();
            assert_eq!(result, Some(true));
            elapsed
        } else {
            std::time::Duration::ZERO
        };

        println!(
            "{n:>14} | {:>8.3} | {:>8.3} | {:>8.3}  (add={}, mul={})",
            add_time.as_secs_f64() * 1000.0,
            mul_time.as_secs_f64() * 1000.0,
            eq_time.as_secs_f64() * 1000.0,
            sum.is_some(),
            product.is_some(),
        );
    }
}
