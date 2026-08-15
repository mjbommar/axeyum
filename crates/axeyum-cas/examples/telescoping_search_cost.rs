//! Measured search cost of the creative-telescoping engine, identity by identity.
//!
//! The point of this example is a number, not a demonstration: the lane that
//! opened this domain reported that the search cost was dominated by the *degree
//! sweep* rather than by the linear algebra, and that Chu-Vandermonde took ~250 s
//! on default limits against seconds on hand-tightened ones. This binary is what
//! makes that claim, and any later claim about it, reproducible.
//!
//! ```sh
//! cargo run -p axeyum-cas --release --example telescoping_search_cost
//! ```
//!
//! Every row runs the untrusted search and then the independent checker, so a
//! fast search that produces garbage shows up as `REJECTED`, not as a win.
//!
//! # The second table
//!
//! The search's binding constraint was, for a while, not the search at all: it
//! was the width of the coefficients `MvPoly::gcd` passed through while reducing
//! a shift quotient. The second table measures that directly with
//! `MvPoly::gcd_cost`, against the reference value **127** — the bits an `i128`
//! numerator holds. A row whose peak exceeds 127 is a GCD that *cannot* be run in
//! a fixed-width `i128`, and every such row declined before the GCD moved into
//! the unbounded-integer ring. Reporting the peak rather than a verdict is the
//! point: it is a number about the polynomials, not about a type.

use std::time::Instant;

use axeyum_cas::mvpoly::MvPoly;
use axeyum_cas::telescoping::{
    Factor, HyperTerm, Limits, LinearForm, RationalFunction, TelescopingOutcome, binomial_factors,
    shift_variable, zeilberger,
};
use axeyum_cas::telescoping_check::{CheckOptions, Verdict, check_certificate};
use axeyum_ir::Rational;

fn form(terms: &[(&str, i64)], constant: i64) -> LinearForm {
    LinearForm::new(terms, constant)
}

/// `C(n,k)^power`.
fn binomial_n_k(power: i32) -> Vec<Factor> {
    binomial_factors(&form(&[("n", 1)], 0), &form(&[("k", 1)], 0), power)
}

/// Time one search, verify the result, and print a single row.
fn row(
    label: &str,
    term: &HyperTerm,
    shift_var: &str,
    sum_var: &str,
    limits: &Limits,
    options: &CheckOptions,
) {
    let started = Instant::now();
    let outcome = zeilberger(term, shift_var, sum_var, limits);
    let search = started.elapsed();
    match outcome {
        TelescopingOutcome::Found(certificate) => {
            let checking = Instant::now();
            let verdict = check_certificate(&certificate, options);
            let check = checking.elapsed();
            let status = if verdict.is_verified() {
                "verified"
            } else {
                "REJECTED"
            };
            println!(
                "{label:<44} order {}  search {:>9.3?}  check {:>9.3?}  {status}",
                certificate.order(),
                search,
                check
            );
            if let Verdict::Rejected(reasons) = &verdict {
                for reason in reasons {
                    println!("    {reason}");
                }
            }
        }
        TelescopingOutcome::Declined => {
            println!("{label:<44} declined                search {search:>9.3?}");
        }
    }
}

/// The four single-binomial identities: order-1 certificates, milliseconds each.
fn classical_rows() {
    row(
        "sum_k C(n,k)",
        &HyperTerm::new(binomial_n_k(1)),
        "n",
        "k",
        &Limits::classical(),
        &CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6, 7], (-2, 14)),
    );

    let mut alternating = vec![Factor::Power {
        base: Rational::integer(-1),
        form: form(&[("k", 1)], 0),
    }];
    alternating.extend(binomial_n_k(1));
    row(
        "sum_k (-1)^k C(n,k)",
        &HyperTerm::new(alternating),
        "n",
        "k",
        &Limits::classical(),
        &CheckOptions::over("n", &[1, 2, 3, 4, 5, 6, 7], (-2, 14)),
    );

    row(
        "sum_k C(n,k)^2",
        &HyperTerm::new(binomial_n_k(2)),
        "n",
        "k",
        &Limits::classical(),
        &CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6], (-2, 12)),
    );

    let mut weighted = vec![Factor::Poly {
        poly: MvPoly::var("k"),
        exponent: 1,
    }];
    weighted.extend(binomial_n_k(1));
    row(
        "sum_k k*C(n,k)",
        &HyperTerm::new(weighted),
        "n",
        "k",
        &Limits::classical(),
        &CheckOptions::over("n", &[1, 2, 3, 4, 5, 6, 7], (-2, 14)),
    );
}

fn main() {
    println!("creative-telescoping search cost (release build)\n");
    classical_rows();

    // Chu-Vandermonde: four variables, and the identity the previous lane had to
    // hand-tighten to get an answer in finite time.
    let mut convolution = binomial_factors(&form(&[("m", 1)], 0), &form(&[("k", 1)], 0), 1);
    convolution.extend(binomial_factors(
        &form(&[("n", 1)], 0),
        &form(&[("p", 1), ("k", -1)], 0),
        1,
    ));
    let convolution = HyperTerm::new(convolution);
    let convolution_options = CheckOptions::over("p", &[0, 1, 2, 3, 4], (-2, 12))
        .with("m", &[3, 5])
        .with("n", &[4, 6]);
    row(
        "sum_k C(m,k)*C(n,p-k)  (Chu-Vandermonde)",
        &convolution,
        "p",
        "k",
        &Limits::classical(),
        &convolution_options,
    );

    // Franel numbers: sum_k C(n,k)^3 needs a SECOND-order recurrence, which the
    // sweep-based search could not afford.
    row(
        "sum_k C(n,k)^3  (Franel, order 2)",
        &HyperTerm::new(binomial_n_k(3)),
        "n",
        "k",
        &Limits::classical(),
        &CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6], (-2, 14)),
    );

    // Apery: sum_k C(n,k)^2*C(n+k,k)^2, the summand of Apery's proof that
    // zeta(3) is irrational. This row DECLINED until the GCD moved into the
    // unbounded-integer ring: the derived degree bound is 2, which is exactly
    // the degree at which the certificate exists, so the search design was never
    // the problem -- the primitive-PRS pseudo-remainder overflowed `i128` on the
    // degree-8 shift quotient. The second table puts a number on it: that
    // sequence passed through a 4187-bit coefficient, against the 127 bits an
    // i128 numerator holds, to produce a GCD whose own coefficients fit in 3.
    // What comes back is Apery's own recurrence,
    //   (n+1)^3, -(2n+3)(17n^2+51n+39), (n+2)^3.
    //
    // The check window starts at k = 0 rather than k = -2: the summand is not
    // evaluable at a negative k when n = 0 (C(n+k,k) becomes C(-1,-1)), so the
    // checker refuses the window edge there -- correctly, and loudly. The
    // certificate's numerator carries a factor k^4, so G still vanishes at the
    // k = 0 edge, which is what the boundary layer actually needs.
    let mut apery = binomial_n_k(2);
    apery.extend(binomial_factors(
        &form(&[("n", 1), ("k", 1)], 0),
        &form(&[("k", 1)], 0),
        2,
    ));
    let apery = HyperTerm::new(apery);
    row(
        "sum_k C(n,k)^2*C(n+k,k)^2  (Apery, order 2)",
        &apery,
        "n",
        "k",
        &Limits::classical(),
        &CheckOptions::over("n", &[0, 1, 2, 3, 4, 5], (0, 12)),
    );

    // sum_k C(m,k)*C(n,k) = C(m+n,n): a second Vandermonde form, symbolic in m.
    let mut cross = binomial_factors(&form(&[("m", 1)], 0), &form(&[("k", 1)], 0), 1);
    cross.extend(binomial_factors(
        &form(&[("n", 1)], 0),
        &form(&[("k", 1)], 0),
        1,
    ));
    let cross = HyperTerm::new(cross);
    row(
        "sum_k C(m,k)*C(n,k)",
        &cross,
        "n",
        "k",
        &Limits::classical(),
        &CheckOptions::over("n", &[0, 1, 2, 3, 4], (-2, 12)).with("m", &[3, 5, 7]),
    );

    growth_table(&convolution, &cross, &apery);
}

/// The second table: what the GCD inside the search actually costs in
/// coefficient width, identity by identity.
fn growth_table(convolution: &HyperTerm, cross: &HyperTerm, apery: &HyperTerm) {
    println!("\nGCD coefficient growth on the shift quotient the search reduces");
    println!("(bits of the widest coefficient magnitude; an i128 numerator holds 127.");
    println!(" `was` is the peak of the same sequence WITHOUT the per-step content");
    println!(" division -- what the previous i128 primitive PRS actually computed, so");
    println!(" `was > 127` is a measured proof that this GCD could not finish before.)\n");
    println!(
        "{:<44} {:>5} {:>5} {:>6} {:>6} {:>5} {:>6}",
        "identity", "order", "in", "was", "peak", "out", "steps"
    );
    growth("sum_k C(n,k)", &HyperTerm::new(binomial_n_k(1)), "n", "k");
    growth("sum_k C(n,k)^2", &HyperTerm::new(binomial_n_k(2)), "n", "k");
    growth(
        "sum_k C(n,k)^3  (Franel)",
        &HyperTerm::new(binomial_n_k(3)),
        "n",
        "k",
    );
    growth(
        "sum_k C(m,k)*C(n,p-k)  (Chu-Vandermonde)",
        convolution,
        "p",
        "k",
    );
    growth("sum_k C(m,k)*C(n,k)", cross, "n", "k");
    growth("sum_k C(n,k)^2*C(n+k,k)^2  (Apery)", apery, "n", "k");
}

/// Measure the GCD the search performs on the shift quotient at each order.
///
/// This mirrors the first half of `attempt_order`: the shift ratios are put over
/// a common denominator `D`, and the known part of the Gosper shift quotient
/// `rho = r(k)*D(k)/D(k+1)` is reduced. That reduction is the GCD that used to
/// decide whether the whole search could proceed.
fn growth(label: &str, term: &HyperTerm, shift_var: &str, sum_var: &str) {
    let Some(current) = term.shift_ratio(sum_var, 1) else {
        println!("{label:<44}  no shift ratio in {sum_var}");
        return;
    };
    let mut outer: Vec<RationalFunction> = Vec::new();
    for order in 0..=2i64 {
        let Some(next) = term.shift_ratio(shift_var, order) else {
            return;
        };
        outer.push(next);

        // D = lcm of the shift-ratio denominators seen so far.
        let mut common = MvPoly::constant(Rational::integer(1));
        for ratio in &outer {
            let Some(shared) = common.gcd(&ratio.denominator) else {
                println!("{label:<44} {order:>5}  lcm GCD declined");
                return;
            };
            let Some(next) = common
                .mul(&ratio.denominator)
                .and_then(|product| product.exact_div(&shared))
            else {
                println!("{label:<44} {order:>5}  lcm product declined");
                return;
            };
            common = next;
        }

        let Some(advanced) = shift_variable(&common, sum_var, 1) else {
            return;
        };
        let (Some(numerator), Some(denominator)) = (
            current.numerator.mul(&common),
            current.denominator.mul(&advanced),
        ) else {
            println!("{label:<44} {order:>5}  rho product overflowed i128");
            continue;
        };
        let cost = numerator.gcd_cost(&denominator);
        let note = if !cost.fits_i128 {
            "ANSWER exceeds i128"
        } else if cost.peak_bits > 127 {
            "needs the big ring"
        } else if cost.legacy_peak_bits > 127 {
            "declined before"
        } else {
            ""
        };
        println!(
            "{label:<44} {order:>5} {:>5} {:>6} {:>6} {:>5} {:>6}  {note}",
            cost.input_bits, cost.legacy_peak_bits, cost.peak_bits, cost.result_bits, cost.steps
        );
    }
}
