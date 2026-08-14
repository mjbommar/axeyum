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

use std::time::Instant;

use axeyum_cas::mvpoly::MvPoly;
use axeyum_cas::telescoping::{
    Factor, HyperTerm, Limits, LinearForm, TelescopingOutcome, binomial_factors, zeilberger,
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

fn main() {
    println!("creative-telescoping search cost (release build)\n");

    let options = CheckOptions::over("n", &[0, 1, 2, 3, 4, 5, 6, 7], (-2, 14));
    row(
        "sum_k C(n,k)",
        &HyperTerm::new(binomial_n_k(1)),
        "n",
        "k",
        &Limits::classical(),
        &options,
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

    // Apery-style: sum_k C(n,k)^2*C(n+k,k)^2 -- the summand of Apery's proof
    // that zeta(3) is irrational. This row DECLINES, and the reason is recorded
    // rather than hidden: the derived degree bound is 2, which is exactly the
    // degree at which the certificate exists (checked independently), so the
    // search design is not the problem. What fails is `MvPoly::gcd` -- the
    // primitive-PRS pseudo-remainder overflows `i128` on the degree-8 shift
    // quotient this term produces. The binding constraint on this route is now
    // the polynomial coefficient type, not the algorithm.
    let mut apery = binomial_n_k(2);
    apery.extend(binomial_factors(
        &form(&[("n", 1), ("k", 1)], 0),
        &form(&[("k", 1)], 0),
        2,
    ));
    row(
        "sum_k C(n,k)^2*C(n+k,k)^2  (Apery, order 2)",
        &HyperTerm::new(apery),
        "n",
        "k",
        &Limits::classical(),
        &CheckOptions::over("n", &[0, 1, 2, 3, 4], (-2, 10)),
    );

    // sum_k C(m,k)*C(n,k) = C(m+n,n): a second Vandermonde form, symbolic in m.
    let mut cross = binomial_factors(&form(&[("m", 1)], 0), &form(&[("k", 1)], 0), 1);
    cross.extend(binomial_factors(
        &form(&[("n", 1)], 0),
        &form(&[("k", 1)], 0),
        1,
    ));
    row(
        "sum_k C(m,k)*C(n,k)",
        &HyperTerm::new(cross),
        "n",
        "k",
        &Limits::classical(),
        &CheckOptions::over("n", &[0, 1, 2, 3, 4], (-2, 12)).with("m", &[3, 5, 7]),
    );
}
