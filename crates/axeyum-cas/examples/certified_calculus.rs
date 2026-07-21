//! A runnable demonstration of axeyum's proof-carrying computer algebra:
//! **compute like a CAS, and certify like a proof engine, in one step.**
//!
//! Run with: `cargo run -p axeyum-cas --example certified_calculus`

use axeyum_cas::{CasExpr, ZeroTest, cancel, equal, expand, integrate};

fn v(name: &str) -> CasExpr {
    CasExpr::var(name)
}

fn main() {
    println!("axeyum CAS — compute + certify\n");

    // 1. Differentiation, then *decide* it against a claimed answer.
    let f = v("x").pow(2) + v("c"); // x^2 + c
    let df = expand(&f.differentiate("x")).expect("polynomial");
    print!("d/dx ({f}) = {df}");
    match equal(&df, &(CasExpr::int(2) * v("x"))) {
        ZeroTest::Certified { equal: true, .. } => println!("   [= 2*x, CERTIFIED]"),
        _ => println!("   [not certified]"),
    }

    // 2. Integration that hands back its own proof.
    let integrand = CasExpr::int(3) * v("x").pow(2) + CasExpr::int(2) * v("x");
    let integral = integrate(&integrand, "x").expect("polynomial");
    println!(
        "\n∫ ({integrand}) dx = {}   [{}]",
        integral.antiderivative,
        if integral.is_certified() {
            "CERTIFIED by differentiate-and-check"
        } else {
            "unverified"
        }
    );

    // 2b. A rational integral, still returned with a proof (Horowitz reduction).
    let rational = CasExpr::int(1) / v("x").pow(2);
    let rat_integral = integrate(&rational, "x").expect("rational antiderivative");
    println!(
        "∫ (1/x^2) dx = {}   [{}]",
        rat_integral.antiderivative,
        if rat_integral.is_certified() {
            "CERTIFIED"
        } else {
            "unverified"
        }
    );

    // 2c. A logarithmic integral — the answer leaves the rational fragment but
    //     is still certified (d/dx ln(x) = 1/x is rational).
    let log_integrand = CasExpr::int(1) / v("x");
    let log_integral = integrate(&log_integrand, "x").expect("logarithmic integral");
    println!(
        "∫ (1/x) dx = {}   [{}]",
        log_integral.antiderivative,
        if log_integral.is_certified() {
            "CERTIFIED"
        } else {
            "unverified"
        }
    );

    // 3. Expand and cancel (canonical forms).
    let cubed = expand(&(v("x") + CasExpr::int(1)).pow(3)).expect("polynomial");
    println!("\nexpand((x + 1)^3) = {cubed}");
    let reduced = cancel(&((v("x").pow(2) - CasExpr::int(1)) / (v("x") - CasExpr::int(1))))
        .expect("rational");
    println!("cancel((x^2 - 1)/(x - 1)) = {reduced}");

    println!("\nEvery result above is decided by exact arithmetic; nothing is trusted.");
}
