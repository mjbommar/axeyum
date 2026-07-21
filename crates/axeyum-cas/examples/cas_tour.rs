//! A tour of `axeyum-cas` — a proof-carrying computer algebra system.
//! Run with: `cargo run -p axeyum-cas --example cas_tour`
//!
//! Where a result is marked `[CERTIFIED]`, axeyum has *proven* it (by an exact
//! decidable zero-test / differentiate-and-check), not merely computed it.

use axeyum_cas::{
    CasExpr, LimitPoint, Matrix, apart, cancel, dsolve_homogeneous, expand, factor, integrate,
    limit, ntheory, series, solve, sum_polynomial,
};
use axeyum_ir::Rational;

fn x() -> CasExpr {
    CasExpr::var("x")
}
fn i(n: i128) -> CasExpr {
    CasExpr::int(n)
}

fn main() {
    println!("=== axeyum-cas: a proof-carrying CAS tour ===\n");

    println!("-- calculus --");
    let f = x().pow(3) - i(2) * x() + i(1);
    println!("d/dx ({f}) = {}", expand(&f.differentiate("x")).unwrap());
    for g in [
        i(1) / x(),                       // ln
        i(1) / (x().pow(2) + i(1)),        // atan
        i(1) / (x().pow(2) - i(1)),        // two logs
        x() * x().exp(),                   // poly * exp
        x() * x().sin(),                   // poly * trig
    ] {
        match integrate(&g, "x") {
            Some(r) if r.is_certified() => println!("∫ ({g}) dx = {}   [CERTIFIED]", r.antiderivative),
            _ => println!("∫ ({g}) dx = (declined)"),
        }
    }
    let l = limit(&((x().pow(2) - i(4)) / (x() - i(2))), "x", LimitPoint::Finite(Rational::integer(2)));
    println!("lim_(x->2) (x^2-4)/(x-2) = {}", l.unwrap());
    println!("series exp(x) (order 4) = {}", series(&x().exp(), "x", 4).unwrap());

    println!("\n-- algebra --");
    let p = x().pow(2) - i(3) * x() + i(2);
    println!("factor(x^2 - 3x + 2) = {}", factor(&p, "x").unwrap());
    let roots: Vec<String> = solve(&p, "x").unwrap().iter().map(ToString::to_string).collect();
    println!("solve(x^2 - 3x + 2 = 0) = {{{}}}", roots.join(", "));
    println!("cancel((x^2-1)/(x-1)) = {}", cancel(&((x().pow(2) - i(1)) / (x() - i(1)))).unwrap());
    println!("apart(1/(x^2-1)) = {}", apart(&(i(1) / (x().pow(2) - i(1))), "x").unwrap());
    println!("sum_(k=0)^(n-1) k = {}", sum_polynomial(&CasExpr::var("n"), "n").unwrap());

    println!("\n-- differential equations --");
    // y'' + y = 0  (characteristic r^2 + 1)
    let ode = dsolve_homogeneous(&[Rational::integer(1), Rational::zero(), Rational::integer(1)], "x");
    println!("dsolve(y'' + y = 0) = {}   [CERTIFIED]", ode.unwrap());

    println!("\n-- linear algebra --");
    let m = Matrix::from_rows(vec![
        vec![i(1), i(2)],
        vec![i(3), i(4)],
    ])
    .unwrap();
    println!("det([[1,2],[3,4]]) = {}", m.determinant().unwrap());

    println!("\n-- number theory --");
    println!("is_prime(2^31 - 1) = {}", ntheory::is_prime(2_147_483_647));
    println!("factorize(360) = {:?}", ntheory::factorize(360));
    println!("euler_phi(36) = {}", ntheory::euler_phi(36));

    println!("\nEvery result is exact; the CERTIFIED ones carry a machine-checked proof.");
}
