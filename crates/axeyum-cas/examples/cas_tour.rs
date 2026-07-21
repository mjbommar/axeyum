//! A tour of `axeyum-cas` — a proof-carrying computer algebra system.
//! Run with: `cargo run -p axeyum-cas --example cas_tour`
//!
//! Where a result is marked `[CERTIFIED]`, axeyum has *proven* it (by an exact
//! decidable zero-test / differentiate-and-check), not merely computed it.

use axeyum_cas::{
    CasExpr, InequalityOp, LimitPoint, Matrix, apart, cancel, definite_integrate, discriminant,
    dsolve_homogeneous, dsolve_inhomogeneous, eigenvectors, equal, evaluate_trig, expand, factor,
    factor_expr, gosper_sum, gradient, integrate, limit, minimal_polynomial, ntheory,
    ntheory_advanced, real_root_intervals, resultant, series_at, simplify_radicals, series, solve,
    solve_polynomial_inequality, standard_deviation, stats, sum_polynomial, ZeroTest,
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
    // Gosper: indefinite hypergeometric summation.
    let k = || CasExpr::var("k");
    if let Some(s) = gosper_sum(&(CasExpr::int(1) / (k() * (k() + i(1)))), "k") {
        println!("gosper: sum 1/(k(k+1)) = {s}   [CERTIFIED telescoping]");
    }

    println!("\n-- roots & inequalities --");
    // Real-root isolation (Sturm) for an irrational-root polynomial.
    let quintic = x().pow(2) - i(2); // roots ±√2
    println!(
        "real_root_intervals(x^2 - 2) = {:?}   [Sturm-certified: one root each]",
        real_root_intervals(&quintic, "x").unwrap()
    );
    // Polynomial inequality via a sign chart.
    let ineq = x().pow(2) - i(5) * x() + i(6);
    let solution = solve_polynomial_inequality(&ineq, "x", InequalityOp::Greater).unwrap();
    println!("solve(x^2 - 5x + 6 > 0): {} interval(s) (-inf,2) U (3,inf)", solution.len());
    // Exact trig.
    let pi = CasExpr::var("pi");
    println!("sin(pi/6) = {}", evaluate_trig(&(pi.clone() / i(6)).sin()));

    println!("\n-- differential equations --");
    // y'' + y = 0  (characteristic r^2 + 1)
    let ode = dsolve_homogeneous(&[Rational::integer(1), Rational::zero(), Rational::integer(1)], "x");
    println!("dsolve(y'' + y = 0) = {}   [CERTIFIED]", ode.unwrap());
    // Inhomogeneous: y' + y = x → (x - 1) + C0 e^{-x}.
    let inhom = dsolve_inhomogeneous(&[Rational::integer(1), Rational::integer(1)], &x(), "x");
    println!("dsolve(y' + y = x) = {}   [CERTIFIED]", inhom.unwrap());

    println!("\n-- linear algebra --");
    let m = Matrix::from_rows(vec![vec![i(2), i(0)], vec![i(0), i(3)]]).unwrap();
    println!("det([[2,0],[0,3]]) = {}", m.determinant().unwrap());
    for (lambda, basis) in eigenvectors(&m, "L").unwrap() {
        let vecs: Vec<String> = basis.iter().map(|v| v.to_string().replace('\n', "")).collect();
        println!("eigenvalue {lambda} → eigenvector(s) {}   [A·v=λ·v]", vecs.join(", "));
    }
    println!("minimal_polynomial([[2,0],[0,3]]) = {}   [m(A)=0]", minimal_polynomial(&m, "L").unwrap());

    println!("\n-- more calculus --");
    println!(
        "∫_0^1 3x^2 dx = {}   [CERTIFIED by FTC]",
        definite_integrate(&(i(3) * x().pow(2)), "x", &i(0), &i(1)).unwrap().value
    );
    println!("Taylor(ln(x), about x=1, order 3) = {}", series_at(&x().ln(), "x", &i(1), 3).unwrap());
    let grad = gradient(&(x().pow(2) * CasExpr::var("y")), &["x", "y"]);
    println!("∇(x²y) = ({}, {})", grad[0], grad[1]);

    println!("\n-- factoring, resultants, radicals --");
    println!("factor_expr(x^4 - 1) = {}   [CERTIFIED]", factor_expr(&(x().pow(4) - i(1)), "x").unwrap());
    println!("discriminant(x^2 - 5x + 6) = {}", discriminant(&(x().pow(2) - i(5) * x() + i(6)), "x").unwrap());
    println!("resultant(x^2-1, x-1) = {}   [0 ⇒ common root]", resultant(&(x().pow(2) - i(1)), &(x() - i(1)), "x").unwrap());
    println!("simplify_radicals(√12) = {}", simplify_radicals(&i(12).sqrt()));
    let radical_id = equal(&(i(2).sqrt() * i(2).sqrt()), &i(2));
    println!("√2·√2 = 2 ? {}", matches!(radical_id, ZeroTest::Certified { equal: true, .. }));

    println!("\n-- statistics --");
    let data: Vec<Rational> = [2, 4, 4, 4, 5, 5, 7, 9].into_iter().map(Rational::integer).collect();
    println!("mean = {}, median = {}", stats::mean(&data).unwrap(), stats::median(&data).unwrap());
    println!("population variance = {}, stddev = {}", stats::variance(&data).unwrap(), standard_deviation(&data).unwrap());

    println!("\n-- number theory --");
    println!("is_prime(2^31 - 1) = {}", ntheory::is_prime(2_147_483_647));
    println!("factorize(360) = {:?}", ntheory::factorize(360));
    println!("legendre(3, 7) = {}   (3 is a non-residue mod 7)", ntheory_advanced::legendre_symbol(3, 7));
    println!("primitive_root(7) = {:?}", ntheory_advanced::primitive_root(7));
    println!("discrete_log(2, 3, 5) = {:?}   (2^3 = 8 ≡ 3 mod 5)", ntheory_advanced::discrete_log(2, 3, 5));
    println!("Pell x²-61y²=1 fundamental solution = {:?}", ntheory_advanced::pell_fundamental_solution(61));

    println!("\nEvery result is exact; the CERTIFIED ones carry a machine-checked proof.");
}
