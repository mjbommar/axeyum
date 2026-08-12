//! Verify the algebraic content of the shell-construction proof with
//! **axeyum's own CAS**, exactly and symbolically in `a`, `b`, `T`.
//!
//! Every identity below is checked as a polynomial identity over Q: the
//! difference of the two sides is built in `MvPoly` and tested with
//! `is_zero()`. That is a proof for ALL values of the variables, not a
//! numeric sample. Symbolic exponents (`a^(k-1)` etc.) are handled by
//! instantiating the integer parameters `k` and `c` over a range while
//! keeping `a`, `b`, `T`, `s` symbolic.
//!
//! Negative controls are included: deliberately wrong variants must NOT
//! reduce to zero, otherwise the checker is vacuous.

use axeyum_cas::MvPoly;
use axeyum_ir::Rational;

fn c(n: i128) -> MvPoly {
    MvPoly::constant(Rational::new(n, 1))
}
fn v(name: &str) -> MvPoly {
    MvPoly::var(name)
}
fn add(x: &MvPoly, y: &MvPoly) -> MvPoly {
    x.add(y).expect("add")
}
fn sub(x: &MvPoly, y: &MvPoly) -> MvPoly {
    x.sub(y).expect("sub")
}
fn mul(x: &MvPoly, y: &MvPoly) -> MvPoly {
    x.mul(y).expect("mul")
}
fn powi(x: &MvPoly, e: u32) -> MvPoly {
    x.pow(e).expect("pow")
}

/// `Sigma_m = a + a^2 + ... + a^m`, with `Sigma_0 = 0`.
fn sigma(a: &MvPoly, m: i64) -> MvPoly {
    let mut acc = MvPoly::zero();
    for i in 1..=m.max(0) {
        acc = add(&acc, &powi(a, i as u32));
    }
    acc
}

/// `T = 1 + a + ... + a^(k-2-c)`, zero when `c = k-1`.
fn tpoly(a: &MvPoly, k: i64, cc: i64) -> MvPoly {
    let top = k - 2 - cc;
    let mut acc = MvPoly::zero();
    for i in 0..=top {
        if i < 0 {
            continue;
        }
        acc = add(&acc, &powi(a, i as u32));
    }
    acc
}

fn main() {
    let a = v("a");
    let b = v("b");
    let t = v("T");
    let mut checks = 0usize;
    let mut fails = 0usize;
    let mut report = |name: &str, diff: &MvPoly, want_zero: bool, checks: &mut usize, fails: &mut usize| {
        *checks += 1;
        let z = diff.is_zero();
        if z != want_zero {
            *fails += 1;
            println!("  FAIL {name}: is_zero = {z}, expected {want_zero}");
        }
    };

    // ---- Identity 1: (a-1) * Sigma_m = a^(m+1) - a  [eq:sigma] -------------
    println!("Identity 1  (a-1)*Sigma_m = a^(m+1) - a");
    for m in 1..=10i64 {
        let lhs = mul(&sub(&a, &c(1)), &sigma(&a, m));
        let rhs = sub(&powi(&a, (m + 1) as u32), &a);
        report(&format!("sigma m={m}"), &sub(&lhs, &rhs), true, &mut checks, &mut fails);
    }

    // ---- Identity 2: Sigma_{k-2} = Sigma_{c-1} + a^c * T  [the split] ------
    println!("Identity 2  Sigma_(k-2) = Sigma_(c-1) + a^c*T");
    for k in 3..=10i64 {
        for cc in 2..=(k - 1) {
            let lhs = sigma(&a, k - 2);
            let rhs = add(&sigma(&a, cc - 1), &mul(&powi(&a, cc as u32), &tpoly(&a, k, cc)));
            report(
                &format!("split k={k} c={cc}"),
                &sub(&lhs, &rhs),
                true,
                &mut checks,
                &mut fails,
            );
        }
    }

    // ---- Identity 3: THE LEMMA 4 CHAIN ------------------------------------
    // (N - 2c_c) - b*a^(c-1)*s_max
    //   where s_max = b*a^(k-1-c) + 2bT + 1, N - 2c_c = b*a^(k-1) + 2b*a^c*T
    // must equal  b*[ a^(k-2)*(a-b) + 2*a^(c-1)*T*(a-b) - a^(c-1) ].
    println!("Identity 3  Lemma 4 (shell gap) final chain");
    for k in 3..=10i64 {
        for cc in 2..=(k - 1) {
            let tt = tpoly(&a, k, cc);
            let n_minus = add(
                &mul(&b, &powi(&a, (k - 1) as u32)),
                &mul(&mul(&c(2), &b), &mul(&powi(&a, cc as u32), &tt)),
            );
            let s_max = add(
                &add(
                    &mul(&b, &powi(&a, (k - 1 - cc) as u32)),
                    &mul(&mul(&c(2), &b), &tt),
                ),
                &c(1),
            );
            let lhs = sub(&n_minus, &mul(&mul(&b, &powi(&a, (cc - 1) as u32)), &s_max));
            let amb = sub(&a, &b);
            let rhs = mul(
                &b,
                &sub(
                    &add(
                        &mul(&powi(&a, (k - 2) as u32), &amb),
                        &mul(&mul(&c(2), &mul(&powi(&a, (cc - 1) as u32), &tt)), &amb),
                    ),
                    &powi(&a, (cc - 1) as u32),
                ),
            );
            report(
                &format!("lemma4 k={k} c={cc}"),
                &sub(&lhs, &rhs),
                true,
                &mut checks,
                &mut fails,
            );
        }
    }

    // ---- Identity 4: Lemma 5 size bound at b = a-1 ------------------------
    // (a-1)*a^(k-1) + 2*(a-1)*Sigma_(k-2) = a^k + a^(k-1) - 2a
    println!("Identity 4  Lemma 5 (size) at b = a-1");
    for k in 2..=10i64 {
        let lhs = add(
            &mul(&sub(&a, &c(1)), &powi(&a, (k - 1) as u32)),
            &mul(&mul(&c(2), &sub(&a, &c(1))), &sigma(&a, k - 2)),
        );
        let rhs = sub(
            &add(&powi(&a, k as u32), &powi(&a, (k - 1) as u32)),
            &mul(&c(2), &a),
        );
        report(&format!("size k={k}"), &sub(&lhs, &rhs), true, &mut checks, &mut fails);
    }

    // ---- Identity 5: Lemma 4 slack at c = k-1 is b*a^(k-2)*(a-b-1) --------
    println!("Identity 5  Lemma 4 slack at c=k-1  ==  b*a^(k-2)*(a-b-1)   [vanishes iff b=a-1]");
    for k in 3..=10i64 {
        let cc = k - 1;
        let tt = tpoly(&a, k, cc); // == 0
        let amb = sub(&a, &b);
        let slack = mul(
            &b,
            &sub(
                &add(
                    &mul(&powi(&a, (k - 2) as u32), &amb),
                    &mul(&mul(&c(2), &mul(&powi(&a, (cc - 1) as u32), &tt)), &amb),
                ),
                &powi(&a, (cc - 1) as u32),
            ),
        );
        let want = mul(
            &mul(&b, &powi(&a, (k - 2) as u32)),
            &sub(&sub(&a, &b), &c(1)),
        );
        report(&format!("slack k={k}"), &sub(&slack, &want), true, &mut checks, &mut fails);
    }

    // ---- Identity 6: THEOREM 2 (the b>a counterexample family) ------------
    // N = b*(a^(k-1) + 2*Sigma_(k-2)),  W = a^(k-1) + 2*Sigma_(k-2) - a,
    // X = N - a*b + 1, Y = 1, Z = a*W.   Claim: a*(X - Y) = b*Z.
    println!("Identity 6  Theorem 2: a*(X-Y) = b*Z for the moving witness");
    for k in 3..=10i64 {
        let inner = add(&powi(&a, (k - 1) as u32), &mul(&c(2), &sigma(&a, k - 2)));
        let n = mul(&b, &inner);
        let w = sub(&inner, &a);
        let x_minus_y = sub(&n, &mul(&a, &b)); // (N - ab + 1) - 1
        let lhs = mul(&a, &x_minus_y);
        let rhs = mul(&b, &mul(&a, &w));
        report(&format!("thm2 k={k}"), &sub(&lhs, &rhs), true, &mut checks, &mut fails);
    }

    // ---- NEGATIVE CONTROLS: these must NOT be zero -----------------------
    println!("Negative controls (must NOT reduce to zero)");
    // wrong sigma: (a-1)*Sigma_m vs a^(m+1) - 1
    for m in 1..=4i64 {
        let lhs = mul(&sub(&a, &c(1)), &sigma(&a, m));
        let bad = sub(&powi(&a, (m + 1) as u32), &c(1));
        report(
            &format!("NEG sigma m={m}"),
            &sub(&lhs, &bad),
            false,
            &mut checks,
            &mut fails,
        );
    }
    // lemma 4 with the truncation dropped (s_max without the +1)
    for k in 4..=7i64 {
        let cc = 2i64;
        let tt = tpoly(&a, k, cc);
        let n_minus = add(
            &mul(&b, &powi(&a, (k - 1) as u32)),
            &mul(&mul(&c(2), &b), &mul(&powi(&a, cc as u32), &tt)),
        );
        let s_no_plus1 = add(
            &mul(&b, &powi(&a, (k - 1 - cc) as u32)),
            &mul(&mul(&c(2), &b), &tt),
        );
        let lhs = sub(&n_minus, &mul(&mul(&b, &powi(&a, (cc - 1) as u32)), &s_no_plus1));
        let amb = sub(&a, &b);
        let rhs = mul(
            &b,
            &sub(
                &add(
                    &mul(&powi(&a, (k - 2) as u32), &amb),
                    &mul(&mul(&c(2), &mul(&powi(&a, (cc - 1) as u32), &tt)), &amb),
                ),
                &powi(&a, (cc - 1) as u32),
            ),
        );
        report(
            &format!("NEG lemma4-no-truncation k={k}"),
            &sub(&lhs, &rhs),
            false,
            &mut checks,
            &mut fails,
        );
    }
    // theorem 2 with a sign slip in W
    for k in 3..=5i64 {
        let inner = add(&powi(&a, (k - 1) as u32), &mul(&c(2), &sigma(&a, k - 2)));
        let n = mul(&b, &inner);
        let w_bad = add(&inner, &a); // should be minus
        let lhs = mul(&a, &sub(&n, &mul(&a, &b)));
        let rhs = mul(&b, &mul(&a, &w_bad));
        report(
            &format!("NEG thm2-sign k={k}"),
            &sub(&lhs, &rhs),
            false,
            &mut checks,
            &mut fails,
        );
    }

    println!();
    println!("axeyum-cas MvPoly exact symbolic checks: {checks} run, {fails} failed");
    if fails > 0 {
        std::process::exit(1);
    }
}
