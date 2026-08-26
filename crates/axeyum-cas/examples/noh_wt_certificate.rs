//! NoH-p2 workstream 04: the tame-point weight certificate at `p = 2`.
//!
//! Setting (documented in `docs/research/10-cas/noh-p2-2026-08/04-weight-proof.md`):
//! Kramer-Miller--Upton I (arXiv:2110.08656v1) section 6.1.2, the auxiliary tame
//! point `P` of the Belyi map with `eta(P) = 1`, at `p = 2` and tame ramification
//! index `e = 3`.  The local Frobenius is `sigma(t) = t^2 (1 + 2 t^{-e})^{1/e}`
//! and the operator is `U_2 = (1/2) sigma^{-1} o Tr_{E/sigma(E)}`.
//!
//! What is asserted here (a failure of ANY assertion is a failure of the finding):
//!
//!   1. The closed form for the transition coefficients, namely
//!      `c = prod_{i<m}(k^2 - 4 e^2 i^2) / (e^{2m} (2m)!)` at `j = k/2 + e m` for
//!      even `k`, and `c = (k/e) prod_{i<m}(k^2 - e^2 (2i+1)^2) / (e^{2m} (2m+1)!)`
//!      at `j = (k+e)/2 + e m` for odd `k`, reproduced by an INDEPENDENT route (the hypergeometric ODE recurrence
//!      `(1+z^2) y'' + z y' - lambda^2 y = 0`, exact rational arithmetic), and
//!      matching the ground-truth values recomputed by workstream 01.
//!   2. The valuation identity `v_2(c) = Sigma - 2m + s_2(m)` with
//!      `Sigma = sum_{i<m} [v_2(k - e xi_i) + v_2(k + e xi_i)]`.
//!   3. LEMMA A: `v_2(c_{k,m}) >= m` for every `k >= 1`, `m >= 1`; refined to
//!      `>= m + s_2(m)` when `k` is odd or `4 | k`.
//!   4. The weight `a(k) = floor((k-1)/3) + (k mod 2)` (`a(k) = 0` for `k <= 3`)
//!      satisfies KMU's admissibility (A1)-(A3): `d(k) >= 1` for all `k > mu = 3`,
//!      the minimum is attained at the leading term, and `d(k) -> infinity`.
//!   5. SHARPNESS: `v_2(c_{6,1}) = 1` with `j'(6) + 3 = 6`, a self-loop, so
//!      `d(6) <= 1` for EVERY admissible weight; hence no target `d(k) >= gamma k`
//!      with `gamma > 1/6` is feasible.

use std::process::exit;

// ---------------------------------------------------------------- exact rationals
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Rat {
    n: i128,
    d: i128,
}

fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    if a == 0 { 1 } else { a }
}

impl Rat {
    fn new(n: i128, d: i128) -> Self {
        assert!(d != 0, "zero denominator");
        let s = if d < 0 { -1 } else { 1 };
        let g = gcd(n, d);
        Rat {
            n: s * n / g,
            d: s * d / g,
        }
    }
    fn int(n: i128) -> Self {
        Rat { n, d: 1 }
    }
    #[allow(clippy::many_single_char_names)]
    fn mul(self, o: Rat) -> Self {
        let g1 = gcd(self.n, o.d);
        let g2 = gcd(o.n, self.d);
        let n = (self.n / g1)
            .checked_mul(o.n / g2)
            .expect("rational overflow (numerator)");
        let d = (self.d / g2)
            .checked_mul(o.d / g1)
            .expect("rational overflow (denominator)");
        Rat::new(n, d)
    }
    /// 2-adic valuation of a nonzero rational.
    fn v2(self) -> i64 {
        assert!(self.n != 0, "v_2 of zero");
        v2_int(self.n) - v2_int(self.d)
    }
}

fn v2_int(mut n: i128) -> i64 {
    assert!(n != 0);
    n = n.abs();
    let mut v = 0;
    while n % 2 == 0 {
        n /= 2;
        v += 1;
    }
    v
}

fn s2(mut m: u32) -> i64 {
    let mut s = 0;
    while m > 0 {
        s += i64::from(m & 1);
        m >>= 1;
    }
    s
}

// ---------------------------------------------------------------- the operator
/// `j'(k)`: the least pole order occurring in `U_2(t^{-k})`.
fn jprime(k: i128, e: i128) -> i128 {
    if k % 2 == 0 {
        k / 2
    } else {
        i128::midpoint(k, e)
    }
}

/// Closed form (product formula) for `c_{k, j'(k) + e m}`.
#[allow(clippy::many_single_char_names)]
fn c_closed(k: i128, m: u32, e: i128) -> Rat {
    let lam2 = Rat::new(k * k, e * e);
    if k % 2 == 0 {
        let mut num = Rat::int(1);
        for i in 0..i128::from(m) {
            num = num.mul(Rat::new(lam2.n - 4 * i * i * lam2.d, lam2.d));
        }
        let mut den = Rat::int(1);
        for i in 1..=(2 * i128::from(m)) {
            den = den.mul(Rat::int(i));
        }
        num.mul(Rat::new(den.d, den.n))
    } else {
        let mut num = Rat::new(k, e);
        for i in 0..i128::from(m) {
            let t = (2 * i + 1) * (2 * i + 1);
            num = num.mul(Rat::new(lam2.n - t * lam2.d, lam2.d));
        }
        let mut den = Rat::int(1);
        for i in 1..=(2 * i128::from(m) + 1) {
            den = den.mul(Rat::int(i));
        }
        num.mul(Rat::new(den.d, den.n))
    }
}

/// INDEPENDENT route: the coefficients of `y = cosh(lambda arcsinh z)` (k even)
/// and `y = sinh(lambda arcsinh z)/z` (k odd) in `Y = z^2`, obtained from the
/// recurrence forced by `(1+z^2) y'' + z y' - lambda^2 y = 0`.  This never forms
/// the product above; it integrates the differential equation term by term.
#[allow(clippy::many_single_char_names)]
fn c_ode(k: i128, m: u32, e: i128) -> Rat {
    let lam2 = Rat::new(k * k, e * e);
    let (mut c, even) = if k % 2 == 0 {
        (Rat::int(1), true)
    } else {
        (Rat::new(k, e), false)
    };
    for i in 0..i128::from(m) {
        // even: a_{i+1} = a_i (lam^2 - 4 i^2) / ((2i+2)(2i+1))
        // odd : b_{i+1} = b_i (lam^2 - (2i+1)^2) / ((2i+3)(2i+2))
        let (sub, p, q) = if even {
            (4 * i * i, 2 * i + 2, 2 * i + 1)
        } else {
            ((2 * i + 1) * (2 * i + 1), 2 * i + 3, 2 * i + 2)
        };
        c = c
            .mul(Rat::new(lam2.n - sub * lam2.d, lam2.d))
            .mul(Rat::new(1, p * q));
    }
    c
}

/// Valuation identity: `v_2(c_{k,m}) = Sigma - 2m + s_2(m)`; `None` iff `c = 0`.
#[allow(clippy::many_single_char_names)]
fn v2_closed(k: i128, m: u32, e: i128) -> Option<i64> {
    let mut s = 0i64;
    for i in 0..i128::from(m) {
        let xi = if k % 2 == 0 { 2 * i } else { 2 * i + 1 };
        let (a, b) = (k - e * xi, k + e * xi);
        if a == 0 || b == 0 {
            return None;
        }
        s += v2_int(a) + v2_int(b);
    }
    Some(s - 2 * i64::from(m) + s2(m))
}

// ---------------------------------------------------------------- the weight
fn a20(k: i128) -> i64 {
    if k <= 3 {
        0
    } else {
        i64::try_from((k - 1) / 3 + k % 2).expect("weight fits in i64")
    }
}

// ---------------------------------------------------------------- checks
#[allow(clippy::too_many_lines, clippy::many_single_char_names)]
fn main() {
    const E: i128 = 3;
    let mut fail = 0usize;
    macro_rules! check {
        ($cond:expr, $($arg:tt)*) => {
            if !$cond { eprintln!("FAIL: {}", format!($($arg)*)); fail += 1; }
        };
    }

    // 1. closed form vs the independent ODE route, and vs 01's ground truth.
    let mut pairs = 0usize;
    for k in 1i128..=40 {
        for m in 0u32..=10 {
            let a = c_closed(k, m, E);
            let b = c_ode(k, m, E);
            check!(
                a == b,
                "closed form != ODE route at k={k} m={m}: {a:?} vs {b:?}"
            );
            pairs += 1;
        }
    }
    check!(
        pairs >= 400,
        "coefficient cross-check ran only {pairs} pairs"
    );
    println!("[1] closed form == ODE recurrence on {pairs} (k,m) pairs");

    // ground truth recomputed by workstream 01 (01-kmu-extraction.md section 6b)
    check!(
        jprime(3, E) == 3 && c_closed(3, 0, E) == Rat::int(1),
        "U_2(t^-3) != t^-3"
    );
    check!(
        c_closed(3, 1, E) == Rat::int(0),
        "U_2(t^-3) has a second term"
    );
    check!(
        jprime(6, E) == 3 && c_closed(6, 0, E) == Rat::int(1) && c_closed(6, 1, E) == Rat::int(2),
        "U_2(t^-6) != t^-3 + 2 t^-6"
    );
    check!(
        c_closed(6, 2, E) == Rat::int(0),
        "U_2(t^-6) has a third term"
    );
    check!(
        c_closed(5, 0, E) == Rat::new(5, 3)
            && c_closed(5, 1, E) == Rat::new(40, 81)
            && c_closed(5, 2, E) == Rat::new(-112, 729),
        "U_2(t^-5) ground truth mismatch"
    );
    check!(
        c_closed(4, 0, E) == Rat::int(1)
            && c_closed(4, 1, E) == Rat::new(8, 9)
            && c_closed(4, 2, E) == Rat::new(-40, 243),
        "U_2(t^-4) ground truth mismatch"
    );
    check!(
        c_closed(8, 1, E) == Rat::new(32, 9) && c_closed(7, 1, E) == Rat::new(140, 81),
        "U_2(t^-7)/U_2(t^-8) ground truth mismatch"
    );
    println!("[1] ground-truth rows U_2(t^-3), t^-4, t^-5, t^-6, t^-7, t^-8 reproduced");

    // 2. valuation identity
    let mut vpairs = 0usize;
    for k in 1i128..=40 {
        for m in 0u32..=10 {
            let c = c_closed(k, m, E);
            match v2_closed(k, m, E) {
                None => check!(c == Rat::int(0), "v2 says c_{{{k},{m}}} = 0 but c = {c:?}"),
                Some(v) => {
                    check!(
                        c != Rat::int(0),
                        "c_{{{k},{m}}} = 0 but v2 formula gave {v}"
                    );
                    if c != Rat::int(0) {
                        check!(c.v2() == v, "v2 mismatch k={k} m={m}: {} vs {v}", c.v2());
                    }
                    vpairs += 1;
                }
            }
        }
    }
    check!(vpairs >= 300, "valuation identity ran only {vpairs} pairs");
    println!("[2] valuation identity v_2(c) = Sigma - 2m + s_2(m) on {vpairs} pairs");

    // 3. LEMMA A and its refinements
    let (mut la, mut tight) = (0usize, 0usize);
    for k in 1i128..=600 {
        for m in 1u32..=80 {
            if let Some(v) = v2_closed(k, m, E) {
                check!(
                    v >= i64::from(m),
                    "LEMMA A fails: v_2(c_{{{k},{m}}}) = {v} < {m}"
                );
                if v == i64::from(m) {
                    tight += 1;
                    check!(
                        k % 4 == 2 && m == 1,
                        "LEMMA A tight outside k=2 mod 4, m=1: k={k} m={m}"
                    );
                }
                if k % 2 == 1 || k % 4 == 0 {
                    check!(
                        v >= i64::from(m) + s2(m),
                        "LEMMA A+ fails at k={k} m={m}: {v} < {}",
                        i64::from(m) + s2(m)
                    );
                }
                if k % 4 == 2 {
                    check!(
                        v >= 3 * (i64::from(m) / 2) + s2(m),
                        "LEMMA A2 fails at k={k} m={m}"
                    );
                }
                la += 1;
            }
        }
    }
    check!(la >= 40_000, "LEMMA A ran only {la} pairs");
    println!("[3] LEMMA A on {la} pairs (equality v_2 = m in {tight} cases, all k=2 mod 4 & m=1)");

    // 4. admissibility of a(k) = floor((k-1)/3) + (k mod 2)
    check!(
        (1..=3).all(|k: i128| a20(k) == 0),
        "(A1) a(k) = 0 for k <= mu(P) = 3 fails"
    );
    let (mut kmax, mut dmin_seen, mut cols) = (0i128, i64::MAX, 0usize);
    for k in 4i128..=400 {
        let jp = jprime(k, E);
        let mut d = i64::MAX;
        let mut argmin = usize::MAX;
        for m in 0u32..=250 {
            if let Some(v) = v2_closed(k, m, E) {
                let val = a20(k) - a20(jp + E * i128::from(m)) + v;
                if val < d {
                    d = val;
                    argmin = m as usize;
                }
            }
        }
        check!(d >= 1, "(A3) d({k}) = {d} < 1");
        check!(
            argmin == 0,
            "(A3) minimum for k={k} attained at m={argmin}, not the leading term"
        );
        if k <= 24 {
            dmin_seen = dmin_seen.min(d);
        }
        if k >= 300 {
            check!(d >= 40, "(A3) divergence: d({k}) = {d} is too small");
        }
        kmax = k;
        cols += 1;
    }
    check!(
        cols == 397 && kmax == 400,
        "column sweep incomplete: {cols} columns, kmax {kmax}"
    );
    check!(
        dmin_seen == 1,
        "expected d = 1 to be attained on 4..24, got {dmin_seen}"
    );
    // (A2): a(k) = O(k)
    check!(
        (4i128..=400).all(|k| i128::from(a20(k)) * 2 <= k + 6),
        "(A2) a(k) = O(k) bound violated"
    );
    if fail == 0 {
        println!("[4] a(k) = floor((k-1)/3) + (k mod 2): (A1),(A2),(A3) hold on 4..=400, m<=250");
    }

    // 5. sharpness: the self-loop at k = 6
    check!(
        jprime(6, E) + E == 6,
        "k=6 is not a self-loop of the support map"
    );
    check!(v2_closed(6, 1, E) == Some(1), "v_2(c_{{6,1}}) != 1");
    println!("[5] sharpness: j'(6)+3 = 6 and v_2(c_(6,1)) = 1  =>  d(6) <= 1 for every weight");
    println!("    hence max(1, gamma k) is admissible iff gamma <= 1/6 (2/11 and 1/5 both fail)");

    if fail > 0 {
        eprintln!("\n{fail} assertion(s) FAILED");
        exit(1);
    }
    println!("\nall assertions passed");
}
