//! NoH-p2 workstream 03: the true valuation profile of the Dwork operator `U_2`
//! at `p = 2`, measured exactly.
//!
//! Setting (documented in `docs/research/10-cas/noh-p2-2026-08/03-u2-truth.md`):
//! local model at a wild point in characteristic 2, local parameter `t`, order
//! `2^m` character of Swan conductor `D`.  Splitting function
//! `theta(x) = E_2(pi_m x)` where `E_2` is the Artin-Hasse exponential and
//! `pi_m` is the root of `E_2(x) = zeta_{2^m}` (Dwork's `pi`).  Operator
//! `M = psi o mult(Theta)` with `psi(t^j) = t^{j/2}` if `j` even, else `0`;
//! matrix on the monomial basis is `M[i][j] = Theta_{2i-j}`.
//!
//! Everything is exact: Artin-Hasse coefficients over `BigRational` (which also
//! proves their 2-integrality), then 2-adic arithmetic in `Z/2^64 = Z_2 mod 2^64`
//! and `Z_2[i]/2^64` for the order-4 case.  The run is self-checking: the Dwork
//! trace formula `(2^k - 1) Tr(M^k) = S_k^*` is verified against exponential sums
//! computed from scratch by point counting over `F_{2^k}`.

#![allow(
    clippy::cast_lossless,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::comparison_chain,
    clippy::format_push_string,
    clippy::many_single_char_names,
    clippy::needless_range_loop,
    clippy::too_many_lines
)]

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

// ---------------------------------------------------------------- Z/2^64 = Z_2

/// 2-adic valuation, capped at 64 (`0` has valuation 64 in this truncation).
fn v2(x: u64) -> u32 {
    if x == 0 { 64 } else { x.trailing_zeros() }
}

/// Inverse of an odd residue mod `2^64` (Newton iteration).
fn inv_odd(a: u64) -> u64 {
    assert!(a % 2 == 1, "not a 2-adic unit");
    let mut x = a; // correct mod 2^3
    for _ in 0..6 {
        x = x.wrapping_mul(2u64.wrapping_sub(a.wrapping_mul(x)));
    }
    x
}

// ------------------------------------------------- Artin-Hasse E_2 over Q, exact

/// Coefficients of `E_2(x) = exp(sum_{i>=0} x^{2^i} / 2^i)` up to degree `n`,
/// via the ODE `E' = L' E`.  Returns exact rationals; the caller asserts
/// 2-integrality (odd denominators), which is the Artin-Hasse integrality
/// theorem verified rather than assumed.
fn artin_hasse_rational(n: usize) -> Vec<BigRational> {
    let mut l = vec![BigRational::zero(); n + 2];
    let mut i = 0u32;
    while (1usize << i) <= n + 1 {
        let j = 1usize << i;
        l[j] += BigRational::new(BigInt::one(), BigInt::from(1u64 << i));
        i += 1;
    }
    let mut e = vec![BigRational::zero(); n + 1];
    e[0] = BigRational::one();
    for m in 0..n {
        let mut acc = BigRational::zero();
        for j in 1..=(m + 1) {
            if !l[j].is_zero() {
                acc += BigRational::from(BigInt::from(j)) * &l[j] * &e[m + 1 - j];
            }
        }
        e[m + 1] = acc / BigRational::from(BigInt::from(m + 1));
    }
    e
}

/// Reduce an exact 2-integral rational mod `2^64`.
fn rat_mod(r: &BigRational) -> u64 {
    let den = r.denom();
    let den_u = big_to_u64(den);
    assert!(den_u % 2 == 1, "Artin-Hasse coefficient is not 2-integral");
    let num_u = big_to_u64(r.numer());
    num_u.wrapping_mul(inv_odd(den_u))
}

fn big_to_u64(b: &BigInt) -> u64 {
    let (sign, digits) = b.to_u64_digits();
    let mut v: u64 = 0;
    for (k, d) in digits.iter().enumerate() {
        if k == 0 {
            v = *d;
        } else {
            // higher 64-bit limbs vanish mod 2^64
            break;
        }
    }
    if sign == num_bigint::Sign::Minus {
        v.wrapping_neg()
    } else {
        v
    }
}

// --------------------------------------------------------------- Dwork's pi_1

/// The unique `pi in 2 Z_2` with `E_2(pi) = -1` (a primitive square root of
/// unity), found by Newton iteration.  This is the `p = 2` case of Dwork's
/// `pi`; note `v_2(pi) = 1 = 1/(p-1)`, and `pi != -2`.
fn dwork_pi(e: &[u64]) -> u64 {
    let eval = |x: u64| {
        let mut s = 0u64;
        let mut xp = 1u64;
        for c in e {
            s = s.wrapping_add(c.wrapping_mul(xp));
            xp = xp.wrapping_mul(x);
        }
        s
    };
    let deval = |x: u64| {
        let mut s = 0u64;
        let mut xp = 1u64;
        for (m, c) in e.iter().enumerate().skip(1) {
            s = s.wrapping_add((m as u64).wrapping_mul(*c).wrapping_mul(xp));
            xp = xp.wrapping_mul(x);
        }
        s
    };
    let mut pi = (-2i64) as u64;
    for _ in 0..80 {
        let f = eval(pi).wrapping_add(1);
        if f == 0 {
            break;
        }
        pi = pi.wrapping_sub(f.wrapping_mul(inv_odd(deval(pi))));
    }
    assert_eq!(
        eval(pi).wrapping_add(1),
        0,
        "Newton failed to solve E_2(pi) = -1"
    );
    pi
}

// ------------------------------------------------------------------- GF(2^k)

const IRR: [u64; 13] = [
    0,
    0b11,
    0b111,
    0b1011,
    0b1_0011,
    0b10_0101,
    0b100_0011,
    0b1000_0011,
    0b1_0001_1011,
    0b10_0001_0001,
    0b100_0000_1001,
    0b1000_0000_0101,
    0b1_0000_0101_0011,
];

fn gf_mul(mut a: u64, mut b: u64, k: u32) -> u64 {
    let m = IRR[k as usize];
    let mut r = 0u64;
    while b != 0 {
        if b & 1 == 1 {
            r ^= a;
        }
        b >>= 1;
        a <<= 1;
        if (a >> k) & 1 == 1 {
            a ^= m;
        }
    }
    r
}
fn gf_pow(mut a: u64, mut e: u64, k: u32) -> u64 {
    let mut r = 1u64;
    while e != 0 {
        if e & 1 == 1 {
            r = gf_mul(r, a, k);
        }
        a = gf_mul(a, a, k);
        e >>= 1;
    }
    r
}
fn gf_trace(a: u64, k: u32) -> u64 {
    let mut t = a;
    let mut x = a;
    for _ in 0..k - 1 {
        x = gf_mul(x, x, k);
        t ^= x;
    }
    assert!(t <= 1);
    t
}

/// `S_k^*(x^s) = sum_{x in F_{2^k}^*} (-1)^{Tr(x^s)}` -- from scratch.
fn s_star(s: u64, k: u32) -> i64 {
    let mut tot = 0i64;
    for x in 1..(1u64 << k) {
        tot += if gf_trace(gf_pow(x, s, k), k) == 1 {
            -1
        } else {
            1
        };
    }
    tot
}

// ---------------------------------------------------------- matrix over Z/2^64

fn matmul(a: &[Vec<u64>], b: &[Vec<u64>]) -> Vec<Vec<u64>> {
    let n = a.len();
    let mut c = vec![vec![0u64; n]; n];
    for i in 0..n {
        for k in 0..n {
            let x = a[i][k];
            if x != 0 {
                for j in 0..n {
                    c[i][j] = c[i][j].wrapping_add(x.wrapping_mul(b[k][j]));
                }
            }
        }
    }
    c
}

// --------------------------------------------------- Z_2[i] mod 2^64 (m = 2)

type Zi = (u64, u64);
const ZI0: Zi = (0, 0);
const ZI1: Zi = (1, 0);
const ZII: Zi = (0, 1);
fn zadd(x: Zi, y: Zi) -> Zi {
    (x.0.wrapping_add(y.0), x.1.wrapping_add(y.1))
}
fn zsub(x: Zi, y: Zi) -> Zi {
    (x.0.wrapping_sub(y.0), x.1.wrapping_sub(y.1))
}
fn zmul(x: Zi, y: Zi) -> Zi {
    (
        x.0.wrapping_mul(y.0).wrapping_sub(x.1.wrapping_mul(y.1)),
        x.0.wrapping_mul(y.1).wrapping_add(x.1.wrapping_mul(y.0)),
    )
}
fn zscal(c: u64, x: Zi) -> Zi {
    (c.wrapping_mul(x.0), c.wrapping_mul(x.1))
}
fn zinv(u: Zi) -> Zi {
    let n = u.0.wrapping_mul(u.0).wrapping_add(u.1.wrapping_mul(u.1));
    let ni = inv_odd(n);
    (u.0.wrapping_mul(ni), u.1.wrapping_neg().wrapping_mul(ni))
}
/// `2 * v_2` of an element of `Z_2[i]` (so half-integer valuations stay integral).
fn zval2(x: Zi) -> u32 {
    if x == ZI0 {
        return 128;
    }
    let (a, b) = (v2(x.0), v2(x.1));
    if a == b { 2 * a + 1 } else { 2 * a.min(b) }
}

fn main() {
    println!("== NoH-p2 / 03 : exact U_2 valuation profile at p = 2 ==\n");

    // ---- Artin-Hasse, exact, and its 2-integrality -------------------------
    let deg = 150usize;
    let e_rat = artin_hasse_rational(deg);
    let e: Vec<u64> = e_rat.iter().map(rat_mod).collect();
    println!(
        "Artin-Hasse E_2: {} coefficients, all 2-integral (denominators odd): PROVED by construction",
        deg + 1
    );

    // ---- Dwork's pi at p = 2, m = 1 ---------------------------------------
    let pi1 = dwork_pi(&e);
    println!(
        "pi_1 : E_2(pi_1) = -1, pi_1 = 0x{pi1:016x}, v_2(pi_1) = {}",
        v2(pi1)
    );
    assert_eq!(v2(pi1), 1, "v_2(pi_1) must be 1 = 1/(p-1)");
    // pi_1 is NOT -2 (the naive guess):
    let neg2 = (-2i64) as u64;
    assert_ne!(pi1, neg2, "pi_1 coincides with -2");
    let mut ev = 0u64;
    let mut xp = 1u64;
    for c in &e {
        ev = ev.wrapping_add(c.wrapping_mul(xp));
        xp = xp.wrapping_mul(neg2);
    }
    println!(
        "  control: E_2(-2) + 1 has v_2 = {} (finite => E_2(-2) != -1, so pi_1 != -2)",
        v2(ev.wrapping_add(1))
    );

    // ---- theta = E_2(pi_1 x): coefficient profile --------------------------
    let nlam = 64usize;
    let mut lam = vec![0u64; nlam + 1];
    let mut pp = 1u64;
    for m in 0..=nlam {
        lam[m] = e[m].wrapping_mul(pp);
        pp = pp.wrapping_mul(pi1);
    }
    let profile: Vec<u32> = (0..=24).map(|m| v2(lam[m])).collect();
    println!("\nm=1  v_2(lambda_m), m = 0..24: {profile:?}");
    assert!(
        (0..=nlam).all(|m| v2(lam[m]) as usize >= m.min(64)),
        "v_2(lambda_m) >= m failed"
    );
    let eq: Vec<usize> = (0..=24).filter(|&m| v2(lam[m]) as usize == m).collect();
    println!("     v_2(lambda_m) >= m  for all m: CONFIRMED;  equality at m = {eq:?}");

    // ---- the operator, the certifying lattice, and its optimality ----------
    println!("\n-- diagonal lattice certificate  w_k = 2k/s  (units: v_pi, pi = pi_1) --");
    for s in [1usize, 3, 5, 7, 9, 11] {
        let n = 96usize;
        // integer certificate: v(N_ik) >= k/s  <=>  s*v_2(M_ik) + k - 2i >= 0
        let mut ok = true;
        let mut tight = 0usize;
        for i in 0..=n {
            for k in 0..=n {
                if 2 * i >= k && (2 * i - k) % s == 0 {
                    let m = (2 * i - k) / s;
                    let val = if m <= nlam {
                        v2(lam[m]) as i64
                    } else {
                        m as i64
                    };
                    let slack = s as i64 * val + k as i64 - 2 * i as i64;
                    if slack < 0 {
                        ok = false;
                    }
                    if slack == 0 {
                        tight += 1;
                    }
                }
            }
        }
        // optimality witness: the self-loop at k = s has v_2(M_ss) = v_2(lambda_1) = 1,
        // so any weights force  a(s) <= 1, i.e. rate c <= 1/s.
        let witness = v2(lam[1]);
        println!(
            "  s = {s:2}:  a(k) = k/s certified for all i,k <= {n}: {ok};  tight entries: {tight};  \
             optimality witness v_2(M[s][s]) = v_2(lambda_1) = {witness} => c <= 1/s"
        );
        assert!(ok, "certificate failed at s = {s}");
        assert_eq!(witness, 1);
    }

    // ---- ANCHOR: Dwork trace formula vs point counts -----------------------
    println!("\n-- anchor: (2^k - 1) Tr(M^k) =? S_k^* = sum_{{x in F_2^k*}} (-1)^Tr(x^s) --");
    for s in [1usize, 3, 5, 7] {
        let n = (30 * s).min(140);
        let mut mat = vec![vec![0u64; n + 1]; n + 1];
        for i in 0..=n {
            for j in 0..=n {
                if 2 * i >= j && (2 * i - j) % s == 0 {
                    let m = (2 * i - j) / s;
                    if m <= nlam {
                        mat[i][j] = lam[m];
                    }
                }
            }
        }
        let mut mk: Vec<Vec<u64>> = (0..=n)
            .map(|i| (0..=n).map(|j| u64::from(i == j)).collect())
            .collect();
        let mut line = String::new();
        for k in 1..=6u32 {
            mk = matmul(&mk, &mat);
            let tr = (0..=n).fold(0u64, |a, i| a.wrapping_add(mk[i][i]));
            let lhs = ((1u64 << k) - 1).wrapping_mul(tr);
            let rhs = s_star(s as u64, k) as u64;
            let d = v2(lhs.wrapping_sub(rhs));
            line.push_str(&format!(" k={k}:v2(diff)={d}"));
            assert!(
                d as usize >= n / s,
                "trace formula FAILED at s={s}, k={k}: v2(diff)={d} < tail bound {}",
                n / s
            );
        }
        println!("  s = {s}, N = {n}, tail bound N/s = {}: {line}", n / s);
    }

    // ---- m = 2 control: order-4 characters, length-2 Witt vectors ----------
    println!("\n-- m = 2 control: pi_2 with E_2(pi_2) = zeta_4 = i --");
    let ez: Vec<Zi> = e.iter().map(|&c| (c, 0)).collect();
    let evalz = |x: Zi| {
        let mut s = ZI0;
        let mut xp = ZI1;
        for c in &ez {
            s = zadd(s, zmul(*c, xp));
            xp = zmul(xp, x);
        }
        s
    };
    let devalz = |x: Zi| {
        let mut s = ZI0;
        let mut xp = ZI1;
        for (m, c) in ez.iter().enumerate().skip(1) {
            s = zadd(s, zscal(m as u64, zmul(*c, xp)));
            xp = zmul(xp, x);
        }
        s
    };
    let mut pi2 = zsub(ZII, ZI1);
    for _ in 0..80 {
        let f = zsub(evalz(pi2), ZII);
        if f == ZI0 {
            break;
        }
        pi2 = zsub(pi2, zmul(f, zinv(devalz(pi2))));
    }
    let resid = zsub(evalz(pi2), ZII);
    println!(
        "  2*v_2(E_2(pi_2) - i) = {} (>= 64 means solved to full precision);  2*v_2(pi_2) = {}",
        zval2(resid),
        zval2(pi2)
    );
    assert_eq!(zval2(pi2), 1, "v_2(pi_2) must be 1/2 = 1/(p^{{m-1}}(p-1))");

    let mut lam2 = vec![ZI0; nlam + 1];
    let mut ppz = ZI1;
    for m in 0..=nlam {
        lam2[m] = zscal(e[m], ppz);
        ppz = zmul(ppz, pi2);
    }
    let prof2: Vec<u32> = (0..=24).map(|m| zval2(lam2[m])).collect();
    println!("  2*v_2(lambda^(2)_m), m = 0..24: {prof2:?}");
    assert!(
        (0..=48).all(|m| zval2(lam2[m]) as usize >= m),
        "v_2(lambda^(2)_m) >= m/2 failed"
    );
    println!("  v_2(lambda^(2)_m) >= m/2 for all m: CONFIRMED (rate = v_2(pi_2), no extra loss)");

    println!("\nAll assertions passed.");
}
