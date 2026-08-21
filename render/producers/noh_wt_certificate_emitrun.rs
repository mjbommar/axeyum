// noh_wt_certificate_emitrun.rs -- the NoH-p2 tame-point weight certificate,
// patched to emit a machine-readable run record.
//
// PROVENANCE
//   Base           crates/axeyum-cas/examples/noh_wt_certificate.rs, pinned at
//                  axeyum commit 75663ef85c2dad4390a3b6d77361919a914642a9
//                  (branch agent/noh-p2-axeyum-examples, committer epoch
//                  1787307950). The base file is 376 lines and is reproduced
//                  below verbatim apart from the additions listed next.
//                  It is byte-identical to
//                  newton-over-hodge-char2/replication/axeyum-examples/noh_wt_certificate.rs,
//                  which replication/certificate/run-certificate.sh builds with a
//                  bare `rustc --edition 2024` and mutation-tests.
//   Patched by     render strand P0-A, agent CERT, 2026-08-21
//                  (docs/render-2026-08/04-prototype-plan.md, P0-A step 1).
//   Emits          a RunRecord per artifacts/ontology/docir.schema.json
//                  ($defs/RunRecord), schema_version 1.
//
// WHAT WAS ADDED -- nothing was removed, relaxed, or made conditional
//   1. `--emit-run <path>`: write a run record describing every check the
//      certificate performed, its measured values, and its outcome.
//      `--source <path>` (REQUIRED with --emit-run) names the file to SHA-256
//      into the record's provenance. `--record-id`, `--replay-line`,
//      `--replay-seconds` and `--notes` fill the remaining record fields.
//      With no arguments the program behaves exactly as the base pin did.
//   2. A pure-std SHA-256 (FIPS 180-4) and a deterministic JSON writer, so the
//      file still builds under a bare `rustc` with no dependencies.
//   3. Per-section claim records. A section's recorded status is the DELTA of
//      the certificate's own `fail` counter across that section -- it is not a
//      second, independent judgement that could disagree with the assertions
//      that ran. Every recorded number is recomputed by the same functions the
//      assertions used.
//
// SOUNDNESS OF THE ADDITION
//   * Every assertion in the base file still runs, in the same order, over the
//     same ranges, whether or not --emit-run is passed.
//   * A failing run still exits 1 -- after writing the record -- and that
//     record has provenance.exit_status 1, outcome "refuted", and status
//     "refuted" on the claim whose section failed.
//     render/examples-input/cert/run-mutant-M1.json is such a record, produced
//     by applying the M1 mutant patch and running it, not by editing a passing
//     record.
//   * All 7 mutants in newton-over-hodge-char2/replication/certificate/mutants/
//     still exit nonzero against THIS file, each with its recorded catcher.
//   * No wall clock: `epoch` is SOURCE_DATE_EPOCH when set and the pinned
//     commit time otherwise, and the recorded `command` normalises argv[0] to a
//     fixed program name. Two runs in different directories are byte-identical.
//   * `--emit-run` without `--source` is a usage error (exit 2): a run record
//     with no hashed input is not evidence.
//
// FAITHFULNESS NOTE -- carried from the audit, do not drop
//   20-verify.md P2-8 established that the "independent ODE route" of check [1]
//   is NOT independent of the closed form: it is the same product in a different
//   association order. The record says so in claim c1's note and in the record
//   notes, and records that the certificate's only binding to the operator U_2
//   is the hard-coded ground-truth rows (claim c2).

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
    let args = parse_args();
    let mut rec = RunRecord::new();
    let mut fail = 0usize;
    // Snapshot of the certificate's own failure counter at the start of the
    // current section.  A section's recorded status is the DELTA of this
    // counter, so a recorded `evidence` cannot disagree with the assertions
    // that actually ran.
    let mut mark = 0usize;
    rec.stat("tame-ramification-index-e", E.to_string());
    rec.stat("truncation-parameter-mu-p", "3".to_string());
    rec.stat("residue-characteristic-p", "2".to_string());
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
    rec.stat("c1-pairs-compared", pairs.to_string());
    rec.stat("c1-k-min", "1".to_string());
    rec.stat("c1-k-max", "40".to_string());
    rec.stat("c1-m-min", "0".to_string());
    rec.stat("c1-m-max", "10".to_string());
    rec.stat("c1-mismatches", (fail - mark).to_string());
    rec.claim(ClaimRec {
        key: "c1-closed-form-vs-ode-recurrence",
        statement: "Theorem 1, arithmetic cross-check: the closed-form product for \
                    c_{k, j'(k)+e m} and the value obtained by iterating the recurrence \
                    forced by (1+z^2) y'' + z y' - lambda^2 y = 0 agree in exact rational \
                    arithmetic for every 1 <= k <= 40 and 0 <= m <= 10 (440 pairs).",
        note: "NOT an independence check. 20-verify.md P2-8 established that c_ode \
               iterates the same product in a different association order, so this \
               verifies exact rational arithmetic, not the operator U_2. The \
               certificate's only binding to U_2 is claim c2.",
        failures: fail - mark,
    });
    mark = fail;

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
    {
        // Exactly the (k,m) pairs whose coefficient values are asserted literally
        // above; recomputed here from the same function the assertions used.
        #[rustfmt::skip]
        let gt: [(i128, u32); 13] = [
            (3, 0), (3, 1), (4, 0), (4, 1), (4, 2), (5, 0), (5, 1), (5, 2),
            (6, 0), (6, 1), (6, 2), (7, 1), (8, 1),
        ];
        let rows: Vec<String> = gt
            .iter()
            .map(|&(k, m)| {
                let c = c_closed(k, m, E);
                format!(
                    "[{}, {}, {}, {}, {}, {}]",
                    k,
                    m,
                    jprime(k, E) + E * i128::from(m),
                    jstr(&rat_str(c)),
                    c.n,
                    c.d
                )
            })
            .collect();
        rec.table(
            "ground-truth-coefficients",
            &["k", "m", "j", "c", "c_num", "c_den"],
            &rows,
        );
    }
    rec.stat("c2-coefficients-asserted", "13".to_string());
    rec.stat("c2-support-map-values-asserted", "2".to_string());
    rec.stat("c2-mismatches", (fail - mark).to_string());
    rec.claim(ClaimRec {
        key: "c2-ground-truth-coefficient-rows",
        statement: "Theorem 1 against the operator: the closed form reproduces the U_2 \
                    expansions recomputed independently by workstream 01 \
                    (01-kmu-extraction.md sec. 6b) for k = 3..8 -- in particular \
                    U_2(t^-3) = t^-3 and U_2(t^-6) = t^-3 + 2 t^-6, both terminating -- \
                    across 13 coefficient values and 2 support-map values.",
        note: "This is the certificate's ONLY binding to the actual operator U_2; \
               claims c1, c3 and c4 are arithmetic over the closed form. Widening it \
               (by adding the series solve) is 20-verify.md P2-8's open recommendation.",
        failures: fail - mark,
    });
    mark = fail;

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
    rec.stat("c3-nonzero-pairs-checked", vpairs.to_string());
    rec.stat("c3-zero-pairs-checked", (pairs - vpairs).to_string());
    rec.stat("c3-k-max", "40".to_string());
    rec.stat("c3-m-max", "10".to_string());
    rec.stat("c3-mismatches", (fail - mark).to_string());
    rec.claim(ClaimRec {
        key: "c3-valuation-identity",
        statement: "Theorem 2 (valuation identity): v_2(c_{k, j'(k)+e m}) = \
                    Sigma_m(k) - 2m + s_2(m), with Sigma_m(k) = sum_{i<m} \
                    [v_2(k - e xi_i) + v_2(k + e xi_i)] and xi_i = 2i for k even, \
                    2i+1 for k odd; and the formula is undefined exactly when the \
                    coefficient vanishes. Checked on 352 nonzero and 88 zero pairs.",
        note: "Arithmetic over the closed form of claim c1; its binding to U_2 is c2.",
        failures: fail - mark,
    });
    mark = fail;

    // 3. LEMMA A and its refinements
    let (mut la, mut tight) = (0usize, 0usize);
    let mut tight_pairs: Vec<String> = Vec::new();
    for k in 1i128..=600 {
        for m in 1u32..=80 {
            if let Some(v) = v2_closed(k, m, E) {
                check!(
                    v >= i64::from(m),
                    "LEMMA A fails: v_2(c_{{{k},{m}}}) = {v} < {m}"
                );
                if v == i64::from(m) {
                    tight += 1;
                    tight_pairs.push(format!("[{k}, {m}, {v}]"));
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
    rec.table("lemma-a-tight-pairs", &["k", "m", "v2"], &tight_pairs);
    rec.stat("c4-pairs-checked", la.to_string());
    rec.stat("c4-k-max", "600".to_string());
    rec.stat("c4-m-max", "80".to_string());
    rec.stat("c4-tight-pairs", tight.to_string());
    rec.stat(
        "c4-tight-pairs-shape",
        jstr("k = 2 mod 4 and m = 1; asserted separately for every tight pair found"),
    );
    rec.stat("c4-violations", (fail - mark).to_string());
    rec.claim(ClaimRec {
        key: "c4-lemma-a-tail-bound",
        statement: "Lemma A and its two refinements: v_2(c_{k, j'(k)+e m}) >= m for all \
                    k >= 1, m >= 1; >= m + s_2(m) when k is odd or 4 | k; and \
                    >= 3*floor(m/2) + s_2(m) when k = 2 mod 4. Equality v_2 = m is \
                    attained only at k = 2 mod 4 with m = 1. Checked on 41600 pairs \
                    over k <= 600, 1 <= m <= 80.",
        note: "A finite sweep of the valuation formula, not a proof of the Lemma; the \
               proof is 04-weight-proof.md sec. 2, audited at 20-verify.md P2-2.",
        failures: fail - mark,
    });
    mark = fail;

    // 4. admissibility of a(k) = floor((k-1)/3) + (k mod 2)
    check!(
        (1..=3).all(|k: i128| a20(k) == 0),
        "(A1) a(k) = 0 for k <= mu(P) = 3 fails"
    );
    let (mut kmax, mut dmin_seen, mut cols) = (0i128, i64::MAX, 0usize);
    let mut d_rows: Vec<String> = Vec::new();
    let mut d_milestones: Vec<(i128, i64)> = Vec::new();
    let mut argmin_violations = 0usize;
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
        if argmin != 0 {
            argmin_violations += 1;
        }
        if matches!(k, 100 | 200 | 400) {
            d_milestones.push((k, d));
        }
        d_rows.push(format!(
            "[{k}, {jp}, {}, {}, {d}, {argmin}]",
            a20(k),
            a20(jp)
        ));
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
    rec.table(
        "d-table",
        &["k", "jprime", "a_k", "a_jprime", "d", "argmin_m"],
        &d_rows,
    );
    rec.table(
        "weight-series",
        &["k", "a_k"],
        &(1i128..=60)
            .map(|k| format!("[{k}, {}]", a20(k)))
            .collect::<Vec<_>>(),
    );
    rec.stat("c5-columns-swept", cols.to_string());
    rec.stat("c5-k-min", "4".to_string());
    rec.stat("c5-k-max", kmax.to_string());
    rec.stat("c5-m-max", "250".to_string());
    rec.stat("c5-min-d-over-k-4-to-24", dmin_seen.to_string());
    rec.stat(
        "c5-argmin-not-at-leading-term",
        argmin_violations.to_string(),
    );
    for (k, d) in &d_milestones {
        match k {
            100 => rec.stat("c5-d-at-k-100", d.to_string()),
            200 => rec.stat("c5-d-at-k-200", d.to_string()),
            _ => rec.stat("c5-d-at-k-400", d.to_string()),
        }
    }
    rec.stat("c5-violations", (fail - mark).to_string());
    rec.claim(ClaimRec {
        key: "c5-theorem-3-admissibility",
        statement: "Theorem 3 (admissibility) for a(k) = 0 (k <= 3), \
                    a(k) = floor((k-1)/3) + (k mod 2) (k >= 4): (A1) a(k) = 0 for \
                    k <= mu(P) = 3; (A2) 2 a(k) <= k + 6, so a(k) = O(k); (A3) \
                    d(k) = min over the computed support of [a(k) - a(j) + v_2(c_{k,j})] \
                    is >= 1 for every 4 <= k <= 400, the minimum is attained at the \
                    leading term m = 0 for every such k, and d(k) >= 40 once k >= 300.",
        note: "d(k) here is the minimum over the support the certificate actually \
               computes (m <= 250) for 4 <= k <= 400; the infinite tail beyond that is \
               covered by Lemma A (claim c4), not by this sweep.",
        failures: fail - mark,
    });
    mark = fail;

    // 5. sharpness: the self-loop at k = 6
    check!(
        jprime(6, E) + E == 6,
        "k=6 is not a self-loop of the support map"
    );
    check!(v2_closed(6, 1, E) == Some(1), "v_2(c_{{6,1}}) != 1");
    println!("[5] sharpness: j'(6)+3 = 6 and v_2(c_(6,1)) = 1  =>  d(6) <= 1 for every weight");
    println!("    hence max(1, gamma k) is admissible iff gamma <= 1/6 (2/11 and 1/5 both fail)");
    {
        let jp6 = jprime(6, E);
        rec.stat("c6-k", "6".to_string());
        rec.stat("c6-jprime-of-6", jp6.to_string());
        rec.stat("c6-self-loop-j", (jp6 + E).to_string());
        rec.stat("c6-c-6-3", jstr(&rat_str(c_closed(6, 0, E))));
        rec.stat("c6-c-6-6", jstr(&rat_str(c_closed(6, 1, E))));
        rec.stat("c6-c-6-9", jstr(&rat_str(c_closed(6, 2, E))));
        rec.stat(
            "c6-v2-of-c-6-6",
            v2_closed(6, 1, E).map_or_else(|| "null".to_string(), |v| v.to_string()),
        );
        rec.stat("c6-a-of-6", a20(6).to_string());
        rec.stat("c6-a-of-3", a20(3).to_string());
        rec.stat("c6-d-of-6", (a20(6) - a20(jp6)).to_string());
        rec.stat("c6-d-of-6-upper-bound-for-every-weight", "1".to_string());
        rec.stat("c6-violations", (fail - mark).to_string());
    }
    rec.claim(ClaimRec {
        key: "c6-theorem-4-sharpness",
        statement: "Theorem 4 (sharpness): j'(6) + e = 6, so k = 6 lies in its own \
                    support, and the (A3) constraint there reads \
                    a(6) - a(6) + v_2(c_{6,6}) >= d(6), in which the weight cancels \
                    identically. Since c_{6,6} = 2 and v_2(c_{6,6}) = 1, d(6) <= 1 for \
                    EVERY admissible weight whatsoever.",
        note: "What is ASSERTED is exactly two computed facts: j'(6) + 3 = 6 and \
               v_2(c_{6,6}) = 1. That a target d(k) >= max(1, gamma k) is therefore \
               achievable iff gamma <= 1/6 follows in one line (6 gamma <= 1) and is \
               argued in 04-weight-proof.md sec. 5; the certificate prints that \
               consequence but does not separately check it.",
        failures: fail - mark,
    });
    mark = fail;
    rec.stat("c7-pairs-measured", pairs.to_string());
    rec.stat("c7-pairs-required", "400".to_string());
    rec.stat("c7-vpairs-measured", vpairs.to_string());
    rec.stat("c7-vpairs-required", "300".to_string());
    rec.stat("c7-lemma-a-pairs-measured", la.to_string());
    rec.stat("c7-lemma-a-pairs-required", "40000".to_string());
    rec.stat("c7-columns-measured", cols.to_string());
    rec.stat("c7-columns-required", "397".to_string());
    rec.stat("c7-kmax-measured", kmax.to_string());
    rec.stat("c7-kmax-required", "400".to_string());
    rec.stat("c7-min-d-over-k-4-to-24-measured", dmin_seen.to_string());
    rec.stat("c7-min-d-over-k-4-to-24-required", "1".to_string());
    // c7's status is derived from the MEASURED values against the thresholds the
    // certificate asserts, not from `fail - mark`: each of these guards is asserted
    // inside an earlier section, so its failure is counted in that section's delta
    // and would otherwise leave c7 recording "pass" over a violated guard -- the
    // checker-that-cannot-fail pattern this repository has shipped before.
    let guards_violated = usize::from(pairs < 400)
        + usize::from(vpairs < 300)
        + usize::from(la < 40_000)
        + usize::from(cols != 397)
        + usize::from(kmax != 400)
        + usize::from(dmin_seen != 1);
    rec.stat("c7-guards-total", "6".to_string());
    rec.stat("c7-guards-violated", guards_violated.to_string());
    rec.claim(ClaimRec {
        key: "c7-census-guards",
        statement: "Mutation-facing census guards: the certificate asserts a minimum \
                    amount of work actually done, so a mutation that empties a sweep \
                    cannot pass by checking nothing -- pairs >= 400, vpairs >= 300, \
                    Lemma-A pairs >= 40000, columns == 397 and kmax == 400, and the \
                    minimum of d over 4 <= k <= 24 equals 1.",
        note: "These guards are asserted in line in the sweeps above; this claim records \
               their measured values so a reader can see the sweeps were not empty. \
               The mutation suite that exercises them is \
               newton-over-hodge-char2/replication/certificate/run-certificate.sh --mutants \
               (7 mutants, all caught). This claim's status is derived from the measured \
               values against the thresholds, so a guard violated inside an earlier \
               section refutes c7 as well as that section -- the two counts deliberately \
               overlap rather than partition.",
        failures: guards_violated,
    });
    let _ = mark;
    rec.stat("assertion-failures", fail.to_string());
    rec.stat(
        "claims-failed",
        rec.claims
            .iter()
            .filter(|c| c.failures > 0)
            .count()
            .to_string(),
    );

    let exit_status = i32::from(fail > 0);
    if let Some(path) = args.emit_run.clone() {
        match rec.render(&args, exit_status, fail) {
            Ok(json) => {
                if let Err(e) = std::fs::write(&path, json) {
                    eprintln!("FATAL: cannot write run record to {path}: {e}");
                    exit(3);
                }
                println!("[run-record] wrote {path} (exit_status {exit_status})");
            }
            Err(e) => {
                eprintln!("FATAL: cannot build run record: {e}");
                exit(3);
            }
        }
    }

    if fail > 0 {
        eprintln!("\n{fail} assertion(s) FAILED");
        exit(1);
    }
    println!("\nall assertions passed");
}

// ============================================================================
// ADDED (render strand P0-A, agent CERT, 2026-08-21): `--emit-run` run-record
// emission, conforming to `artifacts/ontology/docir.schema.json#/$defs/RunRecord`.
// Everything below this line is a pure addition: no assertion above it is
// removed, relaxed, or made conditional on any flag.
// ============================================================================

/// Committer time of the base pin (`git log -1 --format=%ct 75663ef8`).  Used as
/// the record epoch when `SOURCE_DATE_EPOCH` is unset.  There is no wall-clock
/// read anywhere in this file.
const PINNED_EPOCH: i64 = 1_787_307_950;
const PINNED_COMMIT: &str = "75663ef85c2dad4390a3b6d77361919a914642a9";

/// Logical name of this program in the recorded `command`: argv[0] is a build
/// artifact path and would make the record non-deterministic.
const PROGRAM_NAME: &str = "noh_wt_certificate";

struct Args {
    emit_run: Option<String>,
    source: Option<String>,
    record_id: String,
    replay_line: Option<String>,
    replay_seconds: Option<i64>,
    notes: Option<String>,
    rest: Vec<String>,
}

fn usage_and_die(msg: &str) -> ! {
    eprintln!("noh_wt_certificate: {msg}");
    eprintln!(
        "usage: noh_wt_certificate [--emit-run <path> --source <path> \
         [--record-id R:<slug>] [--replay-line <cmd>] [--replay-seconds <n>] \
         [--notes <text>]]"
    );
    exit(2);
}

fn parse_args() -> Args {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let mut a = Args {
        emit_run: None,
        source: None,
        record_id: "R:noh-wt-certificate".to_string(),
        replay_line: None,
        replay_seconds: None,
        notes: None,
        rest: argv.clone(),
    };
    let need = |i: usize, flag: &str| -> String {
        if i + 1 >= argv.len() {
            usage_and_die(&format!("{flag} needs a value"));
        }
        argv[i + 1].clone()
    };
    let mut i = 0;
    while i < argv.len() {
        match argv[i].as_str() {
            "--emit-run" => a.emit_run = Some(need(i, "--emit-run")),
            "--source" => a.source = Some(need(i, "--source")),
            "--record-id" => a.record_id = need(i, "--record-id"),
            "--replay-line" => a.replay_line = Some(need(i, "--replay-line")),
            "--replay-seconds" => {
                a.replay_seconds = Some(
                    need(i, "--replay-seconds")
                        .parse::<i64>()
                        .unwrap_or_else(|_| usage_and_die("--replay-seconds needs an integer")),
                );
            }
            "--notes" => a.notes = Some(need(i, "--notes")),
            other => usage_and_die(&format!("unknown argument {other:?}")),
        }
        i += 2;
    }
    // Fail-closed: a run record with no hashed input is not evidence.
    if a.emit_run.is_some() && a.source.is_none() {
        usage_and_die("--emit-run requires --source <path> (the file to hash)");
    }
    a
}

// ---------------------------------------------------------------- SHA-256 (std only)
// FIPS 180-4.  Written out here because this file must keep building under a
// bare `rustc --edition 2024` with no dependencies: that is what
// newton-over-hodge-char2/replication/certificate/run-certificate.sh does, and
// it is what makes the mutation suite runnable by a reader.
#[rustfmt::skip]
#[allow(clippy::unreadable_literal)]
const K256: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

#[allow(clippy::unreadable_literal, clippy::many_single_char_names)]
fn sha256_hex(data: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut msg = data.to_vec();
    let bitlen = (data.len() as u64).wrapping_mul(8);
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bitlen.to_be_bytes());
    for chunk in msg.chunks_exact(64) {
        let mut w = [0u32; 64];
        for (i, word) in chunk.chunks_exact(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let (mut a, mut b, mut c, mut d) = (h[0], h[1], h[2], h[3]);
        let (mut e, mut f, mut g, mut hh) = (h[4], h[5], h[6], h[7]);
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ ((!e) & g);
            let t1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K256[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (slot, v) in h.iter_mut().zip([a, b, c, d, e, f, g, hh]) {
            *slot = slot.wrapping_add(v);
        }
    }
    let mut out = String::with_capacity(64);
    for v in h {
        let _ = write!(out, "{v:08x}");
    }
    out
}

// ---------------------------------------------------------------- JSON (deterministic)
fn jstr(s: &str) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// One-line JSON object from pre-rendered values.
fn jline(fields: &[(&str, String)]) -> String {
    let body: Vec<String> = fields
        .iter()
        .map(|(k, v)| format!("{}: {}", jstr(k), v))
        .collect();
    format!("{{{}}}", body.join(", "))
}

/// Multi-line JSON object; each field on its own line indented by `ind`.
fn jblock(ind: usize, fields: &[(&str, String)]) -> String {
    if fields.is_empty() {
        return "{}".to_string();
    }
    let pad = " ".repeat(ind);
    let body: Vec<String> = fields
        .iter()
        .map(|(k, v)| format!("{pad}{}: {}", jstr(k), v))
        .collect();
    format!("{{\n{}\n{}}}", body.join(",\n"), " ".repeat(ind - 2))
}

/// JSON array of pre-rendered items, one per line indented by `ind`.
fn jlist(ind: usize, items: &[String]) -> String {
    if items.is_empty() {
        return "[]".to_string();
    }
    let pad = " ".repeat(ind);
    format!(
        "[\n{}{}\n{}]",
        pad,
        items.join(&format!(",\n{pad}")),
        " ".repeat(ind - 2)
    )
}

/// A rational as a reader-facing cell: `2`, `8/9`, `-40/243`.
fn rat_str(r: Rat) -> String {
    if r.d == 1 {
        r.n.to_string()
    } else {
        format!("{}/{}", r.n, r.d)
    }
}

// ---------------------------------------------------------------- the record
/// One entry of the record's `claims` array.  `status` is DERIVED from the
/// certificate's own failure counter across the section that established it --
/// it is not a second, independent judgement that could disagree with the
/// assertions that actually ran.
struct ClaimRec {
    key: &'static str,
    statement: &'static str,
    note: &'static str,
    failures: usize,
}

impl ClaimRec {
    fn status(&self) -> &'static str {
        // `evidence`: a finite computation, carrying no universal credit
        // (docir.schema.json EvidenceStatus).  `refuted`: a witness against
        // the statement -- which is exactly what a failed assertion here is.
        if self.failures == 0 {
            "evidence"
        } else {
            "refuted"
        }
    }
    fn render(&self, ind: usize) -> String {
        jblock(
            ind + 2,
            &[
                ("key", jstr(self.key)),
                ("status", jstr(self.status())),
                ("statement", jstr(self.statement)),
                ("note", jstr(self.note)),
            ],
        )
    }
}

struct RunRecord {
    claims: Vec<ClaimRec>,
    stats: Vec<(&'static str, String)>,
    tables: Vec<(&'static str, String)>,
}

impl RunRecord {
    fn new() -> Self {
        RunRecord {
            claims: Vec::new(),
            stats: Vec::new(),
            tables: Vec::new(),
        }
    }
    fn claim(&mut self, c: ClaimRec) {
        self.claims.push(c);
    }
    fn stat(&mut self, key: &'static str, value: String) {
        self.stats.push((key, value));
    }
    fn table(&mut self, key: &'static str, columns: &[&str], rows: &[String]) {
        let cols = format!(
            "[{}]",
            columns
                .iter()
                .map(|c| jstr(c))
                .collect::<Vec<_>>()
                .join(", ")
        );
        self.tables.push((
            key,
            jblock(8, &[("columns", cols), ("rows", jlist(10, rows))]),
        ));
    }

    #[allow(clippy::too_many_lines)]
    fn render(
        &self,
        args: &Args,
        exit_status: i32,
        total_failures: usize,
    ) -> Result<String, String> {
        let source = args.source.as_ref().expect("checked in parse_args");
        let bytes =
            std::fs::read(source).map_err(|e| format!("cannot read --source {source}: {e}"))?;
        let sha = sha256_hex(&bytes);
        let (epoch_unix, epoch_source, epoch_commit) = match std::env::var("SOURCE_DATE_EPOCH") {
            Ok(v) => (
                v.trim()
                    .parse::<i64>()
                    .map_err(|e| format!("SOURCE_DATE_EPOCH is not an integer: {e}"))?,
                "source-date-epoch",
                None,
            ),
            Err(_) => (PINNED_EPOCH, "commit", Some(PINNED_COMMIT)),
        };
        let mut epoch_fields = vec![
            ("unix", epoch_unix.to_string()),
            ("source", jstr(epoch_source)),
        ];
        if let Some(c) = epoch_commit {
            epoch_fields.push(("commit", jstr(c)));
        }
        let command = {
            let mut parts = vec![PROGRAM_NAME.to_string()];
            parts.extend(args.rest.iter().map(|a| {
                if a.contains(' ') {
                    format!("'{a}'")
                } else {
                    a.clone()
                }
            }));
            parts.join(" ")
        };
        let provenance = jblock(
            4,
            &[
                (
                    "generator",
                    jstr(
                        "noh_wt_certificate.rs with --emit-run (render strand P0-A); \
                         base pin axeyum 75663ef8, built with rustc --edition 2024",
                    ),
                ),
                ("command", jstr(&command)),
                (
                    "inputs",
                    jlist(
                        6,
                        &[jline(&[
                            ("path", jstr(source)),
                            ("sha256", jstr(&sha)),
                            ("role", jstr("source")),
                        ])],
                    ),
                ),
                ("exit_status", exit_status.to_string()),
                ("epoch", jblock(6, &epoch_fields)),
            ],
        );

        let passed = self.claims.iter().filter(|c| c.failures == 0).count();
        let failed = self.claims.len() - passed;
        let summary = if exit_status == 0 {
            format!(
                "{} of {} checks of the p = 2 tame-point weight certificate passed; \
                 {total_failures} assertion failures.",
                passed,
                self.claims.len()
            )
        } else {
            format!(
                "{failed} of {} checks of the p = 2 tame-point weight certificate FAILED \
                 ({total_failures} assertion failures); the run exited {exit_status}.",
                self.claims.len()
            )
        };
        let outcome = if exit_status == 0 {
            "established"
        } else {
            "refuted"
        };

        // The replay line is DERIVED from the arguments this run actually
        // received, so pasting it reproduces this record byte for byte.
        let derived_replay = format!(
            "rustc --edition 2024 -O -o /tmp/noh_wt_cert {source} && /tmp/noh_wt_cert {}",
            command
                .strip_prefix(PROGRAM_NAME)
                .unwrap_or(&command)
                .trim_start()
        );
        let mut replay = vec![(
            "line",
            jstr(args.replay_line.as_deref().unwrap_or(&derived_replay)),
        )];
        replay.push(("cwd", jstr(".")));
        replay.push(("expected_exit_status", exit_status.to_string()));
        if let Some(s) = args.replay_seconds {
            replay.push(("expected_seconds", s.to_string()));
        }

        let notes = args.notes.clone().unwrap_or_else(|| {
            "Claim c1 compares two routes that are NOT independent (20-verify.md P2-8): \
             c_ode iterates the same product in a different association order, so c1 checks \
             exact rational arithmetic, not the operator U_2. The only binding to U_2 is \
             claim c2, the hard-coded coefficient rows recomputed by workstream 01."
                .to_string()
        });

        Ok(format!(
            "{}\n",
            jblock(
                2,
                &[
                    ("schema_version", "1".to_string()),
                    ("id", jstr(&args.record_id)),
                    ("provenance", provenance),
                    ("summary", jstr(&summary)),
                    ("outcome", jstr(outcome)),
                    (
                        "claims",
                        jlist(
                            4,
                            &self.claims.iter().map(|c| c.render(4)).collect::<Vec<_>>()
                        )
                    ),
                    ("stats", jblock(4, &self.stats)),
                    ("tables", jblock(4, &self.tables)),
                    ("replay", jblock(4, &replay)),
                    ("notes", jstr(&notes)),
                ]
            )
        ))
    }
}
