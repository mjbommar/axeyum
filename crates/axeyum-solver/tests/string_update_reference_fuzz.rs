//! Self-checking soundness fuzzer for `str.update` (task #74).
//!
//! `str.update` is an underspecified/partial operator on its `idx` axis (a
//! negative index or one `≥ len(s)` is a no-op; the replacement is clipped to
//! `len(s)`). The Hard Rule (CLAUDE.md) requires a fuzz seed-class that
//! DELIBERATELY emits those degenerate corners, or the soundness gate is blind
//! exactly where the operator is most fragile.
//!
//! The natural differential oracle (the system Z3 binary) does NOT implement
//! `str.update` — it answers `unknown constant str.update` and then decides
//! `(check-sat)` on the partial context, a false verdict — so it cannot
//! adjudicate this operator. cvc5 (the corpus's authority) does, but rather than
//! depend on an external binary this fuzz is **self-checking**: a tiny,
//! obviously-correct Rust reference implements the SMT-LIB semantics, and each
//! random ground `(str.update s i t)` is pinned against the reference result.
//! Every reference value below was confirmed against cvc5:
//! `(str.update "" 0 "XY") = ""`, `(str.update "AAAAAA" 5 "XY") = "AAAAAX"`
//! (clip), `(str.update "A" 0 "XYZ") = "X"`, out-of-range `idx` → `s` unchanged.
#![cfg(feature = "full")]
#![allow(clippy::many_single_char_names, clippy::similar_names)]
//!
//! Method: for each seed we draw a ground `s`, an `idx` spanning
//! `[-2 .. len(s)+2]` (so negatives and `≥ len` are dense), and a `t` that can
//! overrun `len(s) − idx`. We compute the reference result `r` and assert:
//!   - `(= (str.update s idx t) r)` is **sat** — axeyum produces exactly `r`
//!     (for ground terms, sat ⟺ the bytes match; the model is replay-checked).
//!   - `(= (str.update s idx t) (str.++ r "Z"))` is **NOT sat** — a result one
//!     byte longer than `len(s)` is unproducible (an update never changes the
//!     length), guarding against a "matches everything" encoding bug.

use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

/// The trusted SMT-LIB `str.update` reference (confirmed against cvc5): replace
/// the bytes of `s` from position `i` with `t`, but only when `0 ≤ i < len(s)`
/// (else `s` unchanged), and clip the write at `len(s)` (the length is
/// invariant).
fn reference_update(s: &[u8], i: i64, t: &[u8]) -> Vec<u8> {
    let n = i64::try_from(s.len()).expect("bounded length");
    if i < 0 || i >= n {
        return s.to_vec(); // out of range → no-op
    }
    let mut r = s.to_vec();
    for (k, &b) in t.iter().enumerate() {
        let pos = i + i64::try_from(k).expect("bounded index");
        if pos >= n {
            break; // clip to len(s)
        }
        r[usize::try_from(pos).expect("non-negative")] = b;
    }
    r
}

// --- deterministic RNG (mirrors the other string fuzzers) --------------------

struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("modulus fits usize")
    }
    fn in_range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = u64::try_from(hi - lo + 1).expect("non-negative span");
        lo + i64::try_from(self.next_u64() % span).expect("offset within span")
    }
}

/// A short escape-free ASCII string over a tiny alphabet (max length `max`), so
/// the SMT-LIB literal needs no quoting/escaping.
fn gen_str(rng: &mut Lcg, max: usize) -> Vec<u8> {
    const ALPHABET: &[u8] = b"ABCXYZ";
    let len = rng.below((max + 1) as u64);
    (0..len)
        .map(|_| ALPHABET[rng.below(ALPHABET.len() as u64)])
        .collect()
}

/// Format an `Int` literal, using `(- k)` for negatives (SMT-LIB has no signed
/// numerals).
fn int_lit(i: i64) -> String {
    if i < 0 {
        format!("(- {})", -i)
    } else {
        i.to_string()
    }
}

fn decide(text: &str) -> CheckResult {
    solve_smtlib(text, &config())
        .expect("ground str.update script decides without error")
        .result
}

#[test]
fn str_update_matches_reference_disagree_zero() {
    // The bounded string model caps length at 8; keep operands well inside it.
    const MAX_S: usize = 6;
    const MAX_T: usize = 4;
    const SEEDS: u64 = 500;

    let mut checked = 0u32;
    for seed in 0..SEEDS {
        let mut rng = Lcg::new(seed);
        let s = gen_str(&mut rng, MAX_S);
        let t = gen_str(&mut rng, MAX_T);
        // idx densely spans the degenerate axis: [-2 .. len(s)+2].
        let n = i64::try_from(s.len()).expect("bounded");
        let idx = rng.in_range(-2, n + 2);
        let r = reference_update(&s, idx, &t);

        let s_lit = String::from_utf8(s.clone()).expect("ascii");
        let t_lit = String::from_utf8(t.clone()).expect("ascii");
        let r_lit = String::from_utf8(r.clone()).expect("ascii");
        let update = format!("(str.update \"{s_lit}\" {} \"{t_lit}\")", int_lit(idx));

        // (1) axeyum must produce EXACTLY the reference bytes → sat.
        let ok = format!("(set-logic QF_SLIA)\n(assert (= {update} \"{r_lit}\"))\n(check-sat)\n");
        let ok_res = decide(&ok);
        assert!(
            matches!(ok_res, CheckResult::Sat(_)),
            "seed {seed}: str.update(\"{s_lit}\", {idx}, \"{t_lit}\") must equal \
             reference \"{r_lit}\" (got {ok_res:?})"
        );

        // (2) a result one byte longer than len(s) is UNPRODUCIBLE (length is
        //     invariant under update) → must NOT be sat. Guards vacuous-sat.
        let grown =
            format!("(set-logic QF_SLIA)\n(assert (= {update} \"{r_lit}Z\"))\n(check-sat)\n");
        let grown_res = decide(&grown);
        assert!(
            !matches!(grown_res, CheckResult::Sat(_)),
            "seed {seed}: str.update never changes the length — \"{r_lit}Z\" \
             (len {}) must be unproducible from a len-{} source (got {grown_res:?})",
            r.len() + 1,
            s.len()
        );
        checked += 1;
    }
    assert!(checked >= 400, "fuzz must exercise the operator broadly");
}

/// The exact empty-string corner the z3-differential fuzz flagged as a spurious
/// disagreement (z3 lacks `str.update`): `(str.update "" 0 s)` is `""` for every
/// `s`, so its length is `0` and it can never be `4`. Axeyum's `unsat`/no-model
/// here is CORRECT.
#[test]
fn str_update_empty_source_is_noop() {
    assert_eq!(reference_update(b"", 0, b"XY"), b"".to_vec());
    // Ground: the length is 0, so equality to a length-1 result is not sat.
    let text = "(set-logic QF_S)\n\
                (assert (= (str.len (str.update \"\" 0 \"X\")) 1))\n\
                (check-sat)\n";
    assert!(
        !matches!(decide(text), CheckResult::Sat(_)),
        "update of the empty string is the empty string (length 0, never 1)"
    );
}
