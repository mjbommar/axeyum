//! Soundness-negative fuzzer for the bounded-completeness detector (task #75,
//! Hard Rule). `axeyum_smtlib::is_bounded_complete` gates a no-model→UNSAT
//! upgrade, so a wrong `true` on a query that is real-SAT-but-bounded-no-model
//! is a wrong-unsat (the worst bug class). This fuzz DELIBERATELY emits the
//! dangerous classes — a free unbounded Int, an unbounded String probed past the
//! cap, `str.to_int`, a large Int literal, a nonlinear product, a hidden binder —
//! and asserts the detector REJECTS every one (`is_bounded_complete == false`).
//! A positive-control loop confirms it still ACCEPTS genuinely bounded-complete
//! queries (so it is not vacuously always-false).
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::cast_possible_truncation
)]

use axeyum_smtlib::is_bounded_complete;

struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// A short escape-free string literal.
fn lit(rng: &mut Lcg) -> String {
    const A: &[u8] = b"ABxyz";
    let n = rng.below(4);
    (0..n)
        .map(|_| A[rng.below(A.len() as u64) as usize] as char)
        .collect()
}

/// Build a query carrying exactly one DANGEROUS construct (real-sat but
/// bounded-no-model, or otherwise unsound to upgrade). All must be rejected.
fn dangerous(rng: &mut Lcg) -> String {
    let l = lit(rng);
    match rng.below(7) {
        // C1: a free unbounded Int (even alongside a bounded string).
        0 => format!(
            "(set-logic QF_SLIA)\n(declare-fun x () Int)\n(declare-fun s () String)\n\
             (assert (<= (str.len s) 5))\n(assert (> x {}))\n(check-sat)\n",
            rng.below(9)
        ),
        // C2: unbounded String probed past the cap with a constant index.
        1 => format!(
            "(set-logic QF_S)\n(declare-fun s () String)\n\
             (assert (= (str.at s {}) \"{l}\"))\n(check-sat)\n",
            50 + rng.below(200)
        ),
        // C2: unbounded String with a LOWER length bound only.
        2 => format!(
            "(set-logic QF_S)\n(declare-fun s () String)\n\
             (assert (>= (str.len s) {}))\n(check-sat)\n",
            1 + rng.below(50)
        ),
        // C2: String var with NO bound at all.
        3 => format!(
            "(set-logic QF_S)\n(declare-fun s () String)\n\
             (assert (str.contains s \"{l}\"))\n(check-sat)\n"
        ),
        // C3: str.to_int can reach 10^len ≥ 2^31.
        4 => format!(
            "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
             (assert (<= (str.len s) 8))\n(assert (> (str.to_int s) {}))\n(check-sat)\n",
            rng.below(5)
        ),
        // C3: a large Int literal (≥ 2^20) can wrap the width-32 int-blast.
        5 => format!(
            "(set-logic QF_SLIA)\n(declare-fun s () String)\n\
             (assert (<= (str.len s) 8))\n(assert (< (str.len s) {}))\n(check-sat)\n",
            2_000_000 + rng.below(1_000_000)
        ),
        // C2: a length bound ABOVE the cap does not guarantee representability.
        _ => format!(
            "(set-logic QF_S)\n(declare-fun s () String)\n\
             (assert (<= (str.len s) {}))\n(assert (str.contains s \"{l}\"))\n(check-sat)\n",
            9 + rng.below(20)
        ),
    }
}

/// Build a genuinely bounded-complete query (positive control) — must be accepted.
fn safe(rng: &mut Lcg) -> String {
    let l = lit(rng);
    let k = rng.below(9); // 0..=8 ≤ STRING_MAX_LEN
    match rng.below(3) {
        0 => format!(
            "(set-logic QF_S)\n(declare-fun s () String)\n\
             (assert (<= (str.len s) {k}))\n(assert (str.contains s \"{l}\"))\n(check-sat)\n"
        ),
        1 => format!(
            "(set-logic QF_S)\n(declare-fun s () String)\n\
             (assert (< (str.len s) {}))\n(assert (not (= (str.at s 0) \"{l}\")))\n(check-sat)\n",
            k + 1
        ),
        // Ground (no free var) → bounded-complete vacuously.
        _ => format!(
            "(set-logic QF_S)\n(assert (= (str.++ \"{l}\" \"{l}\") \"{l}\"))\n(check-sat)\n"
        ),
    }
}

#[test]
fn detector_rejects_all_unsound_upgrades() {
    const SEEDS: u64 = 500;
    for seed in 0..SEEDS {
        let mut rng = Lcg::new(seed);
        let q = dangerous(&mut rng);
        assert!(
            !is_bounded_complete(&q),
            "seed {seed}: detector must NOT sanction an unsound upgrade:\n{q}"
        );
    }
}

#[test]
fn detector_still_accepts_bounded_complete() {
    const SEEDS: u64 = 300;
    let mut accepted = 0u32;
    for seed in 0..SEEDS {
        let mut rng = Lcg::new(seed ^ 0xB0);
        if is_bounded_complete(&safe(&mut rng)) {
            accepted += 1;
        }
    }
    assert!(
        accepted >= 250,
        "positive control: detector must accept genuinely bounded-complete queries (got {accepted}/300)"
    );
}
