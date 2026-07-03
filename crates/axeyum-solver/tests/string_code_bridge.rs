//! The `str.to_code` ↔ LIA code-point bridge (P2.7 A.2 code/len↔LIA).
//!
//! The unbounded length/code abstraction gives `str.to_code s` a fresh `Int`
//! code twin tied to `len(s)` by its SMT-LIB definition
//! (`(len=1 ∧ 0≤c≤0x2FFFF) ∨ (len≠1 ∧ c=-1)`), plus a single-character
//! code↔equality link (`len(p)=1 ∧ len(q)=1 ∧ c_p=c_q ⇒ p=q`). Both are sound
//! **relaxations** of the real (Unicode) string theory, so the abstraction being
//! `unsat` proves the original `unsat` — which lets the string gate close the
//! `str-code-unsat*` regressions the bounded integer bit-blast could not.
//!
//! These tests pin (1) the three real corpus shapes decide `unsat`, (2) the
//! abstraction never refutes a satisfiable instance (≥1000 model-consistent
//! scripts stay non-`unsat`), and (3) an adversarial brute-force cross-check over
//! a small byte-model universe agrees with the solver's `unsat` verdict.
#![allow(
    clippy::needless_raw_string_hashes,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop
)]

use std::fmt::Write as _;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

fn decide(text: &str) -> CheckResult {
    solve_smtlib(text, &SolverConfig::default())
        .expect("code-bridge scripts parse and decide")
        .result
}

fn is_unsat(text: &str) -> bool {
    matches!(decide(text), CheckResult::Unsat)
}

// ---------------------------------------------------------------------------
// (1) Per-file integration tests — inline minimal versions of the real corpus
//     shapes (r1_QF_SLIA_str-code-unsat{,-2,-3}.smt2).
// ---------------------------------------------------------------------------

#[test]
fn code_range_sum_distinct_is_unsat() {
    // str-code-unsat.smt2: x,y,z single chars in [65,75]; x+y = x+z = 140 forces
    // code(y) = code(z), so y = z, contradicting distinct.
    let t = r#"(set-logic QF_SLIA)
(declare-fun x () String)(declare-fun y () String)(declare-fun z () String)
(assert (>= (str.to_code x) 65))(assert (<= (str.to_code x) 75))
(assert (>= (str.to_code y) 65))(assert (<= (str.to_code y) 75))
(assert (>= (str.to_code z) 65))(assert (<= (str.to_code z) 75))
(assert (= (+ (str.to_code x) (str.to_code y)) 140))
(assert (= (+ (str.to_code x) (str.to_code z)) 140))
(assert (distinct x y z))
(check-sat)"#;
    assert!(is_unsat(t), "code range + sum + distinct must be unsat");
}

#[test]
fn code_single_char_out_of_byte_range_is_unsat() {
    // str-code-unsat-2.smt2: len(x)=1 forces code(x) ∈ [0,0x2FFFF]; the assertion
    // demands code(x) < 0 or code(x) > 10^28 — impossible.
    let t = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 1))
(assert (or (< (str.to_code x) 0) (> (str.to_code x) 10000000000000000000000000000)))
(check-sat)"#;
    assert!(
        is_unsat(t),
        "single char with impossible code must be unsat"
    );
}

#[test]
fn code_sum_distinct_with_literals_is_unsat() {
    // str-code-unsat-3.smt2: x+y=140, x+z=141 with codes in [65,75] and all of
    // x,y,z distinct from each other and from "B".."E" (66..69) has no solution.
    let t = r#"(set-logic QF_SLIA)
(declare-fun x () String)(declare-fun y () String)(declare-fun z () String)
(assert (>= (str.to_code x) 65))(assert (<= (str.to_code x) 75))
(assert (>= (str.to_code y) 65))(assert (<= (str.to_code y) 75))
(assert (>= (str.to_code z) 65))(assert (<= (str.to_code z) 75))
(assert (= (+ (str.to_code x) (str.to_code y)) 140))
(assert (= (+ (str.to_code x) (str.to_code z)) 141))
(assert (distinct x y z "B" "C" "D" "E"))
(check-sat)"#;
    assert!(
        is_unsat(t),
        "code sum + distinct-with-literals must be unsat"
    );
}

#[test]
fn code_bridge_does_not_over_refute_above_byte_range() {
    // Regression guard: the code domain caps at the SMT-LIB max code point
    // (0x2FFFF), NOT the byte model's 255. A single char with code 300 is
    // satisfiable in the real theory, so the abstraction must NOT report unsat.
    let t = r#"(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.len x) 1))
(assert (= (str.to_code x) 300))
(check-sat)"#;
    assert!(
        !is_unsat(t),
        "code 300 is satisfiable in the real theory — must not wrongly refute"
    );
}

#[test]
fn code_range_satisfiable_is_not_unsat() {
    // A genuinely satisfiable code problem: two distinct chars whose codes sum to
    // a reachable value. Must never be refuted by the abstraction upgrade.
    let t = r#"(set-logic QF_SLIA)
(declare-fun x () String)(declare-fun y () String)
(assert (>= (str.to_code x) 65))(assert (<= (str.to_code x) 75))
(assert (>= (str.to_code y) 65))(assert (<= (str.to_code y) 75))
(assert (= (+ (str.to_code x) (str.to_code y)) 141))
(assert (distinct x y))
(check-sat)"#;
    assert!(!is_unsat(t), "reachable code sum + distinct is satisfiable");
}

// ---------------------------------------------------------------------------
// A tiny deterministic LCG (no clock / OS entropy) for the property tests.
// ---------------------------------------------------------------------------

struct Lcg(u64);
impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed ^ 0x9E37_79B9_7F4A_7C15)
    }
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
}

// ---------------------------------------------------------------------------
// (2) Property: the abstraction never refutes a model-consistent instance.
//     Build a concrete distinct single-char assignment, generate constraints it
//     satisfies, and require the verdict is never `unsat`.
// ---------------------------------------------------------------------------

#[test]
fn never_refutes_model_consistent_code_problems() {
    let mut rng = Lcg::new(0x00C0_DE01);
    let mut checked = 0u32;
    for _ in 0..1500 {
        let n = rng.below(3) as usize + 1; // 1..=3 vars
        // Distinct single-char codes in [65, 90] (uppercase ASCII, byte-safe).
        let mut codes: Vec<i64> = Vec::new();
        while codes.len() < n {
            let c = rng.range(65, 90);
            if !codes.contains(&c) {
                codes.push(c);
            }
        }
        let mut text = String::from("(set-logic QF_SLIA)\n");
        for i in 0..n {
            let _ = writeln!(text, "(declare-fun x{i} () String)");
        }
        // Range brackets consistent with the assignment.
        for i in 0..n {
            let lo = codes[i] - rng.range(0, 5);
            let hi = codes[i] + rng.range(0, 5);
            let _ = writeln!(text, "(assert (>= (str.to_code x{i}) {lo}))");
            let _ = writeln!(text, "(assert (<= (str.to_code x{i}) {hi}))");
        }
        // A sum constraint using the real sum (satisfiable).
        if n >= 2 {
            let a = rng.below(n as u64) as usize;
            let mut b = rng.below(n as u64) as usize;
            if b == a {
                b = (a + 1) % n;
            }
            let sum = codes[a] + codes[b];
            let _ = writeln!(
                text,
                "(assert (= (+ (str.to_code x{a}) (str.to_code x{b})) {sum}))"
            );
        }
        // Distinct is valid because the codes are pairwise distinct.
        if n >= 2 && rng.below(2) == 0 {
            let mut d = String::from("(assert (distinct");
            for i in 0..n {
                let _ = write!(d, " x{i}");
            }
            d.push_str("))\n");
            text.push_str(&d);
        }
        text.push_str("(check-sat)\n");
        assert!(
            !is_unsat(&text),
            "model-consistent code problem wrongly refuted:\n{text}"
        );
        checked += 1;
    }
    assert!(checked >= 1000, "expected >= 1000 checks, got {checked}");
}

// ---------------------------------------------------------------------------
// (3) Adversarial: random small constraints, cross-checked against a brute-force
//     byte-model enumeration over a small string universe.
// ---------------------------------------------------------------------------

/// A code-fragment atom, emittable to SMT and evaluable under a byte-model
/// assignment (`Vec<u8>` per variable).
#[derive(Clone)]
enum Atom {
    Ge(usize, i64),
    Le(usize, i64),
    EqK(usize, i64),
    Sum2(usize, usize, i64),
    DistinctAll,
}

const ALPHA: u8 = 6; // byte alphabet 0..=6
const MAXK: i64 = 6; // constants 0..=6

fn to_code(s: &[u8]) -> i64 {
    if s.len() == 1 { i64::from(s[0]) } else { -1 }
}

fn eval_atom(atom: &Atom, model: &[Vec<u8>]) -> bool {
    match *atom {
        Atom::Ge(v, k) => to_code(&model[v]) >= k,
        Atom::Le(v, k) => to_code(&model[v]) <= k,
        Atom::EqK(v, k) => to_code(&model[v]) == k,
        Atom::Sum2(a, b, k) => to_code(&model[a]) + to_code(&model[b]) == k,
        Atom::DistinctAll => {
            for i in 0..model.len() {
                for j in i + 1..model.len() {
                    if model[i] == model[j] {
                        return false;
                    }
                }
            }
            true
        }
    }
}

/// SMT-LIB numeral: a negative integer must be written `(- n)`.
fn smt_int(k: i64) -> String {
    if k < 0 {
        format!("(- {})", -k)
    } else {
        k.to_string()
    }
}

fn emit_atom(atom: &Atom) -> String {
    match *atom {
        Atom::Ge(v, k) => format!("(>= (str.to_code x{v}) {})", smt_int(k)),
        Atom::Le(v, k) => format!("(<= (str.to_code x{v}) {})", smt_int(k)),
        Atom::EqK(v, k) => format!("(= (str.to_code x{v}) {})", smt_int(k)),
        Atom::Sum2(a, b, k) => {
            format!(
                "(= (+ (str.to_code x{a}) (str.to_code x{b})) {})",
                smt_int(k)
            )
        }
        Atom::DistinctAll => String::new(), // handled by caller (needs all vars)
    }
}

/// Every string over the small universe (lengths 0..=2, alphabet 0..=ALPHA).
fn universe() -> Vec<Vec<u8>> {
    let mut u = vec![vec![]];
    for a in 0..=ALPHA {
        u.push(vec![a]);
    }
    for a in 0..=ALPHA {
        for b in 0..=ALPHA {
            u.push(vec![a, b]);
        }
    }
    u
}

/// Brute-force satisfiability over the small universe.
fn brute_sat(n: usize, atoms: &[Atom]) -> bool {
    let uni = universe();
    let mut idx = vec![0usize; n];
    loop {
        let model: Vec<Vec<u8>> = (0..n).map(|i| uni[idx[i]].clone()).collect();
        if atoms.iter().all(|a| eval_atom(a, &model)) {
            return true;
        }
        // increment odometer
        let mut k = 0;
        loop {
            if k == n {
                return false;
            }
            idx[k] += 1;
            if idx[k] < uni.len() {
                break;
            }
            idx[k] = 0;
            k += 1;
        }
    }
}

#[test]
fn adversarial_brute_force_agreement() {
    let mut rng = Lcg::new(0x00C0_DE02);
    let mut jointly = 0u32;
    for _ in 0..400 {
        let n = rng.below(2) as usize + 1; // 1..=2 vars (brute universe stays small)
        let num_atoms = rng.below(4) as usize + 1;
        let mut atoms: Vec<Atom> = Vec::new();
        // Bound every var's code into the alphabet so any single-char model stays
        // inside the brute-force universe (keeps the sat direction sound to check).
        for v in 0..n {
            atoms.push(Atom::Le(v, MAXK));
        }
        for _ in 0..num_atoms {
            let v = rng.below(n as u64) as usize;
            let atom = match rng.below(5) {
                0 => Atom::Ge(v, rng.range(-1, MAXK)),
                1 => Atom::Le(v, rng.range(-1, MAXK)),
                2 => Atom::EqK(v, rng.range(-1, MAXK)),
                3 if n >= 2 => {
                    let b = (v + 1) % n;
                    Atom::Sum2(v, b, rng.range(-2, 2 * MAXK))
                }
                _ => Atom::DistinctAll,
            };
            atoms.push(atom);
        }
        // Build SMT text.
        let mut text = String::from("(set-logic QF_SLIA)\n");
        for i in 0..n {
            let _ = writeln!(text, "(declare-fun x{i} () String)");
        }
        for atom in &atoms {
            if matches!(atom, Atom::DistinctAll) {
                if n >= 2 {
                    let mut d = String::from("(assert (distinct");
                    for i in 0..n {
                        let _ = write!(d, " x{i}");
                    }
                    d.push_str("))\n");
                    text.push_str(&d);
                }
            } else {
                let _ = writeln!(text, "(assert {})", emit_atom(atom));
            }
        }
        text.push_str("(check-sat)\n");

        let brute = brute_sat(n, &atoms);
        match decide(&text) {
            CheckResult::Unsat => {
                assert!(
                    !brute,
                    "solver said UNSAT but brute-force found a model:\n{text}"
                );
                jointly += 1;
            }
            CheckResult::Sat(_) => {
                assert!(
                    brute,
                    "solver said SAT but brute-force found no model in-universe:\n{text}"
                );
                jointly += 1;
            }
            CheckResult::Unknown(_) => {}
        }
    }
    assert!(
        jointly >= 20,
        "expected some jointly-decided cases, got {jointly}"
    );
}
