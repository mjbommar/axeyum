//! Property / differential test for the regex-membership sub-solver (T-C.5,
//! ADR-0054).
//!
//! For each random single-variable membership problem over a tiny alphabet we
//! cross-check the sub-solver's verdict against an **independent brute-force
//! enumeration** driven by the reference matcher:
//!
//! * a `Sat(w)` witness must replay (`accepts(w)`) — no wrong `sat` (the same
//!   gate the solver enforces, re-asserted here);
//! * an `Unsat` verdict must be consistent with brute force: **no** string over
//!   the alphabet up to the enumeration bound may satisfy the problem — a wrong
//!   `unsat` (the dangerous direction) is caught here;
//! * conversely, when brute force *finds* a short witness the solver must not say
//!   `Unsat`.
//!
//! The generator biases toward the shapes that stress the engine: intersection,
//! complement, native loops, and nesting.

use axeyum_strings::SearchBudget;
use axeyum_strings::regex::membership::{Membership, MembershipOutcome};
use axeyum_strings::regex::{Regex, matches};

/// The alphabet the brute force enumerates over (code points for `a`, `b`, `c` —
/// `u32::from` is not const-stable on the MSRV, so the literals are inline).
const ALPHABET: [u32; 3] = [0x61, 0x62, 0x63];
/// The maximum brute-force string length (strings of length `0..=BRUTE_LEN`).
const BRUTE_LEN: usize = 6;

/// A tiny deterministic xorshift RNG (no external dependency; the crate forbids
/// `unsafe` and has no `rand`).
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: u32) -> u32 {
        u32::try_from(self.next() % u64::from(n)).expect("< n fits u32")
    }
}

/// Generates a random regex over [`ALPHABET`] with a bounded structural `depth`.
fn gen_regex(rng: &mut Rng, depth: u32) -> Regex {
    if depth == 0 {
        // Leaf: a single alphabet character or a small range.
        return match rng.below(4) {
            0 => Regex::character(ALPHABET[0]),
            1 => Regex::character(ALPHABET[1]),
            2 => Regex::character(ALPHABET[2]),
            _ => Regex::char_range(ALPHABET[0], ALPHABET[2]),
        };
    }
    match rng.below(11) {
        0 => Regex::character(ALPHABET[rng.below(3) as usize]),
        1 => Regex::concat(gen_regex(rng, depth - 1), gen_regex(rng, depth - 1)),
        2 => Regex::union(gen_regex(rng, depth - 1), gen_regex(rng, depth - 1)),
        3 => Regex::inter(gen_regex(rng, depth - 1), gen_regex(rng, depth - 1)),
        4 => Regex::comp(gen_regex(rng, depth - 1)),
        5 => Regex::star(gen_regex(rng, depth - 1)),
        6 => Regex::plus(gen_regex(rng, depth - 1)),
        7 => Regex::opt(gen_regex(rng, depth - 1)),
        8 => {
            let lo = rng.below(3);
            let hi = lo + rng.below(3);
            Regex::repeat(gen_regex(rng, depth - 1), lo, Some(hi))
        }
        9 => Regex::repeat(gen_regex(rng, depth - 1), rng.below(3), None),
        _ => Regex::char_range(ALPHABET[0], ALPHABET[2]),
    }
}

/// A random single-variable membership problem.
fn gen_problem(rng: &mut Rng) -> Membership {
    let n_pos = 1 + rng.below(2); // 1..=2 positives
    let n_neg = rng.below(2); // 0..=1 negatives
    let positives = (0..n_pos).map(|_| gen_regex(rng, 3)).collect();
    let negatives = (0..n_neg).map(|_| gen_regex(rng, 3)).collect();
    // Occasional small length bounds.
    let (len_lo, len_hi) = match rng.below(4) {
        0 => (rng.below(3), None),
        1 => (0, Some(rng.below(5))),
        2 => {
            let lo = rng.below(3);
            (lo, Some(lo + rng.below(3)))
        }
        _ => (0, None),
    };
    Membership {
        positives,
        negatives,
        len_lo,
        len_hi,
    }
}

/// Whether any string over [`ALPHABET`] of length `0..=BRUTE_LEN` satisfies `m`,
/// decided purely by the reference matcher (no derivative code) — the independent
/// oracle. Returns the first such witness for diagnostics.
fn brute_witness(m: &Membership) -> Option<Vec<u32>> {
    let mut s: Vec<u32> = Vec::new();
    brute_rec(m, &mut s)
}

fn brute_rec(m: &Membership, s: &mut Vec<u32>) -> Option<Vec<u32>> {
    if accepts(m, s) {
        return Some(s.clone());
    }
    if s.len() >= BRUTE_LEN {
        return None;
    }
    for &c in &ALPHABET {
        s.push(c);
        if let Some(w) = brute_rec(m, s) {
            return Some(w);
        }
        s.pop();
    }
    None
}

/// The reference acceptance predicate (matcher only), mirroring the sub-solver's
/// own replay gate.
fn accepts(m: &Membership, s: &[u32]) -> bool {
    let len = u32::try_from(s.len()).unwrap_or(u32::MAX);
    if len < m.len_lo || m.len_hi.is_some_and(|h| len > h) {
        return false;
    }
    m.positives.iter().all(|p| matches(p, s)) && m.negatives.iter().all(|n| !matches(n, s))
}

#[test]
fn membership_matches_brute_force() {
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let budget = SearchBudget::new(200_000);
    let mut sat = 0u32;
    let mut unsat = 0u32;
    let mut unknown = 0u32;
    for _ in 0..2_000 {
        let m = gen_problem(&mut rng);
        let brute = brute_witness(&m);
        match m.solve(&budget) {
            MembershipOutcome::Sat(w) => {
                sat += 1;
                assert!(
                    accepts(&m, &w),
                    "sat witness failed replay: {w:?} for {m:?}"
                );
            }
            MembershipOutcome::Unsat => {
                unsat += 1;
                assert!(
                    brute.is_none(),
                    "solver said UNSAT but brute force found witness {:?} for {m:?}",
                    brute.unwrap()
                );
            }
            MembershipOutcome::Unknown => unknown += 1,
        }
    }
    // Sanity: the generator produces a healthy mix of all three verdicts.
    assert!(sat > 100, "too few sat cases: {sat}");
    assert!(unsat > 50, "too few unsat cases: {unsat}");
    eprintln!("membership property: sat={sat} unsat={unsat} unknown={unknown}");
}

#[test]
fn adversarial_unsat_seeds_never_sat() {
    let budget = SearchBudget::new(200_000);
    // Hand-built empty-language problems: the solver must never say `sat`, and a
    // sat witness (if it ever wrongly claimed one) must fail replay.
    let seeds = [
        // a* ∩ b*  with len ≥ 1  (only common string is ε).
        Membership {
            positives: vec![Regex::star(Regex::character(u32::from(b'a')))],
            negatives: vec![],
            len_lo: 1,
            len_hi: None,
        },
        // x ∈ "a"  ∧  x ∉ "a".
        Membership {
            positives: vec![Regex::character(u32::from(b'a'))],
            negatives: vec![Regex::character(u32::from(b'a'))],
            len_lo: 0,
            len_hi: None,
        },
        // a* ∩ ∁(a*)  is empty.
        Membership {
            positives: vec![Regex::star(Regex::character(u32::from(b'a')))],
            negatives: vec![Regex::star(Regex::character(u32::from(b'a')))],
            len_lo: 0,
            len_hi: None,
        },
        // impossible length window.
        Membership {
            positives: vec![Regex::star(Regex::character(u32::from(b'a')))],
            negatives: vec![],
            len_lo: 5,
            len_hi: Some(2),
        },
    ];
    let mut m = seeds[0].clone();
    m.positives
        .push(Regex::star(Regex::character(u32::from(b'b'))));
    let all = [m, seeds[1].clone(), seeds[2].clone(), seeds[3].clone()];
    for prob in &all {
        match prob.solve(&budget) {
            MembershipOutcome::Sat(w) => {
                panic!("adversarial unsat seed returned sat with witness {w:?}: {prob:?}")
            }
            MembershipOutcome::Unsat | MembershipOutcome::Unknown => {}
        }
    }
}
