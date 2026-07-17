//! Adversarial differential soundness fuzzer for the bounded `QF_SEQ` (SMT-LIB
//! Sequences, ADR-0029/0051 packed-BV model) theory against the Z3 oracle.
//!
//! Until this file there was **no sequence differential fuzz in the repo at all**
//! ([underspecified-operator-fuzz-coverage.md](../../../docs/research/01-foundations/underspecified-operator-fuzz-coverage.md),
//! GAP-Q1). Sequences carry the exact soundness hazard the Hard Rule is written
//! for: **`seq.nth` out of bounds is UNDERSPEC** — SMT-LIB leaves the result
//! *any* total value of the element sort, so a stray fold to a fixed convention
//! (zero-padding) would turn a legitimate `sat` into a **wrong `unsat`** (the
//! same shape as the `div`-by-const-0 `a946f925` wrong-unsat, the `str.from_code`
//! wrong-sat, and the FP signed-zero wrong-unsat). The precise semantics stressed
//! here (nailed against parse.rs and Z3 4.13.3):
//!
//! - **UNDERSPEC (the genuine risk axis)** — `(seq.nth s i)` for `i` out of
//!   `[0, len(s))` (negative, `≥ len`, or on the empty sequence): axeyum models
//!   the out-of-bounds result as a **fresh, free** value of the element sort,
//!   keyed per syntactic `(s, i)` with an eager Ackermann congruence pass so it
//!   stays a *function* (parse.rs `seq_nth` / `seq_nth_oob_value`). A formula
//!   that pins the OOB value to a constant must therefore be **SAT** (the value
//!   is free) and must NEVER be refuted — `(not (= (seq.nth s i_oob) 0))` is SAT,
//!   proving the OOB value is not folded to `0`.
//! - **TOTAL-with-edges (must match the convention Z3 also uses)** — `seq.at` OOB
//!   is the empty sequence (total, mirrors `str.at`); `seq.extract` OOB start/len
//!   clamps / yields empty; `seq.len`/`seq.++`/`seq.unit`/`seq.rev`/`seq.update`
//!   are total.
//!
//! **Bounded-model soundness (why an `unsat` is trustworthy).** The packed layout
//! bounds each sequence's length (`SEQ_LEN_SOFT_CAP`) and, for `(Seq Int)`, the
//! element width. A bounded `unsat` is only sound if it is *bound-independent*:
//! axeyum's unbounded length abstraction (P2.7 A.2) downgrades a bounded `unsat`
//! to `unknown` whenever the encoding bound could have caused it (the `overcap
//! len 12` case decides `unknown`, not `unsat`). So axeyum is *incomplete* on many
//! sequence unsats (they SKIP as `unknown`) but must never emit a **wrong**
//! verdict — which is exactly what this fuzz checks.
//!
//! **Domain-alignment note (why the differential is sound despite the BV model).**
//! `(Seq Int)` packs each element as a two's-complement `BitVec(16)`; an element
//! literal outside the signed 16-bit range is *declined* (never wrapped), so the
//! generator keeps `Int` element literals tiny. `(Seq (_ BitVec 4))` and
//! `(Seq Bool)` are exactly representable, so those carry no domain mismatch at
//! all. Sequence length in the generated scripts stays within the packed bound
//! for the SAT-biased families; the length-contradiction / order-violation
//! families produce bound-independent unsats the abstraction confirms.
//!
//! Method (mirroring `fp_differential_fuzz.rs`): a fixed-seed LCG (no clock, no OS
//! entropy) deterministically generates hundreds of small random `QF_SEQ` scripts
//! as **SMT-LIB 2 text**, biased to plant the degenerate `seq.nth` OOB shapes.
//! Each script is decided two ways and the verdicts must agree:
//!
//! - axeyum: `solve_smtlib` — parse → lower → solve, and (for `Sat`) replay the
//!   model against the original term. A wrong `Sat` whose model does not replay
//!   surfaces as an error, never a silent `Sat`.
//! - Z3: the same text piped to the system Z3 binary (`/usr/bin/z3`; full
//!   `Seq` theory under `(set-logic ALL)`), with a per-call wall-clock timeout.
//!
//! The joint gate:
//!
//! - axeyum `Sat`   ∧ Z3 `unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `sat`   → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Unknown`/decline    → SKIP (sound-incomplete is allowed; the bounded
//!   model legitimately declines / downgrades many shapes).
//! - Z3 `unknown`/timeout/error  → SKIP (cannot adjudicate).
#![cfg(feature = "full")]
#![cfg(feature = "z3")]

use std::fmt::Write as _;
use std::io::Write as _;
use std::process::{Command, Stdio};
use std::time::Duration;

use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

/// Path to the system Z3 binary (full `Seq` theory under `(set-logic ALL)`).
const Z3_BIN: &str = "/usr/bin/z3";

/// Number of random scripts generated and adjudicated. Each is tiny (≤ 2 seq
/// vars, shallow trees, lengths ≤ a few) so both sides decide quickly. Many
/// shapes legitimately decline / downgrade on the axeyum side (a sound SKIP), so
/// this is sized to leave well over 30 *jointly*-decided scripts after skips.
const INSTANCES: u64 = 700;

/// Per-call Z3 wall-clock budget.
const Z3_TIMEOUT: Duration = Duration::from_secs(3);

/// axeyum wall-clock budget per script.
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(8);

/// Deterministic LCG (MMIX constants) — reproducible from the seed.
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
    fn flip(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
}

/// The three exactly-or-safely representable element sorts. `(_ BitVec 8)` is
/// reserved for `String` (declined), and wider `Int` literals are declined, so
/// these keep the differential free of modeling-difference false positives.
#[derive(Clone, Copy)]
enum Elem {
    /// `(Seq Bool)` — 1-bit element, every value representable.
    Bool,
    /// `(Seq (_ BitVec 4))` — 4-bit element, values `0..=15` representable.
    Bv4,
    /// `(Seq Int)` — 16-bit two's-complement element; the generator only ever
    /// emits *small* literals so nothing is declined for range.
    Int,
}

impl Elem {
    fn pick(rng: &mut Lcg) -> Elem {
        match rng.below(3) {
            0 => Elem::Bool,
            1 => Elem::Bv4,
            _ => Elem::Int,
        }
    }
    /// The SMT-LIB element sort s-expression.
    fn sort(self) -> &'static str {
        match self {
            Elem::Bool => "Bool",
            Elem::Bv4 => "(_ BitVec 4)",
            Elem::Int => "Int",
        }
    }
    /// `(Seq E)` sort s-expression.
    fn seq_sort(self) -> String {
        format!("(Seq {})", self.sort())
    }
    /// A random element literal of this sort.
    fn lit(self, rng: &mut Lcg) -> String {
        match self {
            Elem::Bool => if rng.flip() { "true" } else { "false" }.to_string(),
            Elem::Bv4 => format!("(_ bv{} 4)", rng.below(16)),
            // Small signed ints, comfortably inside the 16-bit packed range.
            Elem::Int => {
                let v = i64::try_from(rng.below(7)).expect("fits") - 3; // -3..=3
                if v < 0 {
                    format!("(- {})", -v)
                } else {
                    v.to_string()
                }
            }
        }
    }
    /// `(as seq.empty (Seq E))` — the empty sequence in this element sort.
    fn empty(self) -> String {
        format!("(as seq.empty {})", self.seq_sort())
    }
}

/// An index expression, biased HARD toward the out-of-bounds shapes (negative,
/// large, and the symbolic variable `i`) that fire the UNDERSPEC `seq.nth` axis.
fn index(rng: &mut Lcg) -> String {
    match rng.below(10) {
        0 | 1 => "(- 1)".to_string(), // negative OOB
        2 => "(- 2)".to_string(),     // negative OOB
        3 => "5".to_string(),         // large OOB
        4 => "9".to_string(),         // large OOB
        5 => "0".to_string(),         // in-range-ish
        6 => "1".to_string(),
        7 => "2".to_string(),
        _ => "i".to_string(), // symbolic (declared by the caller)
    }
}

/// A nested `seq.++` chain of `k` (`1..=3`) unit-of-literal elements — a concrete
/// short sequence. Concatenating *unit* chains stays within the packed bound
/// (concatenating two full-length sequence VARIABLES would exceed it and decline).
fn unit_chain(rng: &mut Lcg, e: Elem, k: usize) -> String {
    let mut acc = format!("(seq.unit {})", e.lit(rng));
    for _ in 1..k {
        acc = format!("(seq.++ (seq.unit {}) {acc})", e.lit(rng));
    }
    acc
}

/// A small non-negative length literal, occasionally over the packed cap (to
/// stress the bound-bite downgrade — axeyum must answer `unknown`, never a wrong
/// `unsat`, when a length exceeds the encoding bound).
fn small_len(rng: &mut Lcg) -> u64 {
    match rng.below(10) {
        0..=6 => rng.below(4) as u64,       // 0..=3, within bound
        7 | 8 => (rng.below(4) + 4) as u64, // 4..=7, near cap
        _ => (rng.below(6) + 8) as u64,     // 8..=13, over cap → axeyum unknown
    }
}

/// Wrap an atom in `(not …)` about half the time (to exercise both verdicts).
fn maybe_negate(rng: &mut Lcg, atom: String) -> String {
    if rng.flip() {
        format!("(not {atom})")
    } else {
        atom
    }
}

/// Generate one coherent `QF_SEQ` script. Each instance picks a single "family"
/// so the script is decidable (a random soup of atoms tends to decline); the
/// families collectively exercise both verdicts on the degenerate shapes.
fn generate(rng: &mut Lcg) -> String {
    let e = Elem::pick(rng);
    let mut text = String::from("(set-logic ALL)\n");
    writeln!(text, "(declare-fun s () {})", e.seq_sort()).expect("write");
    writeln!(text, "(declare-fun t () {})", e.seq_sort()).expect("write");
    writeln!(text, "(declare-fun i () Int)").expect("write");

    let body = match rng.below(100) {
        // Family A — `seq.nth` OOB (the UNDERSPEC core), SAT-biased. A length
        // fact fixes a short sequence, then an nth (OOB-biased index) is pinned
        // to a literal (or its negation). The OOB value is free ⇒ SAT; the
        // in-bounds hits agree with the fixed element. Occasionally paired with a
        // length contradiction so the degenerate nth also appears in an UNSAT.
        0..=39 => {
            let n = small_len(rng);
            let idx = index(rng);
            let pin = format!("(= (seq.nth s {idx}) {})", e.lit(rng));
            let pin = maybe_negate(rng, pin);
            if rng.below(10) < 2 {
                // nth OOB coexisting with an independent length contradiction:
                // UNSAT on both sides — the free OOB value cannot rescue it.
                format!(
                    "(and (= (seq.len s) {n}) (= (seq.len s) {}) {pin})",
                    n.wrapping_add(1)
                )
            } else {
                format!("(and (= (seq.len s) {n}) {pin})")
            }
        }
        // Family B — pure length facts. One or two `seq.len` (dis)equalities /
        // inequalities; a contradictory pair is a bound-independent UNSAT the
        // abstraction confirms; a satisfiable pair is SAT.
        40..=63 => {
            let a = small_len(rng);
            match rng.below(3) {
                0 => {
                    // Possibly contradictory equality pair.
                    let b = if rng.flip() { a } else { small_len(rng) };
                    format!("(and (= (seq.len s) {a}) (= (seq.len s) {b}))")
                }
                1 => format!("(<= (seq.len s) {a})"),
                _ => {
                    // len(s) = a AND len(s) < a  ⇒ UNSAT (bound-independent).
                    let atom = format!("(and (= (seq.len s) {a}) (< (seq.len s) {a}))");
                    if rng.flip() {
                        atom
                    } else {
                        format!("(>= (seq.len s) {a})")
                    }
                }
            }
        }
        // Family C — order predicate (prefix/suffix/contains) + a length
        // comparison. A prefix that is strictly longer than its host is a
        // bound-independent UNSAT; otherwise SAT.
        64..=82 => {
            // "`t` is inside host `s`" for all three, minding the differing
            // argument order (`seq.contains` takes `(host sub)`, the prefix/suffix
            // predicates take `(sub host)`). In every case the sub-sequence `t`
            // cannot be strictly longer than its host `s`, so `(< (len s) (len t))`
            // is the length necessary condition (violating it forces UNSAT).
            let ord = match rng.below(3) {
                0 => "(seq.prefixof t s)".to_string(),
                1 => "(seq.suffixof t s)".to_string(),
                _ => "(seq.contains s t)".to_string(),
            };
            let cmp = "(< (seq.len s) (seq.len t))".to_string();
            if rng.flip() {
                format!("(and {ord} {cmp})") // violated length ⇒ UNSAT
            } else {
                maybe_negate(rng, ord) // plain (dis)containment ⇒ usually SAT
            }
        }
        // Family D — `seq.at` / `seq.extract` over concrete unit chains. Total
        // operators; SAT-biased identities and their negations. (`seq.rev` is
        // omitted: this Z3 build does not support it, so it cannot adjudicate.)
        83..=94 => {
            let k = rng.below(3) + 1; // 1..=3
            let chain = unit_chain(rng, e, k);
            if rng.flip() {
                // at OOB is the empty sequence (total).
                let idx = index(rng);
                maybe_negate(rng, format!("(= (seq.at {chain} {idx}) {})", e.empty()))
            } else {
                // extract with an OOB offset yields the empty sequence.
                maybe_negate(rng, format!("(= (seq.extract {chain} 9 1) {})", e.empty()))
            }
        }
        // Family E — `seq.nth` congruence: equal operands must return the same
        // OOB value (a function). Z3 decides this UNSAT; axeyum typically
        // downgrades to `unknown` (SKIP). Included to confirm it never wrong-SATs.
        _ => {
            let idx = index(rng);
            format!("(and (= s t) (not (= (seq.nth s {idx}) (seq.nth t {idx}))))")
        }
    };

    writeln!(text, "(assert {body})\n(check-sat)").expect("write");
    text
}

/// A coarse verdict label.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    /// Unknown / unsupported / declined / timeout — adjudication-neutral.
    Skip,
}

/// Decide a script with axeyum's SMT-LIB front door. Any error (parse decline,
/// unsupported construct) or `Unknown` is a sound SKIP. `Sat` is already
/// replay-checked against the original term inside `solve`.
fn axeyum_decide(text: &str) -> Verdict {
    let text = text.to_string();
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || {
            let config = SolverConfig::new().with_timeout(AXEYUM_TIMEOUT);
            let v = match solve_smtlib(&text, &config) {
                Ok(outcome) => match outcome.result {
                    CheckResult::Sat(_) => Verdict::Sat,
                    CheckResult::Unsat => Verdict::Unsat,
                    CheckResult::Unknown(_) => Verdict::Skip,
                },
                Err(_) => Verdict::Skip,
            };
            let _ = tx.send(v);
        })
        .expect("spawn solver thread");
    rx.recv_timeout(AXEYUM_TIMEOUT + Duration::from_secs(2))
        .unwrap_or(Verdict::Skip)
}

/// Decide a script with the system Z3 binary. Returns `Skip` on
/// `unknown`/timeout/error/missing-binary.
///
/// **Critical soundness guard:** if Z3 reports ANY `(error …)` (e.g. an operator
/// this build does not support, like `seq.rev` on Z3 4.13.3), it drops the
/// offending command and answers `check-sat` for a DIFFERENT (weaker) assertion
/// stack — a bogus verdict that would manufacture a false disagreement. We
/// capture BOTH streams and treat any error output as a hard SKIP.
fn z3_decide(text: &str) -> Verdict {
    let Ok(mut child) = Command::new(Z3_BIN)
        .arg(format!("-T:{}", Z3_TIMEOUT.as_secs().max(1)))
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    else {
        return Verdict::Skip;
    };
    if let Some(stdin) = child.stdin.as_mut() {
        let _ = stdin.write_all(text.as_bytes());
    }
    drop(child.stdin.take());
    let Ok(output) = child.wait_with_output() else {
        return Verdict::Skip;
    };
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    // An error on EITHER stream (Z3 prints parse/sort errors to stdout under
    // `-in`, unsupported-logic notes to stderr) means the check-sat verdict is
    // untrustworthy — skip.
    if stdout.contains("(error") || stderr.contains("(error") {
        return Verdict::Skip;
    }
    for line in stdout.lines() {
        match line.trim() {
            "sat" => return Verdict::Sat,
            "unsat" => return Verdict::Unsat,
            "unknown" => return Verdict::Skip,
            _ => {}
        }
    }
    Verdict::Skip
}

fn z3_available() -> bool {
    !(z3_decide("(set-logic ALL)\n(check-sat)\n") == Verdict::Skip
        && Command::new(Z3_BIN).arg("--version").output().is_err())
}

/// Assert a single script agrees (or is jointly-undecided) — the shared body of
/// the explicit degenerate-seed tests below. A `WRONG-SAT`/`WRONG-UNSAT`
/// disagreement panics with the script.
fn assert_agrees(text: &str, note: &str) {
    if !z3_available() {
        eprintln!("[seq-fuzz] {Z3_BIN} unavailable; skipping seed '{note}'");
        return;
    }
    let ax = axeyum_decide(text);
    let z3 = z3_decide(text);
    if ax == Verdict::Skip || z3 == Verdict::Skip {
        eprintln!("[seq-fuzz] seed '{note}': jointly-undecided (ax={ax:?}, z3={z3:?}) — skip");
        return;
    }
    assert_eq!(
        ax, z3,
        "DISAGREEMENT on seed '{note}': axeyum={ax:?}, Z3={z3:?}\nscript:\n{text}"
    );
}

#[test]
fn seq_differential_fuzz_disagree_zero() {
    if !z3_available() {
        eprintln!("[seq-fuzz] {Z3_BIN} unavailable; skipping (no adjudicator)");
        return;
    }

    let mut total = 0u64;
    let mut jointly_decided = 0u64;
    let mut agreements = 0u64;
    let mut ax_skip = 0u64;
    let mut z3_skip = 0u64;
    let mut sat_seen = 0u64;
    let mut unsat_seen = 0u64;

    for seed in 0..INSTANCES {
        total += 1;
        if seed % 100 == 0 {
            eprintln!(
                "[seq-fuzz] seed {seed}/{INSTANCES} (joint={jointly_decided}, agree={agreements}, \
                 ax_skip={ax_skip}, z3_skip={z3_skip}, sat={sat_seen}, unsat={unsat_seen})"
            );
        }
        let text = generate(&mut Lcg::new(seed));

        let ax = axeyum_decide(&text);
        if ax == Verdict::Skip {
            ax_skip += 1;
            continue;
        }
        let z3 = z3_decide(&text);
        if z3 == Verdict::Skip {
            z3_skip += 1;
            continue;
        }

        jointly_decided += 1;
        match z3 {
            Verdict::Sat => sat_seen += 1,
            Verdict::Unsat => unsat_seen += 1,
            Verdict::Skip => {}
        }

        if ax == z3 {
            agreements += 1;
        } else {
            panic!(
                "DISAGREEMENT (seed {seed}): axeyum = {ax:?}, Z3 = {z3:?}.\n\
                 This is a {} soundness bug in the QF_SEQ theory.\n\
                 script:\n{}",
                match (ax, z3) {
                    (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                    _ => "verdict",
                },
                text
            );
        }
    }

    println!("=== QF_SEQ differential fuzz tally ===");
    println!("total scripts:   {total}");
    println!("jointly decided: {jointly_decided}");
    println!("agreements:      {agreements}");
    println!("axeyum skipped:  {ax_skip}");
    println!("Z3 skipped:      {z3_skip}");
    println!("verdicts:        {sat_seen} sat / {unsat_seen} unsat");
    println!("DISAGREEMENTS:   0");

    // The gate is only meaningful if the sweep jointly decides a real share AND
    // exercises BOTH verdicts on the (degenerate-biased) fragment — a fuzz that
    // only ever produces `sat` is half-blind on exactly the wrong-unsat axis.
    assert!(
        jointly_decided > 30,
        "too few jointly-decided QF_SEQ scripts ({jointly_decided}); the differential gate is vacuous"
    );
    assert!(
        sat_seen > 0 && unsat_seen > 0,
        "the seq fuzz must exercise BOTH verdicts (got {sat_seen} sat / {unsat_seen} unsat)"
    );
}

// ---------------------------------------------------------------------------
// Explicit degenerate-shape seeds (GAP-Q1). Each is a hand-written witness for
// one underspecified / edge sequence corner; the assertion is agreement with Z3.
// These make the exact shapes the Hard Rule names impossible to lose to a
// generator-coverage gap.
// ---------------------------------------------------------------------------

/// UNDERSPEC KEYSTONE — `(seq.nth s i)` out of bounds is a FREE value, so pinning
/// it to a constant is SAT, and pinning it away from `0` is ALSO SAT (proving the
/// OOB value is NOT folded to zero — a fold would be the P0 wrong-unsat). Covers a
/// negative index, an index past the end, and the empty-sequence case, over all
/// three element sorts.
#[test]
fn seed_seq_nth_oob_is_free_not_folded() {
    // Empty sequence, index 0 OOB, pinned to a nonzero value ⇒ SAT (free).
    assert_agrees(
        "(set-logic ALL)\n(declare-fun s () (Seq (_ BitVec 4)))\n\
         (assert (= (seq.len s) 0))\n(assert (= (seq.nth s 0) (_ bv7 4)))\n(check-sat)\n",
        "bv4 empty nth[0] = 7 SAT (OOB free)",
    );
    // The zero-fold tripwire: OOB nth pinned AWAY from 0 must be SAT, not a wrong
    // unsat. If the OOB value were folded to 0 this would be UNSAT.
    assert_agrees(
        "(set-logic ALL)\n(declare-fun s () (Seq (_ BitVec 4)))\n\
         (assert (= (seq.len s) 1))\n(assert (not (= (seq.nth s 4) (_ bv0 4))))\n(check-sat)\n",
        "bv4 nth[4] != 0 SAT (OOB not folded to zero)",
    );
    // Same tripwire for (Seq Int) — the packed-Int lift must not force 0 either.
    assert_agrees(
        "(set-logic ALL)\n(declare-fun s () (Seq Int))\n\
         (assert (= (seq.len s) 1))\n(assert (not (= (seq.nth s 4) 0)))\n(check-sat)\n",
        "int nth[4] != 0 SAT (OOB not folded to zero)",
    );
    // Negative index is out of bounds ⇒ free ⇒ pin to a specific value is SAT.
    assert_agrees(
        "(set-logic ALL)\n(declare-fun s () (Seq (_ BitVec 4)))\n\
         (assert (= (seq.len s) 2))\n(assert (= (seq.nth s (- 1)) (_ bv5 4)))\n(check-sat)\n",
        "bv4 nth[-1] = 5 SAT (negative index OOB free)",
    );
    // (Seq Bool) OOB nth pinned to true ⇒ SAT.
    assert_agrees(
        "(set-logic ALL)\n(declare-fun s () (Seq Bool))\n\
         (assert (= (seq.len s) 0))\n(assert (= (seq.nth s 3) true))\n(check-sat)\n",
        "bool nth[3] = true SAT (OOB free)",
    );
}

/// UNDERSPEC — the free OOB value cannot rescue an INDEPENDENT contradiction: an
/// OOB `seq.nth` pin alongside a length contradiction is UNSAT on both sides
/// (exercises the UNSAT verdict on a shape that contains the degenerate nth). If
/// axeyum's length reasoning were unsound this would flip.
#[test]
fn seed_seq_nth_oob_does_not_rescue_length_contradiction() {
    assert_agrees(
        "(set-logic ALL)\n(declare-fun s () (Seq (_ BitVec 4)))\n\
         (assert (= (seq.len s) 0))\n(assert (= (seq.len s) 1))\n\
         (assert (= (seq.nth s 0) (_ bv7 4)))\n(check-sat)\n",
        "nth OOB + len 0∧1 contradiction UNSAT",
    );
}

/// TOTAL-with-edges — `(seq.at s i)` out of bounds is the EMPTY sequence (total,
/// mirrors `str.at`): OOB `seq.at` = empty is SAT; `not (= … empty)` is UNSAT.
#[test]
fn seed_seq_at_oob_is_empty() {
    assert_agrees(
        "(set-logic ALL)\n(declare-fun s () (Seq (_ BitVec 4)))\n\
         (assert (= (seq.len s) 1))\n\
         (assert (= (seq.at s 5) (as seq.empty (Seq (_ BitVec 4)))))\n(check-sat)\n",
        "seq.at OOB = empty SAT",
    );
}

/// TOTAL — `seq.extract` with an out-of-bounds offset yields the empty sequence.
#[test]
fn seed_seq_extract_oob_is_empty() {
    assert_agrees(
        "(set-logic ALL)\n(declare-fun s () (Seq Int))\n\
         (assert (= s (seq.++ (seq.unit 1) (seq.unit 2))))\n\
         (assert (= (seq.extract s 5 1) (as seq.empty (Seq Int))))\n(check-sat)\n",
        "seq.extract OOB offset = empty SAT",
    );
}

/// Bounded-model soundness — a length past the packed cap must NOT be a wrong
/// `unsat`. Z3 says SAT (sequences are unbounded); axeyum downgrades the bounded
/// `unsat` to `unknown` (a sound SKIP), never refutes it. `assert_agrees` skips a
/// jointly-undecided pair, so this asserts only that axeyum never emits `unsat`.
#[test]
fn seed_over_cap_length_is_not_wrong_unsat() {
    let text = "(set-logic ALL)\n(declare-fun s () (Seq (_ BitVec 4)))\n\
                (assert (= (seq.len s) 12))\n(check-sat)\n";
    if z3_available() {
        assert_ne!(
            axeyum_decide(text),
            Verdict::Unsat,
            "over-cap length must be `sat` or `unknown`, never a wrong `unsat`\n{text}"
        );
    }
    assert_agrees(text, "over-cap len 12 (axeyum unknown, Z3 sat)");
}
