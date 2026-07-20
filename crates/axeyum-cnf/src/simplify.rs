//! CNF subsumption simplification (Track 1, P1.1 / tasks T1.1.1, T1.1.4).
//!
//! Bit-blasting an AIG via Tseitin floods the CNF with intermediate variables
//! and redundant clauses; collapsing them before (and during) solving is the
//! single biggest performance lever for a bit-blasting solver. This module is the
//! warm-up step toward bounded variable elimination: **forward subsumption** plus
//! **self-subsuming resolution**, the cheapest high-value inprocessing.
//!
//! All three transformations applied here are **model-preserving** (the simplified
//! formula has exactly the same satisfying assignments), so they are sound for
//! both `sat` (models lift back unchanged) and `unsat`:
//!
//! * **Tautology removal** — a clause containing both `l` and `¬l` is always true;
//!   dropping it changes no model.
//! * **Forward subsumption** — if clause `D ⊆ C` (as literal sets) and `D` remains
//!   in the formula, then `C` is entailed by `D`, so removing `C` is sound and
//!   model-preserving (`F ≡ F \ {C}`).
//! * **Self-subsuming resolution** — if some clause `D` contains `¬l` and
//!   `D \ {¬l} ⊆ C \ {l}`, then `C` can be strengthened to `C \ {l}`; because the
//!   witness `D` stays in the formula, `F'' ∧ C ≡ F'' ∧ (C \ {l})` (model-preserving,
//!   not merely equisatisfiable).
//!
//! **Implementation (T1.1.4): forward subsumption over literal occurrence lists**,
//! the `CaDiCaL`/`Kissat` scheme (`subsume.cpp` `subsume_round`/`try_to_subsume_clause`,
//! `Kissat` `forward.c`), which replaces the original O(clauses²) all-pairs sweep:
//!
//! * Clauses are processed shortest-first and each is connected on **one** literal
//!   — the globally least-frequent one (`noccs`). A connected clause therefore
//!   appears in exactly one occurrence list, so a candidate `C` is checked only
//!   against the (few) clauses sharing one of its literals, never all clauses.
//! * The subset test uses signed per-variable **marks** (`+1`/`-1`/`0`) plus a
//!   per-clause variable **signature** as an O(1) pre-reject; both subsumption and
//!   self-subsuming strengthening are detected in the same single pass over a
//!   candidate's literals. The signature is keyed by *variable* (not literal) so a
//!   strengthening witness — which carries `¬l` where `C` carries `l` — is not
//!   falsely rejected.
//! * Rounds repeat to a fixpoint (strengthening exposes new subsumptions); a work
//!   budget and occurrence/size caps keep each round near-linear and bounded.
//!
//! It is a pure `CnfFormula → CnfFormula` transform and does not yet emit DRAT
//! deletion steps (the proof-pipeline integration is a separate task).

// Monotonic clock for the optional inprocessing deadline: on wasm32 the browser
// has no `std` clock, so use `web-time`'s drop-in `Instant` (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use crate::{CnfClause, CnfFormula, CnfLit};

/// What a [`simplify`] pass removed, for diagnostics and benchmark accounting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SubsumeStats {
    /// Always-true clauses (containing `l` and `¬l`) dropped.
    pub tautologies_removed: usize,
    /// Clauses removed because another clause subsumes them (incl. duplicates).
    pub clauses_subsumed: usize,
    /// Literals removed by self-subsuming resolution.
    pub literals_strengthened: usize,
}

impl SubsumeStats {
    /// Whether the pass changed anything.
    #[must_use]
    pub fn is_empty(self) -> bool {
        self == SubsumeStats::default()
    }
}

/// Maximum literals in a clause considered for subsumption work (`CaDiCaL`
/// `subsumeclslim`). Larger clauses are still kept verbatim; they are simply not
/// used as subsumption candidates or connected, bounding occurrence-list growth.
const SUBSUME_CLAUSE_LIMIT: usize = 100;

/// Maximum length of the occurrence list a clause is connected onto (`CaDiCaL`
/// `subsumeocclim`). A clause whose least-frequent literal already occurs this
/// often is left unconnected (it will not subsume others, still sound).
const SUBSUME_OCCURRENCE_LIMIT: usize = 1_000;

/// Hard cap on subsumption rounds. Real inputs reach a fixpoint in a couple of
/// rounds; the cap only bounds pathological inputs (soundness is unaffected —
/// stopping early leaves a still model-preserving formula).
const SUBSUME_MAX_ROUNDS: usize = 32;

/// One bit of the signature for a literal, keyed by **variable** (sign-agnostic).
///
/// Subset rejection must pass both pure subsumption (`D ⊆ C`) and self-subsuming
/// resolution (`D = D' ∪ {¬l}`, `C = C' ∪ {l}`): in both cases every variable of
/// `D` occurs in `C`, so a variable-keyed signature is a sound pre-filter, while a
/// literal-keyed one would wrongly reject the `¬l`/`l` strengthening witness.
pub(crate) fn lit_bit(lit: CnfLit) -> u64 {
    1u64 << (lit.var().index() % 64)
}

/// Zero-based occurrence-list index for a literal: `2 * variable + sign`.
fn lit_index(lit: CnfLit) -> usize {
    2 * lit.var().index() + usize::from(lit.is_negated())
}

/// A normalized clause: literals sorted + deduplicated, with a variable-keyed
/// 64-bit signature for fast subset rejection. Shared with [`crate::bve`].
#[derive(Debug, Clone)]
pub(crate) struct NormClause {
    pub(crate) lits: Vec<CnfLit>,
    pub(crate) sig: u64,
}

impl NormClause {
    /// Normalizes a clause; returns `None` if it is a tautology (always true).
    pub(crate) fn from_lits(clause: &[CnfLit]) -> Option<Self> {
        let mut lits = clause.to_vec();
        lits.sort_unstable();
        lits.dedup();
        // Tautology: some variable appears both positive and negative.
        for (i, &l) in lits.iter().enumerate() {
            if lits[i + 1..].iter().any(|&m| m == l.negated()) {
                return None;
            }
        }
        let sig = lits.iter().fold(0u64, |acc, &l| acc | lit_bit(l));
        Some(Self { lits, sig })
    }

    /// Removes `lit` from the clause (if present) and refreshes the signature.
    fn remove_lit(&mut self, lit: CnfLit) {
        if let Some(pos) = self.lits.iter().position(|&l| l == lit) {
            self.lits.remove(pos);
            self.sig = self.lits.iter().fold(0u64, |acc, &l| acc | lit_bit(l));
        }
    }
}

/// Signed membership of literal `m` in the currently marked clause: `+1` if `m`
/// occurs (same phase), `-1` if `¬m` occurs (opposite phase), `0` if absent.
fn marked(marks: &[i8], m: CnfLit) -> i8 {
    let stored = marks[m.var().index()];
    if stored == 0 {
        return 0;
    }
    let want = if m.is_negated() { -1 } else { 1 };
    if stored == want { 1 } else { -1 }
}

/// Outcome of checking a candidate clause against the marked clause `C`.
enum Check {
    /// The candidate subsumes `C` (every literal present, same phase).
    Subsumed,
    /// Self-subsuming resolution: the candidate's clashing literal is `m`, so the
    /// literal `¬m` can be removed from `C`.
    Strengthen(CnfLit),
    /// No relationship.
    No,
}

/// Tests a connected candidate `d` against the marked clause `C` (whose literals
/// set `marks`). `d` is known to be no longer than `C`.
fn subsume_check(d: &NormClause, marks: &[i8]) -> Check {
    let mut flipped: Option<CnfLit> = None;
    for &m in &d.lits {
        match marked(marks, m) {
            0 => return Check::No, // a literal of d is absent from C
            s if s < 0 => {
                if flipped.is_some() {
                    return Check::No; // two clashes: neither subsume nor single strengthen
                }
                flipped = Some(m);
            }
            _ => {} // present, same phase
        }
    }
    match flipped {
        None => Check::Subsumed,
        Some(m) => Check::Strengthen(m),
    }
}

/// What [`try_subsume`] decided for a candidate clause.
enum Outcome {
    /// The clause is subsumed and should be removed.
    Subsumed,
    /// The clause should be strengthened by removing this literal.
    Strengthen(CnfLit),
    /// Keep the clause unchanged.
    Keep,
}

/// Checks clause `ci` against the already-connected clauses, using `marks` as the
/// signed membership scratch (left zeroed on return). Reads only immutable state.
fn try_subsume(
    ci: usize,
    clauses: &[Option<NormClause>],
    occs: &[Vec<usize>],
    marks: &mut [i8],
    checks: &mut usize,
) -> Outcome {
    let c = clauses[ci].as_ref().expect("live candidate");
    let c_len = c.lits.len();
    let c_sig = c.sig;
    for &l in &c.lits {
        marks[l.var().index()] = if l.is_negated() { -1 } else { 1 };
    }

    let mut outcome = Outcome::Keep;
    // A subsuming/strengthening witness is connected on one of its literals, which
    // is a literal of `C` (subsumption) or the negation of one (strengthening), so
    // walking both phases of each literal of `C` finds every witness exactly once.
    'outer: for &l in &c.lits {
        for sgn in [l, l.negated()] {
            for &d_id in &occs[lit_index(sgn)] {
                if d_id == ci {
                    continue;
                }
                let Some(d) = clauses[d_id].as_ref() else {
                    continue; // removed earlier this round
                };
                if d.lits.len() > c_len || (d.sig & !c_sig) != 0 {
                    continue;
                }
                *checks += 1;
                match subsume_check(d, marks) {
                    Check::Subsumed => {
                        outcome = Outcome::Subsumed;
                        break 'outer;
                    }
                    Check::Strengthen(m) => {
                        // `m` is `d`'s clashing literal; `C` carries `¬m`.
                        outcome = Outcome::Strengthen(m.negated());
                        break 'outer;
                    }
                    Check::No => {}
                }
            }
        }
    }

    for &l in &c.lits {
        marks[l.var().index()] = 0;
    }
    outcome
}

/// Connects clause `ci` onto its globally least-frequent literal (one-watch),
/// unless that list is already at the occurrence cap or the clause is empty.
fn connect(ci: usize, clause: &NormClause, occs: &mut [Vec<usize>], noccs: &[u32]) {
    let Some(&watch) = clause
        .lits
        .iter()
        .min_by_key(|&&l| (noccs[lit_index(l)], lit_index(l)))
    else {
        return; // empty clause (unsat): nothing to connect
    };
    let slot = lit_index(watch);
    if occs[slot].len() < SUBSUME_OCCURRENCE_LIMIT {
        occs[slot].push(ci);
    }
}

/// One forward-subsumption round over the live clauses; returns whether anything
/// changed (a clause was subsumed or strengthened).
fn subsume_round(
    clauses: &mut [Option<NormClause>],
    nvars: usize,
    marks: &mut [i8],
    deadline: Option<Instant>,
) -> Option<SubsumeStats> {
    let lit_slots = 2 * nvars;
    let mut noccs = vec![0u32; lit_slots];
    let mut order: Vec<usize> = Vec::new();
    let mut total_lits = 0usize;
    for (ci, slot) in clauses.iter().enumerate() {
        if let Some(c) = slot {
            if c.lits.len() > SUBSUME_CLAUSE_LIMIT {
                continue; // too large to use as a subsumption candidate
            }
            for &l in &c.lits {
                noccs[lit_index(l)] += 1;
            }
            total_lits += c.lits.len();
            order.push(ci);
        }
    }
    order.sort_by_key(|&ci| (clauses[ci].as_ref().map_or(0, |c| c.lits.len()), ci));

    let mut occs: Vec<Vec<usize>> = vec![Vec::new(); lit_slots];
    let mut stats = SubsumeStats::default();
    let mut checks = 0usize;
    let budget = 64 * (total_lits + nvars) + (1 << 16);

    for &ci in &order {
        if clauses[ci].is_none() {
            continue; // subsumed earlier this round
        }
        match try_subsume(ci, clauses, &occs, marks, &mut checks) {
            Outcome::Subsumed => {
                clauses[ci] = None;
                stats.clauses_subsumed += 1;
            }
            Outcome::Strengthen(remove) => {
                clauses[ci]
                    .as_mut()
                    .expect("live candidate")
                    .remove_lit(remove);
                stats.literals_strengthened += 1;
                // The shrunken clause is reconsidered (and reconnected) next round.
            }
            Outcome::Keep => {
                connect(
                    ci,
                    clauses[ci].as_ref().expect("live candidate"),
                    &mut occs,
                    &noccs,
                );
            }
        }
        if checks > budget || deadline.is_some_and(|dl| Instant::now() >= dl) {
            break; // bounded work / out of time: stop early (still sound)
        }
    }

    if stats.is_empty() { None } else { Some(stats) }
}

/// Simplifies `formula` by tautology removal, forward subsumption, and
/// self-subsuming resolution, iterated to a fixpoint. Returns the simplified
/// formula and the [`SubsumeStats`]. The result is **logically equivalent** to the
/// input (same variable count, same satisfying assignments).
#[must_use]
pub fn simplify(formula: &CnfFormula) -> (CnfFormula, SubsumeStats) {
    simplify_within(formula, None)
}

/// Like [`simplify`], but stops starting new subsumption rounds once `deadline`
/// passes (checked between clauses within a round). The partial result is still
/// logically equivalent; only fewer redundancies are removed. `None` = no deadline.
#[must_use]
pub fn simplify_within(
    formula: &CnfFormula,
    deadline: Option<Instant>,
) -> (CnfFormula, SubsumeStats) {
    let nvars = formula.variable_count();
    let mut stats = SubsumeStats::default();

    // Normalize; drop tautologies up front (they constrain nothing).
    let mut clauses: Vec<Option<NormClause>> = Vec::with_capacity(formula.clauses().len());
    for clause in formula.clauses() {
        match NormClause::from_lits(clause) {
            Some(nc) => clauses.push(Some(nc)),
            None => stats.tautologies_removed += 1,
        }
    }

    // Rounds to a fixpoint: strengthening a clause can expose new subsumptions.
    let mut marks = vec![0i8; nvars];
    for _ in 0..SUBSUME_MAX_ROUNDS {
        if deadline.is_some_and(|dl| Instant::now() >= dl) {
            break;
        }
        match subsume_round(&mut clauses, nvars, &mut marks, deadline) {
            Some(round) => {
                stats.clauses_subsumed += round.clauses_subsumed;
                stats.literals_strengthened += round.literals_strengthened;
            }
            None => break,
        }
    }

    let mut out = CnfFormula::new(nvars);
    for c in clauses.into_iter().flatten() {
        // Infallible: variables are a subset of the original's, already validated.
        let _ = out.add_clause(CnfClause::new(c.lits));
    }
    (out, stats)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CnfFormula, CnfLit, CnfVar};

    fn v(i: usize) -> CnfVar {
        CnfVar::new(i).unwrap()
    }
    fn p(i: usize) -> CnfLit {
        CnfLit::positive(v(i))
    }
    fn n(i: usize) -> CnfLit {
        CnfLit::positive(v(i)).negated()
    }
    fn clause(lits: &[CnfLit]) -> CnfClause {
        CnfClause::new(lits.to_vec())
    }

    fn formula(nvars: usize, clauses: &[&[CnfLit]]) -> CnfFormula {
        let mut f = CnfFormula::new(nvars);
        for c in clauses {
            f.add_clause(clause(c)).unwrap();
        }
        f
    }

    /// Brute-force: two formulas over `nvars` variables agree on every assignment.
    fn equivalent(a: &CnfFormula, b: &CnfFormula, nvars: usize) {
        assert_eq!(a.variable_count(), b.variable_count());
        for mask in 0u32..(1u32 << nvars) {
            let asg: Vec<bool> = (0..nvars).map(|i| (mask >> i) & 1 == 1).collect();
            assert_eq!(
                a.evaluate(&asg).unwrap(),
                b.evaluate(&asg).unwrap(),
                "disagree on assignment {asg:?}"
            );
        }
    }

    #[test]
    fn removes_a_subsumed_clause() {
        // (a) subsumes (a ∨ b): drop the longer clause.
        let f = formula(2, &[&[p(0)], &[p(0), p(1)]]);
        let (out, stats) = simplify(&f);
        assert_eq!(stats.clauses_subsumed, 1);
        assert_eq!(out.clauses().len(), 1);
        assert_eq!(out.clause(0), Some(&[p(0)][..]));
        equivalent(&f, &out, 2);
    }

    #[test]
    fn removes_duplicate_clauses() {
        let f = formula(2, &[&[p(0), p(1)], &[p(1), p(0)]]);
        let (out, stats) = simplify(&f);
        assert_eq!(
            stats.clauses_subsumed, 1,
            "one of the duplicates is dropped"
        );
        assert_eq!(out.clauses().len(), 1);
        equivalent(&f, &out, 2);
    }

    #[test]
    fn drops_tautologies() {
        // (a ∨ ¬a) is always true; (b) stays.
        let f = formula(2, &[&[p(0), n(0)], &[p(1)]]);
        let (out, stats) = simplify(&f);
        assert_eq!(stats.tautologies_removed, 1);
        assert_eq!(out.clauses().len(), 1);
        assert_eq!(out.clause(0), Some(&[p(1)][..]));
        equivalent(&f, &out, 2);
    }

    #[test]
    fn self_subsuming_resolution_strengthens() {
        // (a ∨ b) and (¬a ∨ b): resolving on a gives (b), strengthening both.
        // Self-subsumption: (¬a ∨ b) lets us drop a from (a ∨ b) → (b), and
        // symmetrically. The result is equivalent to the original.
        let f = formula(2, &[&[p(0), p(1)], &[n(0), p(1)]]);
        let (out, stats) = simplify(&f);
        assert!(
            stats.literals_strengthened >= 1,
            "expected a strengthening, got {stats:?}"
        );
        equivalent(&f, &out, 2);
        // The strengthened formula entails (b).
        for mask in 0u32..4 {
            let asg: Vec<bool> = (0..2).map(|i| (mask >> i) & 1 == 1).collect();
            if out.evaluate(&asg).unwrap() {
                assert!(asg[1], "every model of the simplified formula has b true");
            }
        }
    }

    #[test]
    fn is_idempotent() {
        let f = formula(
            3,
            &[
                &[p(0), p(1), p(2)],
                &[p(0)],
                &[p(0), p(1)],
                &[p(1), n(1)],
                &[n(2), p(0)],
            ],
        );
        let (once, _) = simplify(&f);
        let (twice, stats2) = simplify(&once);
        assert!(
            stats2.is_empty(),
            "second pass should be a fixpoint: {stats2:?}"
        );
        assert_eq!(once, twice);
        equivalent(&f, &once, 3);
    }

    #[test]
    fn sat_result_and_drat_are_preserved_after_simplification() {
        use crate::{
            ProofSolveOutcome, SatResult, check_drat, solve_with_drat_proof,
            solve_with_rustsat_batsat,
        };
        // UNSAT: (a) ∧ (¬a) ∧ (a ∨ b) — the last clause is subsumed by (a).
        let f = formula(2, &[&[p(0)], &[n(0)], &[p(0), p(1)]]);
        let (out, stats) = simplify(&f);
        assert!(stats.clauses_subsumed >= 1, "expected a subsumed clause");
        assert!(
            out.clauses().len() < f.clauses().len(),
            "clause count dropped"
        );

        // Both formulas are still UNSAT (satisfiability preserved).
        assert!(matches!(
            solve_with_rustsat_batsat(&f).unwrap(),
            SatResult::Unsat(_)
        ));
        assert!(matches!(
            solve_with_rustsat_batsat(&out).unwrap(),
            SatResult::Unsat(_)
        ));

        // The simplified UNSAT still carries a DRAT proof that re-checks.
        match solve_with_drat_proof(&out) {
            ProofSolveOutcome::Unsat(proof) => {
                assert!(check_drat(&out, &proof).unwrap(), "DRAT must still check");
            }
            other => panic!("expected an unsat proof, got {other:?}"),
        }
    }

    #[test]
    fn preserves_models_on_a_larger_random_ish_formula() {
        // A hand-built formula with redundancy across 4 variables; brute-force
        // confirms exact equivalence (the soundness contract).
        let f = formula(
            4,
            &[
                &[p(0), p(1)],
                &[p(0), p(1), p(2)], // subsumed by (a ∨ b)
                &[n(0), p(1)],       // self-subsumes (a ∨ b) on a
                &[p(2), p(3)],
                &[p(2), p(3), n(0)], // subsumed by (c ∨ d)
                &[p(3), n(3)],       // tautology
            ],
        );
        let (out, stats) = simplify(&f);
        assert!(!stats.is_empty());
        assert!(out.clauses().len() < f.clauses().len());
        equivalent(&f, &out, 4);
    }

    /// Deterministic xorshift PRNG (no `Math.random`/clock; reproducible).
    fn xorshift(state: &mut u64) -> u64 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        *state = x;
        x
    }

    /// A pseudo-random `usize` (no lossy casts; `u64`→`usize` is total on 64-bit
    /// and saturates harmlessly elsewhere — the value is only ever used modulo a
    /// small bound).
    fn rand_usize(state: &mut u64) -> usize {
        usize::try_from(xorshift(state)).unwrap_or(usize::MAX)
    }

    #[test]
    fn random_formulas_are_logically_equivalent() {
        // Stress the occurrence-list subsumption + strengthening against the
        // brute-force semantics on many random 5-variable formulas.
        const NVARS: usize = 5;
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        for _ in 0..400 {
            let nclauses = 1 + rand_usize(&mut state) % 12;
            let mut f = CnfFormula::new(NVARS);
            for _ in 0..nclauses {
                let width = 1 + rand_usize(&mut state) % 4;
                let mut lits = Vec::new();
                for _ in 0..width {
                    let var = rand_usize(&mut state) % NVARS;
                    let lit = if xorshift(&mut state) & 1 == 0 {
                        p(var)
                    } else {
                        n(var)
                    };
                    lits.push(lit);
                }
                f.add_clause(clause(&lits)).unwrap();
            }
            let (out, _) = simplify(&f);
            equivalent(&f, &out, NVARS);
            // Re-simplifying is a fixpoint.
            let (again, stats2) = simplify(&out);
            assert!(stats2.is_empty(), "not a fixpoint: {stats2:?}");
            assert_eq!(out, again);
        }
    }

    #[test]
    fn large_formula_simplifies_quickly_and_soundly() {
        // ~6000 clauses: the occurrence-list pass must complete near-instantly
        // (the old O(clauses²) sweep would do ~36M subset checks here). We can't
        // brute-force 200 variables, so assert structural soundness: the result
        // never grows, and a known model of the input still satisfies the output.
        const NVARS: usize = 200;
        let mut state = 0x0123_4567_89AB_CDEFu64;
        let mut f = CnfFormula::new(NVARS);
        // A fixed all-true model: every clause includes at least one positive lit.
        for _ in 0..6000 {
            let width = 2 + rand_usize(&mut state) % 4;
            let mut lits = vec![p(rand_usize(&mut state) % NVARS)];
            for _ in 1..width {
                let var = rand_usize(&mut state) % NVARS;
                let lit = if xorshift(&mut state) & 1 == 0 {
                    p(var)
                } else {
                    n(var)
                };
                lits.push(lit);
            }
            f.add_clause(clause(&lits)).unwrap();
        }
        let (out, _) = simplify(&f);
        assert!(out.clauses().len() <= f.clauses().len());
        let all_true = vec![true; NVARS];
        assert!(f.evaluate(&all_true).unwrap());
        assert!(
            out.evaluate(&all_true).unwrap(),
            "a model of the input must satisfy the simplified formula"
        );
    }
}
