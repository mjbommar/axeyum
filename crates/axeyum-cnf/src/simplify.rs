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
//! # `DRAT` accounting
//!
//! [`simplify`] / [`simplify_within`] are pure `CnfFormula → CnfFormula`
//! transforms and emit nothing. `simplify_within_recorded` (crate-internal, and
//! what [`crate::inprocess`] calls) additionally records a `DRAT` derivation of
//! every change **in the order the pass made it**, so the whole prefix
//! re-verifies against the original formula with [`crate::check_drat`]. Every
//! added clause is plain `RUP`; nothing here needs `RAT` or an extension
//! variable. See that function's docs for why the order — rather than a diff of
//! the input and output formulas — is the part that has to be right.

// Monotonic clock for the optional inprocessing deadline: on wasm32 the browser
// has no `std` clock, so use `web-time`'s drop-in `Instant` (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use crate::pass_work::PassWork;
use crate::{CnfClause, CnfFormula, CnfLit, DratStep};

/// What a [`simplify`] pass removed, for diagnostics and benchmark accounting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct SubsumeStats {
    /// Always-true clauses (containing `l` and `¬l`) dropped.
    pub tautologies_removed: usize,
    /// Clauses removed because another clause subsumes them (incl. duplicates).
    pub clauses_subsumed: usize,
    /// Literals removed by self-subsuming resolution.
    pub literals_strengthened: usize,
    /// Deterministic work the pass spent, in occurrence-list steps
    /// ([`crate::pass_work`]'s unit, the same one `crate::bve` charges in).
    /// Always recorded, whether or not [`SubsumeOptions::work_budget`] was set —
    /// a budget you cannot see the spend against is a constant nobody can
    /// calibrate.
    pub work_spent: u64,
    /// `true` if the pass stopped because [`SubsumeOptions::work_budget`] ran
    /// out. Distinguishing this from "reached its own fixpoint" is the whole
    /// point: the two look identical in a wall-clock timing and call for
    /// opposite work.
    pub work_exhausted: bool,
    /// The meter reading at the **last** clause subsumed or strengthened, or the
    /// first round's setup cost if nothing changed.
    ///
    /// [`Self::work_spent`] minus this is spend after the last useful action.
    /// A budget at or above this number costs the run nothing at all, so one
    /// sweep with the budget disabled prices every candidate budget.
    pub work_at_last_progress: u64,
    /// Occurrence entries examined whose clause had **already been removed**.
    ///
    /// This is the lazy-removal constant, measured rather than assumed. In
    /// `crate::bve` it is large — a clause eliminated early leaves its id in
    /// every occurrence list it was ever in, and every later scan pays for it —
    /// which is what makes compaction a candidate fix there. Here it is
    /// structurally zero, and this counter is how that is checked rather than
    /// argued: see `try_subsume`'s scan loop.
    pub dead_occurrence_entries: u64,
}

impl SubsumeStats {
    /// Whether the pass changed anything.
    ///
    /// Named fields rather than `self == Self::default()`: the work counters
    /// are non-zero on every run, including one that changed nothing, and a
    /// derived comparison would have silently turned this into "the pass ran".
    #[must_use]
    pub fn is_empty(self) -> bool {
        self.tautologies_removed == 0
            && self.clauses_subsumed == 0
            && self.literals_strengthened == 0
    }
}

/// Tuning knobs for [`simplify_with_options`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SubsumeOptions {
    /// Deterministic **total** work budget across all rounds, in
    /// [`SubsumeStats::work_spent`]'s unit. `None` is unbounded — the pass then
    /// stops only at its per-round check cap, [`SUBSUME_MAX_ROUNDS`], or the
    /// caller's wall-clock deadline, which is exactly today's behaviour.
    ///
    /// **This is the budget that should bind, and the per-round check cap is
    /// not it.** That cap counts *subsumption checks* — the candidates that
    /// survive the length and signature pre-filters — and measured 2026-09-08
    /// on the pinned 200-file `QF_BV` parity list, the file where subsumption
    /// costs the most spends 10.7 s of an 11.4 s inprocessing slice here
    /// without ever reaching it. The dominant cost is the occurrence-list scan,
    /// which the check cap does not count at all.
    pub work_budget: Option<u64>,
}

impl SubsumeOptions {
    /// The shipping default: unbudgeted, i.e. exactly the behaviour every
    /// caller had before the meter existed.
    ///
    /// There is deliberately no compaction knob here, unlike
    /// `crate::bve::BveOptions`. This pass cannot produce a dead occurrence
    /// entry to compact — see `this_pass_cannot_produce_a_dead_occurrence_entry`
    /// and `SubsumeStats::dead_occurrence_entries`, which measures the zero
    /// rather than asserting it in prose.
    pub const DEFAULT: Self = Self { work_budget: None };
}

impl Default for SubsumeOptions {
    fn default() -> Self {
        Self::DEFAULT
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
pub const SUBSUME_MAX_ROUNDS: usize = 32;

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
    pub(crate) fn from_clause(clause: &CnfClause) -> Option<Self> {
        let mut lits = clause.lits().to_vec();
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
    work: &mut PassWork,
) -> Outcome {
    let c = clauses[ci].as_ref().expect("live candidate");
    let c_len = c.lits.len();
    let c_sig = c.sig;
    // Marking and unmarking each literal of the candidate: `O(|C|)` twice, paid
    // on every candidate whether or not a witness is found.
    work.charge(2 * c_len as u64);
    for &l in &c.lits {
        marks[l.var().index()] = if l.is_negated() { -1 } else { 1 };
    }

    let mut outcome = Outcome::Keep;
    // A subsuming/strengthening witness is connected on one of its literals, which
    // is a literal of `C` (subsumption) or the negation of one (strengthening), so
    // walking both phases of each literal of `C` finds every witness exactly once.
    'outer: for &l in &c.lits {
        for sgn in [l, l.negated()] {
            let slot = lit_index(sgn);
            for &d_id in &occs[slot] {
                // ONE STEP PER ENTRY EXAMINED, not per entry that survives the
                // filters. The gap between those two is the finding: removal is
                // lazy, so a dead id stays here forever and every later scan
                // keeps paying for it, and the pre-existing `checks` cap counts
                // only the entries that reach `subsume_check`.
                //
                // Charged per entry rather than as the list length up front
                // because the scan can exit early on a witness, and a budget
                // must be denominated in work done, not work available.
                work.charge(1);
                if d_id == ci {
                    continue;
                }
                let Some(d) = clauses[d_id].as_ref() else {
                    // A dead entry: the id of a clause removed earlier. Counted
                    // rather than merely skipped, because "how many of these are
                    // there" is the question compaction answers, and the honest
                    // answer for THIS pass is zero — a clause is connected only
                    // on the `Keep` arm, and the only clause a round ever
                    // removes is the candidate it is currently examining, which
                    // is not yet connected. The branch stays because the
                    // invariant is a property of the schedule, not of the type.
                    work.charge_dead(1);
                    continue;
                };
                if d.lits.len() > c_len || (d.sig & !c_sig) != 0 {
                    continue;
                }
                // The subset test walks every literal of `d`.
                work.charge(d.lits.len() as u64);
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
    work: &mut PassWork,
    deadline: Option<Instant>,
    mut proof: Option<&mut Vec<DratStep>>,
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

    // THIS ROUND'S SETUP, charged before any candidate is examined: one step per
    // literal occurrence counted into `noccs` and one per occurrence-list slot
    // allocated. Every round pays it again, because the occurrence lists are
    // rebuilt from scratch each time — which is why the meter lives outside this
    // function and accumulates across rounds. On the first round it is bounded
    // by `literal_occurrences(formula) + 2 * nvars`, the same quantity `crate::bve`
    // charges and an admission test computes from the formula; it is below that
    // only because clauses past `SUBSUME_CLAUSE_LIMIT` are not connected.
    work.charge((total_lits + lit_slots) as u64);

    for &ci in &order {
        // The deterministic budget, checked between candidates (an in-flight
        // candidate always finishes, so `marks` is left zeroed). Checked before
        // the wall clock at the bottom of the loop so a run that would stop for
        // both reasons reports the reproducible one.
        if work.must_stop() {
            break;
        }
        if clauses[ci].is_none() {
            continue; // subsumed earlier this round
        }
        match try_subsume(ci, clauses, &occs, marks, &mut checks, work) {
            Outcome::Subsumed => {
                if let Some(p) = proof.as_deref_mut() {
                    // Pure deletion. Sound unconditionally in `DRAT` — a deletion
                    // only weakens the active set, so it can make a later step
                    // harder to verify but never lets a wrong one through.
                    p.push(DratStep::Delete(
                        clauses[ci].as_ref().expect("live candidate").lits.clone(),
                    ));
                }
                clauses[ci] = None;
                stats.clauses_subsumed += 1;
                work.note_progress();
            }
            Outcome::Strengthen(remove) => {
                let before = clauses[ci].as_ref().expect("live candidate").lits.clone();
                clauses[ci]
                    .as_mut()
                    .expect("live candidate")
                    .remove_lit(remove);
                if let Some(p) = proof.as_deref_mut() {
                    // `Add` FIRST, while both `C` and its witness `D` are still in
                    // the checker's active set: `C \ {l}` is `RUP` in exactly two
                    // propagations (negate it, `C` becomes unit on `l`, and that
                    // falsifies `D ∋ ¬l` because `D \ {¬l} ⊆ C \ {l}`). Deleting
                    // `C` first would remove the clause the step is derived from.
                    p.push(DratStep::Add(
                        clauses[ci].as_ref().expect("live candidate").lits.clone(),
                    ));
                    p.push(DratStep::Delete(before));
                }
                stats.literals_strengthened += 1;
                work.note_progress();
                // The shrunken clause is reconsidered (and reconnected) next round.
            }
            Outcome::Keep => {
                // Choosing the watch literal walks the clause, and connecting
                // writes one occurrence entry.
                work.charge(clauses[ci].as_ref().map_or(0, |c| c.lits.len() as u64) + 1);
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
    simplify_with_options(formula, SubsumeOptions::DEFAULT, deadline)
}

/// Like [`simplify_within`], but under an explicit [`SubsumeOptions`] — a
/// deterministic work budget, occurrence-list compaction, or both.
///
/// [`SubsumeOptions::DEFAULT`] reproduces [`simplify_within`] exactly, so this
/// is a widening of the API and not a change to it.
#[must_use]
pub fn simplify_with_options(
    formula: &CnfFormula,
    opts: SubsumeOptions,
    deadline: Option<Instant>,
) -> (CnfFormula, SubsumeStats) {
    simplify_within_recorded(formula, opts, deadline, None)
}

/// Like [`simplify_within`], but records a `DRAT` derivation of every change
/// into `proof`, **in the order the pass made it**.
///
/// # Why derivation order, and not a diff of the two formulas
///
/// The pass runs rounds to a fixpoint, and a round-`n` strengthening's witness
/// can itself be a clause round `n-1` strengthened. A proof reconstructed by
/// comparing the input formula against the output formula therefore has no
/// ordering that is guaranteed to verify: the witness a step needs may be a
/// clause the reconstructed sequence only adds later, and the checker then
/// rejects a step that describes a correct transformation. Recording as the
/// pass mutates is the only arrangement that cannot get this wrong, which is
/// why the recorder is threaded through the round rather than bolted on after.
///
/// # What is emitted
///
/// * **Normalization prelude.** A tautology becomes `Delete(original)`; a clause
///   whose literals deduplicate becomes `Add(deduped)` then `Delete(original)`.
///   This exists because a `DRAT` checker's unit propagation reads a clause's
///   literals verbatim, so `(b ∨ b)` is not a unit to it while our normalized
///   `(b)` is — without the prelude a later step that relies on `(b)`
///   propagating verifies in this engine and is rejected by the checker. Same
///   reasoning and same steps as [`crate::vivify`]'s prelude.
/// * **Subsumption / duplicate removal.** `Delete(C)`.
/// * **Self-subsuming resolution.** `Add(C \ {l})` then `Delete(C)`.
///
/// Every emitted `Add` is plain `RUP`; no step here needs `RAT` or an extension
/// variable, so the prefix verifies against the original formula on its own.
pub fn simplify_within_recorded(
    formula: &CnfFormula,
    opts: SubsumeOptions,
    deadline: Option<Instant>,
    mut proof: Option<&mut Vec<DratStep>>,
) -> (CnfFormula, SubsumeStats) {
    let nvars = formula.variable_count();
    let mut stats = SubsumeStats::default();
    // The meter spans every round, because every round rebuilds the occurrence
    // lists and pays their setup again. A per-round budget would bound each
    // round and nothing at all about the pass, which is `SUBSUME_MAX_ROUNDS`
    // times larger. Normalization below is charged as one step per literal read.
    let mut work = PassWork::with_setup(0, opts.work_budget);

    // Normalize; drop tautologies up front (they constrain nothing).
    let mut clauses: Vec<Option<NormClause>> = Vec::with_capacity(formula.clauses().len());
    for clause in formula.clauses() {
        work.charge(clause.lits().len() as u64);
        if let Some(nc) = NormClause::from_clause(clause) {
            if let Some(p) = proof.as_deref_mut()
                && nc.lits.len() != clause.lits().len()
            {
                p.push(DratStep::Add(nc.lits.clone()));
                p.push(DratStep::Delete(clause.lits().to_vec()));
            }
            clauses.push(Some(nc));
        } else {
            if let Some(p) = proof.as_deref_mut() {
                p.push(DratStep::Delete(clause.lits().to_vec()));
            }
            stats.tautologies_removed += 1;
        }
    }

    // Rounds to a fixpoint: strengthening a clause can expose new subsumptions.
    let mut marks = vec![0i8; nvars];
    for _ in 0..SUBSUME_MAX_ROUNDS {
        // Checked before the round starts, because starting one costs a full
        // `O(|F|)` rebuild of the occurrence lists before it can subsume
        // anything.
        if work.must_stop() {
            break;
        }
        if deadline.is_some_and(|dl| Instant::now() >= dl) {
            break;
        }
        match subsume_round(
            &mut clauses,
            nvars,
            &mut marks,
            &mut work,
            deadline,
            proof.as_deref_mut(),
        ) {
            Some(round) => {
                stats.clauses_subsumed += round.clauses_subsumed;
                stats.literals_strengthened += round.literals_strengthened;
            }
            None => break,
        }
    }

    stats.work_spent = work.spent();
    stats.work_exhausted = work.exhausted();
    // Seeded at the setup floor by `PassWork`, so a run that changed nothing
    // reports "all of it after setup" rather than zero.
    stats.work_at_last_progress = work.at_last_progress();
    stats.dead_occurrence_entries = work.dead_entries();

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
        assert_eq!(out.clauses()[0].lits(), &[p(0)]);
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
        assert_eq!(out.clauses()[0].lits(), &[p(1)]);
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
            ProofSolveOutcome, SatResult, check_drat, solve_with_drat_proof, solve_with_native_core,
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
            solve_with_native_core(&f).unwrap(),
            SatResult::Unsat(_)
        ));
        assert!(matches!(
            solve_with_native_core(&out).unwrap(),
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

    /// A formula with many clauses that die mid-round, so their ids sit in
    /// occurrence lists that later candidates keep re-scanning. This is the
    /// population compaction exists for.
    fn stale_entry_fixture() -> CnfFormula {
        const NVARS: usize = 10;
        let mut f = CnfFormula::new(NVARS);
        // Every long clause here is subsumed by a short one, so the long ones
        // die while their neighbours are still being examined.
        for i in 0..NVARS {
            f.add_clause(clause(&[p(i), n((i + 1) % NVARS)])).unwrap();
        }
        for i in 0..NVARS {
            for j in 0..NVARS {
                if i != j {
                    f.add_clause(clause(&[p(i), n((i + 1) % NVARS), p(j)]))
                        .unwrap();
                }
            }
        }
        f
    }

    /// Every charge site, on a formula small enough to enumerate by hand.
    ///
    /// The expectation is a SUM OF NAMED TERMS, not a total: each line is one
    /// place the pass touches memory proportionally to formula size, so
    /// deleting any single charge — including the occurrence-entry charge this
    /// lane exists for — moves the number and fails this test. A test asserting
    /// only `work_spent > setup` would not: the marking and connect charges
    /// alone satisfy that inequality, which is exactly how the sibling lane's
    /// first scan-charge guard survived its own mutation.
    ///
    /// The fixture: `(a ∨ b)` and `(a ∨ b ∨ c)` over three variables, so
    /// `SUBSUME_CLAUSE_LIMIT` and the occurrence cap are both far away and the
    /// only interesting event is the second clause being subsumed by the first.
    #[test]
    fn every_occurrence_step_is_charged_exactly_once() {
        let f = formula(3, &[&[p(0), p(1)], &[p(0), p(1), p(2)]]);
        let (_, stats) = simplify(&f);
        assert_eq!(stats.clauses_subsumed, 1, "the fixture must subsume");

        let expected = 2 + 3   // normalization reads 2 then 3 literals
            + (5 + 6)          // round 1 setup: 5 literal occurrences, 6 lit slots
            + 2 * 2            // (a v b) marked and unmarked
            + (2 + 1)          // ...kept: 2 literals walked for the watch, 1 entry written
            + 2 * 3            // (a v b v c) marked and unmarked
            + 1                // ONE occurrence entry examined: the scan charge
            + 2                // the subset test walks (a v b)'s two literals
            + (2 + 6)          // round 2 setup: 2 literal occurrences, 6 lit slots
            + 2 * 2            // (a v b) marked and unmarked again
            + (2 + 1); // ...and connected again
        assert_eq!(
            stats.work_spent, expected,
            "every step the pass takes must be charged exactly once"
        );
    }

    /// One unbudgeted run prices every candidate budget: a budget at the
    /// last-progress reading costs the run **nothing at all**.
    ///
    /// This is the property the corpus measurement is derived from, so it is
    /// asserted rather than assumed. It is also the guard on `note_progress`:
    /// delete the call in the `Subsumed` arm and the recorded reading falls back
    /// to an earlier one, which truncates the pass and changes the output
    /// formula, failing here.
    #[test]
    fn a_budget_at_the_last_progress_reading_loses_nothing() {
        let f = stale_entry_fixture();
        let (unbudgeted, free) = simplify(&f);
        assert!(free.clauses_subsumed > 0, "the fixture must subsume");
        assert!(
            !free.work_exhausted,
            "the unbudgeted run must not stop early"
        );
        assert!(
            free.work_at_last_progress < free.work_spent,
            "the fixture must waste work after its last useful action"
        );

        let (bounded, capped) = simplify_with_options(
            &f,
            SubsumeOptions {
                work_budget: Some(free.work_at_last_progress),
            },
            None,
        );
        assert!(capped.work_exhausted, "the budget must have bound");
        assert_eq!(capped.clauses_subsumed, free.clauses_subsumed);
        assert_eq!(capped.literals_strengthened, free.literals_strengthened);
        assert_eq!(
            bounded.clauses(),
            unbudgeted.clauses(),
            "a budget at the last-progress reading must cost the run nothing"
        );
    }

    /// A budget below that reading stops the pass, and the partial result is
    /// still logically equivalent to the input.
    ///
    /// Mutation control for the `work.must_stop()` check in `subsume_round`'s
    /// candidate loop: delete it and the pass runs to its fixpoint, so
    /// `work_exhausted` is false and `work_spent` overruns the budget.
    #[test]
    fn the_work_budget_stops_the_pass_and_keeps_the_result_equivalent() {
        const NVARS: usize = 6;
        let mut f = CnfFormula::new(NVARS);
        for i in 0..NVARS {
            f.add_clause(clause(&[p(i)])).unwrap();
            for j in 0..NVARS {
                f.add_clause(clause(&[p(i), p(j), n((i + j) % NVARS)]))
                    .unwrap();
            }
        }
        let (_, free) = simplify(&f);
        let limit = free.work_spent / 4;
        assert!(limit > 0);

        let (out, stats) = simplify_with_options(
            &f,
            SubsumeOptions {
                work_budget: Some(limit),
            },
            None,
        );
        assert!(stats.work_exhausted, "the budget must have bound");
        assert!(
            stats.work_spent < free.work_spent,
            "a bound pass must spend less than a free one: {} vs {}",
            stats.work_spent,
            free.work_spent
        );
        equivalent(&f, &out, NVARS);
    }

    /// **This pass cannot produce a dead occurrence entry**, so compaction has
    /// nothing to remove here.
    ///
    /// That is a property of the schedule, not of the fixture. Occurrence lists
    /// are rebuilt from the live clauses at the top of every round, and the only
    /// clause a round ever removes is the candidate it is currently examining —
    /// which is connected on the `Keep` arm, i.e. only when it is *not* removed.
    /// So no entry in any list can ever refer to a removed clause.
    ///
    /// The claim is asserted through the counter rather than argued in a
    /// comment, on a fixture that subsumes dozens of clauses and would show a large
    /// count if the invariant were false. It is the negative half of the
    /// compaction question: `crate::bve`'s lists live for the whole pass and its
    /// eliminations kill clauses sitting in many of them, which is where the
    /// dead-id constant actually is.
    #[test]
    fn this_pass_cannot_produce_a_dead_occurrence_entry() {
        let f = stale_entry_fixture();
        let (_, stats) = simplify(&f);
        assert!(
            stats.clauses_subsumed >= 50,
            "the fixture must remove many clauses mid-round: {}",
            stats.clauses_subsumed
        );
        assert_eq!(
            stats.dead_occurrence_entries, 0,
            "a connected clause is never removed, so no scan can meet a dead id"
        );
    }

    /// The default options are today's behaviour, stated as a test rather than
    /// as a comment: an unbudgeted, non-compacting run must never report a
    /// budget stop.
    #[test]
    fn the_default_options_never_stop_the_pass() {
        assert_eq!(SubsumeOptions::DEFAULT.work_budget, None);
        let (_, stats) = simplify(&stale_entry_fixture());
        assert!(!stats.work_exhausted);
        assert!(stats.work_spent > 0, "the meter must run even unbudgeted");
    }

    /// The budget binds WITHIN a round, not only between rounds.
    ///
    /// This guard was added because its mutation **survived**: deleting the
    /// `must_stop()` check in the candidate loop left every other test green,
    /// since the round loop checks too and the budget still appeared to bind.
    /// It does not: the first round always starts, so with only the round-level
    /// check a single round overruns the budget by however much that round
    /// costs — unbounded on a large formula, which is the entire population a
    /// budget exists for.
    ///
    /// The fixture reaches its fixpoint in ONE round (no clause subsumes or
    /// strengthens another, so `subsume_round` reports no change and the loop
    /// stops), which makes the round-level check unable to stop anything at
    /// all. A budget at a quarter of the unbudgeted spend must therefore be
    /// enforced by the candidate loop or not at all.
    #[test]
    fn the_budget_binds_within_a_round_and_not_only_between_rounds() {
        const NVARS: usize = 400;
        let mut f = CnfFormula::new(NVARS);
        for i in 0..NVARS {
            f.add_clause(clause(&[p(i), p((i + 1) % NVARS)])).unwrap();
        }
        let (_, free) = simplify(&f);
        assert_eq!(
            free.clauses_subsumed, 0,
            "the fixture must reach its fixpoint in one round"
        );
        assert_eq!(free.literals_strengthened, 0);

        let limit = free.work_spent / 4;
        assert!(limit > 0);
        let (_, capped) = simplify_with_options(
            &f,
            SubsumeOptions {
                work_budget: Some(limit),
            },
            None,
        );
        assert!(capped.work_exhausted, "the budget must have bound");
        assert!(
            capped.work_spent < free.work_spent / 2,
            "a budget enforced only between rounds lets the single round run to \
             completion: spent {} against an unbudgeted {}",
            capped.work_spent,
            free.work_spent
        );
    }

    /// A dead occurrence entry IS counted when one is reachable.
    ///
    /// The pass cannot produce one (see
    /// `this_pass_cannot_produce_a_dead_occurrence_entry`), which makes that
    /// invariant test vacuous on its own: a counter hard-wired to zero would
    /// satisfy it. This plants one directly — a connected id whose clause slot
    /// is `None`, the state the scan's `else` branch exists for — and requires
    /// the counter to see it.
    ///
    /// So the pair says both halves: the counting path works, and the pass
    /// never exercises it. Without this one, "subsumption reports zero dead
    /// entries" would be a statement about the instrument rather than about the
    /// pass.
    #[test]
    fn a_dead_occurrence_entry_is_counted_when_one_is_reachable() {
        let nvars = 4;
        let live = NormClause::from_clause(&clause(&[p(0), p(1)])).expect("not a tautology");
        let candidate = NormClause::from_clause(&clause(&[p(2), p(3)])).expect("not a tautology");
        // Slot 0 is dead; slot 1 is the candidate being examined.
        let clauses = vec![None, Some(candidate)];
        let mut occs: Vec<Vec<usize>> = vec![Vec::new(); 2 * nvars];
        // Connect the DEAD clause id on a literal the candidate carries, so the
        // candidate's scan reaches it.
        occs[lit_index(p(2))].push(0);
        drop(live);

        let mut marks = vec![0i8; nvars];
        let mut checks = 0usize;
        let mut work = PassWork::with_setup(0, None);
        let outcome = try_subsume(1, &clauses, &occs, &mut marks, &mut checks, &mut work);
        assert!(
            matches!(outcome, Outcome::Keep),
            "a dead entry must not decide anything"
        );
        assert_eq!(
            work.dead_entries(),
            1,
            "the scan must count the entry it paid for and got nothing from"
        );
        assert_eq!(
            checks, 0,
            "and a dead entry must never reach the subsumption check"
        );
        assert_eq!(marks, vec![0i8; nvars], "marks must be left zeroed");
    }
}
