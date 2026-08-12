//! Backward (core-first) DRAT checking (ADR-0382).
//!
//! [`crate::check_drat`] is the *reference* checker and stays exactly as it is:
//! a few dozen lines that walk the proof forward and verify every added clause
//! against the clause set accumulated so far. It is small enough to audit by
//! reading it, which is the whole basis of the trust story for `unsat`.
//!
//! It is also, at search scale, unusably slow: every step re-scans an
//! accumulating clause database to fixpoint, so the cost grows superlinearly in
//! the proof length. Measured on a 35,858-clause instance (release build):
//! 1,674 steps in 2.3 s, 38,015 steps in 200.6 s, 145,836 steps in 1,031.6 s,
//! and a 1.2M-step proof unfinished after 30 minutes — while *solving* the same
//! instances is 470–670× faster than checking them.
//!
//! [`check_drat_backward`] verifies the same claim by the standard technique
//! (Wetzler, Heule, Hunt, *DRAT-trim: Efficient Checking and Trimming Using
//! Expressive Clausal Proofs*, SAT 2014): replay the proof backwards from the
//! first empty clause, verify only the lemmas the refutation actually depends
//! on, and drive every unit propagation through watched literals over a clause
//! arena instead of a rescan. The verdict is the same; the work is a small
//! fraction of it.
//!
//! The engine has three moving parts:
//!
//! 1. **Clause lifetimes.** One forward pass turns the proof into records with
//!    a birth step and a death step, so "which clauses are live at step `i`" is
//!    an interval test rather than a replay. Deletions are matched exactly the
//!    way the reference matches them (by literal set, one live clause per
//!    deletion, unmatched deletions ignored).
//! 2. **Deletion-aware watched literals.** Clauses enter and leave the working
//!    database as the walk retreats past their birth and death steps; the two
//!    watch lists are maintained eagerly so propagation never visits a clause
//!    that is not live at the step being checked.
//! 3. **Core marking with a reused unit-propagation trail.** The literals
//!    forced by the database alone are computed once and reused across lemma
//!    checks, and recomputed only when a clause that justifies part of that
//!    trail leaves the database. Each verified lemma marks the cone of clauses
//!    its refutation used; only marked clauses are ever verified.
//!
//! # What else the marked core is good for
//!
//! The core is the expensive thing this engine computes, and checking throws it
//! away. Two public routes keep it (ADR-0382):
//!
//! - [`trim_drat_proof`] emits the core as a standalone DRAT proof — the same
//!   refutation with the dead weight removed. It is a *checked* artifact: the
//!   trimmed proof is re-verified by this checker before being returned, so a
//!   trim that broke the proof is an error rather than a shorter file that does
//!   not check.
//! - [`crate::elaborate_drat_to_lrat_backward`] emits the core as an LRAT proof
//!   with explicit antecedent hints, which [`crate::check_lrat`] replays without
//!   searching at all. RAT lemmas are refused rather than approximated, because
//!   [`crate::LratStep`] cannot express them.
//!
//! Both reuse the walk above; neither re-derives anything.

use std::collections::HashMap;

use crate::drat::sorted;
use crate::lrat::{LratError, LratStep};
use crate::{CnfFormula, CnfLit, DratError, DratStep};

/// A literal packed as `2 * variable index + is_negated`, so `code ^ 1` is the
/// complement and both the watch lists and the assignment are flat vectors
/// indexed by literal.
type Code = usize;

/// Sentinel for "no clause": the reason of an assumed literal, an absent
/// record, and the pivot of an empty clause.
const NO_CLAUSE: usize = usize::MAX;

/// Sentinel for "never deleted" in [`ClauseRecord::died`].
const NEVER: usize = usize::MAX;

/// Packs a literal.
fn code_of(lit: CnfLit) -> Code {
    lit.var().index() * 2 + usize::from(lit.is_negated())
}

/// The variable of a packed literal.
const fn var_of(code: Code) -> usize {
    code >> 1
}

/// One clause of the working database, with the proof interval over which it is
/// available.
///
/// `born` and `died` are proof-step indices: the clause is available to the
/// checks at steps `born..died`. A formula clause has `born == 0`; a clause
/// added by step `s` has `born == s + 1`, because the forward checker only sees
/// it from the *next* step on. A clause deleted by step `d` has `died == d`,
/// for the same reason.
struct ClauseRecord {
    /// Start of the clause's literals in the arena.
    start: usize,
    /// Number of literals (occurrences, not distinct variables).
    len: usize,
    /// First proof-step index at which the clause is available.
    born: usize,
    /// First proof-step index at which the clause is no longer available.
    died: usize,
    /// The clause's *first literal as written*, which is the RAT pivot the
    /// reference checker uses. Watch maintenance permutes the arena span, so
    /// the pivot cannot be recovered from it; `NO_CLAUSE` for an empty clause.
    pivot: Code,
    /// The refutation depends on this clause, so it must itself be verified.
    core: bool,
    /// Currently in the working database.
    live: bool,
    /// Justifies part of the current root-level trail (a reason, or the
    /// conflicting clause). Removing such a clause invalidates the trail.
    forced: bool,
}

/// The proof compiled into clause records with lifetimes: the whole of phase 1.
struct Plan {
    /// Literals of every clause, back to back.
    arena: Vec<Code>,
    /// Formula clauses first, then one record per addition, in proof order.
    records: Vec<ClauseRecord>,
    /// Record added by each proof step (`NO_CLAUSE` for a deletion step).
    added_by_step: Vec<usize>,
    /// Record removed by each proof step (`NO_CLAUSE` for an addition step, or
    /// for a deletion that matched no live clause — which the reference ignores
    /// and so do we).
    deleted_by_step: Vec<usize>,
    /// Number of variables the assignment must cover: the formula's count and
    /// every variable the proof mentions.
    variable_count: usize,
    /// Number of leading records that come from the formula rather than the
    /// proof. Records below it are present whatever the proof does, which is
    /// what makes them retained by [`trim_drat_proof`] without being core.
    formula_len: usize,
}

impl Plan {
    /// Compiles `formula` plus the proof prefix `steps` into clause records.
    ///
    /// Only the prefix up to and including the empty-clause addition is ever
    /// passed here: nothing after it can be part of the refutation.
    fn build(formula: &CnfFormula, steps: &[DratStep]) -> Result<Self, DratError> {
        let variable_count = variable_count(formula, steps)?;
        let mut plan = Self {
            arena: Vec::new(),
            records: Vec::new(),
            added_by_step: vec![NO_CLAUSE; steps.len()],
            deleted_by_step: vec![NO_CLAUSE; steps.len()],
            variable_count,
            formula_len: formula.clauses().len(),
        };
        // Live clauses by literal *set*, which is how the reference matches a
        // deletion. Never iterated — only looked up — so no output of this
        // module depends on hash order.
        let mut live: HashMap<Vec<(usize, bool)>, Vec<usize>> = HashMap::new();
        for clause in formula.clauses() {
            let record = plan.push_clause(clause.lits(), 0);
            live.entry(sorted(clause.lits())).or_default().push(record);
        }
        for (index, step) in steps.iter().enumerate() {
            match step {
                DratStep::Add(lits) => {
                    let record = plan.push_clause(lits, index + 1);
                    plan.added_by_step[index] = record;
                    live.entry(sorted(lits)).or_default().push(record);
                }
                DratStep::Delete(lits) => {
                    // Which of several identical live clauses is removed is
                    // immaterial — they have the same literal set, and a
                    // clause's stored literal order affects nothing but its own
                    // RAT pivot, which a database clause never supplies.
                    if let Some(records) = live.get_mut(&sorted(lits))
                        && let Some(record) = records.pop()
                    {
                        plan.records[record].died = index;
                        plan.deleted_by_step[index] = record;
                    }
                }
            }
        }
        Ok(plan)
    }

    /// Appends a clause to the arena and returns its record id.
    fn push_clause(&mut self, lits: &[CnfLit], born: usize) -> usize {
        let start = self.arena.len();
        self.arena.extend(lits.iter().copied().map(code_of));
        let record = self.records.len();
        self.records.push(ClauseRecord {
            start,
            len: lits.len(),
            born,
            died: NEVER,
            pivot: lits.first().copied().map_or(NO_CLAUSE, code_of),
            core: false,
            live: false,
            forced: false,
        });
        record
    }
}

/// Number of variables the checker must size its vectors for.
///
/// # Errors
///
/// Returns [`DratError::Parse`] when twice the variable count does not fit in
/// `usize` — the literal encoding would overflow. Only reachable on a 32-bit
/// target with an absurd variable count.
fn variable_count(formula: &CnfFormula, steps: &[DratStep]) -> Result<usize, DratError> {
    let mut count = formula.variable_count();
    let mut widen = |lits: &[CnfLit]| {
        for lit in lits {
            count = count.max(lit.var().index() + 1);
        }
    };
    for clause in formula.clauses() {
        widen(clause.lits());
    }
    for step in steps {
        // Deletion literals never reach the arena or the assignment: a deletion
        // is resolved by literal set alone.
        if let DratStep::Add(lits) = step {
            widen(lits);
        }
    }
    if count.checked_mul(2).is_none() {
        return Err(DratError::Parse(format!(
            "proof mentions {count} variables, which overflows the literal encoding"
        )));
    }
    Ok(count)
}

/// Verifies `proof` against `formula` by backward (core-first) checking
/// (ADR-0382).
///
/// Returns `Ok(true)` when the proof establishes UNSAT, `Ok(false)` when it
/// contains no empty-clause addition (so UNSAT is not established), and `Err`
/// when a step the refutation depends on fails to verify.
///
/// # Relationship to [`crate::check_drat`]
///
/// The forward checker verifies *every* added clause. This one verifies only
/// the clauses the empty clause actually depends on — the core it extracts
/// while replaying the proof backwards. On any proof the forward checker
/// accepts, the two agree exactly: every lemma verifies there, so in particular
/// every core lemma does, and both report the same `Ok(true)`/`Ok(false)`.
///
/// They differ in one direction, deliberately, and that difference is the
/// technique:
///
/// - A step no core lemma propagates through is never checked. A proof that
///   contains a valid refutation **plus** unjustified dead weight is therefore
///   accepted here and rejected by [`crate::check_drat`]. This is sound —
///   `Ok(true)` still means "this proof contains a verified refutation of
///   `formula`", because a lemma is skipped only when nothing the refutation
///   used depended on it — and it is the contract `drat-trim` has had since
///   2014. When the question is "is every line of this proof justified?" rather
///   than "is this formula unsatisfiable?", use [`crate::check_drat`].
/// - For the same reason, the `step` in [`DratError::StepNotVerified`] names
///   *a* step the refutation depends on which does not verify; the forward
///   checker names the *first* unverified step of any kind. When the earliest
///   failure is in the core — a corrupted or truncated real proof — they are
///   the same index.
///
/// Unlike [`crate::check_drat_streaming`], backward checking is inherently
/// non-streaming: the whole proof prefix up to the empty clause has to be
/// resident, because it is walked in reverse.
///
/// # Errors
///
/// Returns [`DratError::StepNotVerified`] for a core clause addition that is
/// neither RUP nor RAT, or [`DratError::Parse`] if the proof's variable count
/// overflows the internal literal encoding.
pub fn check_drat_backward(formula: &CnfFormula, proof: &[DratStep]) -> Result<bool, DratError> {
    Ok(run_backward(formula, proof, Options::CHECK)?.is_some())
}

/// Engine knobs.
///
/// Deliberately private: each public entry point picks one fixed configuration,
/// so a checker's behaviour stays a function of its inputs alone (determinism is
/// a public API promise). The struct exists because the walk is shared by three
/// consumers that want different work out of it, and because A/B-ing
/// [`Options::core_first`] is how its value was decided (ADR-0382).
#[derive(Clone, Copy)]
struct Options {
    /// Propagate over clauses already in the core before the rest, so a
    /// conflict prefers antecedents the core has already paid for. Shrinks the
    /// core; costs one clause migration per newly marked clause.
    core_first: bool,
    /// Record the antecedent chain of every verified core lemma, which is what
    /// LRAT elaboration emits as hints.
    trace: bool,
}

impl Options {
    /// Plain checking: no chain recording.
    const CHECK: Self = Self {
        core_first: true,
        trace: false,
    };
    /// Checking with hint chains, for LRAT elaboration.
    const TRACE: Self = Self {
        core_first: true,
        trace: true,
    };
}

/// Runs the backward check and hands back the engine, whose marks and traces are
/// what [`trim_drat_proof`] and LRAT elaboration read.
///
/// `Ok(None)` means the proof contains no empty-clause addition, so there is no
/// refutation to check, trim, or elaborate.
fn run_backward(
    formula: &CnfFormula,
    proof: &[DratStep],
    options: Options,
) -> Result<Option<BackwardChecker>, DratError> {
    // The refutation is rooted at the *first* empty clause: once it is added,
    // every later addition is trivially RUP over a database that contains it,
    // so nothing after it can carry weight.
    let Some(root) = proof
        .iter()
        .position(|step| matches!(step, DratStep::Add(lits) if lits.is_empty()))
    else {
        return Ok(None);
    };
    let plan = Plan::build(formula, &proof[..=root])?;
    let mut checker = BackwardChecker::new(plan, options);
    checker.run(root)?;
    Ok(Some(checker))
}

/// Trims `proof` down to the lemmas its refutation actually uses (ADR-0382).
///
/// Returns `Ok(None)` when the proof contains no empty-clause addition (there is
/// no refutation to trim, exactly as [`check_drat_backward`] returns
/// `Ok(false)`), and otherwise a proof that
///
/// - stops at the first empty clause,
/// - keeps only the additions the refutation propagates through, and
/// - keeps a deletion exactly when the clause it removed is one of those (or a
///   formula clause).
///
/// That last rule is the load-bearing one. Dropping deletions wholesale would
/// *enlarge* the active database, and a RAT step is only valid against the
/// database it was checked against — a larger one can add resolution candidates
/// and break it. Keeping the deletions that still have a target reproduces the
/// original database minus the clauses nothing used, which is a *subset*: RUP
/// steps keep every antecedent they used (the core marks them), and RAT steps
/// see no candidate they did not already survive.
///
/// The result is re-verified by [`check_drat_backward`] before it is returned,
/// so this function never hands back a "proof" that does not check. It is also,
/// by construction, free of the dead weight that is the one place
/// [`check_drat_backward`] and [`crate::check_drat`] disagree: the forward
/// checker accepts a trimmed proof too.
///
/// # Errors
///
/// Returns [`DratError::StepNotVerified`] when the input proof's refutation does
/// not check, or — a guard that should be unreachable — when the trimmed proof
/// fails re-verification. Returns [`DratError::Parse`] if the proof's variable
/// count overflows the internal literal encoding.
pub fn trim_drat_proof(
    formula: &CnfFormula,
    proof: &[DratStep],
) -> Result<Option<Vec<DratStep>>, DratError> {
    let Some(checker) = run_backward(formula, proof, Options::CHECK)? else {
        return Ok(None);
    };
    let mut trimmed = Vec::new();
    for (step, entry) in proof.iter().enumerate().take(checker.added_by_step.len()) {
        let record = match entry {
            DratStep::Add(_) => checker.added_by_step[step],
            DratStep::Delete(_) => checker.deleted_by_step[step],
        };
        // A deletion that matched nothing (`NO_CLAUSE`) is dropped: the
        // reference ignores it, and it cannot be describing a clause the
        // trimmed proof has.
        if record != NO_CLAUSE && checker.retained(record) {
            trimmed.push(entry.clone());
        }
    }
    // Never return an unchecked artifact. This costs a second backward pass over
    // a strictly smaller proof; the alternative is emitting a file that claims
    // to be a refutation without anything having verified that it is one.
    if check_drat_backward(formula, &trimmed)? {
        Ok(Some(trimmed))
    } else {
        Err(DratError::StepNotVerified {
            step: trimmed.len(),
        })
    }
}

/// Elaborates the core of `proof` into an LRAT proof with explicit hints
/// (ADR-0382); [`crate::elaborate_drat_to_lrat_backward`] is the public name.
///
/// # Errors
///
/// See [`crate::elaborate_drat_to_lrat_backward`].
pub(crate) fn elaborate_backward(
    formula: &CnfFormula,
    proof: &[DratStep],
) -> Result<Vec<LratStep>, LratError> {
    let checker = match run_backward(formula, proof, Options::TRACE) {
        Ok(Some(checker)) => checker,
        // No empty clause: nothing is established, and the empty LRAT proof
        // says exactly that (`check_lrat` reports `Ok(false)` for it).
        Ok(None) => return Ok(Vec::new()),
        Err(DratError::StepNotVerified { step }) => {
            return Err(LratError::DratStepNotVerified { step });
        }
        Err(DratError::Parse(what)) => return Err(LratError::Parse(what)),
    };

    // Formula clauses take ids `1..=n`, as `check_lrat` assigns them; core
    // lemmas take ids from `n + 1` in *forward* proof order, which is the order
    // the trace log gets when reversed.
    let mut id_of = vec![0u64; checker.records.len()];
    for (record, id) in id_of.iter_mut().enumerate().take(checker.formula_len) {
        *id = u64::try_from(record + 1)
            .map_err(|_| LratError::Parse("formula clause count does not fit in u64".to_owned()))?;
    }
    let mut next_id = u64::try_from(checker.formula_len + 1)
        .map_err(|_| LratError::Parse("formula clause count does not fit in u64".to_owned()))?;

    let mut out = Vec::with_capacity(checker.trace_log.len());
    // `next_id` is not a plain loop counter: its start is the formula clause
    // count, and `id_of` snapshots it per lemma for later hint resolution.
    #[allow(clippy::explicit_counter_loop)]
    for entry in checker.trace_log.iter().rev() {
        let chain = match &entry.justification {
            Justification::Rup(chain) => chain,
            // A RAT lemma needs a pivot and negative hint blocks, which
            // `LratStep` has no room for. Refusing is the only sound answer:
            // emitting the RUP-shaped step would be a hint chain that does not
            // justify the clause.
            Justification::Rat => return Err(LratError::RatNotSupported { step: entry.step }),
            Justification::ChainFailed => {
                return Err(LratError::HintChainFailed { step: entry.step });
            }
        };
        let mut hints = Vec::with_capacity(chain.len());
        for &record in chain {
            let id = id_of[record];
            if id == 0 {
                // A hint outside the core would name a clause the emitted proof
                // never adds. The cone marks everything a chain rests on, so
                // this is a guard on that invariant, not an expected path.
                return Err(LratError::HintChainFailed { step: entry.step });
            }
            hints.push(id);
        }
        let DratStep::Add(clause) = &proof[entry.step] else {
            return Err(LratError::HintChainFailed { step: entry.step });
        };
        out.push(LratStep::Add {
            id: next_id,
            // From the proof, not the arena: watch maintenance permutes a
            // clause's literals in place.
            clause: clause.clone(),
            hints,
        });
        id_of[entry.record] = next_id;
        next_id += 1;
    }
    Ok(out)
}

/// Why a verified lemma verified, recorded when [`Options::trace`] is on.
enum Justification {
    /// RUP, by this chain of antecedent records in propagation order, ending
    /// with the conflicting record. Empty for a tautology, which needs none.
    Rup(Vec<usize>),
    /// RAT — sound, verified, and not expressible as an [`LratStep`].
    Rat,
    /// RUP held, but the recorded chain could not be replayed under the LRAT
    /// checker's own semantics. A guard: nothing is emitted from it.
    ChainFailed,
}

/// One verified core lemma, in backward-walk order.
struct TraceEntry {
    /// Proof-step index of the addition.
    step: usize,
    /// Record the step added.
    record: usize,
    /// What verified it.
    justification: Justification,
}

/// The backward checking engine: a watched-literal unit propagator over a
/// clause arena whose membership tracks the proof position being checked.
struct BackwardChecker {
    arena: Vec<Code>,
    records: Vec<ClauseRecord>,
    added_by_step: Vec<usize>,
    deleted_by_step: Vec<usize>,
    /// Number of leading records that belong to the formula.
    formula_len: usize,
    /// Propagate over core clauses first (see [`Options::core_first`]).
    core_first: bool,
    /// Record hint chains (see [`Options::trace`]).
    trace: bool,
    /// Watch lists indexed by literal code; a live clause of two or more
    /// literals appears in the lists of `arena[start]` and `arena[start + 1]`.
    /// A live clause is watched in exactly one of the two structures — this one
    /// when it is not (yet) core, [`BackwardChecker::watches_core`] when it is.
    /// [`BackwardChecker::set_core`] migrates it as marks appear.
    watches: Vec<Vec<usize>>,
    /// Watch lists for clauses already in the core. Always empty when
    /// `core_first` is off, which makes the core pass of
    /// [`BackwardChecker::propagate`] a no-op and leaves propagation order
    /// exactly what a single watch structure would give.
    watches_core: Vec<Vec<usize>>,
    /// Records of fewer than two literals, which cannot be watched: empty
    /// clauses (an immediate conflict) and units (seeds of the root trail).
    short: Vec<usize>,
    /// Indexed by literal code: is this literal currently true?
    assign: Vec<bool>,
    trail: Vec<Code>,
    /// Position on the trail of each assigned variable.
    trail_pos: Vec<usize>,
    /// Clause that propagated each assigned variable, `NO_CLAUSE` when the
    /// literal was assumed (the negation of the lemma under test).
    reason: Vec<usize>,
    /// Next trail position to propagate over non-core clauses.
    head: usize,
    /// Next trail position to propagate over core clauses; never behind
    /// [`BackwardChecker::head`].
    head_core: usize,
    /// Trail prefix implied by the database alone, shared by every lemma check.
    root_len: usize,
    /// The database alone is contradictory, by this clause.
    root_conflict: Option<usize>,
    /// The root trail must be recomputed before the next lemma check.
    stale: bool,
    /// Records whose [`ClauseRecord::forced`] flag is set.
    flagged: Vec<usize>,
    /// Per-variable generation stamps for cone marking.
    seen: Vec<u64>,
    generation: u64,
    /// Antecedents collected by the last cone walk, as `(trail position of the
    /// literal it forced, record)`. Sorting by the first component puts the
    /// chain in propagation order, which is the order LRAT hints must be in.
    cone_order: Vec<(usize, usize)>,
    /// Conflicting record of the last cone walk.
    cone_conflict: usize,
    /// Hint chain of the last successful [`BackwardChecker::check_rup`], in
    /// propagation order and ending with the conflict. Only maintained when
    /// tracing.
    chain: Vec<usize>,
    /// One entry per verified core lemma, in backward-walk order. Only
    /// maintained when tracing.
    trace_log: Vec<TraceEntry>,
    /// Assignment of the hint-chain replay, independent of the engine's own so
    /// a chain can be validated after the check that produced it has
    /// backtracked.
    sim: Vec<bool>,
    /// Literals set in [`BackwardChecker::sim`], so it can be cleared in time
    /// proportional to what was assigned.
    sim_trail: Vec<Code>,
    /// Scratch buffers, reused so a lemma check allocates nothing.
    lemma: Vec<Code>,
    resolvent: Vec<Code>,
    stack: Vec<usize>,
}

impl BackwardChecker {
    fn new(plan: Plan, options: Options) -> Self {
        let Plan {
            arena,
            records,
            added_by_step,
            deleted_by_step,
            variable_count,
            formula_len,
        } = plan;
        let short = records
            .iter()
            .enumerate()
            .filter(|(_, record)| record.len < 2)
            .map(|(id, _)| id)
            .collect();
        Self {
            arena,
            records,
            added_by_step,
            deleted_by_step,
            formula_len,
            core_first: options.core_first,
            trace: options.trace,
            watches: vec![Vec::new(); variable_count * 2],
            watches_core: vec![Vec::new(); variable_count * 2],
            short,
            assign: vec![false; variable_count * 2],
            trail: Vec::new(),
            trail_pos: vec![0; variable_count],
            reason: vec![NO_CLAUSE; variable_count],
            head: 0,
            head_core: 0,
            root_len: 0,
            root_conflict: None,
            stale: true,
            flagged: Vec::new(),
            seen: vec![0; variable_count],
            generation: 0,
            cone_order: Vec::new(),
            cone_conflict: NO_CLAUSE,
            chain: Vec::new(),
            trace_log: Vec::new(),
            sim: vec![false; variable_count * 2],
            sim_trail: Vec::new(),
            lemma: Vec::new(),
            resolvent: Vec::new(),
            stack: Vec::new(),
        }
    }

    /// Is `record` present in a proof trimmed to the core?
    ///
    /// Formula clauses are, whatever the proof does — they are not part of the
    /// proof — and so is every clause the refutation propagated through.
    fn retained(&self, record: usize) -> bool {
        record < self.formula_len || self.records[record].core
    }

    /// Checks the refutation rooted at the empty clause added by step `root`.
    fn run(&mut self, root: usize) -> Result<(), DratError> {
        for record in 0..self.records.len() {
            self.set_membership(record, root);
        }
        if !self.verify(self.added_by_step[root], root) {
            return Err(DratError::StepNotVerified { step: root });
        }
        for step in (0..root).rev() {
            self.retreat_to(step);
            let record = self.added_by_step[step];
            if record != NO_CLAUSE && self.records[record].core && !self.verify(record, step) {
                return Err(DratError::StepNotVerified { step });
            }
        }
        Ok(())
    }

    /// Moves the working database from the clauses live at `step + 1` to those
    /// live at `step`.
    ///
    /// Exactly two records can change status: the one the step at `step` added
    /// (born at `step + 1`, so it must go) and the one the step at `step + 1`
    /// deleted (died at `step + 1`, so it comes back). Both are re-derived from
    /// the record's interval rather than assumed, which keeps the degenerate
    /// case — a clause added and deleted by consecutive steps — correct without
    /// a special case.
    fn retreat_to(&mut self, step: usize) {
        let born_here = self.added_by_step[step];
        if born_here != NO_CLAUSE {
            self.set_membership(born_here, step);
        }
        let died_next = self.deleted_by_step[step + 1];
        if died_next != NO_CLAUSE {
            self.set_membership(died_next, step);
        }
    }

    /// Attaches or detaches `record` so the database matches its lifetime at
    /// `step`.
    fn set_membership(&mut self, record: usize, step: usize) {
        let wanted = self.records[record].born <= step && step < self.records[record].died;
        match (wanted, self.records[record].live) {
            (true, false) => self.attach(record),
            (false, true) => self.detach(record),
            _ => {}
        }
    }

    /// Adds `record` to the working database.
    ///
    /// Watches are placed on two literals that are not false under the current
    /// root trail, which is what keeps the watch invariant true without a
    /// propagation pass. A clause that has fewer than two such literals is unit
    /// or falsified *right now*, so it can force new literals: the root trail is
    /// marked stale and recomputed before the next lemma check.
    fn attach(&mut self, record: usize) {
        self.records[record].live = true;
        let start = self.records[record].start;
        let len = self.records[record].len;
        if len < 2 {
            // An empty clause is an immediate conflict and a unit always forces
            // its literal; either way the trail must be rebuilt.
            self.stale = true;
            return;
        }
        let mut placed = 0;
        for position in start..start + len {
            if !self.assign[self.arena[position] ^ 1] {
                self.arena.swap(start + placed, position);
                placed += 1;
                if placed == 2 {
                    break;
                }
            }
        }
        if placed < 2 {
            self.stale = true;
        }
        // Even when the watch invariant could not be established, the clause is
        // attached to *some* pair of literals: the stale flag forces a rebuild
        // from an empty assignment before anything propagates, and under an
        // empty assignment every placement is valid.
        let first = self.arena[start];
        let second = self.arena[start + 1];
        let core = self.core_first && self.records[record].core;
        let watches = if core {
            &mut self.watches_core
        } else {
            &mut self.watches
        };
        watches[first].push(record);
        watches[second].push(record);
    }

    /// Removes `record` from the working database.
    fn detach(&mut self, record: usize) {
        self.records[record].live = false;
        let start = self.records[record].start;
        if self.records[record].len >= 2 {
            let first = self.arena[start];
            let second = self.arena[start + 1];
            let core = self.core_first && self.records[record].core;
            let watches = if core {
                &mut self.watches_core
            } else {
                &mut self.watches
            };
            // One occurrence per watched position: a clause with a repeated
            // literal is watched twice on the same literal and must be removed
            // twice.
            remove_watch(&mut watches[first], record);
            remove_watch(&mut watches[second], record);
        }
        if self.records[record].forced {
            self.stale = true;
        }
    }

    /// Marks `record` as part of the core, migrating its watches into the
    /// core-first structure (ADR-0382, follow-on A8).
    ///
    /// Marking is monotone — nothing ever leaves the core — so a clause moves at
    /// most once, and the invariant "a live clause is watched in exactly the
    /// structure its `core` flag names" holds by construction. Migration is safe
    /// here because every caller is *between* propagations, never inside the
    /// loop that walks a watch list.
    fn set_core(&mut self, record: usize) {
        if self.records[record].core {
            return;
        }
        self.records[record].core = true;
        if !self.core_first || !self.records[record].live || self.records[record].len < 2 {
            return;
        }
        let start = self.records[record].start;
        let first = self.arena[start];
        let second = self.arena[start + 1];
        remove_watch(&mut self.watches[first], record);
        remove_watch(&mut self.watches[second], record);
        self.watches_core[first].push(record);
        self.watches_core[second].push(record);
    }

    /// Recomputes the trail of literals implied by the database alone, if a
    /// clause that justified it has left.
    ///
    /// Rebuilding from an empty assignment is what makes the watch invariant
    /// self-healing: no literal is false, so every watch placement — including
    /// the arbitrary ones [`BackwardChecker::attach`] fell back on — is valid
    /// again.
    fn refresh_root(&mut self) {
        if !self.stale {
            return;
        }
        for &lit in &self.trail {
            self.assign[lit] = false;
        }
        self.trail.clear();
        self.head = 0;
        self.head_core = 0;
        self.root_len = 0;
        self.root_conflict = None;
        for &record in &self.flagged {
            self.records[record].forced = false;
        }
        self.flagged.clear();

        let short = std::mem::take(&mut self.short);
        let mut conflict = None;
        for &record in &short {
            if !self.records[record].live {
                continue;
            }
            if self.records[record].len == 0 {
                conflict = Some(record);
                break;
            }
            let unit = self.arena[self.records[record].start];
            if self.assign[unit] {
                continue;
            }
            if self.assign[unit ^ 1] {
                conflict = Some(record);
                break;
            }
            self.assign_lit(unit, record);
        }
        self.short = short;
        if conflict.is_none() {
            conflict = self.propagate();
        }

        self.root_len = self.trail.len();
        self.head = self.trail.len();
        self.head_core = self.trail.len();
        self.root_conflict = conflict;
        // Flag everything the trail rests on, so that removing any of it — and
        // only then — invalidates the cache.
        for position in 0..self.trail.len() {
            let reason = self.reason[var_of(self.trail[position])];
            if reason != NO_CLAUSE {
                self.flag(reason);
            }
        }
        if let Some(record) = conflict {
            self.flag(record);
        }
        self.stale = false;
    }

    /// Marks `record` as justifying the root trail.
    fn flag(&mut self, record: usize) {
        if !self.records[record].forced {
            self.records[record].forced = true;
            self.flagged.push(record);
        }
    }

    /// Assigns `lit` true with the given reason and pushes it on the trail.
    fn assign_lit(&mut self, lit: Code, reason: usize) {
        self.assign[lit] = true;
        self.trail_pos[var_of(lit)] = self.trail.len();
        self.reason[var_of(lit)] = reason;
        self.trail.push(lit);
    }

    /// Undoes everything assigned past the root trail.
    fn backtrack(&mut self) {
        while self.trail.len() > self.root_len {
            let lit = self.trail.pop().expect("trail is longer than the root");
            self.assign[lit] = false;
        }
        self.head = self.root_len;
        self.head_core = self.root_len;
    }

    /// Unit-propagates to fixpoint, returning the conflicting clause if one
    /// arises.
    ///
    /// Two passes with two trail pointers: the core watch lists are driven to
    /// fixpoint, then one literal's non-core list is visited, then back to the
    /// core lists. Any conflict a full propagation would find is still found —
    /// unit propagation has a unique fixpoint, so a conflict reachable under one
    /// visit order is reachable under every complete one — but a conflict that
    /// core clauses alone can produce is found *first*, and the cone marked from
    /// it adds nothing new to the core. That is the whole point of core-first
    /// propagation: it shrinks what has to be verified, not what a single
    /// propagation costs.
    ///
    /// With `core_first` off the core lists stay empty, the core pass is a
    /// no-op, and the visit order is literally the single-structure one.
    fn propagate(&mut self) -> Option<usize> {
        loop {
            while self.head_core < self.trail.len() {
                let falsified = self.trail[self.head_core] ^ 1;
                self.head_core += 1;
                if let Some(conflict) = self.visit(falsified, true) {
                    return Some(conflict);
                }
            }
            if self.head >= self.trail.len() {
                return None;
            }
            let falsified = self.trail[self.head] ^ 1;
            self.head += 1;
            if let Some(conflict) = self.visit(falsified, false) {
                return Some(conflict);
            }
        }
    }

    /// Visits the clauses watching `falsified` in one of the two watch
    /// structures, propagating or reporting a conflict.
    ///
    /// Textbook two-watched-literal propagation over the arena: the watched
    /// literals of a clause are always the first two of its span, so moving a
    /// watch is a swap inside the span. A watch never moves *between* the two
    /// structures here — only [`BackwardChecker::set_core`] does that, and it
    /// never runs inside this loop.
    fn visit(&mut self, falsified: Code, core: bool) -> Option<usize> {
        let mut index = 0;
        loop {
            let record = {
                let watches = if core {
                    &self.watches_core
                } else {
                    &self.watches
                };
                if index >= watches[falsified].len() {
                    return None;
                }
                watches[falsified][index]
            };
            let start = self.records[record].start;
            let len = self.records[record].len;
            if self.arena[start] == falsified {
                self.arena.swap(start, start + 1);
            }
            let other = self.arena[start];
            if self.assign[other] {
                index += 1;
                continue;
            }
            let mut moved = false;
            for position in start + 2..start + len {
                let candidate = self.arena[position];
                if !self.assign[candidate ^ 1] {
                    self.arena.swap(start + 1, position);
                    let watches = if core {
                        &mut self.watches_core
                    } else {
                        &mut self.watches
                    };
                    watches[falsified].swap_remove(index);
                    watches[candidate].push(record);
                    moved = true;
                    break;
                }
            }
            if moved {
                continue;
            }
            if self.assign[other ^ 1] {
                return Some(record);
            }
            self.assign_lit(other, record);
            index += 1;
        }
    }

    /// Verifies the lemma in `record` — RUP, or failing that RAT on its first
    /// literal — and marks it core.
    ///
    /// The order and the pivot choice are the reference checker's, literally:
    /// `is_rup(active, clause) || is_rat(active, clause)`, with `clause[0]` as
    /// the pivot.
    fn verify(&mut self, record: usize, step: usize) -> bool {
        self.set_core(record);
        let start = self.records[record].start;
        let len = self.records[record].len;
        let pivot = self.records[record].pivot;
        let mut lemma = std::mem::take(&mut self.lemma);
        lemma.clear();
        lemma.extend_from_slice(&self.arena[start..start + len]);
        let rup = self.check_rup(&lemma);
        let verified = rup || self.check_rat(&lemma, pivot);
        if self.trace && verified {
            let justification = if rup {
                let chain = std::mem::take(&mut self.chain);
                let replayed = self.replay_chain(&lemma, &chain);
                self.chain = chain;
                match replayed {
                    Some(hints) => Justification::Rup(hints),
                    None => Justification::ChainFailed,
                }
            } else {
                Justification::Rat
            };
            self.trace_log.push(TraceEntry {
                step,
                record,
                justification,
            });
        }
        self.lemma = lemma;
        verified
    }

    /// Replays `chain` under the LRAT checker's own semantics and returns the
    /// hints to emit, or `None` if the chain cannot be made into a valid one.
    ///
    /// The engine's antecedents are recorded against a trail that already
    /// carries the database's root-level implications; an LRAT checker starts
    /// from nothing and falsifies the lemma up front. The two agree on the
    /// ordinary path, and this pass is what makes them agree on the rest:
    ///
    /// - a hint the lemma's own falsification has already *satisfied*
    ///   contributed nothing to the replay and is dropped (the literal it would
    ///   have forced is true either way, so every later hint still fires);
    /// - a hint that is already a *conflict* ends the chain, because
    ///   [`crate::check_lrat`] insists the conflict is the last hint;
    /// - anything else is a chain that would be rejected, and reporting that is
    ///   better than emitting it.
    ///
    /// It doubles as a self-check on the chains this module emits: no hint list
    /// leaves here without having been replayed against the semantics the
    /// checker will apply to it.
    fn replay_chain(&mut self, lemma: &[Code], chain: &[usize]) -> Option<Vec<usize>> {
        debug_assert!(self.sim_trail.is_empty(), "the replay assignment is clear");
        let mut hints = Vec::new();
        let mut reached_conflict = false;
        // Falsify the lemma. A tautology is refuted by that alone, with no
        // antecedents at all — which is exactly the empty hint chain
        // `check_lrat` accepts for it.
        let mut tautology = false;
        for &lit in lemma {
            if self.sim[lit] {
                tautology = true;
                break;
            }
            if !self.sim[lit ^ 1] {
                self.sim[lit ^ 1] = true;
                self.sim_trail.push(lit ^ 1);
            }
        }
        if !tautology {
            for &record in chain {
                let start = self.records[record].start;
                let len = self.records[record].len;
                let mut satisfied = false;
                let mut unassigned = NO_CLAUSE;
                let mut unassigned_count = 0usize;
                for slot in start..start + len {
                    let lit = self.arena[slot];
                    if self.sim[lit] {
                        satisfied = true;
                        break;
                    }
                    if !self.sim[lit ^ 1] {
                        unassigned = lit;
                        unassigned_count += 1;
                    }
                }
                if satisfied {
                    continue;
                }
                if unassigned_count == 0 {
                    hints.push(record);
                    reached_conflict = true;
                    break;
                }
                // Not unit: the chain cannot be replayed. Unreachable for a
                // cone-derived chain — every antecedent's other literals are
                // forced by antecedents earlier in the chain — and a guard
                // rather than a silent emission if it ever is reached.
                debug_assert!(unassigned_count == 1, "a cone chain hint is not unit");
                if unassigned_count > 1 {
                    break;
                }
                hints.push(record);
                self.sim[unassigned] = true;
                self.sim_trail.push(unassigned);
            }
        }
        for &lit in &self.sim_trail {
            self.sim[lit] = false;
        }
        self.sim_trail.clear();
        if tautology {
            return Some(Vec::new());
        }
        reached_conflict.then_some(hints)
    }

    /// Reverse unit propagation: are `lits` refuted by the live database?
    ///
    /// On success the clauses whose propagation produced the conflict are
    /// marked core, so they will themselves be verified when the walk reaches
    /// them.
    fn check_rup(&mut self, lits: &[Code]) -> bool {
        self.refresh_root();
        if self.trace {
            // A verdict of `true` with no cone — the tautology path — must not
            // inherit the previous lemma's chain.
            self.chain.clear();
        }
        if let Some(record) = self.root_conflict {
            // The database alone is contradictory: everything is RUP over it,
            // and the contradiction is what has to be justified.
            self.mark_cone(record);
            return true;
        }
        let mut verified = None;
        for &lit in lits {
            if self.assign[lit ^ 1] {
                // Already false, which is what assuming the negation wants.
                continue;
            }
            if self.assign[lit] {
                if self.trail_pos[var_of(lit)] >= self.root_len {
                    // A literal assumed false earlier in this very clause: the
                    // clause is a tautology, refuted with no antecedents at all
                    // — exactly what the reference concludes.
                    verified = Some(true);
                } else {
                    // The database forces this literal, so assuming its
                    // negation contradicts the chain that forced it.
                    let reason = self.reason[var_of(lit)];
                    // Every root-level literal was propagated by some clause.
                    // If that ever stopped holding, the cone would be marked
                    // short and a lemma could rest on something never verified,
                    // so this fails loudly rather than under-marking.
                    assert!(
                        reason != NO_CLAUSE,
                        "root-level literal without a reason clause"
                    );
                    self.mark_cone(reason);
                    verified = Some(true);
                }
                break;
            }
            self.assign_lit(lit ^ 1, NO_CLAUSE);
        }
        if verified.is_none() {
            verified = Some(match self.propagate() {
                Some(conflict) => {
                    self.mark_cone(conflict);
                    true
                }
                None => false,
            });
        }
        self.backtrack();
        verified.expect("a verdict is set on every path")
    }

    /// Resolution asymmetric tautology on `pivot`: is every resolvent of `lits`
    /// with a live clause containing the pivot's complement RUP?
    ///
    /// The live clauses containing the complement are found by a scan of the
    /// clause records rather than by occurrence lists, which trades a linear
    /// scan per RAT check for not maintaining an occurrence index over every
    /// addition and deletion. RAT is only reached when RUP has already failed:
    /// never for a proof from this workspace's CDCL core (which is RUP-only),
    /// and once for a broken proof — at the failing step, just before the check
    /// returns. A proof that genuinely leans on RAT for many of its core
    /// lemmas would pay that scan per lemma; occurrence lists are the fix if
    /// such a producer ever appears.
    fn check_rat(&mut self, lits: &[Code], pivot: Code) -> bool {
        if pivot == NO_CLAUSE {
            // The empty clause has no pivot, so it is never RAT.
            return false;
        }
        let complement = pivot ^ 1;
        let mut resolvent = std::mem::take(&mut self.resolvent);
        let mut verified = true;
        for record in 0..self.records.len() {
            if !self.records[record].live {
                continue;
            }
            let start = self.records[record].start;
            let len = self.records[record].len;
            if !self.arena[start..start + len].contains(&complement) {
                continue;
            }
            resolvent.clear();
            resolvent.extend_from_slice(lits);
            for position in start..start + len {
                let lit = self.arena[position];
                if lit != complement {
                    resolvent.push(lit);
                }
            }
            if !self.check_rup(&resolvent) {
                verified = false;
                break;
            }
        }
        self.resolvent = resolvent;
        verified
    }

    /// Marks `conflict` and every clause that propagated a literal it depends
    /// on, transitively.
    ///
    /// The traversal is stamped per call, not gated on the core flag: a clause
    /// already in the core still has to contribute *this* derivation's
    /// antecedents, which are the reasons of the current assignment and have
    /// nothing to do with why it was marked before.
    fn mark_cone(&mut self, conflict: usize) {
        self.generation += 1;
        let generation = self.generation;
        let mut stack = std::mem::take(&mut self.stack);
        stack.clear();
        stack.push(conflict);
        self.cone_order.clear();
        self.cone_conflict = conflict;
        while let Some(record) = stack.pop() {
            self.set_core(record);
            let start = self.records[record].start;
            let len = self.records[record].len;
            for position in start..start + len {
                let lit = self.arena[position];
                let var = var_of(lit);
                if self.seen[var] == generation {
                    continue;
                }
                self.seen[var] = generation;
                let reason = self.reason[var];
                // A stale reason belongs to a variable that is no longer
                // assigned, and an assumed literal has none.
                if reason != NO_CLAUSE && (self.assign[lit] || self.assign[lit ^ 1]) {
                    if self.trace {
                        // One reason per variable and one variable per reason
                        // (a clause that has propagated stays satisfied), so
                        // the trail position is a total order on the
                        // antecedents.
                        self.cone_order.push((self.trail_pos[var], reason));
                    }
                    stack.push(reason);
                }
            }
        }
        self.stack = stack;
        if self.trace {
            self.record_chain();
        }
    }

    /// Turns the antecedents of the last cone walk into a hint chain: the
    /// reasons in propagation order, then the conflict.
    fn record_chain(&mut self) {
        let mut cone_order = std::mem::take(&mut self.cone_order);
        cone_order.sort_unstable();
        self.chain.clear();
        self.chain
            .extend(cone_order.iter().map(|&(_, record)| record));
        self.chain.push(self.cone_conflict);
        self.cone_order = cone_order;
    }
}

/// Removes one occurrence of `record` from a watch list.
fn remove_watch(watch: &mut Vec<usize>, record: usize) {
    if let Some(position) = watch.iter().position(|&entry| entry == record) {
        watch.swap_remove(position);
    }
}

#[cfg(test)]
mod tests {
    use super::{BackwardChecker, Options, Plan, check_drat_backward};
    use crate::{
        CnfClause, CnfFormula, CnfLit, CnfVar, DratError, DratStep, ProofSolveOutcome, check_drat,
        solve_with_drat_proof,
    };

    fn lit(value: i64) -> CnfLit {
        let var = CnfVar::new(usize::try_from(value.unsigned_abs() - 1).unwrap()).unwrap();
        if value < 0 {
            CnfLit::positive(var).negated()
        } else {
            CnfLit::positive(var)
        }
    }

    fn formula(variable_count: usize, clauses: &[&[i64]]) -> CnfFormula {
        let mut f = CnfFormula::new(variable_count);
        for clause in clauses {
            f.add_clause(CnfClause::new(clause.iter().map(|&v| lit(v)).collect()))
                .unwrap();
        }
        f
    }

    /// Runs both checkers, asserts they agree exactly, and returns the verdict.
    /// Every equivalence claim in this module goes through this one helper.
    fn agree(f: &CnfFormula, proof: &[DratStep]) -> Result<bool, DratError> {
        let reference = check_drat(f, proof);
        let backward = check_drat_backward(f, proof);
        assert_eq!(
            backward, reference,
            "backward and reference checkers disagree on {proof:?}"
        );
        backward
    }

    /// The four-clause contradiction over two variables: `()` is not RUP over
    /// it, so a refutation needs a real intermediate lemma.
    fn unsat_2x2() -> CnfFormula {
        formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]])
    }

    /// Pigeonhole: `pigeons` pigeons into `pigeons - 1` holes. Unsatisfiable,
    /// and famously exponential for resolution, so it yields long proofs from a
    /// small input.
    fn pigeonhole(pigeons: usize) -> CnfFormula {
        let holes = pigeons - 1;
        let var = |pigeon: usize, hole: usize| {
            i64::try_from(pigeon * holes + hole).unwrap() + 1 // 1-based
        };
        let mut clauses: Vec<Vec<i64>> = Vec::new();
        for pigeon in 0..pigeons {
            clauses.push((0..holes).map(|hole| var(pigeon, hole)).collect());
        }
        for hole in 0..holes {
            for first in 0..pigeons {
                for second in first + 1..pigeons {
                    clauses.push(vec![-var(first, hole), -var(second, hole)]);
                }
            }
        }
        let refs: Vec<&[i64]> = clauses.iter().map(Vec::as_slice).collect();
        formula(pigeons * holes, &refs)
    }

    /// A Rado/Schur-style colouring instance — the same generator the streaming
    /// proof tests use: is `[1, n]` `colours`-colourable with no monochromatic
    /// solution of `a(x - y) = b z`? `(a, b) = (1, 1)` is the Schur equation.
    fn rado_colouring(n: i64, colours: i64, a: i64, b: i64) -> CnfFormula {
        let var = |i: i64, c: i64| (i - 1) * colours + c;
        let mut clauses: Vec<Vec<i64>> = Vec::new();
        for i in 1..=n {
            clauses.push((1..=colours).map(|c| var(i, c)).collect());
        }
        for x in 1..=n {
            for y in 1..=n {
                for z in 1..=n {
                    if a * (x - y) != b * z {
                        continue;
                    }
                    for c in 1..=colours {
                        let mut lits = vec![-var(x, c), -var(y, c), -var(z, c)];
                        lits.sort_unstable();
                        lits.dedup();
                        clauses.push(lits);
                    }
                }
            }
        }
        let refs: Vec<&[i64]> = clauses.iter().map(Vec::as_slice).collect();
        formula(usize::try_from(n * colours).unwrap(), &refs)
    }

    /// Solves `f` and returns its DRAT proof, insisting the reference checker
    /// accepts it first.
    fn proof_of(f: &CnfFormula) -> Vec<DratStep> {
        match solve_with_drat_proof(f) {
            ProofSolveOutcome::Unsat(proof) => {
                assert_eq!(check_drat(f, &proof), Ok(true), "fixture proof must verify");
                proof
            }
            other => panic!("expected unsat, got {other:?}"),
        }
    }

    /// A deterministic xorshift, so every fuzz here is reproducible.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn below(&mut self, bound: u64) -> usize {
            usize::try_from(self.next() % bound).unwrap()
        }
    }

    /// Random small CNF over `vars` variables.
    fn random_formula(rng: &mut Rng, vars: usize, clause_count: usize, width: usize) -> CnfFormula {
        let mut f = CnfFormula::new(vars);
        let bound = u64::try_from(vars).unwrap();
        for _ in 0..clause_count {
            let mut lits = Vec::new();
            for _ in 0..width {
                let value = i64::try_from(rng.next() % bound).unwrap() + 1;
                lits.push(lit(if rng.next() & 1 == 0 { value } else { -value }));
            }
            f.add_clause(CnfClause::new(lits)).unwrap();
        }
        f
    }

    // ----------------------------------------------------------------------
    // Equivalence with the reference checker
    // ----------------------------------------------------------------------

    /// A named formula, a proof for it, and the verdict both checkers owe.
    type Case = (
        &'static str,
        CnfFormula,
        Vec<DratStep>,
        Result<bool, DratError>,
    );

    /// Runs every case through [`agree`], which is what pins the equivalence.
    fn run_cases(cases: Vec<Case>) {
        assert!(!cases.is_empty());
        for (name, f, proof, expected) in cases {
            assert_eq!(agree(&f, &proof), expected, "case `{name}`");
        }
    }

    #[test]
    fn agrees_with_the_reference_on_the_hand_written_battery() {
        run_cases(vec![
            (
                "unit contradiction",
                formula(1, &[&[1], &[-1]]),
                vec![DratStep::Add(vec![])],
                Ok(true),
            ),
            (
                "rup chain",
                unsat_2x2(),
                vec![DratStep::Add(vec![lit(1)]), DratStep::Add(vec![])],
                Ok(true),
            ),
            (
                "rup chain with a deletion in the middle",
                unsat_2x2(),
                vec![
                    DratStep::Add(vec![lit(1)]),
                    DratStep::Delete(vec![lit(1), lit(2)]),
                    DratStep::Add(vec![]),
                ],
                Ok(true),
            ),
            (
                "deletion of a clause that is not present is ignored",
                unsat_2x2(),
                vec![
                    DratStep::Delete(vec![lit(1), lit(1), lit(1)]),
                    DratStep::Add(vec![lit(1)]),
                    DratStep::Add(vec![]),
                ],
                Ok(true),
            ),
            (
                "the formula already contains the empty clause",
                formula(1, &[&[]]),
                vec![DratStep::Add(vec![])],
                Ok(true),
            ),
            (
                "verified proof without an empty clause",
                formula(2, &[&[1, 2]]),
                vec![DratStep::Add(vec![lit(1)])],
                Ok(false),
            ),
            (
                "empty proof for an unsat formula",
                unsat_2x2(),
                vec![],
                Ok(false),
            ),
            (
                "unjustified empty clause",
                formula(1, &[&[1]]),
                vec![DratStep::Add(vec![])],
                Err(DratError::StepNotVerified { step: 0 }),
            ),
        ]);
    }

    /// The corners: clause shapes and proof shapes that a hand-rolled
    /// propagator is most likely to get subtly different from the reference.
    #[test]
    fn agrees_with_the_reference_on_degenerate_clause_shapes() {
        run_cases(vec![
            (
                "a tautological lemma needs no antecedents",
                unsat_2x2(),
                vec![
                    DratStep::Add(vec![lit(1), lit(-1)]),
                    DratStep::Add(vec![lit(1)]),
                    DratStep::Add(vec![]),
                ],
                Ok(true),
            ),
            (
                "a lemma whose literal the database already forces",
                formula(2, &[&[1], &[-1, 2], &[-2]]),
                vec![DratStep::Add(vec![lit(-1)]), DratStep::Add(vec![])],
                Ok(true),
            ),
            (
                // A proof may mention variables the formula never declares
                // (extended resolution does exactly that); the checker sizes
                // itself from both.
                "a lemma over a variable the formula never mentions",
                unsat_2x2(),
                vec![
                    DratStep::Add(vec![lit(3), lit(1)]),
                    DratStep::Add(vec![lit(1)]),
                    DratStep::Add(vec![]),
                ],
                Ok(true),
            ),
            (
                // Everything past the first empty clause is irrelevant: the
                // refutation is already complete there.
                "the empty clause added, deleted, and re-derived",
                unsat_2x2(),
                vec![
                    DratStep::Add(vec![lit(1)]),
                    DratStep::Add(vec![]),
                    DratStep::Delete(vec![]),
                    DratStep::Add(vec![]),
                ],
                Ok(true),
            ),
            (
                // Both checkers count literal *occurrences*, so `(1 1)` is a
                // two-literal clause that never propagates: it is RUP itself,
                // but it does not force `1`, and the empty clause after it is
                // therefore unjustified. Pinned because it is the sharpest
                // place the engine could have drifted from the reference —
                // a distinct-variable count here would accept a proof the
                // reference rejects.
                "duplicate literals in a lemma",
                unsat_2x2(),
                vec![DratStep::Add(vec![lit(1), lit(1)]), DratStep::Add(vec![])],
                Err(DratError::StepNotVerified { step: 1 }),
            ),
            (
                // The same clause reached through the database instead: with
                // `(1 1)` deleted, `(1)` is available and the empty clause goes
                // through.
                "duplicate literals, then the real unit",
                unsat_2x2(),
                vec![
                    DratStep::Add(vec![lit(1), lit(1)]),
                    DratStep::Add(vec![lit(1)]),
                    DratStep::Add(vec![]),
                ],
                Ok(true),
            ),
        ]);
    }

    /// Deletions are where a backward checker earns its keep and where it can
    /// most easily be wrong: walking backwards has to *undo* them, restoring
    /// clauses that were not in the database when the empty clause was reached.
    ///
    /// This proof is built so the backward walk hits every one of those paths in
    /// order: a formula clause deleted and restored, a **unit** lemma deleted
    /// and restored (which forces the shared root trail to be rebuilt), a
    /// database that is contradictory by unit propagation alone at one point in
    /// the walk, and a lemma whose justification is only available once the
    /// deleted formula clause is back.
    #[test]
    fn agrees_with_the_reference_when_deletions_must_be_undone() {
        let f = unsat_2x2();
        let proof = vec![
            DratStep::Add(vec![lit(1)]),
            DratStep::Delete(vec![lit(1), lit(2)]),
            DratStep::Add(vec![lit(2)]),
            DratStep::Delete(vec![lit(1)]),
            DratStep::Add(vec![]),
        ];
        assert_eq!(agree(&f, &proof), Ok(true));
        // Both halves matter: without the unit lemma the middle step is not
        // justified, and the reference agrees about that too.
        let without_unit = vec![
            DratStep::Delete(vec![lit(1), lit(2)]),
            DratStep::Add(vec![lit(2)]),
            DratStep::Add(vec![]),
        ];
        assert_eq!(
            agree(&f, &without_unit),
            Err(DratError::StepNotVerified { step: 1 })
        );
    }

    #[test]
    fn agrees_with_the_reference_on_a_blocked_clause_rat_proof() {
        // Over [(1 2)] the unit (1) is RAT on pivot 1 (nothing contains -1) but
        // is not RUP: the only route to accepting this proof is the RAT check.
        let f = formula(2, &[&[1, 2], &[-1, 2], &[-2]]);
        let proof = vec![
            DratStep::Add(vec![lit(2), lit(-1)]),
            DratStep::Add(vec![lit(2)]),
            DratStep::Add(vec![]),
        ];
        assert_eq!(agree(&f, &proof), Ok(true));

        // A genuinely blocked clause: over [(1 2)] alone, (1) is RAT-only, and
        // adding it does not make the formula unsat.
        let satisfiable = formula(2, &[&[1, 2]]);
        assert_eq!(
            agree(&satisfiable, &[DratStep::Add(vec![lit(1)])]),
            Ok(false)
        );
    }

    #[test]
    fn agrees_with_the_reference_on_solver_proofs_and_their_prefixes() {
        let instances = [
            ("php(6)", pigeonhole(6)),
            ("schur n=14 k=3", rado_colouring(14, 3, 1, 1)),
            ("schur n=15 k=3", rado_colouring(15, 3, 1, 1)),
        ];
        let mut prefixes = 0u32;
        let mut confirmed = 0u32;
        for (name, f) in instances {
            let proof = proof_of(&f);
            assert!(proof.len() > 10, "{name}: expected a proof with substance");
            assert_eq!(agree(&f, &proof), Ok(true), "{name}");
            confirmed += 1;
            // Every prefix of a valid proof is itself a proof the reference
            // accepts, so each truncation point is an independent equivalence
            // assertion. The sample is spread over the whole proof rather than
            // exhaustive: the reference checker is quadratic, so sweeping every
            // prefix of a few-thousand-step proof is minutes of test time for
            // no extra coverage.
            let stride = 1 + proof.len() / 40;
            for cut in (0..proof.len()).step_by(stride) {
                assert_eq!(
                    agree(&f, &proof[..cut]),
                    Ok(false),
                    "{name}: prefix of length {cut} establishes nothing"
                );
                prefixes += 1;
            }
        }
        assert_eq!(confirmed, 3);
        assert!(
            prefixes > 60,
            "expected a broad prefix sweep, got {prefixes}"
        );
    }

    /// The engine's per-lemma verdict — RUP-or-RAT against a live database —
    /// must equal the reference's on every clause, not merely on whole proofs.
    /// A one-step proof over `f` is `Ok(_)` exactly when the reference accepts
    /// the clause, which makes the comparison direct.
    #[test]
    fn per_lemma_verdicts_match_the_reference_on_random_clauses() {
        let mut rng = Rng(0x51ed_9e1a_77c3_0e11);
        let mut accepted = 0u32;
        let mut rejected = 0u32;
        for _ in 0..3000 {
            let vars = 2 + rng.below(5);
            let clause_count = 2 + rng.below(8);
            let width = 1 + rng.below(3);
            let f = random_formula(&mut rng, vars, clause_count, width);
            let mut clause = Vec::new();
            for _ in 0..rng.below(4) {
                let value = i64::try_from(rng.next() % u64::try_from(vars).unwrap()).unwrap() + 1;
                clause.push(lit(if rng.next() & 1 == 0 { value } else { -value }));
            }
            let steps = [DratStep::Add(clause.clone())];
            let expected = check_drat(&f, &steps).is_ok();

            let plan = Plan::build(&f, &steps).unwrap();
            let mut checker = BackwardChecker::new(plan, Options::CHECK);
            for record in 0..checker.records.len() {
                checker.set_membership(record, 0);
            }
            let record = checker.added_by_step[0];
            let actual = checker.verify(record, 0);
            assert_eq!(
                actual, expected,
                "lemma {clause:?} over {f:?}: engine and reference disagree"
            );
            if expected {
                accepted += 1;
            } else {
                rejected += 1;
            }
        }
        assert!(accepted > 100, "expected accepted lemmas, got {accepted}");
        assert!(rejected > 100, "expected rejected lemmas, got {rejected}");
    }

    // ----------------------------------------------------------------------
    // Soundness-negative cases
    // ----------------------------------------------------------------------

    #[test]
    fn rejects_a_truncated_proof() {
        let f = unsat_2x2();
        let full = vec![DratStep::Add(vec![lit(1)]), DratStep::Add(vec![])];
        assert_eq!(agree(&f, &full), Ok(true));
        // Dropping the empty clause leaves nothing established.
        assert_eq!(agree(&f, &full[..1]), Ok(false));
        assert_eq!(agree(&f, &full[..0]), Ok(false));

        // The same on a real solver proof: every truncation that keeps the
        // empty clause out must be `Ok(false)`, never a refutation.
        let f = pigeonhole(6);
        let proof = proof_of(&f);
        let last = proof.len() - 1;
        assert_eq!(agree(&f, &proof[..last]), Ok(false));
    }

    #[test]
    fn rejects_a_proof_with_a_step_deleted_from_the_middle() {
        // Removing the lemma the empty clause rests on leaves it unjustified.
        let f = unsat_2x2();
        let gutted = vec![DratStep::Add(vec![])];
        assert_eq!(
            agree(&f, &gutted),
            Err(DratError::StepNotVerified { step: 0 })
        );

        // And on a real proof: dropping the step immediately before the empty
        // clause breaks the refutation the empty clause depends on.
        let f = rado_colouring(14, 3, 1, 1);
        let proof = proof_of(&f);
        let mut mutilated = proof.clone();
        let last_lemma = mutilated.len() - 2;
        mutilated.remove(last_lemma);
        assert_ne!(
            check_drat_backward(&f, &mutilated),
            Ok(true),
            "a refutation missing its penultimate lemma must not verify"
        );
    }

    #[test]
    fn rejects_a_proof_with_an_edited_literal() {
        let f = unsat_2x2();
        // Weakening the learned clause (1) to (1 v 2) — still RUP — leaves the
        // empty clause unjustified.
        let edited = vec![DratStep::Add(vec![lit(1), lit(2)]), DratStep::Add(vec![])];
        assert_eq!(
            agree(&f, &edited),
            Err(DratError::StepNotVerified { step: 1 })
        );

        // On a real proof: flip one literal of one lemma, everywhere in turn.
        // Most flips break the refutation; none may turn it into a certificate
        // for a formula it does not refute (which
        // `never_certifies_a_satisfiable_formula` covers), and every flip the
        // reference still accepts must be accepted here too.
        let f = rado_colouring(14, 3, 1, 1);
        let proof = proof_of(&f);
        let mut broken = 0u32;
        let mut edits = 0u32;
        for index in (0..proof.len()).step_by(1 + proof.len() / 60) {
            let DratStep::Add(lits) = &proof[index] else {
                continue;
            };
            if lits.is_empty() {
                continue;
            }
            let mut edited = proof.clone();
            if let DratStep::Add(lits) = &mut edited[index] {
                lits[0] = lits[0].negated();
            }
            edits += 1;
            let backward = check_drat_backward(&f, &edited);
            if check_drat(&f, &edited) == Ok(true) {
                assert_eq!(
                    backward,
                    Ok(true),
                    "step {index}: an edit the reference still accepts must be accepted here"
                );
            }
            if backward != Ok(true) {
                broken += 1;
            }
        }
        assert!(edits > 20, "expected many editable steps, got {edits}");
        assert!(
            broken * 2 > edits,
            "expected most single-literal edits to break the proof, {broken} of {edits}"
        );
    }

    #[test]
    fn rejects_an_empty_proof_for_an_unsat_formula() {
        assert_eq!(agree(&unsat_2x2(), &[]), Ok(false));
        assert_eq!(agree(&pigeonhole(6), &[]), Ok(false));
    }

    #[test]
    fn rejects_an_unjustified_empty_clause() {
        assert_eq!(
            agree(&formula(1, &[&[1]]), &[DratStep::Add(vec![])]),
            Err(DratError::StepNotVerified { step: 0 })
        );
        // A satisfiable formula with a long, valid-looking preamble.
        let f = formula(3, &[&[1, 2], &[-1, 3]]);
        let proof = vec![
            DratStep::Add(vec![lit(1), lit(2), lit(3)]),
            DratStep::Add(vec![]),
        ];
        assert_eq!(
            agree(&f, &proof),
            Err(DratError::StepNotVerified { step: 1 })
        );
    }

    #[test]
    fn rejects_a_proof_valid_for_a_different_formula() {
        let source = unsat_2x2();
        let proof = proof_of(&source);
        assert_eq!(agree(&source, &proof), Ok(true));

        // Same variables, satisfiable formula: the proof's lemmas are no longer
        // entailed, and the refutation must not go through.
        for other in [
            formula(2, &[&[1, 2]]),
            formula(2, &[&[1, 2], &[1, -2], &[-1, 2]]),
            formula(2, &[]),
        ] {
            assert_ne!(
                check_drat_backward(&other, &proof),
                Ok(true),
                "a proof of a different formula must not certify {other:?}"
            );
        }

        // A proof from a *larger* instance, replayed against a satisfiable one.
        let big = proof_of(&pigeonhole(6));
        let satisfiable = formula(30, &[&[1, 2], &[-1, 3]]);
        assert_ne!(check_drat_backward(&satisfiable, &big), Ok(true));
    }

    /// The property that actually matters: no proof, however constructed,
    /// makes the backward checker certify a satisfiable formula. A proof
    /// borrowed from a genuinely unsatisfiable instance and randomly generated
    /// proof text — both ending in the empty clause — go through the same
    /// assertion. (Mutations of a *valid* proof are covered by
    /// [`mutated_proofs_are_rejected`]; on an unsatisfiable formula acceptance
    /// is sound whatever the proof, which is why the soundness question can
    /// only be asked here.)
    #[test]
    fn never_certifies_a_satisfiable_formula() {
        let mut rng = Rng(0x2f81_44b6_c0de_1234);
        let borrowed = proof_of(&unsat_2x2());
        let mut satisfiable_cases = 0u32;
        for _ in 0..400 {
            let vars = 3 + rng.below(4);
            let clause_count = 3 + rng.below(10);
            let width = 1 + rng.below(3);
            let f = random_formula(&mut rng, vars, clause_count, width);
            if !matches!(solve_with_drat_proof(&f), ProofSolveOutcome::Sat(_)) {
                continue;
            }
            satisfiable_cases += 1;

            // (a) A borrowed proof.
            assert_ne!(check_drat_backward(&f, &borrowed), Ok(true));

            // (b) Random junk ending in the empty clause.
            let mut junk = Vec::new();
            for _ in 0..=rng.below(6) {
                let mut lits = Vec::new();
                for _ in 0..rng.below(3) {
                    let value =
                        i64::try_from(rng.next() % u64::try_from(vars).unwrap()).unwrap() + 1;
                    lits.push(lit(if rng.next() & 1 == 0 { value } else { -value }));
                }
                junk.push(if rng.next().is_multiple_of(5) {
                    DratStep::Delete(lits)
                } else {
                    DratStep::Add(lits)
                });
            }
            junk.push(DratStep::Add(vec![]));
            assert_ne!(
                check_drat_backward(&f, &junk),
                Ok(true),
                "junk proof certified satisfiable formula {f:?}"
            );
        }
        assert!(
            satisfiable_cases > 50,
            "expected many satisfiable instances, got {satisfiable_cases}"
        );
    }

    /// Mutating a real proof must break it far more often than not, and must
    /// never turn it into a certificate for something else. Combined with
    /// [`never_certifies_a_satisfiable_formula`], this is the pair that would
    /// catch a checker that had quietly stopped checking.
    #[test]
    fn mutated_proofs_are_rejected() {
        let f = rado_colouring(14, 3, 1, 1);
        let proof = proof_of(&f);
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        let mut rejected = 0u32;
        let mut tried = 0u32;
        for _ in 0..120 {
            let mut mutated = proof.clone();
            let at = rng.below(u64::try_from(mutated.len()).unwrap());
            match rng.next() % 3 {
                0 => {
                    mutated.remove(at);
                }
                1 => {
                    if let DratStep::Add(lits) = &mut mutated[at]
                        && !lits.is_empty()
                    {
                        let which = rng.below(u64::try_from(lits.len()).unwrap());
                        lits[which] = lits[which].negated();
                    } else {
                        continue;
                    }
                }
                _ => {
                    if let DratStep::Add(lits) = &mut mutated[at]
                        && !lits.is_empty()
                    {
                        lits.pop();
                    } else {
                        continue;
                    }
                }
            }
            tried += 1;
            if check_drat_backward(&f, &mutated) != Ok(true) {
                rejected += 1;
            }
        }
        assert!(tried > 60, "expected most mutations to apply, got {tried}");
        assert!(
            rejected * 2 > tried,
            "expected most mutations to break the proof, {rejected} of {tried}"
        );
    }

    // ----------------------------------------------------------------------
    // Differential fuzz against the reference checker
    // ----------------------------------------------------------------------

    /// Random formulas, solved by the in-tree proof-producing core, checked by
    /// both checkers. The counters are asserted so the fuzz cannot silently
    /// degenerate into "no instances ran" or "only trivial instances ran".
    #[test]
    fn differential_fuzz_against_the_reference_checker() {
        let mut rng = Rng(0x0bad_c0de_dead_beef);
        let mut unsat = 0u32;
        let mut sat = 0u32;
        let mut nontrivial = 0u32;
        for _ in 0..900 {
            // Random 3-CNF near the satisfiability threshold, so the batch is
            // an even mix of sat and unsat and the unsat proofs are not one
            // step long.
            let vars = 8 + rng.below(8);
            let clause_count = vars * 4 + rng.below(8);
            let f = random_formula(&mut rng, vars, clause_count, 3);
            match solve_with_drat_proof(&f) {
                ProofSolveOutcome::Unsat(proof) => {
                    assert_eq!(agree(&f, &proof), Ok(true));
                    if proof.len() > 5 {
                        nontrivial += 1;
                    }
                    // Prefixes of the same proof: the reference accepts them
                    // all, so the two checkers must agree on every one.
                    for cut in (0..proof.len()).step_by(1 + proof.len() / 12) {
                        assert_eq!(agree(&f, &proof[..cut]), Ok(false));
                    }
                    unsat += 1;
                }
                ProofSolveOutcome::Sat(model) => {
                    assert!(model.satisfies(&f).unwrap());
                    sat += 1;
                }
                other => panic!("unexpected outcome {other:?}"),
            }
        }
        assert!(unsat > 100, "expected many unsat cases, got {unsat}");
        assert!(sat > 100, "expected many sat cases, got {sat}");
        assert!(
            nontrivial > 30,
            "expected proofs with several steps, got {nontrivial}"
        );
    }

    /// Random *proof-shaped* inputs over unsat formulas: the two checkers must
    /// agree whenever the reference accepts, which is the equivalence this
    /// module claims. Where they are allowed to differ is pinned separately by
    /// [`accepts_dead_weight_the_reference_rejects`].
    #[test]
    fn differential_fuzz_on_perturbed_proofs() {
        let mut rng = Rng(0x1357_9bdf_2468_ace0);
        let f = unsat_2x2();
        let mut both_accept = 0u32;
        let mut reference_rejects = 0u32;
        for _ in 0..2000 {
            let mut proof = Vec::new();
            for _ in 0..=rng.below(5) {
                let mut lits = Vec::new();
                for _ in 0..rng.below(3) {
                    let value = i64::try_from(rng.next() % 2).unwrap() + 1;
                    lits.push(lit(if rng.next() & 1 == 0 { value } else { -value }));
                }
                proof.push(if rng.next().is_multiple_of(4) {
                    DratStep::Delete(lits)
                } else {
                    DratStep::Add(lits)
                });
            }
            let reference = check_drat(&f, &proof);
            let backward = check_drat_backward(&f, &proof);
            if reference.is_ok() {
                assert_eq!(
                    backward, reference,
                    "on a proof the reference accepts the two must agree: {proof:?}"
                );
                if reference == Ok(true) {
                    both_accept += 1;
                }
            } else {
                reference_rejects += 1;
                // Where the reference rejects, the backward checker is allowed
                // to accept dead weight — but only ever with a verdict from the
                // same vocabulary. A `Parse` error here would mean the engine
                // choked on an input the reference merely disliked.
                assert!(
                    matches!(backward, Ok(_) | Err(DratError::StepNotVerified { .. })),
                    "unexpected verdict {backward:?} on {proof:?}"
                );
            }
        }
        assert!(
            both_accept > 50,
            "expected many accepted refutations, got {both_accept}"
        );
        assert!(
            reference_rejects > 50,
            "expected many rejected proofs, got {reference_rejects}"
        );
    }

    // ----------------------------------------------------------------------
    // The one documented divergence
    // ----------------------------------------------------------------------

    /// Backward checking skips lemmas the refutation does not depend on, so a
    /// proof that contains a valid refutation *plus* an unjustified line is
    /// accepted here and rejected by the reference. This is the technique
    /// working as designed — and it is sound, because the accepted refutation
    /// never propagated through the skipped line.
    ///
    /// Pinned as a test because it is the only place the two checkers part
    /// company, and a silent change to it would be a semantic change.
    #[test]
    fn accepts_dead_weight_the_reference_rejects() {
        // The 2x2 contradiction over variables 1 and 2, plus an unrelated
        // implication over 3 and 4 that makes `(3)` neither RUP (nothing
        // propagates) nor RAT (the resolvent `(3 4)` is not RUP either).
        let f = formula(4, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2], &[-3, 4]]);
        let proof = vec![
            // A lemma nothing entails, and nothing later uses.
            DratStep::Add(vec![lit(3)]),
            DratStep::Add(vec![lit(1)]),
            DratStep::Add(vec![]),
        ];
        assert_eq!(
            check_drat(&f, &proof),
            Err(DratError::StepNotVerified { step: 0 }),
            "the reference verifies every line"
        );
        assert_eq!(
            check_drat_backward(&f, &proof),
            Ok(true),
            "the refutation is (1) then (), which is valid on its own"
        );
        // …and the refutation really is valid without the dead line.
        assert_eq!(agree(&f, &proof[1..]), Ok(true));
    }

    // ----------------------------------------------------------------------
    // Determinism
    // ----------------------------------------------------------------------

    #[test]
    fn repeated_runs_give_the_same_verdict() {
        let f = pigeonhole(7);
        let proof = proof_of(&f);
        let first = check_drat_backward(&f, &proof);
        for _ in 0..4 {
            assert_eq!(check_drat_backward(&f, &proof), first);
        }
        assert_eq!(first, Ok(true));
    }
}
