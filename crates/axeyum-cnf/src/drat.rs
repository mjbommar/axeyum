//! An independent DRAT UNSAT-proof checker (ADR-0011).
//!
//! This is the trusted component that discharges `unsat`: given a CNF formula
//! and a DRAT proof (clause additions and deletions), it verifies each added
//! clause is RUP (reverse unit propagation) or RAT (resolution asymmetric
//! tautology) with respect to the current clauses, and that the empty clause is
//! derived. It depends on nothing but the formula and proof — a small, total,
//! auditable checker, independent of whatever solver produced the proof.
//!
//! # Streaming (ADR-0380)
//!
//! A proof does not have to exist as a `Vec<DratStep>` at any point. [`DratSink`]
//! is the *emission* side — a producer hands it one step at a time, and
//! [`TextProofSink`] writes those steps straight to any [`std::io::Write`] in the
//! same textual format [`write_drat`] produces (byte for byte: both go through
//! one formatting routine). [`check_drat_streaming`] is the *consumption* side —
//! it verifies a proof presented as an iterator of steps, with memory bounded by
//! the **active clause database** rather than by the proof length, and
//! [`DratTextReader`] produces that iterator from any [`std::io::BufRead`].
//! [`VecProofSink`] keeps the in-RAM behavior for callers that want the whole
//! proof as a value.

use std::collections::HashMap;
use std::io::{self, BufRead, Write};

use crate::{CnfFormula, CnfLit, CnfVar};

/// One step of a DRAT proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DratStep {
    /// Add a clause; it must be RUP or RAT w.r.t. the current clause set.
    Add(Vec<CnfLit>),
    /// Delete a clause previously present in the clause set.
    Delete(Vec<CnfLit>),
}

/// Error from DRAT checking or parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DratError {
    /// An added clause is neither RUP nor RAT — the proof is invalid.
    StepNotVerified {
        /// Zero-based index of the failing proof step.
        step: usize,
    },
    /// The proof text could not be parsed.
    Parse(String),
}

impl core::fmt::Display for DratError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DratError::StepNotVerified { step } => {
                write!(f, "DRAT step {step} is neither RUP nor RAT")
            }
            DratError::Parse(what) => write!(f, "DRAT parse error: {what}"),
        }
    }
}

impl core::error::Error for DratError {}

/// Verifies `proof` against `formula`.
///
/// Returns `Ok(true)` when every step verifies and the empty clause is derived
/// (UNSAT confirmed), `Ok(false)` when every step verifies but the empty clause
/// is never derived (UNSAT not established), and `Err` when a step fails to
/// verify.
///
/// # Errors
///
/// Returns [`DratError::StepNotVerified`] for an unjustified clause addition.
pub fn check_drat(formula: &CnfFormula, proof: &[DratStep]) -> Result<bool, DratError> {
    // The whole-proof entry is the streaming entry fed from a slice: forward
    // checking never looks backward, so there is exactly one algorithm here.
    check_drat_streaming(formula, proof.iter().cloned().map(Ok))
}

/// Verifies a proof presented as a *stream* of steps against `formula`
/// (ADR-0380).
///
/// Same verdict discipline as [`check_drat`] — `Ok(true)` when every step
/// verifies and the empty clause is derived (UNSAT confirmed), `Ok(false)` when
/// every step verifies but the empty clause is never derived (UNSAT not
/// established), `Err` when a step fails to verify — but the proof is consumed
/// one step at a time and never accumulated. Peak memory is bounded by the
/// **active clause database** (which deletion steps shrink), not by the number of
/// proof steps, so a search-scale certificate that cannot fit in RAM as a
/// `Vec<DratStep>` can still be checked.
///
/// This is sound because DRAT checking is *forward*: step `i` is justified
/// against the clause set accumulated from the formula and steps `0..i`, so no
/// step is ever revisited. A step that yields `Err` from the producer (a parse or
/// read failure in [`DratTextReader`], say) aborts the check with that error —
/// an unreadable proof is never treated as a verified one.
///
/// # Errors
///
/// Returns [`DratError::StepNotVerified`] for an unjustified clause addition, or
/// whatever [`DratError`] the step producer yields.
pub fn check_drat_streaming(
    formula: &CnfFormula,
    steps: impl Iterator<Item = Result<DratStep, DratError>>,
) -> Result<bool, DratError> {
    let mut checker = ForwardChecker::new(formula);
    for (index, step) in steps.enumerate() {
        checker.apply(index, step?)?;
    }
    Ok(checker.derived_empty)
}

/// Forward DRAT checking state: the currently active clause set plus whether the
/// empty clause has been derived. Deletions shrink `active`, so the footprint
/// tracks the solver's live clause database rather than the proof length — the
/// property that makes [`check_drat_streaming`] bounded-memory.
struct ForwardChecker {
    active: Vec<Vec<CnfLit>>,
    derived_empty: bool,
}

impl ForwardChecker {
    fn new(formula: &CnfFormula) -> Self {
        Self {
            active: formula
                .clauses()
                .iter()
                .map(|clause| clause.lits().to_vec())
                .collect(),
            derived_empty: false,
        }
    }

    /// Applies one step, `index` being its zero-based position in the proof (the
    /// index reported by [`DratError::StepNotVerified`]).
    fn apply(&mut self, index: usize, step: DratStep) -> Result<(), DratError> {
        match step {
            DratStep::Delete(clause) => {
                if let Some(position) = position_of(&self.active, &clause) {
                    self.active.swap_remove(position);
                }
            }
            DratStep::Add(clause) => {
                if !is_rup(&self.active, &clause) && !is_rat(&self.active, &clause) {
                    return Err(DratError::StepNotVerified { step: index });
                }
                if clause.is_empty() {
                    self.derived_empty = true;
                }
                self.active.push(clause);
            }
        }
        Ok(())
    }
}

/// Serializes a DRAT proof to the standard textual format: each step is a
/// `0`-terminated line of DIMACS integer literals, deletions prefixed with `d`.
/// The output is accepted by [`parse_drat`] and by external checkers such as
/// `drat-trim`, so an `unsat` proof can be exported as a checkable artifact.
pub fn write_drat(proof: &[DratStep]) -> String {
    let mut out = String::new();
    for step in proof {
        match step {
            DratStep::Add(lits) => push_step_text(&mut out, false, lits),
            DratStep::Delete(lits) => push_step_text(&mut out, true, lits),
        }
    }
    out
}

/// Appends one step to `out` in the standard textual DRAT format: the literals as
/// DIMACS integers, each followed by a space, then a `0` terminator and a
/// newline; deletions are prefixed with `d `.
///
/// This is the single formatting routine behind both [`write_drat`] and
/// [`TextProofSink`], so a streamed proof is byte-identical to the serialization
/// of the equivalent `Vec<DratStep>` by construction, not by two implementations
/// agreeing.
fn push_step_text(out: &mut String, delete: bool, lits: &[CnfLit]) {
    if delete {
        out.push_str("d ");
    }
    for lit in lits {
        out.push_str(&lit.dimacs().to_string());
        out.push(' ');
    }
    out.push_str("0\n");
}

/// Error from emitting a proof step to a [`DratSink`].
///
/// Small and value-like on purpose: it is carried in solver outcomes, which are
/// `Clone + PartialEq + Eq`, so it stores an [`std::io::ErrorKind`] plus the
/// message text rather than an [`std::io::Error`] (which is neither). The kind is
/// preserved so a caller can distinguish, say, a full disk from a broken pipe.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofSinkError {
    kind: io::ErrorKind,
    message: String,
}

impl ProofSinkError {
    /// Creates an error with an explicit kind and message. Sinks that are not
    /// I/O-backed should use [`std::io::ErrorKind::Other`].
    pub fn new(kind: io::ErrorKind, message: impl Into<String>) -> Self {
        Self {
            kind,
            message: message.into(),
        }
    }

    /// The underlying I/O error kind.
    pub fn kind(&self) -> io::ErrorKind {
        self.kind
    }

    /// The human-readable failure message.
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl From<io::Error> for ProofSinkError {
    fn from(error: io::Error) -> Self {
        Self {
            kind: error.kind(),
            message: error.to_string(),
        }
    }
}

impl core::fmt::Display for ProofSinkError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "DRAT proof sink failed: {}", self.message)
    }
}

impl core::error::Error for ProofSinkError {}

/// The emission side of a DRAT proof (ADR-0380): a proof producer reports each
/// derived clause here instead of appending it to a growing `Vec`.
///
/// Implementations are pure *output*. A producer's search trajectory must not
/// depend on which sink it was given, so the same formula yields the same step
/// sequence through [`VecProofSink`] and [`TextProofSink`] alike — determinism is
/// a public API promise of this workspace, and the sink is the one place where a
/// proof leaves the producer.
///
/// A sink may fail (a full disk, a closed pipe). Failure is reported, never
/// panicked: the producer surfaces it as an *undecided* outcome, because a proof
/// that could not be written is not a proof.
pub trait DratSink {
    /// Records the addition of `lits` — a clause the producer claims is RUP/RAT
    /// w.r.t. the current clause set.
    ///
    /// # Errors
    ///
    /// Returns [`ProofSinkError`] when the step cannot be recorded.
    fn add_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError>;

    /// Records the deletion of `lits` from the clause set.
    ///
    /// # Errors
    ///
    /// Returns [`ProofSinkError`] when the step cannot be recorded.
    fn delete_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError>;
}

/// A [`DratSink`] that collects the whole proof in memory as `Vec<DratStep>` —
/// exactly the representation the non-streaming entry points return.
///
/// Infallible: neither method can fail. Use it when the proof is small enough to
/// hold (the checked-`unsat` path for query-sized instances) and
/// [`TextProofSink`] when it is not.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct VecProofSink {
    steps: Vec<DratStep>,
}

impl VecProofSink {
    /// Creates an empty sink.
    pub fn new() -> Self {
        Self::default()
    }

    /// The steps recorded so far.
    pub fn steps(&self) -> &[DratStep] {
        &self.steps
    }

    /// Consumes the sink and returns the recorded proof.
    pub fn into_steps(self) -> Vec<DratStep> {
        self.steps
    }
}

impl DratSink for VecProofSink {
    fn add_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        self.steps.push(DratStep::Add(lits.to_vec()));
        Ok(())
    }

    fn delete_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        self.steps.push(DratStep::Delete(lits.to_vec()));
        Ok(())
    }
}

/// Size of [`TextProofSink`]'s write buffer. The peak in-RAM proof footprint of
/// a streamed proof is this constant plus one formatted step, whatever the
/// proof's length.
const TEXT_SINK_BUFFER_BYTES: usize = 64 * 1024;

/// A [`DratSink`] that writes the standard textual DRAT format straight to a
/// writer (ADR-0380) — the streaming counterpart of [`write_drat`].
///
/// The caller owns and chooses the writer (a file, a pipe, a `Vec<u8>`); this
/// sink adds its own buffering, so passing an unbuffered [`std::fs::File`] does
/// not cost a syscall per proof step. Output is byte-identical to
/// `write_drat(&equivalent_vec_proof)` because both go through the one private
/// step-formatting routine — not because two implementations agree.
///
/// Because the sink buffers, a writer failure usually surfaces at a later step
/// (when the buffer drains) rather than at the step that filled it. Buffered
/// bytes are flushed when the wrapped [`std::io::BufWriter`] is dropped, where a
/// write error is unobservable; call [`TextProofSink::flush`] or
/// [`TextProofSink::finish`] to surface a final write failure instead of losing
/// it. `finish` also returns the writer.
#[derive(Debug)]
pub struct TextProofSink<W: Write> {
    writer: io::BufWriter<W>,
    /// Reused formatting scratch for the step being emitted, so a proof of any
    /// length allocates once.
    scratch: String,
}

impl<W: Write> TextProofSink<W> {
    /// Wraps `writer` as a proof sink.
    pub fn new(writer: W) -> Self {
        Self {
            writer: io::BufWriter::with_capacity(TEXT_SINK_BUFFER_BYTES, writer),
            scratch: String::new(),
        }
    }

    /// Writes any buffered steps to the writer and flushes it.
    ///
    /// # Errors
    ///
    /// Returns [`ProofSinkError`] when the underlying writer fails.
    pub fn flush(&mut self) -> Result<(), ProofSinkError> {
        self.writer.flush()?;
        Ok(())
    }

    /// Flushes and returns the writer.
    ///
    /// # Errors
    ///
    /// Returns [`ProofSinkError`] when the underlying writer fails; the writer is
    /// dropped in that case, since the bytes it holds are not a complete proof.
    pub fn finish(self) -> Result<W, ProofSinkError> {
        self.writer
            .into_inner()
            .map_err(|error| ProofSinkError::from(error.into_error()))
    }

    /// Formats one step into the scratch buffer and writes it out.
    fn emit(&mut self, delete: bool, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        self.scratch.clear();
        push_step_text(&mut self.scratch, delete, lits);
        self.writer.write_all(self.scratch.as_bytes())?;
        Ok(())
    }
}

impl<W: Write> DratSink for TextProofSink<W> {
    fn add_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        self.emit(false, lits)
    }

    fn delete_clause(&mut self, lits: &[CnfLit]) -> Result<(), ProofSinkError> {
        self.emit(true, lits)
    }
}

/// Parses a DRAT proof in the standard textual format (DIMACS-style integer
/// clauses terminated by `0`, optionally prefixed with `d` for deletions;
/// `c` lines are comments).
///
/// # Errors
///
/// Returns [`DratError::Parse`] for a malformed token or out-of-range variable.
pub fn parse_drat(text: &str) -> Result<Vec<DratStep>, DratError> {
    let mut steps = Vec::new();
    for line in text.lines() {
        if let Some(step) = parse_drat_line(line)? {
            steps.push(step);
        }
    }
    Ok(steps)
}

/// Parses a single textual DRAT line, returning `Ok(None)` for a blank line or a
/// `c` comment. Shared by [`parse_drat`] and [`DratTextReader`] so the whole-text
/// and streaming readers cannot drift apart.
fn parse_drat_line(line: &str) -> Result<Option<DratStep>, DratError> {
    let line = line.trim();
    if line.is_empty() || line.starts_with('c') {
        return Ok(None);
    }
    let mut tokens = line.split_whitespace().peekable();
    let delete = if tokens.peek() == Some(&"d") {
        tokens.next();
        true
    } else {
        false
    };
    let mut lits = Vec::new();
    for token in tokens {
        let value: i64 = token
            .parse()
            .map_err(|_| DratError::Parse(format!("invalid literal `{token}`")))?;
        if value == 0 {
            break;
        }
        lits.push(literal_from_dimacs(value)?);
    }
    Ok(Some(if delete {
        DratStep::Delete(lits)
    } else {
        DratStep::Add(lits)
    }))
}

/// Streams the steps of a textual DRAT proof out of any [`std::io::BufRead`]
/// (ADR-0380), one line at a time.
///
/// The counterpart of [`parse_drat`] for proofs too large to hold: feed it to
/// [`check_drat_streaming`] and neither the proof text nor the step vector is
/// ever materialized. Blank lines and `c` comments are skipped, exactly as in
/// [`parse_drat`].
///
/// The iterator is fused at the first failure: a read or parse error is yielded
/// once and then the stream ends, so a checker cannot spin on a persistently
/// failing reader. Read failures are reported as [`DratError::Parse`] (the error
/// vocabulary of the DRAT surface is deliberately not widened for I/O); the
/// message carries the underlying cause.
#[derive(Debug)]
pub struct DratTextReader<R: BufRead> {
    reader: R,
    line: String,
    done: bool,
}

impl<R: BufRead> DratTextReader<R> {
    /// Creates a reader over `reader`.
    pub fn new(reader: R) -> Self {
        Self {
            reader,
            line: String::new(),
            done: false,
        }
    }
}

impl<R: BufRead> Iterator for DratTextReader<R> {
    type Item = Result<DratStep, DratError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }
        loop {
            self.line.clear();
            match self.reader.read_line(&mut self.line) {
                Ok(0) => {
                    self.done = true;
                    return None;
                }
                Ok(_) => match parse_drat_line(&self.line) {
                    Ok(Some(step)) => return Some(Ok(step)),
                    // Blank line or comment: keep reading.
                    Ok(None) => {}
                    Err(error) => {
                        self.done = true;
                        return Some(Err(error));
                    }
                },
                Err(error) => {
                    self.done = true;
                    return Some(Err(DratError::Parse(format!(
                        "could not read proof stream: {error}"
                    ))));
                }
            }
        }
    }
}

pub(crate) fn literal_from_dimacs(value: i64) -> Result<CnfLit, DratError> {
    let index = usize::try_from(value.unsigned_abs() - 1)
        .map_err(|_| DratError::Parse(format!("variable {value} out of range")))?;
    let var = CnfVar::new(index).map_err(|error| DratError::Parse(error.to_string()))?;
    Ok(if value < 0 {
        CnfLit::positive(var).negated()
    } else {
        CnfLit::positive(var)
    })
}

/// Finds the index of a clause in `active` equal as a set to `clause`.
fn position_of(active: &[Vec<CnfLit>], clause: &[CnfLit]) -> Option<usize> {
    let target = sorted(clause);
    active
        .iter()
        .position(|candidate| sorted(candidate) == target)
}

pub(crate) fn sorted(clause: &[CnfLit]) -> Vec<(usize, bool)> {
    let mut key: Vec<(usize, bool)> = clause
        .iter()
        .map(|lit| (lit.var().index(), lit.is_negated()))
        .collect();
    key.sort_unstable();
    key.dedup();
    key
}

/// Reverse unit propagation: `clause` is RUP if assigning all its literals false
/// and unit-propagating over `active` yields a conflict.
fn is_rup(active: &[Vec<CnfLit>], clause: &[CnfLit]) -> bool {
    let mut assign: HashMap<usize, bool> = HashMap::new();
    for lit in clause {
        // Value that makes `lit` false.
        let falsifying = lit.is_negated();
        if let Some(&prev) = assign.get(&lit.var().index()) {
            if prev != falsifying {
                // The clause contains both a literal and its negation: falsifying
                // it is contradictory, so its negation is immediately unsat.
                return true;
            }
        } else {
            assign.insert(lit.var().index(), falsifying);
        }
    }
    propagate_to_conflict(active, &mut assign)
}

/// Unit-propagates `assign` over `active`, returning `true` on a conflict.
fn propagate_to_conflict(active: &[Vec<CnfLit>], assign: &mut HashMap<usize, bool>) -> bool {
    loop {
        let mut changed = false;
        for clause in active {
            let mut satisfied = false;
            let mut unassigned: Option<CnfLit> = None;
            let mut unassigned_count = 0usize;
            for &lit in clause {
                if let Some(&value) = assign.get(&lit.var().index()) {
                    // `lit` is true iff its value disagrees with its negation flag.
                    if value != lit.is_negated() {
                        satisfied = true;
                        break;
                    }
                } else {
                    unassigned_count += 1;
                    unassigned = Some(lit);
                }
            }
            if satisfied {
                continue;
            }
            if unassigned_count == 0 {
                return true;
            }
            if unassigned_count == 1 {
                let lit = unassigned.expect("exactly one unassigned literal");
                // Assign so `lit` becomes true.
                assign.insert(lit.var().index(), !lit.is_negated());
                changed = true;
            }
        }
        if !changed {
            return false;
        }
    }
}

/// Resolution asymmetric tautology: `clause` (non-empty) is RAT on its first
/// literal `p` if, for every active clause containing `¬p`, the resolvent
/// `clause ∪ (D \ {¬p})` is RUP.
fn is_rat(active: &[Vec<CnfLit>], clause: &[CnfLit]) -> bool {
    let Some(&pivot) = clause.first() else {
        return false;
    };
    let pivot_var = pivot.var().index();
    for d in active {
        let has_neg_pivot = d
            .iter()
            .any(|l| l.var().index() == pivot_var && l.is_negated() != pivot.is_negated());
        if !has_neg_pivot {
            continue;
        }
        let mut resolvent = clause.to_vec();
        for &l in d {
            let is_neg_pivot = l.var().index() == pivot_var && l.is_negated() != pivot.is_negated();
            if !is_neg_pivot {
                resolvent.push(l);
            }
        }
        if !is_rup(active, &resolvent) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::{DratError, DratStep, check_drat, is_rat, is_rup, parse_drat, write_drat};
    use crate::{CnfClause, CnfFormula, CnfLit, CnfVar};

    #[test]
    fn write_drat_round_trips_through_parse() {
        let proof = vec![
            DratStep::Add(vec![lit(1), lit(-2)]),
            DratStep::Delete(vec![lit(1), lit(-2)]),
            DratStep::Add(vec![]), // the empty clause
        ];
        let text = write_drat(&proof);
        assert!(text.contains("d "), "deletions are prefixed with `d`");
        assert_eq!(parse_drat(&text).unwrap(), proof);
    }

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

    #[test]
    fn rup_derives_empty_clause_for_unit_contradiction() {
        // (x) and (¬x): the empty clause is RUP.
        let f = formula(1, &[&[1], &[-1]]);
        let proof = vec![DratStep::Add(vec![])];
        assert_eq!(check_drat(&f, &proof), Ok(true));
    }

    #[test]
    fn rup_chain_proves_unsat_2x2() {
        // All four clauses over x,y: unsat. Proof learns (x) then ().
        let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
        let proof = vec![DratStep::Add(vec![lit(1)]), DratStep::Add(vec![])];
        assert_eq!(check_drat(&f, &proof), Ok(true));
    }

    #[test]
    fn blocked_clause_is_rat_but_not_rup() {
        // Over formula [(1, 2)], the clause (1) is RAT on pivot 1 (no clause has
        // ¬1) but is not RUP.
        let active = vec![vec![lit(1), lit(2)]];
        let clause = vec![lit(1)];
        assert!(!is_rup(&active, &clause));
        assert!(is_rat(&active, &clause));
    }

    #[test]
    fn unjustified_addition_is_rejected() {
        // From [(1)] alone, the empty clause is neither RUP nor RAT.
        let f = formula(1, &[&[1]]);
        let proof = vec![DratStep::Add(vec![])];
        assert_eq!(
            check_drat(&f, &proof),
            Err(DratError::StepNotVerified { step: 0 })
        );
    }

    #[test]
    fn verified_proof_without_empty_clause_is_not_unsat() {
        // A valid RAT addition that does not derive the empty clause.
        let f = formula(2, &[&[1, 2]]);
        let proof = vec![DratStep::Add(vec![lit(1)])];
        assert_eq!(check_drat(&f, &proof), Ok(false));
    }

    #[test]
    fn parse_round_trips_additions_and_deletions() {
        let text = "c a proof\n1 2 0\nd 1 2 0\n0\n";
        let steps = parse_drat(text).unwrap();
        assert_eq!(
            steps,
            vec![
                DratStep::Add(vec![lit(1), lit(2)]),
                DratStep::Delete(vec![lit(1), lit(2)]),
                DratStep::Add(vec![]),
            ]
        );
    }

    #[test]
    fn parsed_proof_checks_end_to_end() {
        let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
        let proof = parse_drat("1 0\n0\n").unwrap();
        assert_eq!(check_drat(&f, &proof), Ok(true));
    }

    // ----------------------------------------------------------------------
    // Streaming emission and checking (ADR-0380)
    // ----------------------------------------------------------------------

    use super::{
        DratSink, DratTextReader, ProofSinkError, TextProofSink, VecProofSink, check_drat_streaming,
    };
    use std::io::{self, BufReader, Write};

    /// Feeds a `Vec` proof through the streaming checker.
    fn check_streamed(f: &CnfFormula, proof: &[DratStep]) -> Result<bool, DratError> {
        check_drat_streaming(f, proof.iter().cloned().map(Ok))
    }

    /// A four-clause unsat formula whose refutation needs one intermediate
    /// learned clause: `()` alone is not RUP over it, so the proof's steps
    /// genuinely carry weight.
    fn unsat_2x2() -> CnfFormula {
        formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]])
    }

    #[test]
    fn streaming_checker_agrees_with_check_drat_on_valid_proofs() {
        let cases: Vec<(CnfFormula, Vec<DratStep>)> = vec![
            // A unit contradiction: the empty clause is immediately RUP.
            (formula(1, &[&[1], &[-1]]), vec![DratStep::Add(vec![])]),
            // A RUP chain.
            (
                unsat_2x2(),
                vec![DratStep::Add(vec![lit(1)]), DratStep::Add(vec![])],
            ),
            // The same chain with a deletion in the middle — the case that makes
            // the checker's memory *shrink* mid-proof.
            (
                unsat_2x2(),
                vec![
                    DratStep::Add(vec![lit(1)]),
                    DratStep::Delete(vec![lit(1), lit(2)]),
                    DratStep::Add(vec![]),
                ],
            ),
            // A verified proof that does not derive the empty clause.
            (formula(2, &[&[1, 2]]), vec![DratStep::Add(vec![lit(1)])]),
            // A real search proof, deletions and all.
            (
                unsat_2x2(),
                match crate::solve_with_drat_proof(&unsat_2x2()) {
                    crate::ProofSolveOutcome::Unsat(proof) => proof,
                    other => panic!("expected unsat, got {other:?}"),
                },
            ),
        ];
        for (index, (f, proof)) in cases.iter().enumerate() {
            assert_eq!(
                check_streamed(f, proof),
                check_drat(f, proof),
                "case {index}: streaming and whole-proof checking must agree"
            );
        }
        // …and the agreement is not the trivial one: at least the confirmed-unsat
        // cases must be `Ok(true)`.
        assert_eq!(check_streamed(&cases[1].0, &cases[1].1), Ok(true));
    }

    #[test]
    fn streaming_checker_rejects_a_truncated_proof() {
        let f = unsat_2x2();
        let full = vec![DratStep::Add(vec![lit(1)]), DratStep::Add(vec![])];
        assert_eq!(check_streamed(&f, &full), Ok(true));
        // Dropping the final empty clause leaves every step verified but UNSAT
        // unestablished — `Ok(false)`, never a confirmed refutation.
        assert_eq!(check_streamed(&f, &full[..1]), Ok(false));
    }

    #[test]
    fn streaming_checker_rejects_an_edited_step() {
        let f = unsat_2x2();
        // Weakening the learned clause `(1)` to `(1 ∨ 2)` — which is still RUP —
        // leaves the following empty clause unjustified.
        let edited = vec![DratStep::Add(vec![lit(1), lit(2)]), DratStep::Add(vec![])];
        assert_eq!(
            check_streamed(&f, &edited),
            Err(DratError::StepNotVerified { step: 1 })
        );
        assert_eq!(check_streamed(&f, &edited), check_drat(&f, &edited));
    }

    #[test]
    fn streaming_checker_rejects_an_empty_proof_for_an_unsat_formula() {
        // The formula is unsatisfiable, but a proof with no steps proves nothing.
        assert_eq!(check_streamed(&unsat_2x2(), &[]), Ok(false));
    }

    #[test]
    fn streaming_checker_propagates_a_producer_error() {
        let f = unsat_2x2();
        let steps = vec![
            Ok(DratStep::Add(vec![lit(1)])),
            Err(DratError::Parse("truncated".to_string())),
            Ok(DratStep::Add(vec![])),
        ];
        assert_eq!(
            check_drat_streaming(&f, steps.into_iter()),
            Err(DratError::Parse("truncated".to_string())),
            "an unreadable proof must never check as verified"
        );
    }

    #[test]
    fn text_proof_sink_output_is_byte_identical_to_write_drat() {
        let proof = vec![
            DratStep::Add(vec![lit(1), lit(-2)]),
            DratStep::Delete(vec![lit(1), lit(-2)]),
            DratStep::Add(vec![lit(-3)]),
            DratStep::Add(vec![]),
        ];
        let mut bytes: Vec<u8> = Vec::new();
        let mut sink = TextProofSink::new(&mut bytes);
        for step in &proof {
            match step {
                DratStep::Add(lits) => sink.add_clause(lits).unwrap(),
                DratStep::Delete(lits) => sink.delete_clause(lits).unwrap(),
            }
        }
        sink.finish().unwrap();
        assert_eq!(String::from_utf8(bytes).unwrap(), write_drat(&proof));
    }

    #[test]
    fn vec_proof_sink_records_steps_verbatim() {
        let mut sink = VecProofSink::new();
        sink.add_clause(&[lit(1), lit(-2)]).unwrap();
        sink.delete_clause(&[lit(1)]).unwrap();
        assert_eq!(sink.steps().len(), 2);
        assert_eq!(
            sink.into_steps(),
            vec![
                DratStep::Add(vec![lit(1), lit(-2)]),
                DratStep::Delete(vec![lit(1)]),
            ]
        );
    }

    /// A writer that fails every write. `TextProofSink` buffers, so the failure
    /// surfaces at `flush`/`finish` (or once the buffer fills) — pinning that
    /// contract, since a caller that never flushes would otherwise believe a
    /// proof was written.
    #[derive(Debug)]
    struct FailingWriter;

    impl Write for FailingWriter {
        fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
            Err(io::Error::new(io::ErrorKind::BrokenPipe, "pipe closed"))
        }

        fn flush(&mut self) -> io::Result<()> {
            Err(io::Error::new(io::ErrorKind::BrokenPipe, "pipe closed"))
        }
    }

    #[test]
    fn text_proof_sink_surfaces_a_writer_failure_on_finish() {
        let mut sink = TextProofSink::new(FailingWriter);
        sink.add_clause(&[lit(1)]).unwrap(); // buffered, not yet written
        let error = sink.finish().expect_err("the writer always fails");
        assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
        assert!(error.to_string().contains("DRAT proof sink failed"));
    }

    #[test]
    fn proof_sink_error_carries_its_kind_and_message() {
        let from_io = ProofSinkError::from(io::Error::new(io::ErrorKind::StorageFull, "no space"));
        assert_eq!(from_io.kind(), io::ErrorKind::StorageFull);
        assert!(from_io.message().contains("no space"));
        let direct = ProofSinkError::new(io::ErrorKind::Other, "sink refused");
        assert_eq!(direct.message(), "sink refused");
    }

    #[test]
    fn text_reader_yields_the_same_steps_as_parse_drat() {
        let text = "c a proof\n\n1 2 0\nd 1 2 0\n  -3 0\n0\n";
        let streamed: Result<Vec<DratStep>, DratError> =
            DratTextReader::new(BufReader::new(text.as_bytes())).collect();
        assert_eq!(streamed.unwrap(), parse_drat(text).unwrap());
    }

    #[test]
    fn text_reader_reports_a_malformed_line_and_then_ends() {
        let mut reader =
            DratTextReader::new(BufReader::new("1 0\nnot-a-literal 0\n1 0\n".as_bytes()));
        assert_eq!(reader.next(), Some(Ok(DratStep::Add(vec![lit(1)]))));
        assert!(matches!(reader.next(), Some(Err(DratError::Parse(_)))));
        assert_eq!(reader.next(), None, "the reader fuses after a failure");
    }

    #[test]
    fn text_reader_feeds_the_streaming_checker_end_to_end() {
        let f = unsat_2x2();
        let proof = vec![DratStep::Add(vec![lit(1)]), DratStep::Add(vec![])];
        let text = write_drat(&proof);
        assert_eq!(
            check_drat_streaming(&f, DratTextReader::new(BufReader::new(text.as_bytes()))),
            Ok(true)
        );
        // Truncating the text (a proof whose writer died) must not verify.
        let truncated = "1 0\n";
        assert_eq!(
            check_drat_streaming(
                &f,
                DratTextReader::new(BufReader::new(truncated.as_bytes()))
            ),
            Ok(false)
        );
    }
}
