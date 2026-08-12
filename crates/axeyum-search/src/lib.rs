//! Cube-and-conquer search and cover certification for parameterised
//! combinatorial instance families.
//!
//! This crate is the housed form of the tooling that computed and certified
//! Rado-number bounds against axeyum's pure-Rust stack: an instance generator,
//! an exhaustive cube cover with per-cell DRAT emission, an offline
//! certification pass, and a local search for the satisfiable side. Everything
//! runs through [`axeyum_cnf`] and `std`. There is no external SAT solver and
//! no external proof checker anywhere in this crate.
//!
//! # The shape of a run
//!
//! A [`ColouringFamily`] turns a parameter `n` into a [`ColouringProblem`],
//! which encodes to a [`CnfFormula`](axeyum_cnf::CnfFormula) that is satisfiable
//! exactly when the family's object of size `n` exists. Establishing a
//! threshold `R` therefore means two jobs:
//!
//! * **`n = R - 1` is satisfiable.** Found by [`search::min_conflicts`] or by
//!   the CDCL core, and *replayed*: the model is evaluated against the original
//!   formula and the decoded colouring is re-checked by
//!   [`ColouringFamily::first_violation`], a brute-force enumerator that shares
//!   no code with the encoder.
//! * **`n = R` is unsatisfiable.** Found by [`harness::run_cover`], which splits
//!   the formula over an exhaustive [`BranchPlan`] and refutes every cell with
//!   a DRAT proof.
//!
//! # What the UNSAT side actually certifies
//!
//! The cover argument has exactly four obligations, and this crate discharges
//! all four mechanically:
//!
//! 1. **Every cell is refuted**, with a DRAT proof of `F + cell units` checked
//!    by [`check_drat_backward`](axeyum_cnf::check_drat_backward) (ADR-0382) or
//!    the reference [`check_drat`](axeyum_cnf::check_drat).
//! 2. **Every branch group's at-least-one clause is present verbatim in `F`**,
//!    located by set-equality search — [`cover::verify_branch_clauses`].
//! 3. **The cells are exactly the full product** of the branch groups' choices,
//!    each tuple present exactly once — [`cover::verify_cell_set`].
//! 4. **Nothing is duplicated in the ledger**, checked independently of 3 at
//!    parse time — [`ledger::parse_ledger`].
//!
//! [`cover::certify_cover`] requires all four and is the only function that
//! returns a [`CoverCertificate`]. Facts 2 and 3 together say every total
//! assignment satisfying `F` extends some cell, so fact 1 for all cells implies
//! `F` is unsatisfiable. That last implication is a meta-argument; it can be
//! turned into checked DRAT steps by [`compose::compose_cover_proof`], which
//! emits one proof of the *original* formula whose acceptance by `check_drat`
//! discharges the whole result with no meta-argument at all.
//!
//! # Cost model
//!
//! Measured on `R_4(3(x-y)=2z)`, `n = 103`, 64 cells at depth 3: a cell *solves*
//! in 0.0–1.3 s and its proof used to take 46–317 s to *check*, because the
//! reference `check_drat` rescans the live clause database on every propagation
//! round. That is why [`CheckMode::Backward`] is the default here: the
//! backward checker (ADR-0382) verifies only the core and turned the same run
//! from ~1460 s of checking into a fraction of it. The second lever is
//! [`CoverOptions::check_step_cap`]: proofs longer than the cap are produced and
//! dumped but not blocked on, to be certified offline by
//! [`certify::certify_dumped_cover`]. Deferring the checking of one instance's
//! cover took it from 42% complete after 5.5 h to complete in 153 s.
//!
//! # Example
//!
//! ```
//! use axeyum_search::{ColouringFamily, Schur, cover, harness};
//!
//! // Schur's theorem: [1..5] has no 2-colouring free of monochromatic x+y=z.
//! let family = Schur::new(2)?;
//! let problem = family.problem(5)?;
//! let formula = problem.encode()?;
//! let plan = cover::colour_branch_plan(&problem, &[2, 3])?;
//!
//! let outcome = harness::run_cover(
//!     &formula,
//!     &plan,
//!     &harness::CoverOptions::default(),
//!     &harness::SilentObserver,
//! )?;
//! let certificate = outcome.certificate().expect("every cell refuted and checked");
//! assert_eq!(certificate.cells, 4);
//! # Ok::<(), axeyum_search::SearchError>(())
//! ```

pub mod certify;
pub mod colouring;
pub mod compose;
pub mod cover;
pub mod family;
pub mod harness;
pub mod ledger;
pub mod search;

pub use certify::certify_dumped_cover;
pub use colouring::{ColouringProblem, Witness};
pub use cover::{BranchGroup, BranchPlan, Cell, CellCheck, CellRecord, CellVerdict, CoverCertificate};
pub use family::{ColouringFamily, Rado, Schur, parse_family};
pub use harness::{CheckMode, CoverOptions, CoverOutcome};
pub use ledger::RunId;
pub use search::{MinConflictsOptions, min_conflicts};

use axeyum_cnf::{CnfError, DratError};

/// Errors from instance construction, cover search, and cover certification.
///
/// Every variant that can be produced by a *certification* path names the cell
/// or branch group it is about: a rejected cover has to say which obligation
/// failed and where, or it is not evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum SearchError {
    /// The CNF layer rejected a formula, clause, or variable.
    Cnf(CnfError),
    /// The DRAT layer rejected a proof or failed to parse one.
    Drat(DratError),
    /// A filesystem operation failed.
    Io {
        /// Path the operation was attempted on.
        path: String,
        /// Operating-system message.
        message: String,
    },
    /// A parameter was outside the range the family or harness accepts.
    InvalidParameter {
        /// What was wrong, in the caller's terms.
        what: String,
    },
    /// A point index was outside `1..=points`.
    PointOutOfRange {
        /// Offending point.
        point: usize,
        /// Number of points in the problem.
        points: usize,
    },
    /// A colour index was outside `1..=colours`.
    ColourOutOfRange {
        /// Offending colour.
        colour: usize,
        /// Number of colours in the problem.
        colours: usize,
    },
    /// A branch plan had no groups, so there is no cover to enumerate.
    EmptyBranchPlan,
    /// A branch group had no literals, so its at-least-one clause is empty.
    EmptyBranchGroup {
        /// Zero-based group position in the plan.
        group: usize,
    },
    /// **Cover obligation 2 failed.** The formula does not contain the group's
    /// at-least-one clause verbatim, so the branch is not exhaustive over it and
    /// the cover argument does not apply to this encoding.
    MissingAtLeastOneClause {
        /// Zero-based group position in the plan.
        group: usize,
        /// The group's label.
        label: String,
    },
    /// A cell index was outside `0..cell_count`.
    CellIndexOutOfRange {
        /// Offending index.
        index: usize,
        /// Number of cells in the plan.
        cells: usize,
    },
    /// **Cover obligation 3 failed.** A product cell has no record.
    MissingCell {
        /// Index of the uncovered cell.
        index: usize,
    },
    /// **Cover obligation 3/4 failed.** A product cell has more than one record.
    ///
    /// This is the shape a restarted run that appended to an existing ledger
    /// produces (finding B2): 1093 rows over a 1024-cell product, with 69
    /// duplicates.
    DuplicateCell {
        /// Index of the doubly covered cell.
        index: usize,
    },
    /// **Cover obligation 1 failed.** A cell's verdict is not `unsat`.
    CellNotRefuted {
        /// Index of the cell.
        index: usize,
        /// The verdict the ledger actually recorded.
        verdict: &'static str,
    },
    /// **Cover obligation 1 failed.** A cell's proof was never checked.
    CellNotChecked {
        /// Index of the cell.
        index: usize,
    },
    /// A ledger row's choice tuple is not the cell the row claims. Such a row
    /// would otherwise pass the set check while certifying a different
    /// augmented formula than the one named.
    CellChoicesMismatch {
        /// Index the row claims.
        index: usize,
        /// Choices the row carries.
        choices: Vec<usize>,
        /// Index those choices actually name.
        actual: usize,
    },
    /// **Cover obligation 1 failed.** A cell's proof was checked and rejected.
    CellCheckFailed {
        /// Index of the cell.
        index: usize,
        /// Why the checker rejected it.
        reason: String,
    },
    /// A cell's proof could not be read from the proof source.
    ProofUnavailable {
        /// Index of the cell.
        index: usize,
        /// Why the proof could not be produced.
        message: String,
    },
    /// Route A composition was asked for a cell whose proof was not retained.
    ComposeMissingProof {
        /// Index of the cell.
        index: usize,
    },
    /// Route A composition did not end in the empty clause, so it is not a
    /// refutation and must not be offered as one.
    ComposeNoEmptyClause,
    /// The status ledger already exists, so this run would append to another
    /// run's rows (finding B2). Use a fresh path or stamp the run.
    LedgerExists {
        /// Path that already exists.
        path: String,
    },
    /// The ledger's header line is not the one this crate writes.
    LedgerHeader {
        /// Header line as found.
        found: String,
    },
    /// A ledger row could not be parsed.
    LedgerRow {
        /// One-based line number in the ledger.
        line: usize,
        /// What was wrong with the row.
        message: String,
    },
    /// **Soundness alarm.** A cell reported `sat` with a model that does not
    /// satisfy the original formula.
    ModelDoesNotSatisfy {
        /// Index of the cell that reported `sat`.
        cell: usize,
    },
    /// A model did not assign exactly one colour to a point.
    ModelNotOneHot {
        /// The point with zero or several colours.
        point: usize,
        /// How many colours the model assigned it.
        colours: usize,
    },
    /// A witness had the wrong number of points.
    WitnessLength {
        /// Points the problem has.
        expected: usize,
        /// Points the witness covers.
        found: usize,
    },
    /// **The search lied.** A reported colouring contains a monochromatic
    /// forbidden set, so it is not a witness.
    WitnessMonochromatic {
        /// The offending set, ascending.
        members: Vec<usize>,
        /// The colour all its members share.
        colour: usize,
    },
}

impl core::fmt::Display for SearchError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Cnf(error) => write!(f, "{error}"),
            Self::Drat(error) => write!(f, "{error}"),
            Self::Io { path, message } => write!(f, "{path}: {message}"),
            Self::InvalidParameter { what } => write!(f, "invalid parameter: {what}"),
            Self::PointOutOfRange { point, points } => {
                write!(f, "point {point} outside 1..={points}")
            }
            Self::ColourOutOfRange { colour, colours } => {
                write!(f, "colour {colour} outside 1..={colours}")
            }
            Self::EmptyBranchPlan => write!(f, "branch plan has no groups"),
            Self::EmptyBranchGroup { group } => write!(f, "branch group {group} has no literals"),
            Self::MissingAtLeastOneClause { group, label } => write!(
                f,
                "no at-least-one clause for branch group {group} ({label}) in the formula; \
                 the cover argument does not apply to this encoding"
            ),
            Self::CellIndexOutOfRange { index, cells } => {
                write!(f, "cell {index} outside 0..{cells}")
            }
            Self::MissingCell { index } => write!(f, "cover is missing cell {index}"),
            Self::DuplicateCell { index } => write!(f, "cover records cell {index} more than once"),
            Self::CellNotRefuted { index, verdict } => {
                write!(f, "cell {index} was not refuted: verdict {verdict}")
            }
            Self::CellNotChecked { index } => {
                write!(f, "cell {index} was refuted but its proof was never checked")
            }
            Self::CellChoicesMismatch {
                index,
                choices,
                actual,
            } => write!(
                f,
                "ledger row claims cell {index} but its choices {choices:?} are cell {actual}"
            ),
            Self::CellCheckFailed { index, reason } => {
                write!(f, "cell {index} proof rejected: {reason}")
            }
            Self::ProofUnavailable { index, message } => {
                write!(f, "cell {index} proof unavailable: {message}")
            }
            Self::ComposeMissingProof { index } => {
                write!(f, "cell {index} proof was not retained; cannot compose")
            }
            Self::ComposeNoEmptyClause => {
                write!(f, "composed proof does not end in the empty clause")
            }
            Self::LedgerExists { path } => write!(
                f,
                "status ledger {path} already exists; refusing to append to another run's rows"
            ),
            Self::LedgerHeader { found } => write!(f, "unexpected ledger header: {found:?}"),
            Self::LedgerRow { line, message } => write!(f, "ledger line {line}: {message}"),
            Self::ModelDoesNotSatisfy { cell } => write!(
                f,
                "SOUNDNESS ALARM: cell {cell} reported sat with a model that does not satisfy \
                 the original formula"
            ),
            Self::ModelNotOneHot { point, colours } => {
                write!(f, "model gives point {point} {colours} colours, want exactly 1")
            }
            Self::WitnessLength { expected, found } => {
                write!(f, "witness covers {found} points, problem has {expected}")
            }
            Self::WitnessMonochromatic { members, colour } => {
                write!(f, "monochromatic {members:?} all coloured {colour}")
            }
        }
    }
}

impl core::error::Error for SearchError {}

impl From<CnfError> for SearchError {
    fn from(error: CnfError) -> Self {
        Self::Cnf(error)
    }
}

impl From<DratError> for SearchError {
    fn from(error: DratError) -> Self {
        Self::Drat(error)
    }
}

impl SearchError {
    /// Wraps an I/O failure with the path it happened on.
    pub(crate) fn io(path: &std::path::Path, error: &std::io::Error) -> Self {
        Self::Io {
            path: path.display().to_string(),
            message: error.to_string(),
        }
    }
}
