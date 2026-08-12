//! Branch plans, cells, and the cover-validity checks.
//!
//! A [`BranchPlan`] is a list of [`BranchGroup`]s. Each group is a set of
//! literals whose at-least-one clause must be present verbatim in the formula;
//! a [`Cell`] picks one literal from each group; the cover is the **full
//! cartesian product** of those choices. Cells that the formula's symmetry
//! breaking already excludes are not skipped — they are enumerated like any
//! other and refuted at decision level zero in microseconds. Enumerating the
//! whole product is what makes the cover argument trivial to state and, more to
//! the point, trivial to *check*.
//!
//! # The obligations, and where they are discharged
//!
//! | # | Obligation | Function |
//! |---|---|---|
//! | 1 | every cell is refuted by a checked proof | [`certify_cover`] |
//! | 2 | every group's at-least-one clause is in `F` verbatim | [`verify_branch_clauses`] |
//! | 3 | the cells are exactly the product, once each | [`verify_cell_set`] |
//! | 4 | the ledger has no duplicate rows | [`crate::ledger::parse_ledger`] |
//!
//! Obligations 3 and 4 overlap on purpose. The duplicate that finding B2
//! produced — a restarted run appending to a live ledger, 1093 rows over a
//! 1024-cell product — was caught only because a downstream checker verified the
//! cover was exactly the product. Two independent detectors now sit on that
//! failure, one at parse time and one at certification time.

use std::collections::BTreeMap;
use std::time::Duration;

use axeyum_cnf::{CnfFormula, CnfLit};

use crate::colouring::ColouringProblem;
use crate::ledger::RunId;
use crate::SearchError;

/// One coordinate of a branch plan: a set of literals, exactly one of which
/// must hold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchGroup {
    label: String,
    literals: Vec<CnfLit>,
}

impl BranchGroup {
    /// Builds a group from its literals.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::EmptyBranchGroup`] if `literals` is empty.
    pub fn new(label: impl Into<String>, literals: Vec<CnfLit>) -> Result<Self, SearchError> {
        if literals.is_empty() {
            return Err(SearchError::EmptyBranchGroup { group: 0 });
        }
        Ok(Self {
            label: label.into(),
            literals,
        })
    }

    /// Human-readable name for the group, used in labels and errors.
    pub fn label(&self) -> &str {
        &self.label
    }

    /// The group's literals, in choice order.
    pub fn literals(&self) -> &[CnfLit] {
        &self.literals
    }

    /// Number of choices this group offers.
    pub fn arity(&self) -> usize {
        self.literals.len()
    }
}

/// An exhaustive branch plan: the cover is the product of its groups.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchPlan {
    groups: Vec<BranchGroup>,
    /// `strides[slot]` is the product of the arities after `slot`, so cell
    /// indices are mixed-radix with the last coordinate varying fastest.
    strides: Vec<usize>,
    cells: usize,
}

impl BranchPlan {
    /// Builds a plan from its groups.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::EmptyBranchPlan`] for no groups,
    /// [`SearchError::EmptyBranchGroup`] for an empty group, and
    /// [`SearchError::InvalidParameter`] if the product of the arities
    /// overflows.
    pub fn new(groups: Vec<BranchGroup>) -> Result<Self, SearchError> {
        if groups.is_empty() {
            return Err(SearchError::EmptyBranchPlan);
        }
        for (position, group) in groups.iter().enumerate() {
            if group.literals.is_empty() {
                return Err(SearchError::EmptyBranchGroup { group: position });
            }
        }
        let mut strides = vec![1usize; groups.len()];
        let mut running = 1usize;
        for slot in (0..groups.len()).rev() {
            strides[slot] = running;
            running = running
                .checked_mul(groups[slot].arity())
                .ok_or_else(|| SearchError::InvalidParameter {
                    what: "branch plan product overflows".to_string(),
                })?;
        }
        Ok(Self {
            groups,
            strides,
            cells: running,
        })
    }

    /// The plan's groups.
    pub fn groups(&self) -> &[BranchGroup] {
        &self.groups
    }

    /// Number of groups, the depth of the decomposition.
    pub fn depth(&self) -> usize {
        self.groups.len()
    }

    /// Number of cells in the full product.
    pub fn cell_count(&self) -> usize {
        self.cells
    }

    /// The cell at `index`, with one-based choices per group.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::CellIndexOutOfRange`] if `index` is not a cell.
    pub fn cell(&self, index: usize) -> Result<Cell, SearchError> {
        if index >= self.cells {
            return Err(SearchError::CellIndexOutOfRange {
                index,
                cells: self.cells,
            });
        }
        let choices = (0..self.groups.len())
            .map(|slot| (index / self.strides[slot]) % self.groups[slot].arity() + 1)
            .collect::<Vec<_>>();
        let literals = self.literals_for(&choices)?;
        Ok(Cell {
            index,
            choices,
            literals,
        })
    }

    /// Every cell of the product, in index order.
    ///
    /// # Errors
    ///
    /// As [`BranchPlan::cell`].
    pub fn cells(&self) -> Result<Vec<Cell>, SearchError> {
        (0..self.cells).map(|index| self.cell(index)).collect()
    }

    /// The index of the cell with these one-based choices.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] if the arity is wrong and
    /// [`SearchError::CellIndexOutOfRange`] if a choice is out of range.
    pub fn index_of(&self, choices: &[usize]) -> Result<usize, SearchError> {
        if choices.len() != self.groups.len() {
            return Err(SearchError::InvalidParameter {
                what: format!(
                    "cell has {} choices, plan has {} groups",
                    choices.len(),
                    self.groups.len()
                ),
            });
        }
        let mut index = 0usize;
        for (slot, &choice) in choices.iter().enumerate() {
            if choice == 0 || choice > self.groups[slot].arity() {
                return Err(SearchError::CellIndexOutOfRange {
                    index: choice,
                    cells: self.groups[slot].arity(),
                });
            }
            index += (choice - 1) * self.strides[slot];
        }
        Ok(index)
    }

    /// The cell literals for a one-based choice tuple.
    ///
    /// # Errors
    ///
    /// As [`BranchPlan::index_of`].
    pub fn literals_for(&self, choices: &[usize]) -> Result<Vec<CnfLit>, SearchError> {
        self.index_of(choices)?;
        Ok(choices
            .iter()
            .enumerate()
            .map(|(slot, &choice)| self.groups[slot].literals[choice - 1])
            .collect())
    }

    /// Number of distinct prefixes of length `level`.
    pub fn prefix_count(&self, level: usize) -> usize {
        self.groups
            .iter()
            .take(level)
            .map(BranchGroup::arity)
            .product()
    }

    /// The `code`-th prefix of length `level`, one-based per group, in the same
    /// mixed-radix order as [`BranchPlan::cell`].
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::CellIndexOutOfRange`] if `code` is out of range
    /// or `level` exceeds the depth.
    pub fn prefix(&self, level: usize, code: usize) -> Result<Vec<usize>, SearchError> {
        let count = self.prefix_count(level);
        if level > self.groups.len() || code >= count {
            return Err(SearchError::CellIndexOutOfRange {
                index: code,
                cells: count,
            });
        }
        let mut rest = code;
        let mut prefix = vec![0usize; level];
        for slot in (0..level).rev() {
            let arity = self.groups[slot].arity();
            prefix[slot] = rest % arity + 1;
            rest /= arity;
        }
        Ok(prefix)
    }
}

/// One cell of the cover: a choice from every branch group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cell {
    index: usize,
    choices: Vec<usize>,
    literals: Vec<CnfLit>,
}

impl Cell {
    /// The cell's index in the product.
    pub fn index(&self) -> usize {
        self.index
    }

    /// One-based choice per group; for a colouring plan, the colour.
    pub fn choices(&self) -> &[usize] {
        &self.choices
    }

    /// The cell's literals, asserted as units when the cell is solved.
    pub fn literals(&self) -> &[CnfLit] {
        &self.literals
    }

    /// `D_c`, the cell's negation clause, used by route A composition.
    pub fn negation(&self) -> Vec<CnfLit> {
        self.literals.iter().map(|lit| lit.negated()).collect()
    }

    /// Renders the cell's choices as a comma-separated ledger field.
    pub fn choice_field(&self) -> String {
        let mut out = String::new();
        for (position, choice) in self.choices.iter().enumerate() {
            if position > 0 {
                out.push(',');
            }
            out.push_str(&choice.to_string());
        }
        out
    }

    /// Human-readable label, e.g. `c(2)=1 c(4)=3`.
    pub fn label(&self, plan: &BranchPlan) -> String {
        let mut out = String::new();
        for (slot, choice) in self.choices.iter().enumerate() {
            if slot > 0 {
                out.push(' ');
            }
            out.push_str(plan.groups[slot].label());
            out.push('=');
            out.push_str(&choice.to_string());
        }
        out
    }
}

/// Builds the branch plan that splits on the colours of the given points.
///
/// # Errors
///
/// Returns [`SearchError::EmptyBranchPlan`] for an empty point list,
/// [`SearchError::InvalidParameter`] for a repeated point, and
/// [`SearchError::PointOutOfRange`] for a point the problem does not have.
pub fn colour_branch_plan(
    problem: &ColouringProblem,
    points: &[usize],
) -> Result<BranchPlan, SearchError> {
    if points.is_empty() {
        return Err(SearchError::EmptyBranchPlan);
    }
    let mut seen = points.to_vec();
    seen.sort_unstable();
    seen.dedup();
    if seen.len() != points.len() {
        return Err(SearchError::InvalidParameter {
            what: format!("branch points {points:?} repeat a point"),
        });
    }
    let groups = points
        .iter()
        .map(|&point| BranchGroup::new(format!("c({point})"), problem.at_least_one(point)?))
        .collect::<Result<Vec<_>, SearchError>>()?;
    BranchPlan::new(groups)
}

/// Canonical set key for a clause: variable index and sign, sorted and deduped.
fn clause_key(lits: &[CnfLit]) -> Vec<(usize, bool)> {
    let mut key: Vec<(usize, bool)> = lits
        .iter()
        .map(|lit| (lit.var().index(), lit.is_negated()))
        .collect();
    key.sort_unstable();
    key.dedup();
    key
}

/// **Cover obligation 2.** Locates every branch group's at-least-one clause in
/// the formula, verbatim, and returns the clause index for each group.
///
/// Without this the branch is not exhaustive: a formula that does not force one
/// of a group's literals has satisfying assignments no cell covers, and
/// refuting every cell says nothing about it.
///
/// # Errors
///
/// Returns [`SearchError::MissingAtLeastOneClause`] naming the first group
/// whose clause is absent.
pub fn verify_branch_clauses(
    formula: &CnfFormula,
    plan: &BranchPlan,
) -> Result<Vec<usize>, SearchError> {
    let mut sites = Vec::with_capacity(plan.depth());
    for (position, group) in plan.groups().iter().enumerate() {
        let want = clause_key(group.literals());
        let site = formula
            .clauses()
            .iter()
            .position(|clause| clause_key(clause.lits()) == want)
            .ok_or_else(|| SearchError::MissingAtLeastOneClause {
                group: position,
                label: group.label().to_string(),
            })?;
        sites.push(site);
    }
    Ok(sites)
}

/// **Cover obligation 3.** Checks that `indices` is exactly the plan's product,
/// each cell present exactly once.
///
/// # Errors
///
/// Returns [`SearchError::CellIndexOutOfRange`] for an index that is not a
/// cell, [`SearchError::DuplicateCell`] for a repeat, and
/// [`SearchError::MissingCell`] for a hole.
pub fn verify_cell_set(plan: &BranchPlan, indices: &[usize]) -> Result<(), SearchError> {
    let mut hits = vec![0u32; plan.cell_count()];
    for &index in indices {
        let slot = hits
            .get_mut(index)
            .ok_or(SearchError::CellIndexOutOfRange {
                index,
                cells: plan.cell_count(),
            })?;
        *slot += 1;
        if *slot > 1 {
            return Err(SearchError::DuplicateCell { index });
        }
    }
    match hits.iter().position(|&hit| hit == 0) {
        Some(index) => Err(SearchError::MissingCell { index }),
        None => Ok(()),
    }
}

/// Whether a cell was refuted, and if not, why not.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CellVerdict {
    /// The cell's augmented formula was refuted.
    Unsat,
    /// The cell's augmented formula is satisfiable, so the instance is.
    Sat,
    /// The conflict budget ran out before a verdict.
    ResourceOut,
    /// The wall-clock deadline passed before a verdict.
    Timeout,
}

impl CellVerdict {
    /// The ledger token for this verdict.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Unsat => "unsat",
            Self::Sat => "sat",
            Self::ResourceOut => "resource-out",
            Self::Timeout => "timeout",
        }
    }

    /// Parses a ledger token.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] for an unknown token.
    pub fn parse(token: &str) -> Result<Self, SearchError> {
        match token {
            "unsat" => Ok(Self::Unsat),
            "sat" => Ok(Self::Sat),
            "resource-out" => Ok(Self::ResourceOut),
            "timeout" => Ok(Self::Timeout),
            _ => Err(SearchError::InvalidParameter {
                what: format!("unknown verdict {token:?}"),
            }),
        }
    }
}

/// What happened when the cell's proof was checked.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CellCheck {
    /// A DRAT checker accepted the proof of `F + cell units`.
    Passed,
    /// The proof was produced but not checked — over the step cap, or checking
    /// was switched off to be done offline.
    Deferred,
    /// A DRAT checker rejected the proof. **Soundness alarm.**
    Failed(String),
}

impl CellCheck {
    /// The ledger token for this outcome.
    pub fn as_field(&self) -> String {
        match self {
            Self::Passed => "passed".to_string(),
            Self::Deferred => "deferred".to_string(),
            Self::Failed(why) => format!("FAILED({why})"),
        }
    }

    /// Parses a ledger token.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] for an unknown token.
    pub fn parse(token: &str) -> Result<Self, SearchError> {
        match token {
            "passed" => Ok(Self::Passed),
            "deferred" => Ok(Self::Deferred),
            _ => token
                .strip_prefix("FAILED(")
                .and_then(|rest| rest.strip_suffix(')'))
                .map(|why| Self::Failed(why.to_string()))
                .ok_or_else(|| SearchError::InvalidParameter {
                    what: format!("unknown check status {token:?}"),
                }),
        }
    }
}

/// One finished cell, as recorded in the status ledger.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CellRecord {
    /// Which run produced the row. Rows from different runs are still
    /// duplicates if they name the same cell.
    pub run: RunId,
    /// Index of the cell in the plan's product.
    pub index: usize,
    /// The cell's one-based choices.
    pub choices: Vec<usize>,
    /// Whether the cell was refuted.
    pub verdict: CellVerdict,
    /// Time the solver spent on the cell.
    pub solve: Duration,
    /// Total DRAT steps in the cell's proof.
    pub steps: usize,
    /// Clause additions in the cell's proof.
    pub adds: usize,
    /// Whether the proof was checked, and with what result.
    pub check: CellCheck,
    /// Time the checker spent on the cell.
    pub check_time: Duration,
}

/// A cover that has passed every obligation.
///
/// Only [`certify_cover`] constructs one, and it does so only when all four
/// obligations hold. The fields exist to be reported, not to be believed on
/// their own.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoverCertificate {
    /// Number of cells, equal to the plan's product size.
    pub cells: usize,
    /// Clause index in `F` of each branch group's at-least-one clause.
    pub branch_clauses: Vec<usize>,
    /// Total DRAT steps across the cover.
    pub steps: usize,
    /// Total time the checker spent across the cover.
    pub check_time: Duration,
}

impl CoverCertificate {
    /// One-line summary suitable for a log or a ledger note.
    pub fn summary(&self) -> String {
        format!(
            "cover certified: {} cells, each refuted by a checked DRAT proof; \
             at-least-one clauses located in F at {:?}; {} proof steps checked in {:.1}s",
            self.cells,
            self.branch_clauses,
            self.steps,
            self.check_time.as_secs_f64()
        )
    }
}

/// **All four cover obligations.** Returns a certificate only if every one
/// holds.
///
/// Obligation 4 (no duplicate rows) is enforced twice over: once here through
/// [`verify_cell_set`], and once at parse time in
/// [`crate::ledger::parse_ledger`].
///
/// # Errors
///
/// Returns the specific obligation failure: [`SearchError::MissingCell`],
/// [`SearchError::DuplicateCell`], [`SearchError::MissingAtLeastOneClause`],
/// [`SearchError::CellNotRefuted`], [`SearchError::CellNotChecked`], or
/// [`SearchError::CellCheckFailed`].
pub fn certify_cover(
    formula: &CnfFormula,
    plan: &BranchPlan,
    records: &[CellRecord],
) -> Result<CoverCertificate, SearchError> {
    let branch_clauses = verify_branch_clauses(formula, plan)?;
    let indices: Vec<usize> = records.iter().map(|record| record.index).collect();
    verify_cell_set(plan, &indices)?;

    // The recorded choices must be the cell they claim to be: a row that says
    // "cell 7" but carries cell 9's colours would otherwise pass the set check
    // while certifying the wrong augmented formula.
    let mut by_index: BTreeMap<usize, &CellRecord> = BTreeMap::new();
    for record in records {
        let actual = plan.index_of(&record.choices)?;
        if actual != record.index {
            return Err(SearchError::CellChoicesMismatch {
                index: record.index,
                choices: record.choices.clone(),
                actual,
            });
        }
        by_index.insert(record.index, record);
    }

    let mut steps = 0usize;
    let mut check_time = Duration::ZERO;
    for (&index, record) in &by_index {
        if record.verdict != CellVerdict::Unsat {
            return Err(SearchError::CellNotRefuted {
                index,
                verdict: record.verdict.as_str(),
            });
        }
        match &record.check {
            CellCheck::Passed => {}
            CellCheck::Deferred => return Err(SearchError::CellNotChecked { index }),
            CellCheck::Failed(reason) => {
                return Err(SearchError::CellCheckFailed {
                    index,
                    reason: reason.clone(),
                });
            }
        }
        steps += record.steps;
        check_time += record.check_time;
    }

    Ok(CoverCertificate {
        cells: plan.cell_count(),
        branch_clauses,
        steps,
        check_time,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::family::{ColouringFamily, Schur};

    fn plan_for(points: &[usize]) -> (ColouringProblem, BranchPlan) {
        let family = Schur::new(3).expect("family");
        let problem = family.problem(8).expect("problem");
        let plan = colour_branch_plan(&problem, points).expect("plan");
        (problem, plan)
    }

    #[test]
    fn cells_are_the_full_product_in_mixed_radix_order() {
        let (_, plan) = plan_for(&[2, 3]);
        assert_eq!(plan.cell_count(), 9);
        let cells = plan.cells().expect("cells");
        assert_eq!(cells[0].choices(), &[1, 1]);
        assert_eq!(cells[1].choices(), &[1, 2]);
        assert_eq!(cells[3].choices(), &[2, 1]);
        assert_eq!(cells[8].choices(), &[3, 3]);
        for cell in &cells {
            assert_eq!(plan.index_of(cell.choices()).expect("index"), cell.index());
        }
    }

    #[test]
    fn prefixes_agree_with_cell_choices() {
        let (_, plan) = plan_for(&[2, 3]);
        assert_eq!(plan.prefix_count(0), 1);
        assert_eq!(plan.prefix(0, 0).expect("root"), Vec::<usize>::new());
        assert_eq!(plan.prefix_count(1), 3);
        assert_eq!(plan.prefix(1, 2).expect("prefix"), vec![3]);
        assert_eq!(plan.prefix_count(2), 9);
        assert_eq!(plan.prefix(2, 5).expect("prefix"), vec![2, 3]);
    }

    #[test]
    fn branch_clauses_are_located_verbatim() {
        let (problem, plan) = plan_for(&[2, 3]);
        let formula = problem.encode().expect("encode");
        let sites = verify_branch_clauses(&formula, &plan).expect("located");
        assert_eq!(sites, vec![1, 2]);
    }

    #[test]
    fn cell_set_check_rejects_holes_and_repeats() {
        let (_, plan) = plan_for(&[2]);
        assert!(verify_cell_set(&plan, &[0, 1, 2]).is_ok());
        assert_eq!(
            verify_cell_set(&plan, &[0, 1]),
            Err(SearchError::MissingCell { index: 2 })
        );
        assert_eq!(
            verify_cell_set(&plan, &[0, 1, 1]),
            Err(SearchError::DuplicateCell { index: 1 })
        );
    }

    #[test]
    fn verdict_and_check_fields_round_trip() {
        for verdict in [
            CellVerdict::Unsat,
            CellVerdict::Sat,
            CellVerdict::ResourceOut,
            CellVerdict::Timeout,
        ] {
            assert_eq!(CellVerdict::parse(verdict.as_str()).expect("verdict"), verdict);
        }
        for check in [
            CellCheck::Passed,
            CellCheck::Deferred,
            CellCheck::Failed("no empty clause".to_string()),
        ] {
            assert_eq!(CellCheck::parse(&check.as_field()).expect("check"), check);
        }
    }
}
