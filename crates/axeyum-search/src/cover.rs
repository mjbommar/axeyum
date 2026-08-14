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

use std::collections::{BTreeMap, BTreeSet};
use std::time::Duration;

use axeyum_cnf::{CnfFormula, CnfLit};

use crate::SearchError;
use crate::colouring::ColouringProblem;
use crate::ledger::RunId;

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
            running = running.checked_mul(groups[slot].arity()).ok_or_else(|| {
                SearchError::InvalidParameter {
                    what: "branch plan product overflows".to_string(),
                }
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

    /// Number of prefixes of length **less than** `level`, i.e. the base of
    /// the code range [`BranchPlan::prefix_code`] assigns to that level.
    ///
    /// `level` is clamped to the plan's depth, since no prefix is longer.
    pub fn prefix_offset(&self, level: usize) -> usize {
        (0..level.min(self.groups.len()))
            .map(|l| self.prefix_count(l))
            .sum()
    }

    /// Total number of prefixes of every length `0..=depth`, i.e. the number
    /// of nodes in the branch trie.
    pub fn node_count(&self) -> usize {
        (0..=self.groups.len()).map(|l| self.prefix_count(l)).sum()
    }

    /// A **shape-independent** identifier for a prefix of any length.
    ///
    /// Codes are what a tree cover records instead of a flat cell index. The
    /// key property is that a code depends only on the plan and the path, never
    /// on which other cubes the cover happens to contain — so two runs that
    /// split the same subtree differently still agree on the identity of every
    /// cube they share, and their ledgers can be concatenated and re-certified
    /// without renumbering. Codes of different lengths never collide: level `L`
    /// occupies `prefix_offset(L) .. prefix_offset(L) + prefix_count(L)`.
    ///
    /// Note that a full-depth path's code is **not** its
    /// [`BranchPlan::index_of`] cell index; it is that index shifted past every
    /// shorter level. Flat covers keep using `index_of`.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] if the path is longer than the
    /// plan's depth and [`SearchError::CellIndexOutOfRange`] for a choice
    /// outside its group's arity.
    pub fn prefix_code(&self, path: &[usize]) -> Result<usize, SearchError> {
        if path.len() > self.groups.len() {
            return Err(SearchError::InvalidParameter {
                what: format!(
                    "cube path has {} choices, plan has {} groups",
                    path.len(),
                    self.groups.len()
                ),
            });
        }
        let mut local = 0usize;
        for (slot, &choice) in path.iter().enumerate() {
            let arity = self.groups[slot].arity();
            if choice == 0 || choice > arity {
                return Err(SearchError::CellIndexOutOfRange {
                    index: choice,
                    cells: arity,
                });
            }
            local = local * arity + (choice - 1);
        }
        Ok(self.prefix_offset(path.len()) + local)
    }

    /// The literals a cube of this shape asserts as units, for a path of any
    /// length `0..=depth`.
    ///
    /// # Errors
    ///
    /// As [`BranchPlan::prefix_code`].
    pub fn literals_for_prefix(&self, path: &[usize]) -> Result<Vec<CnfLit>, SearchError> {
        self.prefix_code(path)?;
        Ok(path
            .iter()
            .enumerate()
            .map(|(slot, &choice)| self.groups[slot].literals[choice - 1])
            .collect())
    }

    /// The cube at `path`.
    ///
    /// # Errors
    ///
    /// As [`BranchPlan::prefix_code`].
    pub fn cube(&self, path: &[usize]) -> Result<Cube, SearchError> {
        Ok(Cube {
            code: self.prefix_code(path)?,
            literals: self.literals_for_prefix(path)?,
            path: path.to_vec(),
        })
    }

    /// Every prefix of length `level`, in code order — the seed set of an
    /// adaptive cover started at that depth.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::CellIndexOutOfRange`] if `level` exceeds the
    /// plan's depth.
    pub fn cubes_at_level(&self, level: usize) -> Result<Vec<Cube>, SearchError> {
        if level > self.groups.len() {
            return Err(SearchError::CellIndexOutOfRange {
                index: level,
                cells: self.groups.len() + 1,
            });
        }
        (0..self.prefix_count(level))
            .map(|code| self.cube(&self.prefix(level, code)?))
            .collect()
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

/// One cube of a **tree** cover: a choice from the first `path.len()` groups.
///
/// A [`Cell`] is the special case `path.len() == plan.depth()`. A tree cover is
/// a set of cubes of mixed lengths whose completeness is checked by
/// [`verify_cube_cover`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cube {
    code: usize,
    path: Vec<usize>,
    literals: Vec<CnfLit>,
}

impl Cube {
    /// The cube's shape-independent code; see [`BranchPlan::prefix_code`].
    pub fn code(&self) -> usize {
        self.code
    }

    /// One-based choice per group, shortest-first; for a colouring plan, the
    /// colours of the first `depth()` branch points.
    pub fn path(&self) -> &[usize] {
        &self.path
    }

    /// How many groups the cube fixes.
    pub fn depth(&self) -> usize {
        self.path.len()
    }

    /// The cube's literals, asserted as units when the cube is solved.
    pub fn literals(&self) -> &[CnfLit] {
        &self.literals
    }

    /// The paths of this cube's children, one per choice in the next group.
    ///
    /// Returns an empty vector at the plan's full depth: there is nothing left
    /// to split on.
    pub fn child_paths(&self, plan: &BranchPlan) -> Vec<Vec<usize>> {
        match plan.groups().get(self.path.len()) {
            None => Vec::new(),
            Some(group) => (1..=group.arity())
                .map(|choice| {
                    let mut child = self.path.clone();
                    child.push(choice);
                    child
                })
                .collect(),
        }
    }

    /// Human-readable label, e.g. `c(2)=1 c(4)=3`.
    pub fn label(&self, plan: &BranchPlan) -> String {
        let mut out = String::new();
        for (slot, choice) in self.path.iter().enumerate() {
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

/// **Cover obligation 3, generalized to a tree.** Checks that `paths` is
/// exactly the leaf set of a complete branch trie: every assignment satisfying
/// the plan's at-least-one clauses lies in exactly one cube.
///
/// A flat product cover is the special case where every path has full depth,
/// and on that input this agrees with [`verify_cell_set`] cell for cell —
/// `cube_cover_agrees_with_flat_cell_set` pins it.
///
/// The three ways a tree cover can be wrong, and what is returned:
///
/// * a **hole** — some node is neither a cube nor fully split:
///   [`SearchError::MissingCell`] carrying the code of the uncovered node;
/// * an **overlap** — a cube strictly inside another cube, so its region is
///   covered twice: [`SearchError::DuplicateCell`] carrying the inner cube's
///   code (a literally repeated path gives the same error);
/// * a **malformed path** — too long, or a choice outside its group's arity:
///   the error from [`BranchPlan::prefix_code`].
///
/// # Errors
///
/// As above.
pub fn verify_cube_cover(plan: &BranchPlan, paths: &[Vec<usize>]) -> Result<(), SearchError> {
    let mut leaves: BTreeMap<usize, usize> = BTreeMap::new();
    for path in paths {
        let code = plan.prefix_code(path)?;
        if leaves.insert(code, path.len()).is_some() {
            return Err(SearchError::DuplicateCell { index: code });
        }
    }

    // Codes of every proper prefix of every cube: the interior of the trie the
    // cover claims to be the leaf set of. A node that is neither a cube nor an
    // interior node has no cube below it, so its whole subtree is uncovered —
    // and reporting *that* node rather than some full-depth descendant of it
    // names the largest hole rather than an arbitrary point inside it.
    let mut interior: BTreeSet<usize> = BTreeSet::new();
    for path in paths {
        for level in 0..path.len() {
            interior.insert(plan.prefix_code(&path[..level])?);
        }
    }

    // Walk the trie from the root. A node that is a cube stops the descent; a
    // node that is not must have every child present, recursively. An
    // iterative stack keeps the walk independent of the plan's depth.
    let mut reached: Vec<usize> = Vec::with_capacity(leaves.len());
    let mut stack: Vec<Vec<usize>> = vec![Vec::new()];
    while let Some(path) = stack.pop() {
        let code = plan.prefix_code(&path)?;
        if leaves.contains_key(&code) {
            reached.push(code);
            continue;
        }
        if !interior.contains(&code) {
            return Err(SearchError::MissingCell { index: code });
        }
        let Some(group) = plan.groups().get(path.len()) else {
            // Unreachable: a full-depth node cannot be a proper prefix of any
            // path, so it cannot be interior. Kept as a closed case rather than
            // an `expect`, because "unreachable" is a claim about code that
            // certifies results.
            return Err(SearchError::MissingCell { index: code });
        };
        for choice in 1..=group.arity() {
            let mut child = path.clone();
            child.push(choice);
            stack.push(child);
        }
    }

    // Every cube must have been reached. One that was not lies strictly inside
    // another cube, so its region is covered twice over.
    if reached.len() != leaves.len() {
        reached.sort_unstable();
        let buried = leaves
            .keys()
            .find(|code| reached.binary_search(code).is_err())
            .copied()
            .unwrap_or_default();
        return Err(SearchError::DuplicateCell { index: buried });
    }
    Ok(())
}

/// **All four cover obligations, for a tree cover.** Returns a certificate only
/// if every one holds.
///
/// The only differences from [`certify_cover`] are that obligation 3 is
/// discharged by [`verify_cube_cover`] rather than [`verify_cell_set`], and
/// that a row's `index` is checked against [`BranchPlan::prefix_code`] of its
/// own recorded choices rather than [`BranchPlan::index_of`].
///
/// Route A composition ([`crate::compose::compose_cover_proof`]) does **not**
/// apply to a tree cover: it is written for the flat product. A tree cover is
/// therefore route B only — per-cube checked proofs plus these four checked
/// obligations.
///
/// # Errors
///
/// As [`certify_cover`], plus [`SearchError::DuplicateCell`] for an overlapping
/// cube and [`SearchError::MissingCell`] for an uncovered subtree.
pub fn certify_tree_cover(
    formula: &CnfFormula,
    plan: &BranchPlan,
    records: &[CellRecord],
) -> Result<CoverCertificate, SearchError> {
    let branch_clauses = verify_branch_clauses(formula, plan)?;

    let mut paths = Vec::with_capacity(records.len());
    for record in records {
        let actual = plan.prefix_code(&record.choices)?;
        if actual != record.index {
            return Err(SearchError::CellChoicesMismatch {
                index: record.index,
                choices: record.choices.clone(),
                actual,
            });
        }
        paths.push(record.choices.clone());
    }
    verify_cube_cover(plan, &paths)?;

    let mut by_code: BTreeMap<usize, &CellRecord> = BTreeMap::new();
    for record in records {
        by_code.insert(record.index, record);
    }
    let mut steps = 0usize;
    let mut check_time = Duration::ZERO;
    for (&code, record) in &by_code {
        if record.verdict != CellVerdict::Unsat {
            return Err(SearchError::CellNotRefuted {
                index: code,
                verdict: record.verdict.as_str(),
            });
        }
        match &record.check {
            CellCheck::Passed => {}
            CellCheck::Deferred => return Err(SearchError::CellNotChecked { index: code }),
            CellCheck::Failed(reason) => {
                return Err(SearchError::CellCheckFailed {
                    index: code,
                    reason: reason.clone(),
                });
            }
        }
        steps += record.steps;
        check_time += record.check_time;
    }

    Ok(CoverCertificate {
        cells: records.len(),
        branch_clauses,
        steps,
        check_time,
    })
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
    /// Number of cover cells: the plan's product size for a flat cover
    /// ([`certify_cover`]), the number of leaf cubes for a tree cover
    /// ([`certify_tree_cover`]).
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
    fn prefix_codes_are_unique_across_levels_and_shape_independent() {
        let (_, plan) = plan_for(&[2, 3]);
        // 1 root + 3 + 9 = 13 nodes in the trie.
        assert_eq!(plan.node_count(), 13);
        let mut codes = Vec::new();
        for level in 0..=plan.depth() {
            for code in 0..plan.prefix_count(level) {
                let path = plan.prefix(level, code).expect("prefix");
                codes.push(plan.prefix_code(&path).expect("code"));
            }
        }
        let mut sorted = codes.clone();
        sorted.sort_unstable();
        sorted.dedup();
        assert_eq!(sorted.len(), codes.len(), "codes collide");
        assert_eq!(sorted, (0..plan.node_count()).collect::<Vec<_>>());
        // A cube's code does not depend on what else is in the cover.
        assert_eq!(plan.prefix_code(&[]).expect("root"), 0);
        assert_eq!(plan.prefix_code(&[1]).expect("code"), 1);
        assert_eq!(plan.prefix_code(&[3]).expect("code"), 3);
        assert_eq!(plan.prefix_code(&[1, 1]).expect("code"), 4);
        assert_eq!(plan.prefix_code(&[3, 3]).expect("code"), 12);
    }

    #[test]
    fn cube_literals_extend_the_parent_and_children_are_the_next_group() {
        let (_, plan) = plan_for(&[2, 3]);
        let parent = plan.cube(&[2]).expect("cube");
        assert_eq!(parent.depth(), 1);
        assert_eq!(parent.literals().len(), 1);
        let children = parent.child_paths(&plan);
        assert_eq!(children, vec![vec![2, 1], vec![2, 2], vec![2, 3]]);
        for child in &children {
            let cube = plan.cube(child).expect("cube");
            assert_eq!(&cube.literals()[..1], parent.literals());
            assert!(
                cube.child_paths(&plan).is_empty(),
                "full depth cannot split"
            );
        }
        assert!(plan.cube(&[1, 1, 1]).is_err(), "path longer than the plan");
        assert!(plan.cube(&[4]).is_err(), "choice outside the group arity");
    }

    #[test]
    fn cube_cover_agrees_with_flat_cell_set() {
        let (_, plan) = plan_for(&[2, 3]);
        let full: Vec<Vec<usize>> = plan
            .cells()
            .expect("cells")
            .iter()
            .map(|cell| cell.choices().to_vec())
            .collect();
        assert!(verify_cube_cover(&plan, &full).is_ok());
        let indices: Vec<usize> = (0..plan.cell_count()).collect();
        assert!(verify_cell_set(&plan, &indices).is_ok());
        // Drop the same cell from each and both reject.
        let mut holed = full.clone();
        let dropped = holed.pop().expect("cell");
        assert!(matches!(
            verify_cube_cover(&plan, &holed),
            Err(SearchError::MissingCell { index })
                if index == plan.prefix_code(&dropped).expect("code")
        ));
        assert!(matches!(
            verify_cell_set(&plan, &indices[..plan.cell_count() - 1]),
            Err(SearchError::MissingCell { .. })
        ));
    }

    #[test]
    fn a_mixed_depth_cover_is_accepted_exactly_when_it_is_complete() {
        let (_, plan) = plan_for(&[2, 3]);
        // Split only the c(2)=2 branch: a genuine adaptive cover.
        let good = vec![vec![1], vec![2, 1], vec![2, 2], vec![2, 3], vec![3]];
        assert!(verify_cube_cover(&plan, &good).is_ok());

        // SOUNDNESS-NEGATIVE: one child of the split branch missing. This is
        // exactly the shape an adaptive run that lost a cube would produce, and
        // it must never certify.
        let incomplete = vec![vec![1], vec![2, 1], vec![2, 3], vec![3]];
        assert!(matches!(
            verify_cube_cover(&plan, &incomplete),
            Err(SearchError::MissingCell { index })
                if index == plan.prefix_code(&[2, 2]).expect("code")
        ));

        // SOUNDNESS-NEGATIVE: a whole branch missing at the top level.
        let truncated = vec![vec![1], vec![2, 1], vec![2, 2], vec![2, 3]];
        assert!(matches!(
            verify_cube_cover(&plan, &truncated),
            Err(SearchError::MissingCell { index })
                if index == plan.prefix_code(&[3]).expect("code")
        ));

        // An empty cover covers nothing.
        assert!(matches!(
            verify_cube_cover(&plan, &[]),
            Err(SearchError::MissingCell { .. })
        ));
    }

    #[test]
    fn overlapping_and_repeated_cubes_are_rejected() {
        let (_, plan) = plan_for(&[2, 3]);
        // A cube strictly inside another: c(2)=2 and c(2)=2,c(3)=1 both present.
        let overlapping = vec![vec![1], vec![2], vec![2, 1], vec![3]];
        assert!(matches!(
            verify_cube_cover(&plan, &overlapping),
            Err(SearchError::DuplicateCell { index })
                if index == plan.prefix_code(&[2, 1]).expect("code")
        ));
        // A literally repeated cube.
        let repeated = vec![vec![1], vec![2], vec![3], vec![3]];
        assert!(matches!(
            verify_cube_cover(&plan, &repeated),
            Err(SearchError::DuplicateCell { index })
                if index == plan.prefix_code(&[3]).expect("code")
        ));
        // A malformed path is refused rather than silently ignored.
        assert!(verify_cube_cover(&plan, &[vec![9]]).is_err());
        assert!(verify_cube_cover(&plan, &[vec![1, 1, 1]]).is_err());
    }

    #[test]
    fn the_root_cube_alone_is_a_complete_cover() {
        // Depth 0 is the degenerate cover: refute F itself, no branching. It is
        // sound, and the checker has to say so rather than fall over.
        let (_, plan) = plan_for(&[2, 3]);
        assert!(verify_cube_cover(&plan, &[Vec::new()]).is_ok());
        assert!(
            plan.literals_for_prefix(&[]).expect("root").is_empty(),
            "the root cube augments F with nothing"
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
            assert_eq!(
                CellVerdict::parse(verdict.as_str()).expect("verdict"),
                verdict
            );
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
