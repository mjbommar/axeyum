//! The cube-and-conquer harness: refute every cell of an exhaustive cover.
//!
//! [`run_cover`] splits a formula over a [`BranchPlan`], asserts each cell's
//! literals as unit clauses, and refutes the augmented formula with axeyum's
//! proof-producing CDCL core. Each cell's DRAT proof is checked immediately
//! (default: [`CheckMode::Backward`], ADR-0382), optionally written to disk for
//! offline certification, and optionally retained for route A composition.
//!
//! # Finding B1: a satisfiable cell must land on disk before anything else
//!
//! The scratch harness wrote its model in the exit path, after the worker pool
//! joined, and its workers kept claiming cells after one came back `sat`. Both
//! halves cost witnesses: a run stopped for any reason between the discovery and
//! the exit — a deadline, an operator, an OOM — lost the model entirely, and the
//! discovery itself was the rarest and most expensive event in the run.
//!
//! The satisfiable path here, in order:
//!
//! 1. **evaluate the model against the *original* formula.** A `sat` whose model
//!    does not satisfy `F` is [`SearchError::ModelDoesNotSatisfy`], a soundness
//!    alarm, not a witness;
//! 2. **write the model and `fsync` it**, inside the worker, before anything
//!    else observes the discovery;
//! 3. notify the observer through [`CoverObserver::on_model_persisted`] — at
//!    that point the bytes are already durable;
//! 4. record the cell in the ledger;
//! 5. set the stop flag, so no further cell is claimed by any worker.
//!
//! `tests/harness_defects.rs` pins all of it: the observer reads the file back
//! from disk *during* the callback, and with one worker no cell after the
//! satisfiable one is ever started.
//!
//! # Determinism
//!
//! Cells are independent, so the verdict and the returned records do not depend
//! on the worker count; [`CoverOutcome`] always carries records in cell-index
//! order. The live status file is a *monitoring* artifact and its row order
//! reflects completion order — use [`crate::ledger::render_ledger`] over the
//! returned records when a byte-stable ledger is wanted.

use std::fs::OpenOptions;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex};
use std::time::{Duration, Instant};

use axeyum_cnf::{
    CnfClause, CnfFormula, DratStep, ProofSolveOutcome, check_drat, check_drat_backward,
    solve_with_drat_proof_with_limits, write_drat,
};

use crate::SearchError;
use crate::cover::{
    BranchPlan, Cell, CellCheck, CellRecord, CellVerdict, CoverCertificate, Cube, certify_cover,
    certify_tree_cover, verify_branch_clauses, verify_cell_set,
};
use crate::ledger::{LedgerWriter, RunId};

/// Which DRAT checker verifies each cell's proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CheckMode {
    /// [`check_drat_backward`] — core-first, the one to use at scale
    /// (ADR-0382).
    #[default]
    Backward,
    /// [`check_drat`] — the small auditable reference checker (ADR-0011).
    Forward,
    /// Do not check inline. Proofs are still produced, and should be dumped and
    /// certified offline by [`crate::certify::certify_dumped_cover`]. Checking
    /// inline throttled one search from 4096 cells in 153 s to 42% in 5.5 h.
    Deferred,
}

/// How a cover run is configured.
#[derive(Debug, Clone)]
pub struct CoverOptions {
    /// Worker threads. Cells are independent, so this affects wall clock only.
    pub workers: usize,
    /// Per-cell conflict budget.
    pub cell_conflicts: usize,
    /// Per-cell wall-clock budget.
    pub cell_time: Option<Duration>,
    /// Whole-run wall-clock budget.
    pub total_time: Option<Duration>,
    /// Which checker to run on each cell's proof.
    pub check: CheckMode,
    /// Proofs longer than this are produced but not checked inline. The
    /// certification is then incomplete until an offline pass runs, and
    /// [`certify_cover`] will say so rather than let it pass.
    pub check_step_cap: usize,
    /// Retain each cell's proof in memory for route A composition.
    pub retain_proofs: bool,
    /// Give up on retention once this many clause additions have accumulated.
    pub compose_step_cap: usize,
    /// Directory to write per-cell proofs into.
    pub proof_dir: Option<PathBuf>,
    /// Filename prefix for per-cell proofs.
    pub proof_prefix: String,
    /// Where a satisfiable cell's model is persisted, immediately (finding B1).
    pub model_path: Option<PathBuf>,
    /// Where the live status ledger is written. Refuses to append (finding B2).
    pub ledger_path: Option<PathBuf>,
    /// Run id stamped on every ledger row.
    pub run: RunId,
}

impl Default for CoverOptions {
    fn default() -> Self {
        Self {
            workers: 1,
            cell_conflicts: usize::MAX,
            cell_time: None,
            total_time: None,
            check: CheckMode::Backward,
            check_step_cap: usize::MAX,
            retain_proofs: false,
            compose_step_cap: 8_000_000,
            proof_dir: None,
            proof_prefix: "cover".to_string(),
            model_path: None,
            ledger_path: None,
            run: RunId::default(),
        }
    }
}

/// Live view of a cover run.
///
/// Every method has a no-op default, so an implementation states only what it
/// cares about. Implementations are called from worker threads and must be
/// cheap.
pub trait CoverObserver: Sync {
    /// A worker claimed a cell.
    fn on_cell_started(&self, index: usize) {
        let _ = index;
    }

    /// A cell finished, with the row that went to the ledger.
    fn on_cell_finished(&self, record: &CellRecord) {
        let _ = record;
    }

    /// A satisfiable cell's model reached the filesystem, durably (finding B1).
    fn on_model_persisted(&self, cell: usize, path: &Path, model: &[bool]) {
        let (_, _, _) = (cell, path, model);
    }

    /// A note worth logging: route changes, alarms, caps being hit.
    fn on_note(&self, message: &str) {
        let _ = message;
    }
}

/// Observer that reports nothing.
#[derive(Debug, Clone, Copy, Default)]
pub struct SilentObserver;

impl CoverObserver for SilentObserver {}

/// Observer that prints notes and one line per finished cell to stdout.
#[derive(Debug, Clone, Copy, Default)]
pub struct PrintObserver;

impl CoverObserver for PrintObserver {
    fn on_cell_finished(&self, record: &CellRecord) {
        println!(
            "cell {index:6} [{choices}] {verdict} in {solve:.2}s | steps={steps} adds={adds} | \
             check={check} in {check_s:.2}s",
            index = record.index,
            choices = record
                .choices
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join(","),
            verdict = record.verdict.as_str(),
            solve = record.solve.as_secs_f64(),
            steps = record.steps,
            adds = record.adds,
            check = record.check.as_field(),
            check_s = record.check_time.as_secs_f64(),
        );
    }

    fn on_model_persisted(&self, cell: usize, path: &Path, model: &[bool]) {
        println!(
            "cell {cell} is SATISFIABLE; {} model values persisted to {}",
            model.len(),
            path.display()
        );
    }

    fn on_note(&self, message: &str) {
        println!("{message}");
    }
}

/// What a cover run established.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoverOutcome {
    /// Every cell was refuted.
    Refuted {
        /// Present only when every cover obligation held; see
        /// [`certify_cover`].
        certificate: Option<CoverCertificate>,
        /// Why the certificate is absent, when it is.
        certificate_gap: Option<String>,
        /// One record per cell, in cell-index order.
        records: Vec<CellRecord>,
        /// Route A composition, when retention was on and stayed affordable.
        composed: Option<Vec<DratStep>>,
        /// Wall-clock time of the run.
        wall: Duration,
    },
    /// A cell was satisfiable, so the whole instance is.
    Satisfiable {
        /// Index of the satisfiable cell.
        cell: usize,
        /// The model, in zero-based CNF variable order.
        model: Vec<bool>,
        /// Where the model was persisted, if a path was configured.
        model_path: Option<PathBuf>,
        /// Records for cells finished before the run stopped.
        records: Vec<CellRecord>,
        /// Wall-clock time of the run.
        wall: Duration,
    },
    /// Some cells hit their budget, so the cover proves nothing.
    Incomplete {
        /// Cells with no `unsat` record.
        unfinished: Vec<usize>,
        /// Records for cells that did finish.
        records: Vec<CellRecord>,
        /// Wall-clock time of the run.
        wall: Duration,
    },
}

impl CoverOutcome {
    /// The certificate, if the run produced one.
    pub fn certificate(&self) -> Option<&CoverCertificate> {
        match self {
            Self::Refuted { certificate, .. } => certificate.as_ref(),
            _ => None,
        }
    }

    /// The cell records, in cell-index order.
    pub fn records(&self) -> &[CellRecord] {
        match self {
            Self::Refuted { records, .. }
            | Self::Satisfiable { records, .. }
            | Self::Incomplete { records, .. } => records,
        }
    }
}

/// Path a cell's proof is written to.
pub fn cell_proof_path(dir: &Path, prefix: &str, index: usize) -> PathBuf {
    dir.join(format!("{prefix}.cell{index:06}.drat"))
}

/// Renders a model as signed DIMACS literals on one line.
pub fn render_model(values: &[bool]) -> String {
    let mut out = String::new();
    for (position, &value) in values.iter().enumerate() {
        if position > 0 {
            out.push(' ');
        }
        if !value {
            out.push('-');
        }
        out.push_str(&(position + 1).to_string());
    }
    out.push('\n');
    out
}

/// Parses a model written by [`render_model`].
///
/// # Errors
///
/// Returns [`SearchError::InvalidParameter`] for a token that is not a signed
/// variable, a zero, or a variable assigned twice inconsistently.
pub fn parse_model(text: &str) -> Result<Vec<bool>, SearchError> {
    let mut values: Vec<Option<bool>> = Vec::new();
    for token in text.split_whitespace() {
        let literal: i64 = token.parse().map_err(|_| SearchError::InvalidParameter {
            what: format!("model token {token:?} is not a literal"),
        })?;
        if literal == 0 {
            continue;
        }
        let index =
            usize::try_from(literal.abs() - 1).map_err(|_| SearchError::InvalidParameter {
                what: format!("model token {token:?} is out of range"),
            })?;
        if values.len() <= index {
            values.resize(index + 1, None);
        }
        let value = literal > 0;
        if values[index].is_some_and(|existing| existing != value) {
            return Err(SearchError::InvalidParameter {
                what: format!("model assigns variable {} both ways", index + 1),
            });
        }
        values[index] = Some(value);
    }
    values
        .into_iter()
        .enumerate()
        .map(|(index, value)| {
            value.ok_or_else(|| SearchError::InvalidParameter {
                what: format!("model does not assign variable {}", index + 1),
            })
        })
        .collect()
}

/// Writes `bytes` to `path` and flushes them to the filesystem before
/// returning.
fn write_durable(path: &Path, bytes: &[u8]) -> Result<(), SearchError> {
    let mut file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(path)
        .map_err(|error| SearchError::io(path, &error))?;
    file.write_all(bytes)
        .map_err(|error| SearchError::io(path, &error))?;
    file.flush()
        .map_err(|error| SearchError::io(path, &error))?;
    file.sync_all()
        .map_err(|error| SearchError::io(path, &error))
}

/// Runs an exhaustive cover of `formula` over `plan`.
///
/// # Errors
///
/// Returns [`SearchError::MissingAtLeastOneClause`] if the plan does not
/// actually partition the formula's assignments (checked *before* any solving),
/// [`SearchError::LedgerExists`] if the status ledger would be appended to,
/// [`SearchError::ModelDoesNotSatisfy`] if a cell reports `sat` with a model
/// that does not satisfy the original formula, and [`SearchError::Io`] for a
/// failed write.
pub fn run_cover(
    formula: &CnfFormula,
    plan: &BranchPlan,
    options: &CoverOptions,
    observer: &dyn CoverObserver,
) -> Result<CoverOutcome, SearchError> {
    let branch_clauses = verify_branch_clauses(formula, plan)?;
    let cells = plan.cells()?;
    verify_cell_set(plan, &cells.iter().map(Cell::index).collect::<Vec<_>>())?;
    observer.on_note(&format!(
        "cover: {} cells over {} branch groups; at-least-one clauses located in F at {branch_clauses:?}",
        cells.len(),
        plan.depth()
    ));
    if let Some(dir) = options.proof_dir.as_deref() {
        std::fs::create_dir_all(dir).map_err(|error| SearchError::io(dir, &error))?;
    }
    let ledger = match options.ledger_path.as_deref() {
        Some(path) => Some(LedgerWriter::create(path)?),
        None => None,
    };

    let run = CoverRun {
        formula,
        plan,
        options,
        observer,
        cells,
        next: AtomicUsize::new(0),
        stop: AtomicBool::new(false),
        records: Mutex::new(Vec::new()),
        proofs: Mutex::new(vec![None; plan.cell_count()]),
        retained_adds: AtomicUsize::new(0),
        retaining: AtomicBool::new(options.retain_proofs),
        sat: Mutex::new(None),
        ledger: Mutex::new(ledger),
        errors: Mutex::new(Vec::new()),
        deadline: options.total_time.map(|budget| Instant::now() + budget),
    };
    run.execute()
}

/// Runs the configured checker on one refuted region's proof.
///
/// Shared by the flat cover and the adaptive cover so the two cannot drift on
/// what "checked" means: over the step cap, or [`CheckMode::Deferred`], is
/// [`CellCheck::Deferred`] and certifies nothing until
/// [`crate::certify::certify_dumped_cover`] finishes the job.
fn check_cell_proof(
    options: &CoverOptions,
    augmented: &CnfFormula,
    proof: &[DratStep],
) -> CellCheck {
    if proof.len() > options.check_step_cap {
        return CellCheck::Deferred;
    }
    let verdict = match options.check {
        CheckMode::Backward => check_drat_backward(augmented, proof),
        CheckMode::Forward => check_drat(augmented, proof),
        CheckMode::Deferred => return CellCheck::Deferred,
    };
    match verdict {
        Ok(true) => CellCheck::Passed,
        Ok(false) => CellCheck::Failed("no empty clause derived".to_string()),
        Err(error) => CellCheck::Failed(error.to_string()),
    }
}

/// Everything a finished cell contributes to its ledger row.
struct CellOutcome {
    verdict: CellVerdict,
    solve: Duration,
    steps: usize,
    adds: usize,
    check: CellCheck,
    check_time: Duration,
}

impl CellOutcome {
    /// A cell with no proof: satisfiable, or out of budget.
    fn unfinished(verdict: CellVerdict, solve: Duration) -> Self {
        Self {
            verdict,
            solve,
            steps: 0,
            adds: 0,
            check: CellCheck::Deferred,
            check_time: Duration::ZERO,
        }
    }
}

/// A satisfiable cell, as the worker that found it saw it.
struct SatFinding {
    cell: usize,
    model: Vec<bool>,
    path: Option<PathBuf>,
}

/// Shared state for one cover run.
struct CoverRun<'a> {
    formula: &'a CnfFormula,
    plan: &'a BranchPlan,
    options: &'a CoverOptions,
    observer: &'a dyn CoverObserver,
    cells: Vec<Cell>,
    next: AtomicUsize,
    stop: AtomicBool,
    records: Mutex<Vec<CellRecord>>,
    proofs: Mutex<Vec<Option<Vec<DratStep>>>>,
    retained_adds: AtomicUsize,
    retaining: AtomicBool,
    sat: Mutex<Option<SatFinding>>,
    ledger: Mutex<Option<LedgerWriter>>,
    errors: Mutex<Vec<SearchError>>,
    deadline: Option<Instant>,
}

impl CoverRun<'_> {
    /// Runs the worker pool and assembles the outcome.
    fn execute(self) -> Result<CoverOutcome, SearchError> {
        let started = Instant::now();
        std::thread::scope(|scope| {
            for _ in 0..self.options.workers.max(1) {
                scope.spawn(|| self.worker());
            }
        });
        let wall = started.elapsed();

        if let Some(error) = self.take_first_error() {
            return Err(error);
        }
        let mut records = self
            .records
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        records.sort_by_key(|record| record.index);

        if let Some(finding) = self
            .sat
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take()
        {
            return Ok(CoverOutcome::Satisfiable {
                cell: finding.cell,
                model: finding.model,
                model_path: finding.path,
                records,
                wall,
            });
        }

        let refuted: Vec<usize> = records
            .iter()
            .filter(|record| record.verdict == CellVerdict::Unsat)
            .map(|record| record.index)
            .collect();
        if refuted.len() != self.plan.cell_count() {
            let unfinished = (0..self.plan.cell_count())
                .filter(|index| !refuted.contains(index))
                .collect();
            return Ok(CoverOutcome::Incomplete {
                unfinished,
                records,
                wall,
            });
        }

        let composed = self.compose_if_retained()?;
        let (certificate, certificate_gap) = match certify_cover(self.formula, self.plan, &records)
        {
            Ok(certificate) => (Some(certificate), None),
            Err(error) => (None, Some(error.to_string())),
        };
        Ok(CoverOutcome::Refuted {
            certificate,
            certificate_gap,
            records,
            composed,
            wall,
        })
    }

    /// Route A, when every proof was retained.
    fn compose_if_retained(&self) -> Result<Option<Vec<DratStep>>, SearchError> {
        if !self.retaining.load(Ordering::SeqCst) {
            return Ok(None);
        }
        let proofs = self
            .proofs
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if proofs.iter().any(Option::is_none) {
            return Ok(None);
        }
        crate::compose::compose_cover_proof(self.formula, self.plan, &proofs).map(Some)
    }

    /// The first error a worker reported, if any.
    fn take_first_error(&self) -> Option<SearchError> {
        self.errors
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .first()
            .cloned()
    }

    /// Reports a fatal error and stops the run.
    fn fail(&self, error: SearchError) {
        self.observer.on_note(&format!("FATAL {error}"));
        self.errors
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push(error);
        self.stop.store(true, Ordering::SeqCst);
    }

    /// Claims and solves cells until the pool is told to stop.
    fn worker(&self) {
        loop {
            if self.stop.load(Ordering::SeqCst) {
                return;
            }
            let index = self.next.fetch_add(1, Ordering::SeqCst);
            if index >= self.cells.len() || self.stop.load(Ordering::SeqCst) {
                return;
            }
            if self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
            {
                return;
            }
            self.observer.on_cell_started(index);
            if let Err(error) = self.solve_cell(index) {
                self.fail(error);
                return;
            }
        }
    }

    /// Solves one cell and records what happened.
    fn solve_cell(&self, index: usize) -> Result<(), SearchError> {
        let cell = &self.cells[index];
        let mut augmented = self.formula.clone();
        for &lit in cell.literals() {
            augmented.add_clause(CnfClause::new(vec![lit]))?;
        }
        let deadline = match (self.options.cell_time, self.deadline) {
            (Some(budget), Some(total)) => Some((Instant::now() + budget).min(total)),
            (Some(budget), None) => Some(Instant::now() + budget),
            (None, total) => total,
        };
        let started = Instant::now();
        let outcome =
            solve_with_drat_proof_with_limits(&augmented, deadline, self.options.cell_conflicts);
        let solve = started.elapsed();

        match outcome {
            ProofSolveOutcome::Sat(assignment) => self.handle_sat(cell, assignment.values(), solve),
            ProofSolveOutcome::Unsat(proof) => self.handle_unsat(cell, &augmented, proof, solve),
            ProofSolveOutcome::ResourceOut => self.record(
                cell,
                CellOutcome::unfinished(CellVerdict::ResourceOut, solve),
            ),
            ProofSolveOutcome::Interrupted => {
                self.record(cell, CellOutcome::unfinished(CellVerdict::Timeout, solve))
            }
        }
    }

    /// **Finding B1.** Verify, persist, notify, record, stop — in that order.
    fn handle_sat(&self, cell: &Cell, model: &[bool], solve: Duration) -> Result<(), SearchError> {
        if !self.formula.evaluate(model).unwrap_or(false) {
            return Err(SearchError::ModelDoesNotSatisfy { cell: cell.index() });
        }
        let path = self.options.model_path.clone();
        if let Some(path) = path.as_deref() {
            write_durable(path, render_model(model).as_bytes())?;
            self.observer.on_model_persisted(cell.index(), path, model);
        }
        *self
            .sat
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(SatFinding {
            cell: cell.index(),
            model: model.to_vec(),
            path,
        });
        self.record(cell, CellOutcome::unfinished(CellVerdict::Sat, solve))?;
        self.observer.on_note(&format!(
            "cell {} is SATISFIABLE — the instance is satisfiable and the run stops here",
            cell.index()
        ));
        self.stop.store(true, Ordering::SeqCst);
        Ok(())
    }

    /// Checks, dumps, and optionally retains a refuted cell's proof.
    fn handle_unsat(
        &self,
        cell: &Cell,
        augmented: &CnfFormula,
        proof: Vec<DratStep>,
        solve: Duration,
    ) -> Result<(), SearchError> {
        let steps = proof.len();
        let adds = proof
            .iter()
            .filter(|step| matches!(step, DratStep::Add(_)))
            .count();
        let started = Instant::now();
        let check = self.check_proof(augmented, &proof);
        let check_time = started.elapsed();
        if let CellCheck::Failed(reason) = &check {
            self.observer.on_note(&format!(
                "SOUNDNESS ALARM: cell {} proof rejected: {reason}",
                cell.index()
            ));
        }
        if let Some(dir) = self.options.proof_dir.as_deref() {
            let path = cell_proof_path(dir, &self.options.proof_prefix, cell.index());
            write_durable(&path, write_drat(&proof).as_bytes())?;
        }
        self.retain(cell.index(), proof, adds);
        self.record(
            cell,
            CellOutcome {
                verdict: CellVerdict::Unsat,
                solve,
                steps,
                adds,
                check,
                check_time,
            },
        )
    }

    /// Runs the configured checker on a cell's proof.
    fn check_proof(&self, augmented: &CnfFormula, proof: &[DratStep]) -> CellCheck {
        check_cell_proof(self.options, augmented, proof)
    }

    /// Keeps a proof for route A while retention is still affordable.
    fn retain(&self, index: usize, proof: Vec<DratStep>, adds: usize) {
        if !self.retaining.load(Ordering::SeqCst) {
            return;
        }
        let running = self.retained_adds.fetch_add(adds, Ordering::SeqCst) + adds;
        let mut proofs = self
            .proofs
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if running <= self.options.compose_step_cap {
            proofs[index] = Some(proof);
            return;
        }
        self.retaining.store(false, Ordering::SeqCst);
        for slot in proofs.iter_mut() {
            *slot = None;
        }
        self.observer.on_note(&format!(
            "route A abandoned: {running} retained clause additions exceed the compose cap {}; \
             falling back to route B (per-cell checked proofs plus a checked cover)",
            self.options.compose_step_cap
        ));
    }

    /// Appends a finished cell to the ledger and the in-memory table.
    fn record(&self, cell: &Cell, outcome: CellOutcome) -> Result<(), SearchError> {
        let record = CellRecord {
            run: self.options.run.clone(),
            index: cell.index(),
            choices: cell.choices().to_vec(),
            verdict: outcome.verdict,
            solve: outcome.solve,
            steps: outcome.steps,
            adds: outcome.adds,
            check: outcome.check,
            check_time: outcome.check_time,
        };
        if let Some(writer) = self
            .ledger
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .as_mut()
        {
            writer.append(&record)?;
        }
        self.observer.on_cell_finished(&record);
        self.records
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push(record);
        Ok(())
    }
}

/// How an adaptive cover splits, and where it resumes from.
///
/// The plan's own depth is the maximum depth: a cube that exhausts its budget
/// at full depth cannot be split further and is reported as *stuck* instead.
/// Give the plan more branch groups to allow deeper splitting.
#[derive(Debug, Clone)]
pub struct AdaptiveOptions {
    /// Depth of the initial frontier, when `seed_cubes` is `None`.
    pub initial_depth: usize,
    /// Conflict budget for a cube at the plan's full depth, where splitting is
    /// no longer possible. Cubes above it use
    /// [`CoverOptions::cell_conflicts`].
    pub final_conflicts: usize,
    /// Resume from these cubes instead of a uniform frontier. This is how a
    /// run continues another run's `pending` file: cube codes are
    /// shape-independent ([`BranchPlan::prefix_code`]), so the ledgers of the
    /// two runs concatenate and certify as one cover.
    pub seed_cubes: Option<Vec<Vec<usize>>>,
    /// Where the cubes that were never refuted are written when the run stops.
    /// Written whatever the outcome, so a stopped run always says exactly where
    /// it stopped.
    pub pending_path: Option<PathBuf>,
}

impl Default for AdaptiveOptions {
    fn default() -> Self {
        Self {
            initial_depth: 1,
            final_conflicts: usize::MAX,
            seed_cubes: None,
            pending_path: None,
        }
    }
}

/// Why a cube is in the pending set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PendingReason {
    /// Queued but never claimed — the run stopped first.
    Unstarted,
    /// Claimed, exhausted its conflict budget, and could not be split because
    /// it is already at the plan's full depth.
    StuckResourceOut,
    /// Claimed, ran out of wall clock, and is at the plan's full depth.
    StuckTimeout,
}

impl PendingReason {
    /// The token used in the pending file.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Unstarted => "unstarted",
            Self::StuckResourceOut => "stuck-resource-out",
            Self::StuckTimeout => "stuck-timeout",
        }
    }
}

/// One cube that the run did not refute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PendingCube {
    /// Shape-independent cube code; see [`BranchPlan::prefix_code`].
    pub code: usize,
    /// The cube's choices, shortest-first.
    pub path: Vec<usize>,
    /// Why it is pending.
    pub reason: PendingReason,
}

/// Header of the pending file this module writes and reads.
pub const PENDING_HEADER: &str = "code\tpath\treason";

/// Renders a pending set, header included.
pub fn render_pending(cubes: &[PendingCube]) -> String {
    let mut out = String::from(PENDING_HEADER);
    out.push('\n');
    for cube in cubes {
        let path: Vec<String> = cube.path.iter().map(usize::to_string).collect();
        out.push_str(&cube.code.to_string());
        out.push('\t');
        out.push_str(&path.join(","));
        out.push('\t');
        out.push_str(cube.reason.as_str());
        out.push('\n');
    }
    out
}

/// Parses a pending file back into cube paths, for a resuming run.
///
/// The `code` column is **re-derived** from the path through the plan and
/// compared, so a hand-edited or truncated file fails closed rather than
/// resuming on a cube nobody meant.
///
/// # Errors
///
/// Returns [`SearchError::LedgerHeader`] for a foreign header and
/// [`SearchError::LedgerRow`] for a malformed row or a code that does not match
/// its own path.
pub fn parse_pending(plan: &BranchPlan, text: &str) -> Result<Vec<PendingCube>, SearchError> {
    let mut lines = text.lines().enumerate();
    let Some((_, header)) = lines.next() else {
        return Err(SearchError::LedgerHeader {
            found: String::new(),
        });
    };
    if header.trim_end() != PENDING_HEADER {
        return Err(SearchError::LedgerHeader {
            found: header.to_string(),
        });
    }
    let mut cubes = Vec::new();
    for (position, line) in lines {
        if line.trim().is_empty() {
            continue;
        }
        let number = position + 1;
        let row = |message: String| SearchError::LedgerRow {
            line: number,
            message,
        };
        let fields: Vec<&str> = line.trim_end().split('\t').collect();
        if fields.len() != 3 {
            return Err(row(format!("{} fields, want 3", fields.len())));
        }
        let code: usize = fields[0]
            .parse()
            .map_err(|_| row(format!("code {:?} is not a number", fields[0])))?;
        let path = if fields[1].is_empty() {
            Vec::new()
        } else {
            fields[1]
                .split(',')
                .map(|token| {
                    token
                        .parse::<usize>()
                        .map_err(|_| row(format!("choice {token:?} is not a number")))
                })
                .collect::<Result<Vec<_>, _>>()?
        };
        let actual = plan.prefix_code(&path)?;
        if actual != code {
            return Err(row(format!(
                "code {code} does not match path {path:?}, which is cube {actual}"
            )));
        }
        let reason = match fields[2] {
            "unstarted" => PendingReason::Unstarted,
            "stuck-resource-out" => PendingReason::StuckResourceOut,
            "stuck-timeout" => PendingReason::StuckTimeout,
            other => return Err(row(format!("unknown reason {other:?}"))),
        };
        cubes.push(PendingCube { code, path, reason });
    }
    Ok(cubes)
}

/// What an adaptive cover run established.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AdaptiveOutcome {
    /// Every cube of a complete tree cover was refuted.
    Refuted {
        /// Present only when every cover obligation held; see
        /// [`certify_tree_cover`].
        certificate: Option<CoverCertificate>,
        /// Why the certificate is absent, when it is.
        certificate_gap: Option<String>,
        /// One record per leaf cube, in cube-code order.
        records: Vec<CellRecord>,
        /// How many cubes were split rather than refuted.
        splits: usize,
        /// Wall-clock time of the run.
        wall: Duration,
    },
    /// A cube was satisfiable, so the whole instance is.
    Satisfiable {
        /// The satisfiable cube's path.
        path: Vec<usize>,
        /// The model, in zero-based CNF variable order.
        model: Vec<bool>,
        /// Where the model was persisted, if a path was configured.
        model_path: Option<PathBuf>,
        /// Records for cubes finished before the run stopped.
        records: Vec<CellRecord>,
        /// Wall-clock time of the run.
        wall: Duration,
    },
    /// The run stopped with cubes still open, so the cover proves nothing yet.
    Incomplete {
        /// Every cube that was not refuted, with why. Feeding these back as
        /// [`AdaptiveOptions::seed_cubes`] resumes exactly where this run
        /// stopped.
        pending: Vec<PendingCube>,
        /// Records for the cubes that were refuted.
        records: Vec<CellRecord>,
        /// How many cubes were split rather than refuted.
        splits: usize,
        /// Wall-clock time of the run.
        wall: Duration,
    },
}

impl AdaptiveOutcome {
    /// The certificate, if the run produced one.
    pub fn certificate(&self) -> Option<&CoverCertificate> {
        match self {
            Self::Refuted { certificate, .. } => certificate.as_ref(),
            _ => None,
        }
    }

    /// The cube records.
    pub fn records(&self) -> &[CellRecord] {
        match self {
            Self::Refuted { records, .. }
            | Self::Satisfiable { records, .. }
            | Self::Incomplete { records, .. } => records,
        }
    }
}

/// Runs an **adaptive** cover: a cube that exhausts its conflict budget is
/// split on the next branch group and its children queued, instead of being
/// abandoned or given a bigger budget.
///
/// The measured motivation (`F_741`, `R_4(5(x-y)=4z)`, 2026-08-12): a flat
/// depth-6 cover left 1132 of 1946 finished cells resource-out at 200k
/// conflicts each while 746 fell to unit propagation instantly. The work is
/// concentrated in a small part of the tree, so uniform deepening multiplies
/// the easy cells for nothing and a uniform budget raise pays the hard cells'
/// worst case everywhere.
///
/// The cover this produces is a **tree**, not the flat product, so obligation 3
/// is discharged by [`crate::cover::verify_cube_cover`] and the certificate by
/// [`certify_tree_cover`]. Route A composition is not available for a tree
/// cover (see [`certify_tree_cover`]), so [`CoverOptions::retain_proofs`] is
/// ignored here.
///
/// Ledger rows are written **only for refuted cubes** — plus the satisfiable
/// one, which ends the run and the question. A cube that is split or stuck goes
/// to the pending set instead. That keeps a resumed run's ledger concatenable
/// with its predecessor's: a row for a cube that a later run refutes would
/// otherwise be a duplicate cell and reject the whole cover.
///
/// # Errors
///
/// As [`run_cover`], plus [`SearchError::InvalidParameter`] if
/// `initial_depth` exceeds the plan's depth.
pub fn run_adaptive_cover(
    formula: &CnfFormula,
    plan: &BranchPlan,
    options: &CoverOptions,
    adaptive: &AdaptiveOptions,
    observer: &dyn CoverObserver,
) -> Result<AdaptiveOutcome, SearchError> {
    let branch_clauses = verify_branch_clauses(formula, plan)?;
    let seeds: Vec<Vec<usize>> = if let Some(cubes) = &adaptive.seed_cubes {
        if cubes.is_empty() {
            return Err(SearchError::InvalidParameter {
                what: "adaptive cover seeded with no cubes".to_string(),
            });
        }
        cubes.clone()
    } else {
        if adaptive.initial_depth > plan.depth() {
            return Err(SearchError::InvalidParameter {
                what: format!(
                    "initial depth {} exceeds the plan's depth {}",
                    adaptive.initial_depth,
                    plan.depth()
                ),
            });
        }
        plan.cubes_at_level(adaptive.initial_depth)?
            .into_iter()
            .map(|cube| cube.path().to_vec())
            .collect()
    };
    // The seed set must itself be a complete cover, or no amount of refuting
    // proves anything. A resumed run's seeds plus the earlier runs' refuted
    // cubes are checked as one set by `certify_tree_cover` at the end; this
    // check is the cheap local one that catches a mangled seed list up front.
    for path in &seeds {
        plan.prefix_code(path)?;
    }
    observer.on_note(&format!(
        "adaptive cover: {} seed cubes, max depth {} ({} groups); \
         at-least-one clauses located in F at {branch_clauses:?}",
        seeds.len(),
        plan.depth(),
        plan.depth()
    ));
    if let Some(dir) = options.proof_dir.as_deref() {
        std::fs::create_dir_all(dir).map_err(|error| SearchError::io(dir, &error))?;
    }
    let ledger = match options.ledger_path.as_deref() {
        Some(path) => Some(LedgerWriter::create(path)?),
        None => None,
    };
    let mut queue: Vec<Vec<usize>> = seeds;
    queue.reverse(); // popped from the back, so cubes are claimed in code order

    let run = AdaptiveRun {
        formula,
        plan,
        options,
        adaptive,
        observer,
        queue: Mutex::new(QueueState {
            pending: queue,
            in_flight: 0,
            stop: false,
        }),
        ready: Condvar::new(),
        records: Mutex::new(Vec::new()),
        stuck: Mutex::new(Vec::new()),
        splits: AtomicUsize::new(0),
        sat: Mutex::new(None),
        ledger: Mutex::new(ledger),
        errors: Mutex::new(Vec::new()),
        deadline: options.total_time.map(|budget| Instant::now() + budget),
    };
    run.execute()
}

/// The shared work queue of an adaptive run.
struct QueueState {
    pending: Vec<Vec<usize>>,
    in_flight: usize,
    stop: bool,
}

/// A satisfiable cube, as the worker that found it saw it.
struct AdaptiveSatFinding {
    path: Vec<usize>,
    model: Vec<bool>,
    file: Option<PathBuf>,
}

/// Shared state for one adaptive run.
struct AdaptiveRun<'a> {
    formula: &'a CnfFormula,
    plan: &'a BranchPlan,
    options: &'a CoverOptions,
    adaptive: &'a AdaptiveOptions,
    observer: &'a dyn CoverObserver,
    queue: Mutex<QueueState>,
    ready: Condvar,
    records: Mutex<Vec<CellRecord>>,
    stuck: Mutex<Vec<PendingCube>>,
    splits: AtomicUsize,
    sat: Mutex<Option<AdaptiveSatFinding>>,
    ledger: Mutex<Option<LedgerWriter>>,
    errors: Mutex<Vec<SearchError>>,
    deadline: Option<Instant>,
}

impl AdaptiveRun<'_> {
    /// Runs the worker pool and assembles the outcome.
    fn execute(self) -> Result<AdaptiveOutcome, SearchError> {
        let started = Instant::now();
        std::thread::scope(|scope| {
            for _ in 0..self.options.workers.max(1) {
                scope.spawn(|| self.worker());
            }
        });
        let wall = started.elapsed();

        if let Some(error) = self.take_first_error() {
            self.write_pending(&self.collect_pending())?;
            return Err(error);
        }
        let mut records = self
            .records
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        records.sort_by_key(|record| record.index);
        let splits = self.splits.load(Ordering::SeqCst);
        let pending = self.collect_pending();
        self.write_pending(&pending)?;

        if let Some(finding) = self
            .sat
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .take()
        {
            return Ok(AdaptiveOutcome::Satisfiable {
                path: finding.path,
                model: finding.model,
                model_path: finding.file,
                records,
                wall,
            });
        }
        if !pending.is_empty() {
            return Ok(AdaptiveOutcome::Incomplete {
                pending,
                records,
                splits,
                wall,
            });
        }
        let (certificate, certificate_gap) =
            match certify_tree_cover(self.formula, self.plan, &records) {
                Ok(certificate) => (Some(certificate), None),
                Err(error) => (None, Some(error.to_string())),
            };
        Ok(AdaptiveOutcome::Refuted {
            certificate,
            certificate_gap,
            records,
            splits,
            wall,
        })
    }

    /// Every cube that was not refuted: the queue remainder plus the stuck set.
    fn collect_pending(&self) -> Vec<PendingCube> {
        let mut pending = self
            .stuck
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .clone();
        let queue = self
            .queue
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        for path in &queue.pending {
            let code = self.plan.prefix_code(path).unwrap_or_default();
            pending.push(PendingCube {
                code,
                path: path.clone(),
                reason: PendingReason::Unstarted,
            });
        }
        pending.sort_by_key(|cube| cube.code);
        pending.dedup_by(|left, right| left.code == right.code);
        pending
    }

    /// Writes the pending set where a resuming run can find it.
    fn write_pending(&self, pending: &[PendingCube]) -> Result<(), SearchError> {
        match self.adaptive.pending_path.as_deref() {
            None => Ok(()),
            Some(path) => write_durable(path, render_pending(pending).as_bytes()),
        }
    }

    /// The first error a worker reported, if any.
    fn take_first_error(&self) -> Option<SearchError> {
        self.errors
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .first()
            .cloned()
    }

    /// Reports a fatal error and stops the run.
    fn fail(&self, error: SearchError) {
        self.observer.on_note(&format!("FATAL {error}"));
        self.errors
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push(error);
        self.halt();
    }

    /// Stops every worker as soon as it next looks.
    fn halt(&self) {
        self.queue
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .stop = true;
        self.ready.notify_all();
    }

    /// Claims the next cube, or `None` when the run is over.
    ///
    /// A worker that finds the queue empty waits: another worker may still be
    /// solving a cube that splits into more work. The run ends when the queue
    /// is empty *and* nothing is in flight.
    fn claim(&self) -> Option<Vec<usize>> {
        let mut queue = self
            .queue
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        loop {
            if queue.stop {
                return None;
            }
            if self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
            {
                queue.stop = true;
                self.ready.notify_all();
                return None;
            }
            if let Some(path) = queue.pending.pop() {
                queue.in_flight += 1;
                return Some(path);
            }
            if queue.in_flight == 0 {
                queue.stop = true;
                self.ready.notify_all();
                return None;
            }
            let (guard, _) = self
                .ready
                .wait_timeout(queue, Duration::from_millis(50))
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            queue = guard;
        }
    }

    /// Releases a claim, queueing `children` (possibly none) behind it.
    fn release(&self, children: Vec<Vec<usize>>) {
        let mut queue = self
            .queue
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        queue.in_flight -= 1;
        for child in children.into_iter().rev() {
            queue.pending.push(child);
        }
        drop(queue);
        self.ready.notify_all();
    }

    /// Claims and solves cubes until the queue drains or the run stops.
    fn worker(&self) {
        while let Some(path) = self.claim() {
            match self.solve_cube(&path) {
                Ok(children) => self.release(children),
                Err(error) => {
                    self.release(Vec::new());
                    self.fail(error);
                    return;
                }
            }
        }
    }

    /// Solves one cube; returns the children to queue if it has to be split.
    fn solve_cube(&self, path: &[usize]) -> Result<Vec<Vec<usize>>, SearchError> {
        let cube = self.plan.cube(path)?;
        let splittable = cube.depth() < self.plan.depth();
        let mut augmented = self.formula.clone();
        for &lit in cube.literals() {
            augmented.add_clause(CnfClause::new(vec![lit]))?;
        }
        let budget = if splittable {
            self.options.cell_conflicts
        } else {
            self.adaptive.final_conflicts
        };
        let deadline = match (self.options.cell_time, self.deadline) {
            (Some(budget), Some(total)) => Some((Instant::now() + budget).min(total)),
            (Some(budget), None) => Some(Instant::now() + budget),
            (None, total) => total,
        };
        self.observer.on_cell_started(cube.code());
        let started = Instant::now();
        let outcome = solve_with_drat_proof_with_limits(&augmented, deadline, budget);
        let solve = started.elapsed();

        match outcome {
            ProofSolveOutcome::Sat(assignment) => {
                self.handle_sat(&cube, assignment.values(), solve)?;
                Ok(Vec::new())
            }
            ProofSolveOutcome::Unsat(proof) => {
                self.handle_unsat(&cube, &augmented, &proof, solve)?;
                Ok(Vec::new())
            }
            ProofSolveOutcome::ResourceOut | ProofSolveOutcome::Interrupted => {
                let timed_out = matches!(outcome, ProofSolveOutcome::Interrupted);
                if splittable && !timed_out {
                    let children = cube.child_paths(self.plan);
                    self.splits.fetch_add(1, Ordering::SeqCst);
                    self.observer.on_note(&format!(
                        "split cube {} [{}] after {:.1}s at {budget} conflicts into {} children",
                        cube.code(),
                        cube.label(self.plan),
                        solve.as_secs_f64(),
                        children.len()
                    ));
                    return Ok(children);
                }
                // A wall-clock stop is not evidence that the cube is hard, so
                // splitting on it would corrupt the census: park it as-is.
                self.stuck
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner)
                    .push(PendingCube {
                        code: cube.code(),
                        path: cube.path().to_vec(),
                        reason: if timed_out {
                            PendingReason::StuckTimeout
                        } else {
                            PendingReason::StuckResourceOut
                        },
                    });
                Ok(Vec::new())
            }
        }
    }

    /// **Finding B1.** Verify, persist, notify, record, stop — in that order.
    fn handle_sat(&self, cube: &Cube, model: &[bool], solve: Duration) -> Result<(), SearchError> {
        if !self.formula.evaluate(model).unwrap_or(false) {
            return Err(SearchError::ModelDoesNotSatisfy { cell: cube.code() });
        }
        let file = self.options.model_path.clone();
        if let Some(path) = file.as_deref() {
            write_durable(path, render_model(model).as_bytes())?;
            self.observer.on_model_persisted(cube.code(), path, model);
        }
        *self
            .sat
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner) = Some(AdaptiveSatFinding {
            path: cube.path().to_vec(),
            model: model.to_vec(),
            file,
        });
        self.record(cube, CellOutcome::unfinished(CellVerdict::Sat, solve))?;
        self.observer.on_note(&format!(
            "cube {} is SATISFIABLE — the instance is satisfiable and the run stops here",
            cube.code()
        ));
        self.halt();
        Ok(())
    }

    /// Checks and dumps a refuted cube's proof.
    fn handle_unsat(
        &self,
        cube: &Cube,
        augmented: &CnfFormula,
        proof: &[DratStep],
        solve: Duration,
    ) -> Result<(), SearchError> {
        let steps = proof.len();
        let adds = proof
            .iter()
            .filter(|step| matches!(step, DratStep::Add(_)))
            .count();
        let started = Instant::now();
        let check = check_cell_proof(self.options, augmented, proof);
        let check_time = started.elapsed();
        if let CellCheck::Failed(reason) = &check {
            self.observer.on_note(&format!(
                "SOUNDNESS ALARM: cube {} proof rejected: {reason}",
                cube.code()
            ));
        }
        if let Some(dir) = self.options.proof_dir.as_deref() {
            let path = cell_proof_path(dir, &self.options.proof_prefix, cube.code());
            write_durable(&path, write_drat(proof).as_bytes())?;
        }
        self.record(
            cube,
            CellOutcome {
                verdict: CellVerdict::Unsat,
                solve,
                steps,
                adds,
                check,
                check_time,
            },
        )
    }

    /// Appends a refuted cube to the ledger and the in-memory table.
    fn record(&self, cube: &Cube, outcome: CellOutcome) -> Result<(), SearchError> {
        let record = CellRecord {
            run: self.options.run.clone(),
            index: cube.code(),
            choices: cube.path().to_vec(),
            verdict: outcome.verdict,
            solve: outcome.solve,
            steps: outcome.steps,
            adds: outcome.adds,
            check: outcome.check,
            check_time: outcome.check_time,
        };
        if let Some(writer) = self
            .ledger
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .as_mut()
        {
            writer.append(&record)?;
        }
        self.observer.on_cell_finished(&record);
        self.records
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push(record);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cover::colour_branch_plan;
    use crate::family::{ColouringFamily, Schur};

    #[test]
    fn model_text_round_trips() {
        let values = vec![true, false, true, true];
        assert_eq!(render_model(&values), "1 -2 3 4\n");
        assert_eq!(parse_model("1 -2 3 4").expect("parse"), values);
    }

    #[test]
    fn parse_model_rejects_gaps_and_contradictions() {
        assert!(parse_model("1 3").is_err());
        assert!(parse_model("1 -1").is_err());
        assert!(parse_model("x").is_err());
    }

    #[test]
    fn schur_five_is_refuted_with_a_certificate() {
        let family = Schur::new(2).expect("family");
        let problem = family.problem(5).expect("problem");
        let formula = problem.encode().expect("encode");
        let plan = colour_branch_plan(&problem, &[2, 3]).expect("plan");
        let outcome =
            run_cover(&formula, &plan, &CoverOptions::default(), &SilentObserver).expect("run");
        let certificate = outcome.certificate().expect("certificate");
        assert_eq!(certificate.cells, 4);
        assert_eq!(outcome.records().len(), 4);
    }

    #[test]
    fn adaptive_cover_refutes_schur_five_and_certifies_a_tree_cover() {
        let family = Schur::new(2).expect("family");
        let problem = family.problem(5).expect("problem");
        let formula = problem.encode().expect("encode");
        let plan = colour_branch_plan(&problem, &[2, 3, 4]).expect("plan");
        let adaptive = AdaptiveOptions {
            initial_depth: 1,
            ..AdaptiveOptions::default()
        };
        let outcome = run_adaptive_cover(
            &formula,
            &plan,
            &CoverOptions::default(),
            &adaptive,
            &SilentObserver,
        )
        .expect("run");
        let AdaptiveOutcome::Refuted {
            certificate,
            certificate_gap,
            records,
            ..
        } = &outcome
        else {
            panic!("expected a refutation, got {outcome:?}");
        };
        assert_eq!(certificate_gap.as_deref(), None);
        let certificate = certificate.as_ref().expect("certificate");
        // Nothing needed splitting at this size, so the cover is the depth-1
        // frontier itself: two cubes, not the depth-3 product's eight cells.
        assert_eq!(certificate.cells, 2);
        assert_eq!(records.len(), 2);
        assert!(certificate.steps > 0, "a certified cover has proof steps");
        for record in records {
            assert_eq!(record.choices.len(), 1);
            assert_eq!(
                record.index,
                plan.prefix_code(&record.choices).expect("code"),
                "row index must be the cube's own code"
            );
        }
    }

    #[test]
    fn a_starved_budget_splits_instead_of_giving_up() {
        // S(3) = 14, so [1, 14] has no sum-free 3-colouring but refuting it
        // takes real conflicts. Starving the per-cube budget therefore forces
        // the run to buy its progress by splitting.
        let family = Schur::new(3).expect("family");
        let problem = family.problem(14).expect("problem");
        let formula = problem.encode().expect("encode");
        let plan = colour_branch_plan(&problem, &[2, 3, 4, 5]).expect("plan");
        let options = CoverOptions {
            cell_conflicts: 1,
            workers: 3,
            ..CoverOptions::default()
        };
        let outcome = run_adaptive_cover(
            &formula,
            &plan,
            &options,
            &AdaptiveOptions {
                initial_depth: 1,
                final_conflicts: usize::MAX,
                ..AdaptiveOptions::default()
            },
            &SilentObserver,
        )
        .expect("run");
        let AdaptiveOutcome::Refuted {
            certificate,
            records,
            splits,
            ..
        } = &outcome
        else {
            panic!("expected a refutation, got {outcome:?}");
        };
        assert!(*splits > 0, "starving the budget must force splits");
        let certificate = certificate.as_ref().expect("certificate");
        assert_eq!(certificate.cells, records.len());
        // Whatever shape it reached, the union is a complete cover.
        let paths: Vec<Vec<usize>> = records.iter().map(|r| r.choices.clone()).collect();
        crate::cover::verify_cube_cover(&plan, &paths).expect("complete tree cover");
    }

    #[test]
    fn an_incomplete_adaptive_run_reports_where_it_stopped_and_certifies_nothing() {
        // SOUNDNESS-NEGATIVE: a run that cannot finish must not produce a
        // certificate, and the cubes it left open must survive as a resumable
        // pending set rather than being silently dropped.
        let family = Schur::new(3).expect("family");
        let problem = family.problem(14).expect("problem");
        let formula = problem.encode().expect("encode");
        let plan = colour_branch_plan(&problem, &[2, 3]).expect("plan");
        let options = CoverOptions {
            cell_conflicts: 1,
            ..CoverOptions::default()
        };
        let outcome = run_adaptive_cover(
            &formula,
            &plan,
            &options,
            &AdaptiveOptions {
                initial_depth: 2,
                final_conflicts: 1, // no budget at full depth: nothing can finish
                ..AdaptiveOptions::default()
            },
            &SilentObserver,
        )
        .expect("run");
        let AdaptiveOutcome::Incomplete {
            pending, records, ..
        } = &outcome
        else {
            panic!("expected an incomplete run, got {outcome:?}");
        };
        assert!(outcome.certificate().is_none());
        assert!(!pending.is_empty(), "the open cubes must be reported");
        assert_eq!(
            pending.len() + records.len(),
            plan.cell_count(),
            "every seeded cube is either refuted or pending; none may vanish"
        );
        assert!(
            pending
                .iter()
                .all(|cube| cube.reason == PendingReason::StuckResourceOut)
        );
        // The pending set round-trips, so the next run resumes exactly here.
        let text = render_pending(pending);
        let parsed = parse_pending(&plan, &text).expect("parse pending");
        assert_eq!(&parsed, pending);
    }

    #[test]
    fn a_pending_row_whose_code_contradicts_its_path_is_refused() {
        let family = Schur::new(2).expect("family");
        let problem = family.problem(5).expect("problem");
        let plan = colour_branch_plan(&problem, &[2, 3]).expect("plan");
        let good = render_pending(&[PendingCube {
            code: plan.prefix_code(&[1, 2]).expect("code"),
            path: vec![1, 2],
            reason: PendingReason::Unstarted,
        }]);
        assert_eq!(parse_pending(&plan, &good).expect("parse").len(), 1);
        let forged = good.replace(
            &plan.prefix_code(&[1, 2]).expect("code").to_string(),
            &plan.prefix_code(&[2, 1]).expect("code").to_string(),
        );
        assert!(matches!(
            parse_pending(&plan, &forged),
            Err(SearchError::LedgerRow { .. })
        ));
        assert!(matches!(
            parse_pending(&plan, "code\tpath\n"),
            Err(SearchError::LedgerHeader { .. })
        ));
    }

    #[test]
    fn an_adaptive_run_finds_the_satisfiable_side() {
        // S(2) = 5, so [1, 4] has a sum-free 2-colouring and the adaptive run
        // must report it rather than manufacture a refutation.
        let family = Schur::new(2).expect("family");
        let problem = family.problem(4).expect("problem");
        let formula = problem.encode().expect("encode");
        let plan = colour_branch_plan(&problem, &[2, 3]).expect("plan");
        let outcome = run_adaptive_cover(
            &formula,
            &plan,
            &CoverOptions::default(),
            &AdaptiveOptions::default(),
            &SilentObserver,
        )
        .expect("run");
        let AdaptiveOutcome::Satisfiable { model, .. } = &outcome else {
            panic!("expected satisfiable, got {outcome:?}");
        };
        assert!(formula.evaluate(model).expect("evaluate"));
        assert!(outcome.certificate().is_none());
    }

    #[test]
    fn a_plan_the_formula_does_not_partition_is_refused_before_solving() {
        let family = Schur::new(2).expect("family");
        let problem = family.problem(5).expect("problem");
        let plan = colour_branch_plan(&problem, &[2]).expect("plan");
        // A formula with no at-least-one clause for point 2: the cover argument
        // does not apply, and the harness must say so rather than run.
        let mut stripped = CnfFormula::new(problem.variable_count());
        for clause in problem.encode().expect("encode").clauses().iter().skip(5) {
            stripped.add_clause(clause.clone()).expect("clause");
        }
        let error = run_cover(&stripped, &plan, &CoverOptions::default(), &SilentObserver)
            .expect_err("no ALO clause");
        assert!(matches!(error, SearchError::MissingAtLeastOneClause { .. }));
    }
}
