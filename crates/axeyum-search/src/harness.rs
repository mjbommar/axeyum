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
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use axeyum_cnf::{
    CnfClause, CnfFormula, DratStep, ProofSolveOutcome, check_drat, check_drat_backward,
    solve_with_drat_proof_with_limits, write_drat,
};

use crate::SearchError;
use crate::cover::{
    BranchPlan, Cell, CellCheck, CellRecord, CellVerdict, CoverCertificate, certify_cover,
    verify_branch_clauses, verify_cell_set,
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
            .unwrap_or_else(|e| e.into_inner())
            .clone();
        records.sort_by_key(|record| record.index);

        if let Some(finding) = self.sat.lock().unwrap_or_else(|e| e.into_inner()).take() {
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
        let proofs = self.proofs.lock().unwrap_or_else(|e| e.into_inner());
        if proofs.iter().any(Option::is_none) {
            return Ok(None);
        }
        crate::compose::compose_cover_proof(self.formula, self.plan, &proofs).map(Some)
    }

    /// The first error a worker reported, if any.
    fn take_first_error(&self) -> Option<SearchError> {
        self.errors
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .first()
            .cloned()
    }

    /// Reports a fatal error and stops the run.
    fn fail(&self, error: SearchError) {
        self.observer.on_note(&format!("FATAL {error}"));
        self.errors
            .lock()
            .unwrap_or_else(|e| e.into_inner())
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
        *self.sat.lock().unwrap_or_else(|e| e.into_inner()) = Some(SatFinding {
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
        if proof.len() > self.options.check_step_cap {
            return CellCheck::Deferred;
        }
        let verdict = match self.options.check {
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

    /// Keeps a proof for route A while retention is still affordable.
    fn retain(&self, index: usize, proof: Vec<DratStep>, adds: usize) {
        if !self.retaining.load(Ordering::SeqCst) {
            return;
        }
        let running = self.retained_adds.fetch_add(adds, Ordering::SeqCst) + adds;
        let mut proofs = self.proofs.lock().unwrap_or_else(|e| e.into_inner());
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
            .unwrap_or_else(|e| e.into_inner())
            .as_mut()
        {
            writer.append(&record)?;
        }
        self.observer.on_cell_finished(&record);
        self.records
            .lock()
            .unwrap_or_else(|e| e.into_inner())
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
