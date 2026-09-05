//! Proof-carrying bounded-makespan search for classical job-shop scheduling.
//!
//! The public instance parser, independent schedule checker, and SAT encoding
//! share only the typed problem. Search models are lifted to start times and
//! replayed against precedence, machine capacity, and the claimed makespan.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use axeyum_cnf::{CnfAssignment, CnfClause, CnfFormula, CnfLit, CnfVar};
use serde::{Deserialize, Serialize};

/// Portable schedule artifact schema.
pub const JOB_SHOP_SCHEDULE_SCHEMA: &str = "axeyum.job-shop-schedule.v1";

/// Portable energetic-overload certificate schema.
pub const JOB_SHOP_ENERGETIC_CONFLICT_SCHEMA: &str = "axeyum.job-shop-energetic-conflict.v1";

/// Portable conditional energetic-overload certificate schema.
pub const JOB_SHOP_CONDITIONAL_ENERGETIC_CONFLICT_SCHEMA: &str =
    "axeyum.job-shop-conditional-energetic-conflict.v1";

/// One non-preemptive operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JobShopOperation {
    /// Zero-based machine index.
    pub machine: usize,
    /// Positive integer processing time.
    pub duration: usize,
}

/// Classical job-shop instance: each job visits every machine exactly once.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JobShopProblem {
    /// Machine count.
    pub machines: usize,
    /// Jobs in precedence order.
    pub jobs: Vec<Vec<JobShopOperation>>,
}

/// A complete integer start-time assignment.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JobShopSchedule {
    /// Stable artifact schema.
    pub schema: String,
    /// Declared completion time of the last operation.
    pub makespan: usize,
    /// Start time for every operation, in problem job/operation order.
    pub starts: Vec<Vec<usize>>,
}

/// Successful independent replay measurements.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JobShopCheck {
    /// Operations checked.
    pub operations: usize,
    /// Recomputed makespan.
    pub makespan: usize,
}

/// Malformed input, failed replay, or resource decline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JobShopError {
    /// Text instance is malformed.
    Parse(String),
    /// Instance or schedule violates a structural contract.
    Malformed(String),
    /// Schedule violates a semantic constraint.
    InvalidSchedule(String),
    /// A stable construction ceiling was exceeded.
    LimitExceeded {
        /// Resource name.
        resource: &'static str,
        /// First value over the limit.
        observed: usize,
        /// Configured maximum.
        limit: usize,
    },
    /// CNF construction or evaluation failed.
    Cnf(String),
}

/// One bounded non-preemptive task on a cumulative resource.
///
/// This type is deliberately independent of job-shop indexing. It is the
/// small semantic input consumed by the energetic checker and can also be
/// reused by project-scheduling and cumulative-resource frontends.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CumulativeTaskWindow {
    /// Stable caller-owned task identifier.
    pub task: usize,
    /// Earliest permitted start.
    pub earliest_start: usize,
    /// Latest permitted start.
    pub latest_start: usize,
    /// Positive non-preemptive duration.
    pub duration: usize,
    /// Positive resource demand while executing.
    pub demand: usize,
}

/// Recomputed energy balance for one half-open time interval.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CumulativeEnergeticCheck {
    /// Start of the checked half-open interval.
    pub interval_start: usize,
    /// End of the checked half-open interval.
    pub interval_end: usize,
    /// Sum of every task's minimum required energy inside the interval.
    pub required_energy: usize,
    /// Available resource energy inside the interval.
    pub capacity_energy: usize,
    /// Tasks with a nonzero compulsory contribution.
    pub contributing_tasks: usize,
    /// Whether required energy strictly exceeds available energy.
    pub overloaded: bool,
}

/// Domain derivation replayed before checking an energetic conflict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum JobShopEnergeticDomain {
    /// Windows implied only by the defining job chains and makespan.
    JobChains,
    /// Windows after deterministic detectable-precedence closure.
    PrecedenceClosure,
    /// Re-run deterministic precedence closure under the certificate assumptions.
    AssumptionClosure,
}

/// One explicit start-domain assumption used by a conditional conflict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum JobShopStartBound {
    /// Assume the operation starts no earlier than `time`.
    StartAtLeast {
        /// Job index.
        job: usize,
        /// Operation index within the job.
        operation: usize,
        /// Inclusive lower bound.
        time: usize,
    },
    /// Assume the operation starts no later than `time`.
    StartAtMost {
        /// Job index.
        job: usize,
        /// Operation index within the job.
        operation: usize,
        /// Inclusive upper bound.
        time: usize,
    },
}

impl JobShopStartBound {
    fn key(self) -> (usize, usize, u8) {
        match self {
            Self::StartAtLeast { job, operation, .. } => (job, operation, 0),
            Self::StartAtMost { job, operation, .. } => (job, operation, 1),
        }
    }
}

/// A portable claim that one machine is energetically overloaded.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JobShopEnergeticConflict {
    /// Stable artifact schema.
    pub schema: String,
    /// Makespan bound whose job-chain windows are checked.
    pub bound: usize,
    /// Zero-based machine index.
    pub machine: usize,
    /// Checked derivation of the task windows used by the inequality.
    pub domain: JobShopEnergeticDomain,
    /// Start of the half-open overload interval.
    pub interval_start: usize,
    /// End of the half-open overload interval.
    pub interval_end: usize,
    /// Claimed required energy; the checker recomputes it exactly.
    pub required_energy: usize,
    /// Claimed available energy; the checker recomputes it exactly.
    pub capacity_energy: usize,
}

/// A portable energetic contradiction under explicit start bounds.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JobShopConditionalEnergeticConflict {
    /// Stable artifact schema.
    pub schema: String,
    /// Makespan bound whose base domains are reconstructed.
    pub bound: usize,
    /// Checked base-domain derivation.
    pub domain: JobShopEnergeticDomain,
    /// Canonically sorted conjunction of start bounds.
    pub assumptions: Vec<JobShopStartBound>,
    /// Zero-based overloaded machine.
    pub machine: usize,
    /// Start of the half-open overload interval.
    pub interval_start: usize,
    /// End of the half-open overload interval.
    pub interval_end: usize,
    /// Claimed required energy; replay recomputes it.
    pub required_energy: usize,
    /// Claimed capacity energy; replay recomputes it.
    pub capacity_energy: usize,
}

/// Successful conditional-conflict replay measurements.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JobShopConditionalEnergeticCheck {
    /// Recomputed energetic inequality.
    pub energetic: CumulativeEnergeticCheck,
    /// Non-tautological bounds applied to the base domains.
    pub assumptions_applied: usize,
}

/// Measurements from one bounded conditional energetic explanation search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JobShopConditionalEnergeticSearch {
    /// Base interval before any assumptions were applied.
    pub base: CumulativeEnergeticCheck,
    /// Number of strict single-operation domain tightenings evaluated.
    pub candidates_checked: usize,
    /// Checked explanation, when the assumption ceiling permits an overload.
    pub conflict: Option<JobShopConditionalEnergeticConflict>,
}

/// Strongest interval found by a deterministic bounded energetic scan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JobShopEnergeticScan {
    /// Machine containing the strongest interval.
    pub machine: usize,
    /// Independently recomputable interval measurement.
    pub check: CumulativeEnergeticCheck,
    /// Number of candidate intervals evaluated across all machines.
    pub intervals_checked: usize,
    /// Number of task/interval contributions evaluated.
    pub task_checks: usize,
    /// Portable conflict when the strongest interval is overloaded.
    pub conflict: Option<JobShopEnergeticConflict>,
}

/// Explicit resource limits for deterministic energetic scans.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JobShopEnergeticLimits {
    /// Maximum makespan horizon scanned exhaustively.
    pub max_horizon: usize,
    /// Maximum machine/interval candidates.
    pub max_intervals: usize,
    /// Maximum task contributions evaluated.
    pub max_task_checks: usize,
}

impl Default for JobShopEnergeticLimits {
    fn default() -> Self {
        Self {
            max_horizon: 10_000,
            max_intervals: 100_000_000,
            max_task_checks: 500_000_000,
        }
    }
}

/// Explicit limits for exhaustive conditional energetic unit scans.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JobShopConditionalEnergeticUnitLimits {
    /// Shared horizon, interval, and task-check ceilings.
    pub energetic: JobShopEnergeticLimits,
    /// Maximum distinct operation/direction deductions retained.
    pub max_conflicts: usize,
}

impl Default for JobShopConditionalEnergeticUnitLimits {
    fn default() -> Self {
        Self {
            energetic: JobShopEnergeticLimits::default(),
            max_conflicts: 100_000,
        }
    }
}

/// Result of an exhaustive strongest-unit energetic scan.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JobShopConditionalEnergeticUnitScan {
    /// Strongest checked deduction retained for each operation and polarity.
    pub conflicts: Vec<JobShopConditionalEnergeticConflict>,
    /// Machine/interval pairs examined.
    pub intervals_checked: usize,
    /// One-sided operation tightenings considered.
    pub candidates_checked: usize,
    /// Exact task-energy contributions evaluated, including bound searches.
    pub task_checks: usize,
}

/// Energetic scan after propagating an explicit conjunction of start bounds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JobShopConditionalEnergeticContextScan {
    /// Propagation measurements under the assumptions.
    pub propagation: JobShopPrecedencePropagation,
    /// Strongest interval after propagation.
    pub check: CumulativeEnergeticCheck,
    /// Machine containing the strongest interval.
    pub machine: usize,
    /// Machine/interval pairs examined.
    pub intervals_checked: usize,
    /// Task contributions evaluated.
    pub task_checks: usize,
    /// Portable conditional conflict when the context overloads a resource.
    pub conflict: Option<JobShopConditionalEnergeticConflict>,
}

/// Explicit limits for contextual energetic unit iteration.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JobShopConditionalEnergeticFixpointLimits {
    /// Per-round exhaustive unit-scan limits.
    pub unit: JobShopConditionalEnergeticUnitLimits,
    /// Maximum contextual rounds.
    pub max_rounds: usize,
    /// Maximum contextual conflicts retained across rounds.
    pub max_total_conflicts: usize,
}

impl Default for JobShopConditionalEnergeticFixpointLimits {
    fn default() -> Self {
        Self {
            unit: JobShopConditionalEnergeticUnitLimits::default(),
            max_rounds: 100,
            max_total_conflicts: 100_000,
        }
    }
}

/// One checked contextual unit-derivation round.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JobShopConditionalEnergeticFixpointRound {
    /// Entailed start bounds before this round.
    pub assumptions_before: Vec<JobShopStartBound>,
    /// Checked contextual explanations found in this round.
    pub conflicts: Vec<JobShopConditionalEnergeticConflict>,
    /// Entailed start bounds after negating the new conflicting bounds.
    pub assumptions_after: Vec<JobShopStartBound>,
    /// Candidate bounds examined.
    pub candidates_checked: usize,
    /// Exact task contributions evaluated.
    pub task_checks: usize,
}

/// Checked contextual energetic unit closure from standalone premise conflicts.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JobShopConditionalEnergeticFixpoint {
    /// Ordered contextual rounds.
    pub rounds: Vec<JobShopConditionalEnergeticFixpointRound>,
    /// Final strongest entailed start bounds.
    pub assumptions: Vec<JobShopStartBound>,
    /// All contextual conflict clauses in derivation order.
    pub conflicts: Vec<JobShopConditionalEnergeticConflict>,
    /// Whether a round produced no stronger bound.
    pub stabilized: bool,
}

fn cumulative_task_energy(
    task: CumulativeTaskWindow,
    interval_start: usize,
    interval_end: usize,
) -> Result<usize, JobShopError> {
    let width = interval_end
        .checked_sub(interval_start)
        .ok_or_else(|| JobShopError::Malformed("energetic interval must be nonempty".to_owned()))?;
    let earliest_completion = task
        .earliest_start
        .checked_add(task.duration)
        .ok_or_else(|| JobShopError::Malformed("task completion overflow".to_owned()))?;
    let compulsory_time = task
        .duration
        .min(width)
        .min(earliest_completion.saturating_sub(interval_start))
        .min(interval_end.saturating_sub(task.latest_start));
    compulsory_time
        .checked_mul(task.demand)
        .ok_or_else(|| JobShopError::Malformed("task energy overflow".to_owned()))
}

/// Check the classical energetic inequality on one cumulative resource.
///
/// For each task this recomputes the minimum amount of its processing that
/// must occur in `[interval_start, interval_end)` over every start in the
/// task's current integer domain. Multiplying by demand gives compulsory
/// energy. A strict excess over `capacity * interval_length` proves that no
/// non-preemptive schedule can satisfy those domains. Search may propose an
/// interval, but it cannot propose or override the arithmetic.
///
/// # Errors
///
/// Refuses an empty/reversed interval, zero capacity/duration/demand,
/// malformed domains, duplicate task identifiers, or arithmetic overflow.
pub fn check_cumulative_energetic_interval(
    tasks: &[CumulativeTaskWindow],
    capacity: usize,
    interval_start: usize,
    interval_end: usize,
) -> Result<CumulativeEnergeticCheck, JobShopError> {
    if interval_start >= interval_end {
        return Err(JobShopError::Malformed(
            "energetic interval must be nonempty".to_owned(),
        ));
    }
    if capacity == 0 {
        return Err(JobShopError::Malformed(
            "cumulative capacity must be positive".to_owned(),
        ));
    }
    let width = interval_end - interval_start;
    let capacity_energy = capacity
        .checked_mul(width)
        .ok_or_else(|| JobShopError::Malformed("capacity energy overflow".to_owned()))?;
    let mut seen = BTreeSet::new();
    let mut required_energy = 0usize;
    let mut contributing_tasks = 0usize;
    for task in tasks {
        if !seen.insert(task.task) {
            return Err(JobShopError::Malformed(format!(
                "duplicate cumulative task {}",
                task.task
            )));
        }
        if task.duration == 0 || task.demand == 0 || task.earliest_start > task.latest_start {
            return Err(JobShopError::Malformed(format!(
                "invalid cumulative task {}",
                task.task
            )));
        }
        // Standard energetic contribution:
        // max(0, min(p, b-a, est+p-a, b-lst)).  Saturating subtraction
        // expresses the outer max(0, ...) without signed arithmetic.
        let energy = cumulative_task_energy(*task, interval_start, interval_end)?;
        if energy == 0 {
            continue;
        }
        contributing_tasks += 1;
        required_energy = required_energy
            .checked_add(energy)
            .ok_or_else(|| JobShopError::Malformed("required energy overflow".to_owned()))?;
    }
    Ok(CumulativeEnergeticCheck {
        interval_start,
        interval_end,
        required_energy,
        capacity_energy,
        contributing_tasks,
        overloaded: required_energy > capacity_energy,
    })
}

impl JobShopProblem {
    /// Parse the common OR-Library/JSPLIB numeric format.
    ///
    /// Comment lines begin with `#`. The first data row is `jobs machines`;
    /// each following row contains exactly one `(machine,duration)` pair per
    /// machine. Machine indices must form a permutation in every job.
    ///
    /// # Errors
    ///
    /// Refuses malformed dimensions, rows, machine indices, durations, or
    /// trailing numeric data.
    pub fn parse_orlib(text: &str) -> Result<Self, JobShopError> {
        let mut rows = text
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with('#'));
        let header = parse_numbers(
            rows.next()
                .ok_or_else(|| JobShopError::Parse("missing jobs/machines header".to_owned()))?,
        )?;
        if header.len() != 2 || header[0] == 0 || header[1] == 0 {
            return Err(JobShopError::Parse(
                "header must contain two positive dimensions".to_owned(),
            ));
        }
        let (job_count, machines) = (header[0], header[1]);
        let mut jobs = Vec::with_capacity(job_count);
        for job in 0..job_count {
            let row = parse_numbers(
                rows.next()
                    .ok_or_else(|| JobShopError::Parse(format!("missing row for job {job}")))?,
            )?;
            if row.len() != machines.saturating_mul(2) {
                return Err(JobShopError::Parse(format!(
                    "job {job} has {} values, expected {}",
                    row.len(),
                    machines.saturating_mul(2)
                )));
            }
            let mut seen = vec![false; machines];
            let mut operations = Vec::with_capacity(machines);
            let (pairs, _tail) = row.as_chunks::<2>();
            for pair in pairs {
                let (machine, duration) = (pair[0], pair[1]);
                if machine >= machines || seen[machine] {
                    return Err(JobShopError::Parse(format!(
                        "job {job} has invalid or repeated machine {machine}"
                    )));
                }
                if duration == 0 {
                    return Err(JobShopError::Parse(format!(
                        "job {job} has a zero-duration operation"
                    )));
                }
                seen[machine] = true;
                operations.push(JobShopOperation { machine, duration });
            }
            jobs.push(operations);
        }
        if rows.next().is_some() {
            return Err(JobShopError::Parse("trailing data rows".to_owned()));
        }
        Ok(Self { machines, jobs })
    }

    fn operation_count(&self) -> usize {
        self.jobs.iter().map(Vec::len).sum()
    }
}

type JobChainWindows = (Vec<Vec<usize>>, Vec<Vec<usize>>);

fn job_chain_windows(
    problem: &JobShopProblem,
    bound: usize,
) -> Result<JobChainWindows, JobShopError> {
    if problem.jobs.is_empty() || problem.machines == 0 {
        return Err(JobShopError::Malformed("empty problem".to_owned()));
    }
    let mut earliest = Vec::with_capacity(problem.jobs.len());
    let mut latest = Vec::with_capacity(problem.jobs.len());
    for (job, operations) in problem.jobs.iter().enumerate() {
        if operations.len() != problem.machines {
            return Err(JobShopError::Malformed(format!(
                "job {job} has {} operations, expected {}",
                operations.len(),
                problem.machines
            )));
        }
        let mut seen_machines = vec![false; problem.machines];
        let mut job_earliest = Vec::with_capacity(operations.len());
        let mut cursor = 0usize;
        for operation in operations {
            if operation.machine >= problem.machines
                || seen_machines[operation.machine]
                || operation.duration == 0
            {
                return Err(JobShopError::Malformed(
                    "invalid or repeated operation machine, or zero duration".to_owned(),
                ));
            }
            seen_machines[operation.machine] = true;
            job_earliest.push(cursor);
            cursor = cursor
                .checked_add(operation.duration)
                .ok_or_else(|| JobShopError::Malformed("job duration sum overflow".to_owned()))?;
        }
        if cursor > bound {
            return Err(JobShopError::InvalidSchedule(format!(
                "job {job} duration {cursor} exceeds bound {bound}"
            )));
        }
        let mut suffix = 0usize;
        let mut job_latest = vec![0; operations.len()];
        for (index, operation) in operations.iter().enumerate().rev() {
            suffix = suffix
                .checked_add(operation.duration)
                .ok_or_else(|| JobShopError::Malformed("job duration sum overflow".to_owned()))?;
            job_latest[index] = bound - suffix;
        }
        earliest.push(job_earliest);
        latest.push(job_latest);
    }
    Ok((earliest, latest))
}

fn job_shop_machine_task_windows(
    problem: &JobShopProblem,
    bound: usize,
    machine: usize,
    propagated_windows: Option<&[JobShopOperationWindow]>,
) -> Result<Vec<CumulativeTaskWindow>, JobShopError> {
    if machine >= problem.machines {
        return Err(JobShopError::Malformed(format!(
            "machine {machine} is out of range"
        )));
    }
    let (earliest, latest) = job_chain_windows(problem, bound)?;
    let mut tasks = Vec::with_capacity(problem.jobs.len());
    let mut task = 0usize;
    for (job, operations) in problem.jobs.iter().enumerate() {
        for (operation, item) in operations.iter().enumerate() {
            let propagated = propagated_windows.and_then(|windows| windows.get(task));
            if propagated.is_some_and(|window| window.job != job || window.operation != operation) {
                return Err(JobShopError::Malformed(
                    "energetic operation-window propagation mismatch".to_owned(),
                ));
            }
            if item.machine == machine {
                tasks.push(CumulativeTaskWindow {
                    task,
                    earliest_start: propagated
                        .map_or(earliest[job][operation], |window| window.earliest),
                    latest_start: propagated.map_or(latest[job][operation], |window| window.latest),
                    duration: item.duration,
                    demand: 1,
                });
            }
            task = task
                .checked_add(1)
                .ok_or_else(|| JobShopError::Malformed("task index overflow".to_owned()))?;
        }
    }
    if tasks.is_empty() {
        return Err(JobShopError::Malformed(format!(
            "machine {machine} has no operations"
        )));
    }
    if propagated_windows.is_some_and(|windows| windows.len() != task) {
        return Err(JobShopError::Malformed(
            "energetic operation-window propagation mismatch".to_owned(),
        ));
    }
    Ok(tasks)
}

fn job_shop_domain_windows(
    problem: &JobShopProblem,
    bound: usize,
    domain: JobShopEnergeticDomain,
) -> Result<Vec<JobShopOperationWindow>, JobShopError> {
    match domain {
        JobShopEnergeticDomain::JobChains => {
            let (earliest, latest) = job_chain_windows(problem, bound)?;
            let mut windows = Vec::with_capacity(problem.operation_count());
            for (job, operations) in problem.jobs.iter().enumerate() {
                for operation in 0..operations.len() {
                    windows.push(JobShopOperationWindow {
                        job,
                        operation,
                        earliest: earliest[job][operation],
                        latest: latest[job][operation],
                    });
                }
            }
            Ok(windows)
        }
        JobShopEnergeticDomain::PrecedenceClosure => {
            let result = propagate_job_shop_precedences(problem, bound)?;
            if result.infeasible {
                return Err(JobShopError::InvalidSchedule(
                    "precedence closure is already infeasible".to_owned(),
                ));
            }
            Ok(result.windows)
        }
        JobShopEnergeticDomain::AssumptionClosure => Err(JobShopError::Malformed(
            "assumption closure requires explicit conditional bounds".to_owned(),
        )),
    }
}

/// Independently replay a portable job-shop energetic conflict.
///
/// Job-chain domains, task membership, unit demands, and interval capacity are
/// reconstructed from the typed problem. The certificate supplies only the
/// machine and interval plus redundant expected totals; any mutation or a
/// merely tight (rather than overloaded) interval is rejected.
///
/// # Errors
///
/// Refuses a wrong schema/bound, invalid machine/interval, mismatched totals,
/// or a claim whose recomputed energy does not strictly exceed capacity.
pub fn check_job_shop_energetic_conflict(
    problem: &JobShopProblem,
    bound: usize,
    conflict: &JobShopEnergeticConflict,
) -> Result<CumulativeEnergeticCheck, JobShopError> {
    if conflict.schema != JOB_SHOP_ENERGETIC_CONFLICT_SCHEMA {
        return Err(JobShopError::Malformed(format!(
            "unsupported energetic-conflict schema `{}`",
            conflict.schema
        )));
    }
    if conflict.bound != bound {
        return Err(JobShopError::Malformed(format!(
            "energetic-conflict bound {} does not match {bound}",
            conflict.bound
        )));
    }
    if conflict.interval_end > bound {
        return Err(JobShopError::Malformed(
            "energetic interval exceeds makespan bound".to_owned(),
        ));
    }
    let windows = job_shop_domain_windows(problem, bound, conflict.domain)?;
    let tasks = job_shop_machine_task_windows(problem, bound, conflict.machine, Some(&windows))?;
    let check = check_cumulative_energetic_interval(
        &tasks,
        1,
        conflict.interval_start,
        conflict.interval_end,
    )?;
    if check.required_energy != conflict.required_energy
        || check.capacity_energy != conflict.capacity_energy
    {
        return Err(JobShopError::InvalidSchedule(format!(
            "energetic totals mismatch: claimed {}/{}, recomputed {}/{}",
            conflict.required_energy,
            conflict.capacity_energy,
            check.required_energy,
            check.capacity_energy
        )));
    }
    if !check.overloaded {
        return Err(JobShopError::InvalidSchedule(
            "energetic interval is not overloaded".to_owned(),
        ));
    }
    Ok(check)
}

fn apply_job_shop_start_bounds(
    problem: &JobShopProblem,
    machine: Option<usize>,
    assumptions: &[JobShopStartBound],
    windows: &mut [JobShopOperationWindow],
) -> Result<(), JobShopError> {
    if assumptions.is_empty() {
        return Err(JobShopError::Malformed(
            "conditional energetic conflict has no assumptions".to_owned(),
        ));
    }
    let mut previous = None;
    for assumption in assumptions {
        let key = assumption.key();
        if previous.is_some_and(|prior| prior >= key) {
            return Err(JobShopError::Malformed(
                "conditional energetic assumptions are not canonical".to_owned(),
            ));
        }
        previous = Some(key);
        let (job, operation, time) = match *assumption {
            JobShopStartBound::StartAtLeast {
                job,
                operation,
                time,
            }
            | JobShopStartBound::StartAtMost {
                job,
                operation,
                time,
            } => (job, operation, time),
        };
        let operations = problem.jobs.get(job).ok_or_else(|| {
            JobShopError::Malformed(format!("conditional job {job} is out of range"))
        })?;
        let item = operations.get(operation).ok_or_else(|| {
            JobShopError::Malformed(format!(
                "conditional operation {job}:{operation} is out of range"
            ))
        })?;
        if machine.is_some_and(|machine| item.machine != machine) {
            return Err(JobShopError::Malformed(format!(
                "conditional operation {job}:{operation} is not on machine {}",
                machine.expect("checked as some")
            )));
        }
        let flat = problem
            .jobs
            .iter()
            .take(job)
            .map(Vec::len)
            .sum::<usize>()
            .checked_add(operation)
            .ok_or_else(|| JobShopError::Malformed("operation index overflow".to_owned()))?;
        let window = windows.get_mut(flat).ok_or_else(|| {
            JobShopError::Malformed("conditional operation window mismatch".to_owned())
        })?;
        if window.job != job || window.operation != operation {
            return Err(JobShopError::Malformed(
                "conditional operation window mismatch".to_owned(),
            ));
        }
        match *assumption {
            JobShopStartBound::StartAtLeast { .. } => {
                if time <= window.earliest || time > window.latest {
                    return Err(JobShopError::Malformed(format!(
                        "conditional lower bound {time} does not strictly narrow {job}:{operation}"
                    )));
                }
                window.earliest = time;
            }
            JobShopStartBound::StartAtMost { .. } => {
                if time >= window.latest || time < window.earliest {
                    return Err(JobShopError::Malformed(format!(
                        "conditional upper bound {time} does not strictly narrow {job}:{operation}"
                    )));
                }
                window.latest = time;
            }
        }
    }
    Ok(())
}

/// Independently replay an energetic conflict under explicit start bounds.
///
/// The checker reconstructs the selected base domains, applies a canonical
/// conjunction of inclusive lower/upper bounds, rebuilds every task on the
/// claimed machine, and recomputes the strict energetic overload. Assumptions
/// may narrow domains but cannot widen them; contradictory assumptions are
/// rejected rather than credited as energetic evidence.
///
/// # Errors
///
/// Refuses wrong schema/bound, noncanonical or redundant assumptions,
/// out-of-range operations, bounds outside the base domain, empty narrowed
/// domains, assumptions irrelevant to the claimed machine, mismatched totals,
/// or a non-overloaded interval.
pub fn check_job_shop_conditional_energetic_conflict(
    problem: &JobShopProblem,
    bound: usize,
    conflict: &JobShopConditionalEnergeticConflict,
) -> Result<JobShopConditionalEnergeticCheck, JobShopError> {
    if conflict.schema != JOB_SHOP_CONDITIONAL_ENERGETIC_CONFLICT_SCHEMA {
        return Err(JobShopError::Malformed(format!(
            "unsupported conditional energetic-conflict schema `{}`",
            conflict.schema
        )));
    }
    if conflict.bound != bound {
        return Err(JobShopError::Malformed(format!(
            "conditional energetic-conflict bound {} does not match {bound}",
            conflict.bound
        )));
    }
    if conflict.interval_end > bound {
        return Err(JobShopError::Malformed(
            "conditional energetic interval exceeds makespan bound".to_owned(),
        ));
    }
    let windows = if conflict.domain == JobShopEnergeticDomain::AssumptionClosure {
        let propagation = propagate_job_shop_precedences_with_start_bounds(
            problem,
            bound,
            &conflict.assumptions,
        )?;
        if propagation.infeasible {
            return Err(JobShopError::InvalidSchedule(
                "assumption precedence closure is already infeasible".to_owned(),
            ));
        }
        propagation.windows
    } else {
        let mut windows = job_shop_domain_windows(problem, bound, conflict.domain)?;
        apply_job_shop_start_bounds(
            problem,
            Some(conflict.machine),
            &conflict.assumptions,
            &mut windows,
        )?;
        windows
    };
    let tasks = job_shop_machine_task_windows(problem, bound, conflict.machine, Some(&windows))?;
    let energetic = check_cumulative_energetic_interval(
        &tasks,
        1,
        conflict.interval_start,
        conflict.interval_end,
    )?;
    if energetic.required_energy != conflict.required_energy
        || energetic.capacity_energy != conflict.capacity_energy
    {
        return Err(JobShopError::InvalidSchedule(format!(
            "conditional energetic totals mismatch: claimed {}/{}, recomputed {}/{}",
            conflict.required_energy,
            conflict.capacity_energy,
            energetic.required_energy,
            energetic.capacity_energy
        )));
    }
    if !energetic.overloaded {
        return Err(JobShopError::InvalidSchedule(
            "conditional energetic interval is not overloaded".to_owned(),
        ));
    }
    Ok(JobShopConditionalEnergeticCheck {
        energetic,
        assumptions_applied: conflict.assumptions.len(),
    })
}

type JobShopEnergeticCandidates = (Vec<(usize, JobShopStartBound)>, usize);

fn conditional_energetic_candidates(
    tasks: &[CumulativeTaskWindow],
    windows: &[JobShopOperationWindow],
    interval_start: usize,
    interval_end: usize,
) -> Result<JobShopEnergeticCandidates, JobShopError> {
    let mut candidates = Vec::new();
    let mut candidates_checked = 0usize;
    for task in tasks {
        if task.earliest_start == task.latest_start {
            continue;
        }
        let operation = windows.get(task.task).ok_or_else(|| {
            JobShopError::Malformed("conditional search operation mismatch".to_owned())
        })?;
        let base_task =
            check_cumulative_energetic_interval(&[*task], 1, interval_start, interval_end)?
                .required_energy;
        let alternatives = [
            (
                JobShopStartBound::StartAtLeast {
                    job: operation.job,
                    operation: operation.operation,
                    time: task.latest_start,
                },
                CumulativeTaskWindow {
                    earliest_start: task.latest_start,
                    ..*task
                },
            ),
            (
                JobShopStartBound::StartAtMost {
                    job: operation.job,
                    operation: operation.operation,
                    time: task.earliest_start,
                },
                CumulativeTaskWindow {
                    latest_start: task.earliest_start,
                    ..*task
                },
            ),
        ];
        let mut best = None;
        for (assumption, narrowed) in alternatives {
            candidates_checked = candidates_checked.checked_add(1).ok_or_else(|| {
                JobShopError::Malformed("conditional candidate count overflow".to_owned())
            })?;
            let narrowed_energy =
                check_cumulative_energetic_interval(&[narrowed], 1, interval_start, interval_end)?
                    .required_energy;
            let gain = narrowed_energy.checked_sub(base_task).ok_or_else(|| {
                JobShopError::Malformed("conditional energetic gain underflow".to_owned())
            })?;
            if gain > 0
                && best.as_ref().is_none_or(
                    |(best_gain, best_bound): &(usize, JobShopStartBound)| {
                        gain > *best_gain
                            || (gain == *best_gain && assumption.key() < best_bound.key())
                    },
                )
            {
                best = Some((gain, assumption));
            }
        }
        candidates.extend(best);
    }
    candidates.sort_unstable_by(|left, right| {
        right
            .0
            .cmp(&left.0)
            .then_with(|| left.1.key().cmp(&right.1.key()))
    });
    Ok((candidates, candidates_checked))
}

fn conditional_energy_with_bounds(
    problem: &JobShopProblem,
    bound: usize,
    machine: usize,
    base_windows: &[JobShopOperationWindow],
    assumptions: &[JobShopStartBound],
    interval_start: usize,
    interval_end: usize,
) -> Result<CumulativeEnergeticCheck, JobShopError> {
    let mut windows = base_windows.to_vec();
    apply_job_shop_start_bounds(problem, Some(machine), assumptions, &mut windows)?;
    let tasks = job_shop_machine_task_windows(problem, bound, machine, Some(&windows))?;
    check_cumulative_energetic_interval(&tasks, 1, interval_start, interval_end)
}

fn relax_conditional_energetic_assumptions(
    problem: &JobShopProblem,
    bound: usize,
    machine: usize,
    base_windows: &[JobShopOperationWindow],
    assumptions: &mut [JobShopStartBound],
    interval_start: usize,
    interval_end: usize,
) -> Result<CumulativeEnergeticCheck, JobShopError> {
    for index in 0..assumptions.len() {
        let (job, operation) = match assumptions[index] {
            JobShopStartBound::StartAtLeast { job, operation, .. }
            | JobShopStartBound::StartAtMost { job, operation, .. } => (job, operation),
        };
        let base = base_windows
            .iter()
            .find(|window| window.job == job && window.operation == operation)
            .ok_or_else(|| {
                JobShopError::Malformed("conditional relaxation operation mismatch".to_owned())
            })?;
        loop {
            let relaxed = match assumptions[index] {
                JobShopStartBound::StartAtLeast { time, .. }
                    if time.saturating_sub(1) > base.earliest =>
                {
                    JobShopStartBound::StartAtLeast {
                        job,
                        operation,
                        time: time - 1,
                    }
                }
                JobShopStartBound::StartAtMost { time, .. }
                    if time.checked_add(1).is_some_and(|next| next < base.latest) =>
                {
                    JobShopStartBound::StartAtMost {
                        job,
                        operation,
                        time: time + 1,
                    }
                }
                _ => break,
            };
            let previous = std::mem::replace(&mut assumptions[index], relaxed);
            let check = conditional_energy_with_bounds(
                problem,
                bound,
                machine,
                base_windows,
                assumptions,
                interval_start,
                interval_end,
            )?;
            if !check.overloaded {
                assumptions[index] = previous;
                break;
            }
        }
    }
    conditional_energy_with_bounds(
        problem,
        bound,
        machine,
        base_windows,
        assumptions,
        interval_start,
        interval_end,
    )
}

/// Find a short checked energetic explanation for one machine interval.
///
/// For every flexible operation on the machine, the search evaluates the two
/// strongest one-sided domain assumptions: pinning its upper bound to the base
/// earliest start, or its lower bound to the base latest start. It retains the
/// direction with the larger exact energetic gain, then takes gains in stable
/// descending order until the interval overloads. Because task contributions
/// are additive, this is complete for an overload using at most
/// `max_assumptions` such extreme bounds, using at most one bound per operation,
/// on this fixed interval. The returned artifact is replayed by the independent
/// checker before it is credited.
///
/// # Errors
///
/// Refuses a zero assumption ceiling, malformed domains/intervals, arithmetic
/// overflow, or any internally proposed artifact that fails replay.
pub fn find_job_shop_conditional_energetic_conflict(
    problem: &JobShopProblem,
    bound: usize,
    domain: JobShopEnergeticDomain,
    machine: usize,
    interval_start: usize,
    interval_end: usize,
    max_assumptions: usize,
) -> Result<JobShopConditionalEnergeticSearch, JobShopError> {
    if max_assumptions == 0 {
        return Err(JobShopError::Malformed(
            "conditional energetic search requires a positive assumption ceiling".to_owned(),
        ));
    }
    let windows = job_shop_domain_windows(problem, bound, domain)?;
    let tasks = job_shop_machine_task_windows(problem, bound, machine, Some(&windows))?;
    let base = check_cumulative_energetic_interval(&tasks, 1, interval_start, interval_end)?;
    if base.overloaded {
        return Ok(JobShopConditionalEnergeticSearch {
            base,
            candidates_checked: 0,
            conflict: None,
        });
    }

    let (candidates, candidates_checked) =
        conditional_energetic_candidates(&tasks, &windows, interval_start, interval_end)?;

    let mut required_energy = base.required_energy;
    let mut assumptions = Vec::new();
    for (gain, assumption) in candidates.into_iter().take(max_assumptions) {
        required_energy = required_energy.checked_add(gain).ok_or_else(|| {
            JobShopError::Malformed("conditional required energy overflow".to_owned())
        })?;
        assumptions.push(assumption);
        if required_energy > base.capacity_energy {
            break;
        }
    }
    if required_energy <= base.capacity_energy {
        return Ok(JobShopConditionalEnergeticSearch {
            base,
            candidates_checked,
            conflict: None,
        });
    }
    assumptions.sort_unstable_by_key(|assumption| assumption.key());
    let relaxed = relax_conditional_energetic_assumptions(
        problem,
        bound,
        machine,
        &windows,
        &mut assumptions,
        interval_start,
        interval_end,
    )?;
    let conflict = JobShopConditionalEnergeticConflict {
        schema: JOB_SHOP_CONDITIONAL_ENERGETIC_CONFLICT_SCHEMA.to_owned(),
        bound,
        domain,
        assumptions,
        machine,
        interval_start,
        interval_end,
        required_energy: relaxed.required_energy,
        capacity_energy: relaxed.capacity_energy,
    };
    check_job_shop_conditional_energetic_conflict(problem, bound, &conflict)?;
    Ok(JobShopConditionalEnergeticSearch {
        base,
        candidates_checked,
        conflict: Some(conflict),
    })
}

#[derive(Clone, Copy)]
enum UnitBoundDirection {
    Lower,
    Upper,
}

#[derive(Clone, Copy)]
struct UnitEnergeticProbe {
    assumption: JobShopStartBound,
    required_energy: usize,
}

type UnitConflictKey = (usize, usize, u8);
type UnitConflictCandidate = (UnitConflictKey, JobShopConditionalEnergeticConflict);

struct UnitIntervalContext {
    interval_start: usize,
    interval_end: usize,
    base_required_energy: usize,
    capacity_energy: usize,
}

fn unit_probe(
    assumption: JobShopStartBound,
    required_energy: usize,
    task_checks: usize,
) -> (Option<UnitEnergeticProbe>, usize) {
    (
        Some(UnitEnergeticProbe {
            assumption,
            required_energy,
        }),
        task_checks,
    )
}

fn find_conditional_energetic_unit_bound(
    task: CumulativeTaskWindow,
    operation: &JobShopOperationWindow,
    direction: UnitBoundDirection,
    interval: &UnitIntervalContext,
) -> Result<(Option<UnitEnergeticProbe>, usize), JobShopError> {
    if task.earliest_start == task.latest_start {
        return Ok((None, 0));
    }
    let mut task_checks = 1usize;
    let base_task = cumulative_task_energy(task, interval.interval_start, interval.interval_end)?;
    let fixed_energy = interval
        .base_required_energy
        .checked_sub(base_task)
        .ok_or_else(|| JobShopError::Malformed("conditional fixed energy underflow".to_owned()))?;
    let mut evaluate = |narrowed: CumulativeTaskWindow| -> Result<usize, JobShopError> {
        task_checks = task_checks
            .checked_add(1)
            .ok_or_else(|| JobShopError::Malformed("conditional task-check overflow".to_owned()))?;
        fixed_energy
            .checked_add(cumulative_task_energy(
                narrowed,
                interval.interval_start,
                interval.interval_end,
            )?)
            .ok_or_else(|| {
                JobShopError::Malformed("conditional required energy overflow".to_owned())
            })
    };
    let (assumption, required_energy) = match direction {
        UnitBoundDirection::Upper => {
            let extreme = CumulativeTaskWindow {
                latest_start: task.earliest_start,
                ..task
            };
            if evaluate(extreme)? <= interval.capacity_energy {
                return Ok((None, task_checks));
            }
            let mut low = task.earliest_start;
            let mut high = task.latest_start - 1;
            while low < high {
                let middle = low + (high - low).div_ceil(2);
                let required = evaluate(CumulativeTaskWindow {
                    latest_start: middle,
                    ..task
                })?;
                if required > interval.capacity_energy {
                    low = middle;
                } else {
                    high = middle - 1;
                }
            }
            let required = evaluate(CumulativeTaskWindow {
                latest_start: low,
                ..task
            })?;
            (
                JobShopStartBound::StartAtMost {
                    job: operation.job,
                    operation: operation.operation,
                    time: low,
                },
                required,
            )
        }
        UnitBoundDirection::Lower => {
            let extreme = CumulativeTaskWindow {
                earliest_start: task.latest_start,
                ..task
            };
            if evaluate(extreme)? <= interval.capacity_energy {
                return Ok((None, task_checks));
            }
            let mut low = task.earliest_start + 1;
            let mut high = task.latest_start;
            while low < high {
                let middle = low + (high - low) / 2;
                let required = evaluate(CumulativeTaskWindow {
                    earliest_start: middle,
                    ..task
                })?;
                if required > interval.capacity_energy {
                    high = middle;
                } else {
                    low = middle + 1;
                }
            }
            let required = evaluate(CumulativeTaskWindow {
                earliest_start: low,
                ..task
            })?;
            (
                JobShopStartBound::StartAtLeast {
                    job: operation.job,
                    operation: operation.operation,
                    time: low,
                },
                required,
            )
        }
    };
    Ok(unit_probe(assumption, required_energy, task_checks))
}

fn stronger_unit_conflict(
    key: (usize, usize, u8),
    candidate: &JobShopConditionalEnergeticConflict,
    current: &JobShopConditionalEnergeticConflict,
) -> bool {
    let candidate = candidate
        .assumptions
        .iter()
        .find(|assumption| assumption.key() == key)
        .copied();
    let current = current
        .assumptions
        .iter()
        .find(|assumption| assumption.key() == key)
        .copied();
    match (candidate, current) {
        (
            Some(JobShopStartBound::StartAtMost {
                time: candidate, ..
            }),
            Some(JobShopStartBound::StartAtMost { time: current, .. }),
        ) => candidate > current,
        (
            Some(JobShopStartBound::StartAtLeast {
                time: candidate, ..
            }),
            Some(JobShopStartBound::StartAtLeast { time: current, .. }),
        ) => candidate < current,
        _ => false,
    }
}

struct UnitScanContext<'a> {
    problem: &'a JobShopProblem,
    bound: usize,
    domain: JobShopEnergeticDomain,
    windows: &'a [JobShopOperationWindow],
    base_assumptions: &'a [JobShopStartBound],
    limits: JobShopConditionalEnergeticUnitLimits,
}

impl UnitScanContext<'_> {
    fn conflict_for_probe(
        &self,
        probe: &UnitEnergeticProbe,
        machine: usize,
        interval_start: usize,
        interval_end: usize,
        base_capacity_energy: usize,
    ) -> Result<Option<UnitConflictCandidate>, JobShopError> {
        let key = probe.assumption.key();
        if self
            .base_assumptions
            .iter()
            .any(|assumption| assumption.key() == key)
        {
            return Ok(None);
        }
        let mut assumptions = self.base_assumptions.to_vec();
        assumptions.push(probe.assumption);
        assumptions.sort_unstable_by_key(|assumption| assumption.key());
        let (required_energy, capacity_energy) =
            if self.domain == JobShopEnergeticDomain::AssumptionClosure {
                let propagation = propagate_job_shop_precedences_with_start_bounds(
                    self.problem,
                    self.bound,
                    &assumptions,
                )?;
                if propagation.infeasible {
                    return Ok(None);
                }
                let tasks = job_shop_machine_task_windows(
                    self.problem,
                    self.bound,
                    machine,
                    Some(&propagation.windows),
                )?;
                let check =
                    check_cumulative_energetic_interval(&tasks, 1, interval_start, interval_end)?;
                if !check.overloaded {
                    return Ok(None);
                }
                (check.required_energy, check.capacity_energy)
            } else {
                (probe.required_energy, base_capacity_energy)
            };
        Ok(Some((
            key,
            JobShopConditionalEnergeticConflict {
                schema: JOB_SHOP_CONDITIONAL_ENERGETIC_CONFLICT_SCHEMA.to_owned(),
                bound: self.bound,
                domain: self.domain,
                assumptions,
                machine,
                interval_start,
                interval_end,
                required_energy,
                capacity_energy,
            },
        )))
    }
}

#[derive(Default)]
struct UnitScanState {
    retained: BTreeMap<(usize, usize, u8), JobShopConditionalEnergeticConflict>,
    candidates_checked: usize,
    task_checks: usize,
}

impl UnitScanState {
    fn check_interval(
        &mut self,
        context: &UnitScanContext<'_>,
        tasks: &[CumulativeTaskWindow],
        machine: usize,
        interval_start: usize,
        interval_end: usize,
    ) -> Result<(), JobShopError> {
        let base = check_cumulative_energetic_interval(tasks, 1, interval_start, interval_end)?;
        if base.overloaded {
            return Err(JobShopError::InvalidSchedule(
                "conditional unit scan encountered a root energetic conflict".to_owned(),
            ));
        }
        self.task_checks = self
            .task_checks
            .checked_add(tasks.len())
            .ok_or_else(|| JobShopError::Malformed("conditional task-check overflow".to_owned()))?;
        let interval = UnitIntervalContext {
            interval_start,
            interval_end,
            base_required_energy: base.required_energy,
            capacity_energy: base.capacity_energy,
        };
        for task in tasks {
            if task.earliest_start == task.latest_start {
                continue;
            }
            let operation = context.windows.get(task.task).ok_or_else(|| {
                JobShopError::Malformed("conditional scan operation mismatch".to_owned())
            })?;
            for direction in [UnitBoundDirection::Lower, UnitBoundDirection::Upper] {
                self.candidates_checked =
                    self.candidates_checked.checked_add(1).ok_or_else(|| {
                        JobShopError::Malformed("conditional candidate count overflow".to_owned())
                    })?;
                let (probe, probe_task_checks) =
                    find_conditional_energetic_unit_bound(*task, operation, direction, &interval)?;
                self.task_checks =
                    self.task_checks
                        .checked_add(probe_task_checks)
                        .ok_or_else(|| {
                            JobShopError::Malformed("conditional task-check overflow".to_owned())
                        })?;
                let Some(probe) = probe else {
                    continue;
                };
                let Some((key, conflict)) = context.conflict_for_probe(
                    &probe,
                    machine,
                    interval_start,
                    interval_end,
                    base.capacity_energy,
                )?
                else {
                    continue;
                };
                if self
                    .retained
                    .get(&key)
                    .is_none_or(|current| stronger_unit_conflict(key, &conflict, current))
                {
                    self.retained.insert(key, conflict);
                    if self.retained.len() > context.limits.max_conflicts {
                        return Err(JobShopError::LimitExceeded {
                            resource: "conditional energetic conflicts",
                            observed: self.retained.len(),
                            limit: context.limits.max_conflicts,
                        });
                    }
                }
            }
        }
        if self.task_checks > context.limits.energetic.max_task_checks {
            return Err(JobShopError::LimitExceeded {
                resource: "conditional energetic task checks",
                observed: self.task_checks,
                limit: context.limits.energetic.max_task_checks,
            });
        }
        Ok(())
    }
}

fn conditional_unit_interval_count(
    problem: &JobShopProblem,
    bound: usize,
    limits: JobShopConditionalEnergeticUnitLimits,
) -> Result<usize, JobShopError> {
    if bound > limits.energetic.max_horizon {
        return Err(JobShopError::LimitExceeded {
            resource: "conditional energetic horizon",
            observed: bound,
            limit: limits.energetic.max_horizon,
        });
    }
    let intervals = bound
        .checked_mul(bound.checked_add(1).ok_or_else(|| {
            JobShopError::Malformed("conditional interval count overflow".to_owned())
        })?)
        .and_then(|value| value.checked_div(2))
        .and_then(|value| value.checked_mul(problem.machines))
        .ok_or_else(|| JobShopError::Malformed("conditional interval count overflow".to_owned()))?;
    if intervals > limits.energetic.max_intervals {
        return Err(JobShopError::LimitExceeded {
            resource: "conditional energetic intervals",
            observed: intervals,
            limit: limits.energetic.max_intervals,
        });
    }
    Ok(intervals)
}

fn scan_conditional_units_from_windows(
    problem: &JobShopProblem,
    bound: usize,
    domain: JobShopEnergeticDomain,
    base_assumptions: &[JobShopStartBound],
    windows: &[JobShopOperationWindow],
    limits: JobShopConditionalEnergeticUnitLimits,
) -> Result<JobShopConditionalEnergeticUnitScan, JobShopError> {
    let intervals_checked = conditional_unit_interval_count(problem, bound, limits)?;
    let context = UnitScanContext {
        problem,
        bound,
        domain,
        windows,
        base_assumptions,
        limits,
    };
    let mut state = UnitScanState::default();
    for machine in 0..problem.machines {
        let tasks = job_shop_machine_task_windows(problem, bound, machine, Some(windows))?;
        for interval_start in 0..bound {
            for interval_end in interval_start + 1..=bound {
                state.check_interval(&context, &tasks, machine, interval_start, interval_end)?;
            }
        }
    }
    let conflicts = state.retained.into_values().collect::<Vec<_>>();
    for conflict in &conflicts {
        check_job_shop_conditional_energetic_conflict(problem, bound, conflict)?;
    }
    Ok(JobShopConditionalEnergeticUnitScan {
        conflicts,
        intervals_checked,
        candidates_checked: state.candidates_checked,
        task_checks: state.task_checks,
    })
}

/// Exhaustively find strongest standalone unit-bound energetic deductions.
///
/// Every integer interval on every machine is checked from the selected base
/// domains. For each flexible task and each polarity, a monotone binary search
/// finds the weakest single assumption that still overloads the interval; its
/// negation is therefore the strongest unit deduction supported by that
/// interval. Only the strongest checked artifact per operation/polarity is
/// retained. This scan derives standalone units: it does not assume deductions
/// found earlier in the same scan.
///
/// # Errors
///
/// Refuses malformed instances, root-overloaded domains, arithmetic overflow,
/// or work exceeding explicit horizon, interval, task-check, or artifact
/// ceilings.
pub fn scan_job_shop_conditional_energetic_unit_conflicts(
    problem: &JobShopProblem,
    bound: usize,
    domain: JobShopEnergeticDomain,
    limits: JobShopConditionalEnergeticUnitLimits,
) -> Result<JobShopConditionalEnergeticUnitScan, JobShopError> {
    let windows = job_shop_domain_windows(problem, bound, domain)?;
    scan_conditional_units_from_windows(problem, bound, domain, &[], &windows, limits)
}

/// Exhaustively derive new unit bounds under an established bound context.
///
/// The context is propagated through job and detectable machine precedences
/// first. Every returned explanation contains the complete context plus one
/// additional conflicting bound and is independently replayed using
/// [`JobShopEnergeticDomain::AssumptionClosure`]. When the context assumptions
/// are already unit clauses, Boolean propagation reduces each returned clause
/// to the newly derived unit.
///
/// # Errors
///
/// Refuses malformed or infeasible contexts, a root energetic conflict that
/// should use the context-scan route, arithmetic overflow, or explicit limit
/// exhaustion.
pub fn scan_job_shop_contextual_energetic_unit_conflicts(
    problem: &JobShopProblem,
    bound: usize,
    assumptions: &[JobShopStartBound],
    limits: JobShopConditionalEnergeticUnitLimits,
) -> Result<JobShopConditionalEnergeticUnitScan, JobShopError> {
    let propagation =
        propagate_job_shop_precedences_with_start_bounds(problem, bound, assumptions)?;
    if propagation.infeasible {
        return Err(JobShopError::InvalidSchedule(
            "start-bound context is already infeasible by precedence propagation".to_owned(),
        ));
    }
    scan_conditional_units_from_windows(
        problem,
        bound,
        JobShopEnergeticDomain::AssumptionClosure,
        assumptions,
        &propagation.windows,
        limits,
    )
}

fn negate_start_bound(bound: JobShopStartBound) -> Result<JobShopStartBound, JobShopError> {
    match bound {
        JobShopStartBound::StartAtMost {
            job,
            operation,
            time,
        } => Ok(JobShopStartBound::StartAtLeast {
            job,
            operation,
            time: time.checked_add(1).ok_or_else(|| {
                JobShopError::Malformed("start-bound negation overflow".to_owned())
            })?,
        }),
        JobShopStartBound::StartAtLeast {
            job,
            operation,
            time,
        } => Ok(JobShopStartBound::StartAtMost {
            job,
            operation,
            time: time.checked_sub(1).ok_or_else(|| {
                JobShopError::InvalidSchedule(
                    "conditional conflict negates an always-true lower bound".to_owned(),
                )
            })?,
        }),
    }
}

fn merge_entailed_start_bound(
    assumptions: &mut Vec<JobShopStartBound>,
    candidate: JobShopStartBound,
) -> bool {
    let key = candidate.key();
    let Some(index) = assumptions
        .iter()
        .position(|assumption| assumption.key() == key)
    else {
        assumptions.push(candidate);
        assumptions.sort_unstable_by_key(|assumption| assumption.key());
        return true;
    };
    let stronger = match (candidate, assumptions[index]) {
        (
            JobShopStartBound::StartAtLeast { time: new, .. },
            JobShopStartBound::StartAtLeast { time: old, .. },
        ) => new > old,
        (
            JobShopStartBound::StartAtMost { time: new, .. },
            JobShopStartBound::StartAtMost { time: old, .. },
        ) => new < old,
        _ => false,
    };
    if stronger {
        assumptions[index] = candidate;
    }
    stronger
}

fn new_conflicting_bound(
    context: &[JobShopStartBound],
    conflict: &JobShopConditionalEnergeticConflict,
) -> Result<JobShopStartBound, JobShopError> {
    let difference = conflict
        .assumptions
        .iter()
        .filter(|assumption| !context.contains(assumption))
        .copied()
        .collect::<Vec<_>>();
    if difference.len() != 1 {
        return Err(JobShopError::Malformed(format!(
            "contextual explanation adds {} bounds instead of one",
            difference.len()
        )));
    }
    Ok(difference[0])
}

/// Iterate checked contextual energetic units to a bounded fixpoint.
///
/// Each premise must be a replayable one-assumption conflict; its negation
/// seeds the entailed context. Every later explanation contains that complete
/// context plus exactly one conflicting bound. Negating the new bound yields
/// the next entailed unit, so the returned ordered clauses form a checkable
/// implication chain rather than an untrusted domain mutation.
///
/// # Errors
///
/// Refuses invalid or non-unit premises, malformed contextual explanations,
/// contradictory propagation, arithmetic overflow, or explicit round/conflict
/// limit exhaustion.
pub fn close_job_shop_conditional_energetic_units(
    problem: &JobShopProblem,
    bound: usize,
    premises: &[JobShopConditionalEnergeticConflict],
    limits: JobShopConditionalEnergeticFixpointLimits,
) -> Result<JobShopConditionalEnergeticFixpoint, JobShopError> {
    if limits.max_rounds == 0 {
        return Err(JobShopError::Malformed(
            "conditional energetic fixpoint requires a positive round limit".to_owned(),
        ));
    }
    let mut assumptions = Vec::new();
    for premise in premises {
        check_job_shop_conditional_energetic_conflict(problem, bound, premise)?;
        if premise.assumptions.len() != 1 {
            return Err(JobShopError::Malformed(
                "conditional energetic fixpoint premise is not unit".to_owned(),
            ));
        }
        merge_entailed_start_bound(
            &mut assumptions,
            negate_start_bound(premise.assumptions[0])?,
        );
    }
    let mut rounds = Vec::new();
    let mut all_conflicts = Vec::new();
    let mut stabilized = false;
    for _ in 0..limits.max_rounds {
        let scan = scan_job_shop_contextual_energetic_unit_conflicts(
            problem,
            bound,
            &assumptions,
            limits.unit,
        )?;
        let before = assumptions.clone();
        let mut changed = false;
        for conflict in &scan.conflicts {
            let bad_bound = new_conflicting_bound(&before, conflict)?;
            changed |= merge_entailed_start_bound(&mut assumptions, negate_start_bound(bad_bound)?);
        }
        all_conflicts.extend(scan.conflicts.iter().cloned());
        if all_conflicts.len() > limits.max_total_conflicts {
            return Err(JobShopError::LimitExceeded {
                resource: "conditional energetic fixpoint conflicts",
                observed: all_conflicts.len(),
                limit: limits.max_total_conflicts,
            });
        }
        rounds.push(JobShopConditionalEnergeticFixpointRound {
            assumptions_before: before,
            conflicts: scan.conflicts,
            assumptions_after: assumptions.clone(),
            candidates_checked: scan.candidates_checked,
            task_checks: scan.task_checks,
        });
        if !changed {
            stabilized = true;
            break;
        }
    }
    Ok(JobShopConditionalEnergeticFixpoint {
        rounds,
        assumptions,
        conflicts: all_conflicts,
        stabilized,
    })
}

/// Exhaustively scan integer intervals for a job-chain energetic overload.
///
/// The returned strongest interval maximizes exact utilization
/// `required_energy / capacity_energy`, with stable machine/start/end order as
/// the tie-breaker. This is a complete scan of integer intervals in
/// `[0,bound]` for the domains implied by job chains alone. A returned conflict
/// is immediately replayable by [`check_job_shop_energetic_conflict`].
///
/// # Errors
///
/// Refuses malformed instances, arithmetic overflow, or a scan exceeding an
/// explicit horizon/interval/task-check ceiling.
pub fn scan_job_shop_energetic_intervals(
    problem: &JobShopProblem,
    bound: usize,
    limits: JobShopEnergeticLimits,
) -> Result<JobShopEnergeticScan, JobShopError> {
    scan_job_shop_energetic_intervals_from_windows(
        problem,
        bound,
        limits,
        JobShopEnergeticDomain::JobChains,
        None,
    )
}

fn scan_job_shop_energetic_intervals_from_windows(
    problem: &JobShopProblem,
    bound: usize,
    limits: JobShopEnergeticLimits,
    domain: JobShopEnergeticDomain,
    propagated_windows: Option<&[JobShopOperationWindow]>,
) -> Result<JobShopEnergeticScan, JobShopError> {
    if bound > limits.max_horizon {
        return Err(JobShopError::LimitExceeded {
            resource: "energetic horizon",
            observed: bound,
            limit: limits.max_horizon,
        });
    }
    let per_machine = bound
        .checked_mul(bound.checked_add(1).ok_or_else(|| {
            JobShopError::Malformed("energetic interval count overflow".to_owned())
        })?)
        .and_then(|value| value.checked_div(2))
        .ok_or_else(|| JobShopError::Malformed("energetic interval count overflow".to_owned()))?;
    let intervals_checked = per_machine
        .checked_mul(problem.machines)
        .ok_or_else(|| JobShopError::Malformed("energetic interval count overflow".to_owned()))?;
    if intervals_checked > limits.max_intervals {
        return Err(JobShopError::LimitExceeded {
            resource: "energetic intervals",
            observed: intervals_checked,
            limit: limits.max_intervals,
        });
    }
    let task_checks = intervals_checked
        .checked_mul(problem.jobs.len())
        .ok_or_else(|| JobShopError::Malformed("energetic task-check overflow".to_owned()))?;
    if task_checks > limits.max_task_checks {
        return Err(JobShopError::LimitExceeded {
            resource: "energetic task checks",
            observed: task_checks,
            limit: limits.max_task_checks,
        });
    }

    let mut strongest: Option<(usize, CumulativeEnergeticCheck)> = None;
    for machine in 0..problem.machines {
        let tasks = job_shop_machine_task_windows(problem, bound, machine, propagated_windows)?;
        for interval_start in 0..bound {
            for interval_end in interval_start + 1..=bound {
                let check =
                    check_cumulative_energetic_interval(&tasks, 1, interval_start, interval_end)?;
                let replace = strongest.as_ref().is_none_or(|(_, best)| {
                    (check.required_energy as u128) * (best.capacity_energy as u128)
                        > (best.required_energy as u128) * (check.capacity_energy as u128)
                });
                if replace {
                    strongest = Some((machine, check));
                }
            }
        }
    }
    let (machine, check) = strongest.ok_or_else(|| {
        JobShopError::Malformed("energetic scan has no candidate intervals".to_owned())
    })?;
    let conflict = check.overloaded.then(|| JobShopEnergeticConflict {
        schema: JOB_SHOP_ENERGETIC_CONFLICT_SCHEMA.to_owned(),
        bound,
        machine,
        domain,
        interval_start: check.interval_start,
        interval_end: check.interval_end,
        required_energy: check.required_energy,
        capacity_energy: check.capacity_energy,
    });
    Ok(JobShopEnergeticScan {
        machine,
        check,
        intervals_checked,
        task_checks,
        conflict,
    })
}

/// Render a bounded job-shop feasibility question as deterministic `FlatZinc`.
///
/// The emitted model uses one bounded integer start variable per operation,
/// exact within-job precedence constraints, and one unit-capacity cumulative
/// constraint per machine (which is exactly disjunctive for positive-duration,
/// unit-demand operations). Its deliberately small predicate surface is shared
/// by Pumpkin's proof-logging solver and independent DRCP checker, allowing an
/// infeasibility certificate to remain bound to the exact portable model.
/// Operation domains include only the bounds implied by the job chain and the
/// requested makespan; no search-derived domain reduction is hidden here.
///
/// # Errors
///
/// Refuses malformed operation metadata, arithmetic overflow, or a bound that
/// is already contradicted by a single job chain.
pub fn job_shop_to_pumpkin_flatzinc(
    problem: &JobShopProblem,
    bound: usize,
) -> Result<String, JobShopError> {
    let (earliest, latest) = job_chain_windows(problem, bound)?;

    let mut text = String::from(
        "% Generated by Axeyum; schema=axeyum.job-shop-flatzinc.v1\n\
         predicate pumpkin_cumulative(array [int] of var int: s, array [int] of int: d, array [int] of int: r, int: b);\n",
    );
    for (job, operations) in problem.jobs.iter().enumerate() {
        for operation in 0..operations.len() {
            writeln!(
                text,
                "var {}..{}: s_{job}_{operation} :: output_var;",
                earliest[job][operation], latest[job][operation]
            )
            .expect("writing to a String cannot fail");
        }
    }
    for (job, operations) in problem.jobs.iter().enumerate() {
        for (operation, item) in operations.iter().enumerate().take(operations.len() - 1) {
            writeln!(
                text,
                "constraint int_lin_le([1,-1],[s_{job}_{operation},s_{job}_{}],-{});",
                operation + 1,
                item.duration
            )
            .expect("writing to a String cannot fail");
        }
    }
    for machine in 0..problem.machines {
        let mut starts = Vec::new();
        let mut durations = Vec::new();
        for (job, operations) in problem.jobs.iter().enumerate() {
            for (operation, item) in operations.iter().enumerate() {
                if item.machine == machine {
                    starts.push(format!("s_{job}_{operation}"));
                    durations.push(item.duration.to_string());
                }
            }
        }
        if starts.is_empty() {
            return Err(JobShopError::Malformed(format!(
                "machine {machine} has no operations"
            )));
        }
        writeln!(
            text,
            "constraint pumpkin_cumulative([{}],[{}],[{}],1);",
            starts.join(","),
            durations.join(","),
            std::iter::repeat_n("1", starts.len())
                .collect::<Vec<_>>()
                .join(",")
        )
        .expect("writing to a String cannot fail");
    }
    text.push_str("solve satisfy;\n");
    Ok(text)
}

fn parse_numbers(line: &str) -> Result<Vec<usize>, JobShopError> {
    line.split_whitespace()
        .map(|word| {
            word.parse::<usize>()
                .map_err(|_| JobShopError::Parse(format!("invalid integer `{word}`")))
        })
        .collect()
}

/// Parse one zero-based job permutation per machine.
///
/// This is the compact solution convention used by several public job-shop
/// archives: row `m` gives the processing order of jobs on machine `m`.
/// Blank lines and lines beginning with `#` are ignored.
///
/// # Errors
///
/// Refuses the wrong number of rows or jobs, non-integers, out-of-range job
/// indices, and repeated or missing jobs on any machine.
pub fn parse_job_shop_machine_orders(
    problem: &JobShopProblem,
    text: &str,
) -> Result<Vec<Vec<usize>>, JobShopError> {
    let rows = text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(parse_numbers)
        .collect::<Result<Vec<_>, _>>()?;
    if rows.len() != problem.machines {
        return Err(JobShopError::Parse(format!(
            "machine-order witness has {} rows, expected {}",
            rows.len(),
            problem.machines
        )));
    }
    for (machine, row) in rows.iter().enumerate() {
        if row.len() != problem.jobs.len() {
            return Err(JobShopError::Parse(format!(
                "machine {machine} has {} jobs, expected {}",
                row.len(),
                problem.jobs.len()
            )));
        }
        let mut seen = vec![false; problem.jobs.len()];
        for &job in row {
            if job >= problem.jobs.len() || seen[job] {
                return Err(JobShopError::Parse(format!(
                    "machine {machine} has invalid or repeated job {job}"
                )));
            }
            seen[job] = true;
        }
    }
    Ok(rows)
}

fn operation_ids_by_job_machine(
    problem: &JobShopProblem,
    ids: &[Vec<usize>],
) -> Result<Vec<Vec<usize>>, JobShopError> {
    let mut result = vec![vec![usize::MAX; problem.machines]; problem.jobs.len()];
    for (job, operations) in problem.jobs.iter().enumerate() {
        if operations.len() != problem.machines {
            return Err(JobShopError::Malformed(format!(
                "job {job} has {} operations, expected {}",
                operations.len(),
                problem.machines
            )));
        }
        for (operation, item) in operations.iter().enumerate() {
            if item.machine >= problem.machines
                || item.duration == 0
                || result[job][item.machine] != usize::MAX
            {
                return Err(JobShopError::Malformed(format!(
                    "job {job} has invalid operation metadata"
                )));
            }
            result[job][item.machine] = ids[job][operation];
        }
    }
    Ok(result)
}

/// Construct the deterministic earliest schedule induced by machine orders.
///
/// The precedence DAG contains every within-job edge and every consecutive
/// pair from each machine row. Stable topological longest paths then give the
/// earliest start of every operation. The result is independently replayed
/// before it is returned.
///
/// # Errors
///
/// Refuses malformed problem/order shapes, arithmetic overflow, or cyclic
/// orders (which do not describe a feasible non-preemptive schedule).
pub fn schedule_job_shop_machine_orders(
    problem: &JobShopProblem,
    orders: &[Vec<usize>],
) -> Result<JobShopSchedule, JobShopError> {
    if orders.len() != problem.machines {
        return Err(JobShopError::Malformed(format!(
            "machine-order witness has {} rows, expected {}",
            orders.len(),
            problem.machines
        )));
    }
    let (flat, ids) = flat_operations(problem);
    let operation_ids = operation_ids_by_job_machine(problem, &ids)?;

    let mut edges = vec![Vec::new(); flat.len()];
    let mut indegree = vec![0usize; flat.len()];
    let mut add_edge = |from: usize, to: usize| {
        edges[from].push(to);
        indegree[to] += 1;
    };
    for job_ids in &ids {
        for pair in job_ids.windows(2) {
            add_edge(pair[0], pair[1]);
        }
    }
    for (machine, row) in orders.iter().enumerate() {
        if row.len() != problem.jobs.len() {
            return Err(JobShopError::Malformed(format!(
                "machine {machine} has {} jobs, expected {}",
                row.len(),
                problem.jobs.len()
            )));
        }
        let mut seen = vec![false; problem.jobs.len()];
        let mut machine_ids = Vec::with_capacity(row.len());
        for &job in row {
            if job >= problem.jobs.len() || seen[job] {
                return Err(JobShopError::Malformed(format!(
                    "machine {machine} has invalid or repeated job {job}"
                )));
            }
            seen[job] = true;
            machine_ids.push(operation_ids[job][machine]);
        }
        for pair in machine_ids.windows(2) {
            add_edge(pair[0], pair[1]);
        }
    }

    let mut ready = indegree
        .iter()
        .enumerate()
        .filter_map(|(id, &degree)| (degree == 0).then_some(id))
        .collect::<BTreeSet<_>>();
    let mut earliest = vec![0usize; flat.len()];
    let mut emitted = 0usize;
    while let Some(id) = ready.pop_first() {
        emitted += 1;
        let end = earliest[id]
            .checked_add(flat[id].duration)
            .ok_or_else(|| JobShopError::Malformed("schedule time overflow".to_owned()))?;
        for &successor in &edges[id] {
            earliest[successor] = earliest[successor].max(end);
            indegree[successor] -= 1;
            if indegree[successor] == 0 {
                ready.insert(successor);
            }
        }
    }
    if emitted != flat.len() {
        return Err(JobShopError::InvalidSchedule(
            "machine orders and job chains contain a cycle".to_owned(),
        ));
    }
    let mut starts = problem
        .jobs
        .iter()
        .map(|operations| vec![0usize; operations.len()])
        .collect::<Vec<_>>();
    let mut makespan = 0usize;
    for (id, operation) in flat.iter().enumerate() {
        starts[operation.job][operation.operation] = earliest[id];
        makespan = makespan.max(
            earliest[id]
                .checked_add(operation.duration)
                .ok_or_else(|| JobShopError::Malformed("schedule time overflow".to_owned()))?,
        );
    }
    let schedule = JobShopSchedule {
        schema: JOB_SHOP_SCHEDULE_SCHEMA.to_owned(),
        makespan,
        starts,
    };
    check_job_shop_schedule(problem, &schedule)?;
    Ok(schedule)
}

/// Replay a complete schedule independently of the SAT encoding.
///
/// # Errors
///
/// Refuses schema/shape mismatch, arithmetic overflow, a wrong declared
/// makespan, precedence violations, or overlapping operations on a machine.
pub fn check_job_shop_schedule(
    problem: &JobShopProblem,
    schedule: &JobShopSchedule,
) -> Result<JobShopCheck, JobShopError> {
    if schedule.schema != JOB_SHOP_SCHEDULE_SCHEMA {
        return Err(JobShopError::Malformed(format!(
            "unsupported schema `{}`",
            schedule.schema
        )));
    }
    if schedule.starts.len() != problem.jobs.len() {
        return Err(JobShopError::Malformed("job count mismatch".to_owned()));
    }
    let mut by_machine = vec![Vec::new(); problem.machines];
    let mut recomputed = 0_usize;
    for (job, (operations, starts)) in problem.jobs.iter().zip(&schedule.starts).enumerate() {
        if starts.len() != operations.len() {
            return Err(JobShopError::Malformed(format!(
                "operation count mismatch for job {job}"
            )));
        }
        let mut previous_end = 0;
        for (operation_index, (&operation, &start)) in operations.iter().zip(starts).enumerate() {
            let end = start
                .checked_add(operation.duration)
                .ok_or_else(|| JobShopError::Malformed("schedule time overflow".to_owned()))?;
            if operation_index > 0 && start < previous_end {
                return Err(JobShopError::InvalidSchedule(format!(
                    "job {job} operation {operation_index} starts {start} before predecessor ends {previous_end}"
                )));
            }
            previous_end = end;
            recomputed = recomputed.max(end);
            by_machine[operation.machine].push((start, end, job, operation_index));
        }
    }
    for (machine, intervals) in by_machine.iter_mut().enumerate() {
        intervals.sort_unstable();
        for pair in intervals.windows(2) {
            if pair[1].0 < pair[0].1 {
                return Err(JobShopError::InvalidSchedule(format!(
                    "machine {machine} overlap: job {} operation {} and job {} operation {}",
                    pair[0].2, pair[0].3, pair[1].2, pair[1].3
                )));
            }
        }
    }
    if schedule.makespan != recomputed {
        return Err(JobShopError::InvalidSchedule(format!(
            "declared makespan {} differs from recomputed {recomputed}",
            schedule.makespan
        )));
    }
    Ok(JobShopCheck {
        operations: problem.operation_count(),
        makespan: recomputed,
    })
}

/// Stable admission limits for a bounded-makespan encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JobShopEncodingLimits {
    /// Maximum operations.
    pub max_operations: usize,
    /// Maximum time horizon.
    pub max_makespan: usize,
    /// Maximum CNF variables.
    pub max_variables: usize,
    /// Maximum CNF clauses.
    pub max_clauses: usize,
}

impl Default for JobShopEncodingLimits {
    fn default() -> Self {
        Self {
            max_operations: 10_000,
            max_makespan: 100_000,
            max_variables: 32_000_000,
            max_clauses: 64_000_000,
        }
    }
}

#[derive(Debug)]
struct Builder {
    variables: usize,
    clauses: Vec<Vec<(usize, bool)>>,
    limits: JobShopEncodingLimits,
}

impl Builder {
    fn variable(&mut self) -> Result<usize, JobShopError> {
        self.variables = self.variables.saturating_add(1);
        if self.variables > self.limits.max_variables {
            return Err(JobShopError::LimitExceeded {
                resource: "variables",
                observed: self.variables,
                limit: self.limits.max_variables,
            });
        }
        Ok(self.variables - 1)
    }

    fn clause(&mut self, literals: &[(usize, bool)]) -> Result<(), JobShopError> {
        self.clauses.push(literals.to_vec());
        if self.clauses.len() > self.limits.max_clauses {
            return Err(JobShopError::LimitExceeded {
                resource: "clauses",
                observed: self.clauses.len(),
                limit: self.limits.max_clauses,
            });
        }
        Ok(())
    }

    /// Sinz sequential at-most-one; returned entries are prefix-OR variables.
    fn at_most_one(&mut self, choices: &[usize]) -> Result<Vec<usize>, JobShopError> {
        if choices.len() < 2 {
            return Ok(Vec::new());
        }
        let mut prefix = Vec::with_capacity(choices.len() - 1);
        for _ in 1..choices.len() {
            prefix.push(self.variable()?);
        }
        self.clause(&[(choices[0], true), (prefix[0], false)])?;
        for index in 1..choices.len() - 1 {
            self.clause(&[(choices[index], true), (prefix[index], false)])?;
            self.clause(&[(prefix[index - 1], true), (prefix[index], false)])?;
            self.clause(&[(choices[index], true), (prefix[index - 1], true)])?;
        }
        self.clause(&[
            (*choices.last().expect("length checked"), true),
            (*prefix.last().expect("length checked"), true),
        ])?;
        Ok(prefix)
    }

    fn exactly_one(&mut self, choices: &[usize]) -> Result<Vec<usize>, JobShopError> {
        self.clause(
            &choices
                .iter()
                .copied()
                .map(|variable| (variable, false))
                .collect::<Vec<_>>(),
        )?;
        self.at_most_one(choices)
    }

    fn finish(self) -> Result<CnfFormula, JobShopError> {
        let mut formula = CnfFormula::new(self.variables);
        for clause in self.clauses {
            let literals = clause
                .into_iter()
                .map(|(variable, negated)| {
                    let literal = CnfLit::positive(
                        CnfVar::new(variable)
                            .map_err(|error| JobShopError::Cnf(format!("variable: {error:?}")))?,
                    );
                    Ok(if negated { literal.negated() } else { literal })
                })
                .collect::<Result<Vec<_>, JobShopError>>()?;
            formula
                .add_clause(CnfClause::new(literals))
                .map_err(|error| JobShopError::Cnf(format!("clause: {error:?}")))?;
        }
        Ok(formula)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct OperationLayout {
    earliest: usize,
    choices: Vec<usize>,
    prefix: Vec<usize>,
}

/// One semantic same-machine ordering decision in a job-shop encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JobShopMachineOrder {
    /// Machine shared by the two operations.
    pub machine: usize,
    /// Job index of the left operation.
    pub left_job: usize,
    /// Operation index within the left job.
    pub left_operation: usize,
    /// Job index of the right operation.
    pub right_job: usize,
    /// Operation index within the right job.
    pub right_operation: usize,
    /// CNF selector; true means the left operation finishes before the right starts.
    pub selector: CnfVar,
    /// Whether exact operation windows already force this selector.
    pub status: JobShopMachineOrderStatus,
}

/// Window-derived status of one same-machine ordering decision.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JobShopMachineOrderStatus {
    /// Both non-overlap directions remain possible from the individual windows.
    Free,
    /// The left operation must finish before the right operation starts.
    ForcedLeftBeforeRight,
    /// The right operation must finish before the left operation starts.
    ForcedRightBeforeLeft,
    /// Neither ordering fits the two operation windows, proving the bound infeasible.
    Infeasible,
}

/// One operation domain after deterministic precedence propagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JobShopOperationWindow {
    /// Job index.
    pub job: usize,
    /// Operation index within the job.
    pub operation: usize,
    /// Smallest start not excluded by the propagated precedence graph.
    pub earliest: usize,
    /// Largest start not excluded by the propagated precedence graph.
    pub latest: usize,
}

/// Reusable result of job-chain and detectable-precedence propagation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JobShopPrecedencePropagation {
    /// Windows in job/operation order. Empty when `infeasible` is true.
    pub windows: Vec<JobShopOperationWindow>,
    /// Machine-pair statuses in the same deterministic order as the encoder.
    pub machine_orders: Vec<JobShopMachineOrderStatus>,
    /// Number of closure rounds that added at least one machine precedence.
    pub rounds: usize,
    /// Whether propagation alone proves that the makespan bound is impossible.
    pub infeasible: bool,
}

#[derive(Debug, Clone)]
struct FlatOperation {
    job: usize,
    operation: usize,
    duration: usize,
}

fn flat_operations(problem: &JobShopProblem) -> (Vec<FlatOperation>, Vec<Vec<usize>>) {
    let mut flat = Vec::with_capacity(problem.operation_count());
    let mut ids = Vec::with_capacity(problem.jobs.len());
    for (job, operations) in problem.jobs.iter().enumerate() {
        let mut job_ids = Vec::with_capacity(operations.len());
        for (operation, item) in operations.iter().enumerate() {
            job_ids.push(flat.len());
            flat.push(FlatOperation {
                job,
                operation,
                duration: item.duration,
            });
        }
        ids.push(job_ids);
    }
    (flat, ids)
}

fn machine_pairs(problem: &JobShopProblem, ids: &[Vec<usize>]) -> Vec<(usize, usize)> {
    let mut pairs = Vec::new();
    for machine in 0..problem.machines {
        let mut on_machine = Vec::new();
        for (job, operations) in problem.jobs.iter().enumerate() {
            for (operation, item) in operations.iter().enumerate() {
                if item.machine == machine {
                    on_machine.push(ids[job][operation]);
                }
            }
        }
        for left in 0..on_machine.len() {
            for right in left + 1..on_machine.len() {
                pairs.push((on_machine[left], on_machine[right]));
            }
        }
    }
    pairs
}

fn precedence_bounds(
    operations: &[FlatOperation],
    edges: &[Vec<usize>],
    bound: usize,
    initial_windows: Option<&[JobShopOperationWindow]>,
) -> Option<(Vec<usize>, Vec<usize>)> {
    let count = operations.len();
    let mut indegree = vec![0usize; count];
    for successors in edges {
        for &successor in successors {
            indegree[successor] += 1;
        }
    }
    let mut emitted = vec![false; count];
    let mut topo = Vec::with_capacity(count);
    while topo.len() < count {
        let next = (0..count).find(|&id| !emitted[id] && indegree[id] == 0)?;
        emitted[next] = true;
        topo.push(next);
        for &successor in &edges[next] {
            indegree[successor] -= 1;
        }
    }

    let mut earliest = if let Some(windows) = initial_windows {
        if windows.len() != count {
            return None;
        }
        windows
            .iter()
            .zip(operations)
            .map(|(window, operation)| {
                (window.job == operation.job && window.operation == operation.operation)
                    .then_some(window.earliest)
            })
            .collect::<Option<Vec<_>>>()?
    } else {
        vec![0usize; count]
    };
    for &operation in &topo {
        let end = earliest[operation].checked_add(operations[operation].duration)?;
        for &successor in &edges[operation] {
            earliest[successor] = earliest[successor].max(end);
        }
    }
    let mut latest = if let Some(windows) = initial_windows {
        windows.iter().map(|window| window.latest).collect()
    } else {
        operations
            .iter()
            .map(|operation| bound.checked_sub(operation.duration))
            .collect::<Option<Vec<_>>>()?
    };
    for &operation in topo.iter().rev() {
        for &successor in &edges[operation] {
            latest[operation] = latest[operation]
                .min(latest[successor].checked_sub(operations[operation].duration)?);
        }
        if earliest[operation] > latest[operation] {
            return None;
        }
    }
    Some((earliest, latest))
}

/// Propagate job precedences and pairwise detectable machine precedences to a
/// deterministic fixpoint.
///
/// Each added machine edge is logically necessary: the opposite direction is
/// impossible under the current exact precedence windows. A cyclic graph,
/// empty operation window, or machine pair with neither feasible direction
/// reports `infeasible` rather than manufacturing a schedule or proof.
///
/// # Errors
///
/// Refuses malformed operation metadata or arithmetic overflow.
fn propagate_job_shop_precedences_from_windows(
    problem: &JobShopProblem,
    bound: usize,
    initial_windows: Option<&[JobShopOperationWindow]>,
) -> Result<JobShopPrecedencePropagation, JobShopError> {
    if problem.jobs.is_empty() || problem.machines == 0 {
        return Err(JobShopError::Malformed("empty problem".to_owned()));
    }
    for operations in &problem.jobs {
        for operation in operations {
            if operation.machine >= problem.machines || operation.duration == 0 {
                return Err(JobShopError::Malformed(
                    "invalid operation machine or duration".to_owned(),
                ));
            }
        }
    }
    let (operations, ids) = flat_operations(problem);
    let pairs = machine_pairs(problem, &ids);
    let mut edges = vec![Vec::new(); operations.len()];
    for job_ids in &ids {
        for pair in job_ids.windows(2) {
            edges[pair[0]].push(pair[1]);
        }
    }
    let mut statuses = vec![JobShopMachineOrderStatus::Free; pairs.len()];
    let mut rounds = 0;
    loop {
        let Some((earliest, latest)) =
            precedence_bounds(&operations, &edges, bound, initial_windows)
        else {
            return Ok(JobShopPrecedencePropagation {
                windows: Vec::new(),
                machine_orders: statuses,
                rounds,
                infeasible: true,
            });
        };
        let mut added = false;
        for (index, &(left, right)) in pairs.iter().enumerate() {
            if statuses[index] != JobShopMachineOrderStatus::Free {
                continue;
            }
            let left_before = earliest[left]
                .checked_add(operations[left].duration)
                .is_some_and(|end| end <= latest[right]);
            let right_before = earliest[right]
                .checked_add(operations[right].duration)
                .is_some_and(|end| end <= latest[left]);
            match (left_before, right_before) {
                (true, false) => {
                    statuses[index] = JobShopMachineOrderStatus::ForcedLeftBeforeRight;
                    if !edges[left].contains(&right) {
                        edges[left].push(right);
                        edges[left].sort_unstable();
                        added = true;
                    }
                }
                (false, true) => {
                    statuses[index] = JobShopMachineOrderStatus::ForcedRightBeforeLeft;
                    if !edges[right].contains(&left) {
                        edges[right].push(left);
                        edges[right].sort_unstable();
                        added = true;
                    }
                }
                (false, false) => {
                    statuses[index] = JobShopMachineOrderStatus::Infeasible;
                    return Ok(JobShopPrecedencePropagation {
                        windows: Vec::new(),
                        machine_orders: statuses,
                        rounds,
                        infeasible: true,
                    });
                }
                (true, true) => {}
            }
        }
        if !added {
            let windows = operations
                .iter()
                .enumerate()
                .map(|(id, operation)| JobShopOperationWindow {
                    job: operation.job,
                    operation: operation.operation,
                    earliest: earliest[id],
                    latest: latest[id],
                })
                .collect();
            return Ok(JobShopPrecedencePropagation {
                windows,
                machine_orders: statuses,
                rounds,
                infeasible: false,
            });
        }
        rounds += 1;
    }
}

/// Propagate job precedences and pairwise detectable machine precedences to a
/// deterministic fixpoint.
///
/// # Errors
///
/// Refuses malformed operation metadata or arithmetic overflow.
pub fn propagate_job_shop_precedences(
    problem: &JobShopProblem,
    bound: usize,
) -> Result<JobShopPrecedencePropagation, JobShopError> {
    propagate_job_shop_precedences_from_windows(problem, bound, None)
}

/// Propagate explicit start bounds through job and detectable machine edges.
///
/// Bounds are canonical semantic assumptions, not raw solver literals. The
/// propagation starts from exact job-chain windows narrowed by those bounds,
/// then repeats deterministic detectable-precedence closure to a fixpoint.
/// Assumptions may concern any machine; their consequences can cross machines
/// through job chains.
///
/// # Errors
///
/// Refuses noncanonical, redundant, contradictory, or out-of-range bounds,
/// malformed problem metadata, or arithmetic overflow.
pub fn propagate_job_shop_precedences_with_start_bounds(
    problem: &JobShopProblem,
    bound: usize,
    assumptions: &[JobShopStartBound],
) -> Result<JobShopPrecedencePropagation, JobShopError> {
    let mut windows = job_shop_domain_windows(problem, bound, JobShopEnergeticDomain::JobChains)?;
    apply_job_shop_start_bounds(problem, None, assumptions, &mut windows)?;
    propagate_job_shop_precedences_from_windows(problem, bound, Some(&windows))
}

/// Scan energetic intervals after detectable-precedence closure.
///
/// This composes two independently replayable inference layers: first the
/// deterministic closure derives tighter operation domains from necessary
/// machine orders, then the generic energetic checker searches those domains
/// for a resource overload. Any emitted conflict records this domain route and
/// [`check_job_shop_energetic_conflict`] recomputes both layers.
///
/// # Errors
///
/// As [`propagate_job_shop_precedences`] and
/// [`scan_job_shop_energetic_intervals`]. If precedence closure alone already
/// proves infeasibility, reports that distinct condition instead of inventing
/// an energetic certificate.
pub fn scan_job_shop_energetic_intervals_with_precedence_closure(
    problem: &JobShopProblem,
    bound: usize,
    limits: JobShopEnergeticLimits,
) -> Result<JobShopEnergeticScan, JobShopError> {
    let propagation = propagate_job_shop_precedences(problem, bound)?;
    if propagation.infeasible {
        return Err(JobShopError::InvalidSchedule(
            "precedence closure is already infeasible".to_owned(),
        ));
    }
    scan_job_shop_energetic_intervals_from_windows(
        problem,
        bound,
        limits,
        JobShopEnergeticDomain::PrecedenceClosure,
        Some(&propagation.windows),
    )
}

/// Propagate explicit start bounds, then exhaustively scan energetic intervals.
///
/// The returned conflict, when present, records the complete assumption
/// conjunction and uses [`JobShopEnergeticDomain::AssumptionClosure`], so
/// independent replay reconstructs both propagation and the overload. A
/// merely strong interval remains a measurement and emits no certificate.
///
/// # Errors
///
/// Refuses malformed assumptions, a context already contradicted by precedence
/// propagation, arithmetic overflow, or scan work exceeding explicit limits.
pub fn scan_job_shop_conditional_energetic_intervals_with_start_bounds(
    problem: &JobShopProblem,
    bound: usize,
    assumptions: &[JobShopStartBound],
    limits: JobShopEnergeticLimits,
) -> Result<JobShopConditionalEnergeticContextScan, JobShopError> {
    let propagation =
        propagate_job_shop_precedences_with_start_bounds(problem, bound, assumptions)?;
    if propagation.infeasible {
        return Err(JobShopError::InvalidSchedule(
            "start-bound context is already infeasible by precedence propagation".to_owned(),
        ));
    }
    let scan = scan_job_shop_energetic_intervals_from_windows(
        problem,
        bound,
        limits,
        JobShopEnergeticDomain::AssumptionClosure,
        Some(&propagation.windows),
    )?;
    let conflict = scan
        .conflict
        .map(|root| JobShopConditionalEnergeticConflict {
            schema: JOB_SHOP_CONDITIONAL_ENERGETIC_CONFLICT_SCHEMA.to_owned(),
            bound,
            domain: JobShopEnergeticDomain::AssumptionClosure,
            assumptions: assumptions.to_vec(),
            machine: root.machine,
            interval_start: root.interval_start,
            interval_end: root.interval_end,
            required_energy: root.required_energy,
            capacity_energy: root.capacity_energy,
        });
    if let Some(conflict) = &conflict {
        check_job_shop_conditional_energetic_conflict(problem, bound, conflict)?;
    }
    Ok(JobShopConditionalEnergeticContextScan {
        propagation,
        check: scan.check,
        machine: scan.machine,
        intervals_checked: scan.intervals_checked,
        task_checks: scan.task_checks,
        conflict,
    })
}

/// Exact CNF question “does this instance have makespan at most `bound`?”.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JobShopEncoding {
    formula: CnfFormula,
    problem: JobShopProblem,
    bound: usize,
    layout: Vec<Vec<OperationLayout>>,
    machine_orders: Vec<JobShopMachineOrder>,
    propagation: Option<JobShopPrecedencePropagation>,
}

impl JobShopEncoding {
    /// Exact deterministic formula.
    pub fn formula(&self) -> &CnfFormula {
        &self.formula
    }

    /// Complete deterministic list of same-machine order decisions.
    ///
    /// Each unordered pair of operations sharing a machine occurs exactly
    /// once. A true selector orders the left operation before the right; a
    /// false selector orders the right operation before the left.
    pub fn machine_orders(&self) -> &[JobShopMachineOrder] {
        &self.machine_orders
    }

    /// Precedence-closure measurements when that encoding route was selected.
    pub fn precedence_propagation(&self) -> Option<&JobShopPrecedencePropagation> {
        self.propagation.as_ref()
    }

    /// Lift a satisfying model and independently replay the schedule.
    ///
    /// # Errors
    ///
    /// Refuses a wrong-width/non-satisfying model or a lifted schedule that
    /// fails the independent checker.
    pub fn lift_model(&self, model: &CnfAssignment) -> Result<JobShopSchedule, JobShopError> {
        if !self
            .formula
            .evaluate(model.values())
            .map_err(|error| JobShopError::Cnf(format!("evaluation: {error:?}")))?
        {
            return Err(JobShopError::InvalidSchedule(
                "model does not satisfy formula".to_owned(),
            ));
        }
        let starts = self
            .layout
            .iter()
            .map(|job| {
                job.iter()
                    .map(|operation| {
                        operation
                            .choices
                            .iter()
                            .position(|&variable| model.values()[variable])
                            .map(|offset| operation.earliest + offset)
                            .ok_or_else(|| {
                                JobShopError::InvalidSchedule(
                                    "operation has no selected start".to_owned(),
                                )
                            })
                    })
                    .collect::<Result<Vec<_>, JobShopError>>()
            })
            .collect::<Result<Vec<_>, JobShopError>>()?;
        let makespan = self
            .problem
            .jobs
            .iter()
            .zip(&starts)
            .flat_map(|(operations, starts)| operations.iter().zip(starts))
            .map(|(operation, &start)| start + operation.duration)
            .max()
            .unwrap_or(0);
        let schedule = JobShopSchedule {
            schema: JOB_SHOP_SCHEDULE_SCHEMA.to_owned(),
            makespan,
            starts,
        };
        check_job_shop_schedule(&self.problem, &schedule)?;
        if schedule.makespan > self.bound {
            return Err(JobShopError::InvalidSchedule(
                "lifted schedule exceeds encoded bound".to_owned(),
            ));
        }
        Ok(schedule)
    }

    /// Pin a checked schedule into the exact formula.
    ///
    /// # Errors
    ///
    /// Refuses an invalid schedule or one exceeding the encoded bound.
    pub fn formula_with_schedule(
        &self,
        schedule: &JobShopSchedule,
    ) -> Result<CnfFormula, JobShopError> {
        check_job_shop_schedule(&self.problem, schedule)?;
        if schedule.makespan > self.bound {
            return Err(JobShopError::InvalidSchedule(format!(
                "makespan {} exceeds bound {}",
                schedule.makespan, self.bound
            )));
        }
        let mut formula = self.formula.clone();
        for (job_layout, starts) in self.layout.iter().zip(&schedule.starts) {
            for (operation, &start) in job_layout.iter().zip(starts) {
                for (offset, &variable) in operation.choices.iter().enumerate() {
                    let time = operation.earliest + offset;
                    let literal =
                        CnfLit::positive(CnfVar::new(variable).map_err(|error| {
                            JobShopError::Cnf(format!("pin variable: {error:?}"))
                        })?);
                    formula
                        .add_clause(CnfClause::new(vec![if time == start {
                            literal
                        } else {
                            literal.negated()
                        }]))
                        .map_err(|error| JobShopError::Cnf(format!("pin: {error:?}")))?;
                }
            }
        }
        Ok(formula)
    }

    /// Translate a checked conditional energetic conflict into a CNF clause.
    ///
    /// Each start-bound assumption is represented by the existing exact
    /// prefix-OR variables. The returned clause is the disjunction of the
    /// assumptions' semantic negations. `None` means one assumption is already
    /// impossible in this encoding's (possibly tighter) operation layout, so
    /// its negation is a tautology and adding a clause would have no effect.
    ///
    /// # Errors
    ///
    /// Refuses a certificate that fails independent energetic replay or an
    /// operation/layout mismatch.
    pub fn conditional_energetic_clause(
        &self,
        conflict: &JobShopConditionalEnergeticConflict,
    ) -> Result<Option<CnfClause>, JobShopError> {
        check_job_shop_conditional_energetic_conflict(&self.problem, self.bound, conflict)?;
        let mut literals = Vec::with_capacity(conflict.assumptions.len());
        for assumption in &conflict.assumptions {
            let (job, operation, time) = match *assumption {
                JobShopStartBound::StartAtLeast {
                    job,
                    operation,
                    time,
                }
                | JobShopStartBound::StartAtMost {
                    job,
                    operation,
                    time,
                } => (job, operation, time),
            };
            let layout = self
                .layout
                .get(job)
                .and_then(|operations| operations.get(operation))
                .ok_or_else(|| {
                    JobShopError::Malformed(
                        "conditional energetic operation/layout mismatch".to_owned(),
                    )
                })?;
            let latest = layout
                .earliest
                .checked_add(layout.choices.len().saturating_sub(1))
                .ok_or_else(|| JobShopError::Malformed("layout bound overflow".to_owned()))?;
            match *assumption {
                JobShopStartBound::StartAtLeast { .. } => {
                    if layout.earliest >= time {
                        continue;
                    }
                    if latest < time {
                        return Ok(None);
                    }
                    let prefix = layout.prefix[time - layout.earliest - 1];
                    literals.push(CnfLit::positive(CnfVar::new(prefix).map_err(|error| {
                        JobShopError::Cnf(format!("conditional prefix variable: {error:?}"))
                    })?));
                }
                JobShopStartBound::StartAtMost { .. } => {
                    if latest <= time {
                        continue;
                    }
                    if layout.earliest > time {
                        return Ok(None);
                    }
                    let prefix = layout.prefix[time - layout.earliest];
                    literals.push(
                        CnfLit::positive(CnfVar::new(prefix).map_err(|error| {
                            JobShopError::Cnf(format!("conditional prefix variable: {error:?}"))
                        })?)
                        .negated(),
                    );
                }
            }
        }
        Ok(Some(CnfClause::new(literals)))
    }

    /// Add one independently checked conditional energetic clause.
    ///
    /// A tautological explanation leaves the formula byte-for-byte unchanged.
    ///
    /// # Errors
    ///
    /// As [`Self::conditional_energetic_clause`], plus CNF insertion errors.
    pub fn formula_with_conditional_energetic_conflict(
        &self,
        conflict: &JobShopConditionalEnergeticConflict,
    ) -> Result<CnfFormula, JobShopError> {
        let mut formula = self.formula.clone();
        if let Some(clause) = self.conditional_energetic_clause(conflict)? {
            formula.add_clause(clause).map_err(|error| {
                JobShopError::Cnf(format!("conditional energetic clause: {error:?}"))
            })?;
        }
        Ok(formula)
    }

    /// Add several independently checked conditional energetic clauses.
    ///
    /// Conflicts are replayed and inserted in caller order. Tautological
    /// explanations are skipped, and the base formula is cloned only once.
    ///
    /// # Errors
    ///
    /// As [`Self::conditional_energetic_clause`], plus CNF insertion errors.
    pub fn formula_with_conditional_energetic_conflicts(
        &self,
        conflicts: &[JobShopConditionalEnergeticConflict],
    ) -> Result<CnfFormula, JobShopError> {
        let mut formula = self.formula.clone();
        for conflict in conflicts {
            if let Some(clause) = self.conditional_energetic_clause(conflict)? {
                formula.add_clause(clause).map_err(|error| {
                    JobShopError::Cnf(format!("conditional energetic clause: {error:?}"))
                })?;
            }
        }
        Ok(formula)
    }
}

fn encode_machine_orders(
    problem: &JobShopProblem,
    layout: &[Vec<OperationLayout>],
    builder: &mut Builder,
    detectable_precedence: bool,
    propagated_statuses: Option<&[JobShopMachineOrderStatus]>,
) -> Result<Vec<JobShopMachineOrder>, JobShopError> {
    let mut orders = Vec::new();
    let mut pair_index = 0;
    for machine in 0..problem.machines {
        let mut operations_on_machine = Vec::new();
        for (job, operations) in problem.jobs.iter().enumerate() {
            for (operation, item) in operations.iter().enumerate() {
                if item.machine == machine {
                    operations_on_machine.push((job, operation));
                }
            }
        }
        for left in 0..operations_on_machine.len() {
            for right in left + 1..operations_on_machine.len() {
                let (left_job, left_operation) = operations_on_machine[left];
                let (right_job, right_operation) = operations_on_machine[right];
                let order = builder.variable()?;
                let left_item = problem.jobs[left_job][left_operation];
                let right_item = problem.jobs[right_job][right_operation];
                let left_layout = &layout[left_job][left_operation];
                let right_layout = &layout[right_job][right_operation];
                let status = if let Some(statuses) = propagated_statuses {
                    *statuses.get(pair_index).ok_or_else(|| {
                        JobShopError::Malformed("machine-order propagation mismatch".to_owned())
                    })?
                } else if detectable_precedence
                    && !left_layout.choices.is_empty()
                    && !right_layout.choices.is_empty()
                {
                    let left_latest = left_layout.earliest + left_layout.choices.len() - 1;
                    let right_latest = right_layout.earliest + right_layout.choices.len() - 1;
                    let left_before_possible =
                        left_layout.earliest + left_item.duration <= right_latest;
                    let right_before_possible =
                        right_layout.earliest + right_item.duration <= left_latest;
                    match (left_before_possible, right_before_possible) {
                        (true, false) => JobShopMachineOrderStatus::ForcedLeftBeforeRight,
                        (false, true) => JobShopMachineOrderStatus::ForcedRightBeforeLeft,
                        (false, false) => JobShopMachineOrderStatus::Infeasible,
                        (true, true) => JobShopMachineOrderStatus::Free,
                    }
                } else {
                    JobShopMachineOrderStatus::Free
                };
                pair_index += 1;
                orders.push(JobShopMachineOrder {
                    machine,
                    left_job,
                    left_operation,
                    right_job,
                    right_operation,
                    selector: CnfVar::new(order)
                        .map_err(|error| JobShopError::Cnf(format!("order variable: {error:?}")))?,
                    status,
                });

                match status {
                    JobShopMachineOrderStatus::Free => {}
                    JobShopMachineOrderStatus::ForcedLeftBeforeRight => {
                        builder.clause(&[(order, false)])?;
                    }
                    JobShopMachineOrderStatus::ForcedRightBeforeLeft => {
                        builder.clause(&[(order, true)])?;
                    }
                    JobShopMachineOrderStatus::Infeasible => builder.clause(&[])?,
                }

                for (offset, &choice) in left_layout.choices.iter().enumerate() {
                    let start = left_layout.earliest + offset;
                    let cutoff = start + left_item.duration - 1;
                    if cutoff >= right_layout.earliest {
                        let mut clause = vec![(order, true), (choice, true)];
                        let relative = cutoff - right_layout.earliest;
                        if relative + 1 < right_layout.choices.len() {
                            clause.push((right_layout.prefix[relative], true));
                        }
                        builder.clause(&clause)?;
                    }
                }
                for (offset, &choice) in right_layout.choices.iter().enumerate() {
                    let start = right_layout.earliest + offset;
                    let cutoff = start + right_item.duration - 1;
                    if cutoff >= left_layout.earliest {
                        let mut clause = vec![(order, false), (choice, true)];
                        let relative = cutoff - left_layout.earliest;
                        if relative + 1 < left_layout.choices.len() {
                            clause.push((left_layout.prefix[relative], true));
                        }
                        builder.clause(&clause)?;
                    }
                }
            }
        }
    }
    if propagated_statuses.is_some_and(|statuses| statuses.len() != pair_index) {
        return Err(JobShopError::Malformed(
            "machine-order propagation mismatch".to_owned(),
        ));
    }
    Ok(orders)
}

/// Encode the complete bounded-makespan question.
///
/// # Errors
///
/// Refuses malformed/resource-exceeding inputs. A duration larger than the
/// bound yields an explicit empty clause, not a construction error.
pub fn encode_job_shop(
    problem: &JobShopProblem,
    bound: usize,
    limits: JobShopEncodingLimits,
) -> Result<JobShopEncoding, JobShopError> {
    encode_job_shop_internal(problem, bound, limits, false, false, false)
}

/// Encode the complete bounded-makespan question after intersecting every
/// operation's start domain with the exact earliest/latest window implied by
/// its own job chain.
///
/// This is equisatisfiable with [`encode_job_shop`], but keeps only starts
/// between the sum of preceding durations and `bound` minus the sum of this
/// and following durations. The independent schedule checker and model lifting
/// remain unchanged.
///
/// # Errors
///
/// As [`encode_job_shop`]. Duration-sum overflow is rejected as malformed.
pub fn encode_job_shop_with_job_windows(
    problem: &JobShopProblem,
    bound: usize,
    limits: JobShopEncodingLimits,
) -> Result<JobShopEncoding, JobShopError> {
    encode_job_shop_internal(problem, bound, limits, true, false, false)
}

/// Encode with exact job-chain windows and explicit detectable-precedence units.
///
/// For each same-machine pair, if one direction is impossible from the two
/// operations' individual earliest/latest windows, this route adds the
/// logically entailed unit for the remaining order. The semantic order list
/// records which selectors were forced. Pairs for which both directions remain
/// possible are unchanged.
///
/// # Errors
///
/// As [`encode_job_shop_with_job_windows`].
pub fn encode_job_shop_with_detectable_precedence(
    problem: &JobShopProblem,
    bound: usize,
    limits: JobShopEncodingLimits,
) -> Result<JobShopEncoding, JobShopError> {
    encode_job_shop_internal(problem, bound, limits, true, true, false)
}

/// Encode after propagating job and detectable machine precedences to a
/// fixpoint, then allocating only the resulting start windows.
///
/// This route is complete for the same bounded-makespan question as
/// [`encode_job_shop`]. Every added precedence is forced by the opposite
/// direction being impossible under the current exact graph windows.
///
/// # Errors
///
/// As [`encode_job_shop_with_job_windows`].
pub fn encode_job_shop_with_precedence_closure(
    problem: &JobShopProblem,
    bound: usize,
    limits: JobShopEncodingLimits,
) -> Result<JobShopEncoding, JobShopError> {
    encode_job_shop_internal(problem, bound, limits, true, true, true)
}

fn encode_operation_layouts(
    problem: &JobShopProblem,
    bound: usize,
    builder: &mut Builder,
    job_windows: bool,
    propagated_windows: Option<&[JobShopOperationWindow]>,
) -> Result<Vec<Vec<OperationLayout>>, JobShopError> {
    let mut layout = Vec::with_capacity(problem.jobs.len());
    let mut window_index = 0;
    for (job, operations) in problem.jobs.iter().enumerate() {
        let total_duration = operations.iter().try_fold(0usize, |sum, operation| {
            sum.checked_add(operation.duration)
                .ok_or_else(|| JobShopError::Malformed("job duration sum overflow".to_owned()))
        })?;
        let mut preceding_duration = 0usize;
        let mut job_layout = Vec::with_capacity(operations.len());
        for (operation_index, operation) in operations.iter().enumerate() {
            if operation.machine >= problem.machines || operation.duration == 0 {
                return Err(JobShopError::Malformed(
                    "invalid operation machine or duration".to_owned(),
                ));
            }
            let propagated = propagated_windows.and_then(|windows| windows.get(window_index));
            if propagated
                .is_some_and(|window| window.job != job || window.operation != operation_index)
            {
                return Err(JobShopError::Malformed(
                    "operation-window propagation mismatch".to_owned(),
                ));
            }
            let earliest = propagated.map_or_else(
                || if job_windows { preceding_duration } else { 0 },
                |window| window.earliest,
            );
            let remaining_duration = total_duration - preceding_duration;
            let latest = propagated.map(|window| window.latest).or_else(|| {
                if job_windows {
                    bound.checked_sub(remaining_duration)
                } else {
                    bound.checked_sub(operation.duration)
                }
            });
            let count = latest
                .filter(|&latest| latest >= earliest)
                .map_or(0, |latest| latest - earliest + 1);
            let mut choices = Vec::with_capacity(count);
            for _ in 0..count {
                choices.push(builder.variable()?);
            }
            let prefix = builder.exactly_one(&choices)?;
            job_layout.push(OperationLayout {
                earliest,
                choices,
                prefix,
            });
            preceding_duration = preceding_duration
                .checked_add(operation.duration)
                .ok_or_else(|| JobShopError::Malformed("job duration sum overflow".to_owned()))?;
            window_index += 1;
        }
        layout.push(job_layout);
    }
    Ok(layout)
}

fn encode_job_shop_internal(
    problem: &JobShopProblem,
    bound: usize,
    limits: JobShopEncodingLimits,
    job_windows: bool,
    detectable_precedence: bool,
    precedence_closure: bool,
) -> Result<JobShopEncoding, JobShopError> {
    if problem.jobs.is_empty() || problem.machines == 0 {
        return Err(JobShopError::Malformed("empty problem".to_owned()));
    }
    let operation_count = problem.operation_count();
    if operation_count > limits.max_operations {
        return Err(JobShopError::LimitExceeded {
            resource: "operations",
            observed: operation_count,
            limit: limits.max_operations,
        });
    }
    if bound > limits.max_makespan {
        return Err(JobShopError::LimitExceeded {
            resource: "makespan",
            observed: bound,
            limit: limits.max_makespan,
        });
    }
    let mut builder = Builder {
        variables: 0,
        clauses: Vec::new(),
        limits,
    };
    let propagation = if precedence_closure {
        Some(propagate_job_shop_precedences(problem, bound)?)
    } else {
        None
    };
    let propagated_windows = propagation
        .as_ref()
        .filter(|result| !result.infeasible)
        .map(|result| result.windows.as_slice());
    let layout = encode_operation_layouts(
        problem,
        bound,
        &mut builder,
        job_windows,
        propagated_windows,
    )?;

    // Successor at u implies predecessor started no later than u-duration.
    for (operations, job_layout) in problem.jobs.iter().zip(&layout) {
        for index in 1..operations.len() {
            let predecessor = &job_layout[index - 1];
            let duration = operations[index - 1].duration;
            for (successor_offset, &successor_variable) in
                job_layout[index].choices.iter().enumerate()
            {
                let successor_start = job_layout[index].earliest + successor_offset;
                if successor_start < duration {
                    builder.clause(&[(successor_variable, true)])?;
                } else {
                    let latest = successor_start - duration;
                    let implication = if latest < predecessor.earliest {
                        builder.clause(&[(successor_variable, true)])?;
                        continue;
                    } else if latest - predecessor.earliest + 1 >= predecessor.choices.len() {
                        None
                    } else {
                        predecessor
                            .prefix
                            .get(latest - predecessor.earliest)
                            .copied()
                    };
                    if let Some(prefix) = implication {
                        builder.clause(&[(successor_variable, true), (prefix, false)])?;
                    }
                }
            }
        }
    }

    // One order bit per same-machine operation pair. Conditional prefix
    // clauses force the selected first operation to finish before the second.
    let propagated_statuses = propagation
        .as_ref()
        .map(|result| result.machine_orders.as_slice());
    let machine_orders = encode_machine_orders(
        problem,
        &layout,
        &mut builder,
        detectable_precedence,
        propagated_statuses,
    )?;
    if propagation.as_ref().is_some_and(|result| result.infeasible) {
        builder.clause(&[])?;
    }
    let formula = builder.finish()?;
    Ok(JobShopEncoding {
        formula,
        problem: problem.clone(),
        bound,
        layout,
        machine_orders,
        propagation,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_cnf::cube::{boolean_product_cubes, covering_formula};
    use axeyum_cnf::{
        ProofSolveOutcome, SatResult, check_drat, check_drat_backward, solve_with_drat_proof,
        solve_with_native_core,
    };

    const TINY: &str = "2 2\n0 2 1 1\n1 2 0 1\n";
    const FT06: &str = "6 6\n\
2 1 0 3 1 6 3 7 5 3 4 6\n\
1 8 2 5 4 10 5 10 0 10 3 4\n\
2 5 3 4 5 8 0 9 1 1 4 7\n\
1 5 0 5 2 5 3 3 4 8 5 9\n\
2 9 1 3 4 5 5 4 0 3 3 1\n\
1 3 3 3 5 9 0 10 4 4 2 1\n";

    #[test]
    fn flatzinc_export_uses_checker_supported_exact_constraints() {
        let problem = JobShopProblem::parse_orlib(TINY).unwrap();
        let model = job_shop_to_pumpkin_flatzinc(&problem, 3).unwrap();
        assert!(model.starts_with("% Generated by Axeyum; schema=axeyum.job-shop-flatzinc.v1\n"));
        assert!(model.contains("var 0..0: s_0_0 :: output_var;"));
        assert!(model.contains("var 2..2: s_0_1 :: output_var;"));
        assert!(model.contains("constraint int_lin_le([1,-1],[s_0_0,s_0_1],-2);"));
        assert!(model.contains("constraint pumpkin_cumulative([s_0_0,s_1_1],[2,1],[1,1],1);"));
        assert!(model.ends_with("solve satisfy;\n"));
        assert_eq!(
            job_shop_to_pumpkin_flatzinc(&problem, 2),
            Err(JobShopError::InvalidSchedule(
                "job 0 duration 3 exceeds bound 2".to_owned()
            ))
        );
    }

    #[test]
    fn cumulative_energetic_checker_recomputes_compulsory_energy() {
        let tasks = [
            CumulativeTaskWindow {
                task: 7,
                earliest_start: 0,
                latest_start: 4,
                duration: 3,
                demand: 2,
            },
            CumulativeTaskWindow {
                task: 9,
                earliest_start: 2,
                latest_start: 2,
                duration: 2,
                demand: 1,
            },
        ];
        let check = check_cumulative_energetic_interval(&tasks, 1, 2, 5).unwrap();
        // Task 7 contributes one compulsory time unit at demand two; task 9
        // contributes its two fixed time units.
        assert_eq!(check.required_energy, 4);
        assert_eq!(check.capacity_energy, 3);
        assert_eq!(check.contributing_tasks, 2);
        assert!(check.overloaded);

        let mut duplicate = tasks;
        duplicate[1].task = 7;
        assert!(matches!(
            check_cumulative_energetic_interval(&duplicate, 1, 2, 5),
            Err(JobShopError::Malformed(_))
        ));
        assert!(matches!(
            check_cumulative_energetic_interval(&tasks, 0, 2, 5),
            Err(JobShopError::Malformed(_))
        ));
        assert!(matches!(
            check_cumulative_energetic_interval(&tasks, 1, 5, 5),
            Err(JobShopError::Malformed(_))
        ));
    }

    #[test]
    fn energetic_contribution_matches_exhaustive_small_domains() {
        for earliest_start in 0usize..=4 {
            for latest_start in earliest_start..=4 {
                for duration in 1usize..=4 {
                    for interval_start in 0usize..=5 {
                        for interval_end in interval_start + 1..=6 {
                            let task = CumulativeTaskWindow {
                                task: 0,
                                earliest_start,
                                latest_start,
                                duration,
                                demand: 1,
                            };
                            let check = check_cumulative_energetic_interval(
                                &[task],
                                1,
                                interval_start,
                                interval_end,
                            )
                            .unwrap();
                            let explicit = (earliest_start..=latest_start)
                                .map(|start| {
                                    let end = start + duration;
                                    end.min(interval_end)
                                        .saturating_sub(start.max(interval_start))
                                })
                                .min()
                                .unwrap();
                            assert_eq!(
                                check.required_energy, explicit,
                                "domain {earliest_start}..={latest_start}, duration {duration}, interval {interval_start}..{interval_end}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn job_shop_energetic_conflict_scans_serializes_and_fails_closed() {
        let problem = JobShopProblem::parse_orlib("2 1\n0 2\n0 2\n").unwrap();
        let scan =
            scan_job_shop_energetic_intervals(&problem, 3, JobShopEnergeticLimits::default())
                .unwrap();
        assert_eq!(scan.intervals_checked, 6);
        assert_eq!(scan.task_checks, 12);
        assert_eq!(scan.machine, 0);
        assert_eq!((scan.check.interval_start, scan.check.interval_end), (1, 2));
        assert_eq!(
            (scan.check.required_energy, scan.check.capacity_energy),
            (2, 1)
        );
        let conflict = scan.conflict.unwrap();
        let bytes = serde_json::to_vec(&conflict).unwrap();
        let replayed: JobShopEnergeticConflict = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(
            check_job_shop_energetic_conflict(&problem, 3, &replayed)
                .unwrap()
                .required_energy,
            2
        );

        let mut mutated = replayed.clone();
        mutated.required_energy -= 1;
        assert!(matches!(
            check_job_shop_energetic_conflict(&problem, 3, &mutated),
            Err(JobShopError::InvalidSchedule(_))
        ));
        mutated = replayed.clone();
        mutated.interval_start = 0;
        assert!(matches!(
            check_job_shop_energetic_conflict(&problem, 3, &mutated),
            Err(JobShopError::InvalidSchedule(_))
        ));
        mutated = replayed.clone();
        mutated.machine = 1;
        assert!(matches!(
            check_job_shop_energetic_conflict(&problem, 3, &mutated),
            Err(JobShopError::Malformed(_))
        ));
        mutated = replayed;
        mutated.schema.push_str("-unknown");
        assert!(matches!(
            check_job_shop_energetic_conflict(&problem, 3, &mutated),
            Err(JobShopError::Malformed(_))
        ));
    }

    #[test]
    fn job_shop_energetic_scan_distinguishes_no_conflict_and_resource_decline() {
        let problem = JobShopProblem::parse_orlib("2 1\n0 2\n0 2\n").unwrap();
        let scan =
            scan_job_shop_energetic_intervals(&problem, 4, JobShopEnergeticLimits::default())
                .unwrap();
        assert_eq!(
            (scan.check.required_energy, scan.check.capacity_energy),
            (4, 4)
        );
        assert!(scan.conflict.is_none());

        let limits = JobShopEnergeticLimits {
            max_intervals: 9,
            ..JobShopEnergeticLimits::default()
        };
        assert_eq!(
            scan_job_shop_energetic_intervals(&problem, 4, limits),
            Err(JobShopError::LimitExceeded {
                resource: "energetic intervals",
                observed: 10,
                limit: 9,
            })
        );
    }

    #[test]
    fn conditional_energetic_conflict_becomes_an_entailed_prefix_clause() {
        let problem = JobShopProblem::parse_orlib("2 1\n0 2\n0 2\n").unwrap();
        let search = find_job_shop_conditional_energetic_conflict(
            &problem,
            4,
            JobShopEnergeticDomain::JobChains,
            0,
            0,
            3,
            2,
        )
        .unwrap();
        assert_eq!(search.candidates_checked, 4);
        assert_eq!(
            (search.base.required_energy, search.base.capacity_energy),
            (2, 3)
        );
        let conflict = search.conflict.unwrap();
        assert_eq!(conflict.assumptions.len(), 2);
        let check = check_job_shop_conditional_energetic_conflict(&problem, 4, &conflict).unwrap();
        assert_eq!(check.assumptions_applied, 2);
        assert_eq!(check.energetic.required_energy, 4);

        let encoding =
            encode_job_shop_with_job_windows(&problem, 4, JobShopEncodingLimits::default())
                .unwrap();
        let clause = encoding
            .conditional_energetic_clause(&conflict)
            .unwrap()
            .unwrap();
        assert_eq!(clause.lits().len(), 2);
        assert!(clause.lits().iter().all(|literal| literal.is_negated()));

        // Falsifying every learned literal recreates the checked assumptions;
        // the original formula must then refute. This validates the semantic
        // prefix mapping independently of adding the learned clause itself.
        let mut falsified = encoding.formula().clone();
        for &literal in clause.lits() {
            falsified
                .add_clause(CnfClause::new(vec![literal.negated()]))
                .unwrap();
        }
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&falsified) else {
            panic!("conditional energetic assumptions must be infeasible");
        };
        assert_eq!(check_drat_backward(&falsified, &proof), Ok(true));

        let strengthened = encoding
            .formula_with_conditional_energetic_conflict(&conflict)
            .unwrap();
        assert_eq!(
            strengthened.clauses().len(),
            encoding.formula().clauses().len() + 1
        );
        let SatResult::Sat(model) = solve_with_native_core(&strengthened).unwrap() else {
            panic!("the makespan-four boundary remains feasible");
        };
        encoding.lift_model(&model).unwrap();

        let mut mutated = conflict.clone();
        mutated.required_energy = 3;
        assert!(matches!(
            check_job_shop_conditional_energetic_conflict(&problem, 4, &mutated),
            Err(JobShopError::InvalidSchedule(_))
        ));
        mutated = conflict.clone();
        mutated.assumptions.reverse();
        assert!(matches!(
            check_job_shop_conditional_energetic_conflict(&problem, 4, &mutated),
            Err(JobShopError::Malformed(_))
        ));
        mutated = conflict;
        let JobShopStartBound::StartAtMost { time, .. } = &mut mutated.assumptions[0] else {
            unreachable!()
        };
        *time = 2;
        assert!(matches!(
            check_job_shop_conditional_energetic_conflict(&problem, 4, &mutated),
            Err(JobShopError::Malformed(_))
        ));
    }

    #[test]
    fn conditional_energetic_unit_scan_finds_and_encodes_strongest_bounds() {
        let problem = JobShopProblem::parse_orlib(FT06).unwrap();
        let scan = scan_job_shop_conditional_energetic_unit_conflicts(
            &problem,
            55,
            JobShopEnergeticDomain::PrecedenceClosure,
            JobShopConditionalEnergeticUnitLimits::default(),
        )
        .unwrap();
        assert_eq!(scan.intervals_checked, 9_240);
        assert_eq!(scan.candidates_checked, 110_880);
        assert_eq!(scan.task_checks, 277_248);
        assert_eq!(scan.conflicts.len(), 2);
        assert_eq!(
            scan.conflicts
                .iter()
                .map(|conflict| conflict.assumptions[0])
                .collect::<Vec<_>>(),
            vec![
                JobShopStartBound::StartAtLeast {
                    job: 1,
                    operation: 2,
                    time: 21,
                },
                JobShopStartBound::StartAtMost {
                    job: 1,
                    operation: 4,
                    time: 33,
                },
            ]
        );
        let encoding =
            encode_job_shop_with_precedence_closure(&problem, 55, JobShopEncodingLimits::default())
                .unwrap();
        let strengthened = encoding
            .formula_with_conditional_energetic_conflicts(&scan.conflicts)
            .unwrap();
        assert_eq!(
            strengthened.clauses().len(),
            encoding.formula().clauses().len() + 2
        );
        let SatResult::Sat(model) = solve_with_native_core(&strengthened).unwrap() else {
            panic!("ft06 at its optimum remains feasible");
        };
        assert_eq!(encoding.lift_model(&model).unwrap().makespan, 55);

        let limited = scan_job_shop_conditional_energetic_unit_conflicts(
            &problem,
            55,
            JobShopEnergeticDomain::PrecedenceClosure,
            JobShopConditionalEnergeticUnitLimits {
                max_conflicts: 1,
                ..JobShopConditionalEnergeticUnitLimits::default()
            },
        );
        assert_eq!(
            limited,
            Err(JobShopError::LimitExceeded {
                resource: "conditional energetic conflicts",
                observed: 2,
                limit: 1,
            })
        );
    }

    #[test]
    fn conditional_energetic_units_close_as_a_checked_clause_chain() {
        let problem = JobShopProblem::parse_orlib(FT06).unwrap();
        let premises = scan_job_shop_conditional_energetic_unit_conflicts(
            &problem,
            55,
            JobShopEnergeticDomain::PrecedenceClosure,
            JobShopConditionalEnergeticUnitLimits::default(),
        )
        .unwrap()
        .conflicts;
        let closure = close_job_shop_conditional_energetic_units(
            &problem,
            55,
            &premises,
            JobShopConditionalEnergeticFixpointLimits::default(),
        )
        .unwrap();
        assert!(closure.stabilized);
        assert!(!closure.rounds.is_empty());
        assert!(closure.rounds.last().unwrap().conflicts.is_empty());
        for conflict in &closure.conflicts {
            check_job_shop_conditional_energetic_conflict(&problem, 55, conflict).unwrap();
        }

        let encoding =
            encode_job_shop_with_precedence_closure(&problem, 55, JobShopEncodingLimits::default())
                .unwrap();
        let mut conflicts = premises.clone();
        conflicts.extend(closure.conflicts);
        let strengthened = encoding
            .formula_with_conditional_energetic_conflicts(&conflicts)
            .unwrap();
        assert_eq!(
            strengthened.clauses().len(),
            encoding.formula().clauses().len() + conflicts.len()
        );
        let SatResult::Sat(model) = solve_with_native_core(&strengthened).unwrap() else {
            panic!("ft06 at its optimum remains feasible after checked unit closure");
        };
        assert_eq!(encoding.lift_model(&model).unwrap().makespan, 55);

        let mut malformed = premises;
        malformed[0]
            .assumptions
            .push(JobShopStartBound::StartAtMost {
                job: 0,
                operation: 0,
                time: 0,
            });
        assert!(matches!(
            close_job_shop_conditional_energetic_units(
                &problem,
                55,
                &malformed,
                JobShopConditionalEnergeticFixpointLimits::default()
            ),
            Err(JobShopError::InvalidSchedule(_) | JobShopError::Malformed(_))
        ));
    }

    #[test]
    fn parser_checker_and_model_lifting_agree() {
        let problem = JobShopProblem::parse_orlib(TINY).unwrap();
        let encoding = encode_job_shop(&problem, 3, JobShopEncodingLimits::default()).unwrap();
        let SatResult::Sat(model) = solve_with_native_core(encoding.formula()).unwrap() else {
            panic!("tiny optimum must fit in three ticks");
        };
        let schedule = encoding.lift_model(&model).unwrap();
        assert_eq!(schedule.makespan, 3);
        assert_eq!(encoding.machine_orders().len(), 2);
        for order in encoding.machine_orders() {
            let left_start = schedule.starts[order.left_job][order.left_operation];
            let left_end = left_start + problem.jobs[order.left_job][order.left_operation].duration;
            let right_start = schedule.starts[order.right_job][order.right_operation];
            let right_end =
                right_start + problem.jobs[order.right_job][order.right_operation].duration;
            if model.values()[order.selector.index()] {
                assert!(left_end <= right_start);
            } else {
                assert!(right_end <= left_start);
            }
        }
        assert_eq!(
            check_job_shop_schedule(&problem, &schedule)
                .unwrap()
                .operations,
            4
        );
    }

    #[test]
    fn machine_order_witness_parses_builds_and_replays() {
        let problem = JobShopProblem::parse_orlib(TINY).unwrap();
        let orders = parse_job_shop_machine_orders(&problem, "# machine rows\n0 1\n1 0\n").unwrap();
        let schedule = schedule_job_shop_machine_orders(&problem, &orders).unwrap();
        assert_eq!(schedule.starts, vec![vec![0, 2], vec![0, 2]]);
        assert_eq!(schedule.makespan, 3);
        assert_eq!(
            check_job_shop_schedule(&problem, &schedule)
                .unwrap()
                .operations,
            4
        );
    }

    #[test]
    fn machine_order_witness_rejects_bad_permutations_and_cycles() {
        let problem = JobShopProblem::parse_orlib(TINY).unwrap();
        assert!(matches!(
            parse_job_shop_machine_orders(&problem, "0 0\n1 0\n"),
            Err(JobShopError::Parse(_))
        ));
        let cyclic = parse_job_shop_machine_orders(&problem, "1 0\n0 1\n").unwrap();
        assert_eq!(
            schedule_job_shop_machine_orders(&problem, &cyclic),
            Err(JobShopError::InvalidSchedule(
                "machine orders and job chains contain a cycle".to_owned()
            ))
        );
    }

    #[test]
    fn lower_boundary_has_a_checked_refutation() {
        let problem = JobShopProblem::parse_orlib(TINY).unwrap();
        let encoding = encode_job_shop(&problem, 2, JobShopEncodingLimits::default()).unwrap();
        let cubes = boolean_product_cubes(
            &encoding
                .machine_orders()
                .iter()
                .map(|order| order.selector)
                .collect::<Vec<_>>(),
        )
        .unwrap();
        let covering = covering_formula(encoding.formula(), &cubes).unwrap();
        let ProofSolveOutcome::Unsat(covering_proof) = solve_with_drat_proof(&covering) else {
            panic!("machine-order product must cover every assignment");
        };
        assert_eq!(check_drat(&covering, &covering_proof), Ok(true));
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(encoding.formula()) else {
            panic!("each job needs three ticks");
        };
        assert_eq!(
            axeyum_cnf::check_drat_backward(encoding.formula(), &proof),
            Ok(true)
        );
    }

    #[test]
    fn job_windows_preserve_boundary_and_lifted_schedules() {
        let problem = JobShopProblem::parse_orlib(TINY).unwrap();
        for bound in 0..=5 {
            let baseline =
                encode_job_shop(&problem, bound, JobShopEncodingLimits::default()).unwrap();
            let windowed =
                encode_job_shop_with_job_windows(&problem, bound, JobShopEncodingLimits::default())
                    .unwrap();
            let propagated = encode_job_shop_with_detectable_precedence(
                &problem,
                bound,
                JobShopEncodingLimits::default(),
            )
            .unwrap();
            let closed = encode_job_shop_with_precedence_closure(
                &problem,
                bound,
                JobShopEncodingLimits::default(),
            )
            .unwrap();
            let baseline_result = solve_with_native_core(baseline.formula()).unwrap();
            let windowed_result = solve_with_native_core(windowed.formula()).unwrap();
            let propagated_result = solve_with_native_core(propagated.formula()).unwrap();
            let closed_result = solve_with_native_core(closed.formula()).unwrap();
            assert_eq!(
                matches!(baseline_result, SatResult::Sat(_)),
                matches!(windowed_result, SatResult::Sat(_)),
                "boundary mismatch at {bound}"
            );
            assert_eq!(
                matches!(baseline_result, SatResult::Sat(_)),
                matches!(propagated_result, SatResult::Sat(_)),
                "detectable-precedence mismatch at {bound}"
            );
            assert_eq!(
                matches!(baseline_result, SatResult::Sat(_)),
                matches!(closed_result, SatResult::Sat(_)),
                "precedence-closure mismatch at {bound}"
            );
            if let SatResult::Sat(model) = windowed_result {
                let schedule = windowed.lift_model(&model).unwrap();
                assert!(schedule.makespan <= bound);
            }
            if let SatResult::Sat(model) = propagated_result {
                let schedule = propagated.lift_model(&model).unwrap();
                for order in propagated.machine_orders() {
                    let value = model.values()[order.selector.index()];
                    match order.status {
                        JobShopMachineOrderStatus::Free => {}
                        JobShopMachineOrderStatus::ForcedLeftBeforeRight => assert!(value),
                        JobShopMachineOrderStatus::ForcedRightBeforeLeft => assert!(!value),
                        JobShopMachineOrderStatus::Infeasible => {
                            panic!("SAT encoding contains an infeasible pair")
                        }
                    }
                }
                assert!(schedule.makespan <= bound);
            }
            if let SatResult::Sat(model) = closed_result {
                assert!(closed.lift_model(&model).unwrap().makespan <= bound);
            }
        }
        let baseline = encode_job_shop(&problem, 3, JobShopEncodingLimits::default()).unwrap();
        let windowed =
            encode_job_shop_with_job_windows(&problem, 3, JobShopEncodingLimits::default())
                .unwrap();
        assert!(windowed.formula().variable_count() < baseline.formula().variable_count());
        assert!(windowed.formula().clauses().len() < baseline.formula().clauses().len());
        let propagated = encode_job_shop_with_detectable_precedence(
            &problem,
            3,
            JobShopEncodingLimits::default(),
        )
        .unwrap();
        assert!(
            propagated
                .machine_orders()
                .iter()
                .any(|order| order.status != JobShopMachineOrderStatus::Free)
        );
    }

    #[test]
    fn detectable_precedence_exposes_pairwise_infeasibility() {
        let problem = JobShopProblem::parse_orlib("2 1\n0 2\n0 2\n").unwrap();
        let encoding = encode_job_shop_with_detectable_precedence(
            &problem,
            3,
            JobShopEncodingLimits::default(),
        )
        .unwrap();
        assert_eq!(encoding.machine_orders().len(), 1);
        assert_eq!(
            encoding.machine_orders()[0].status,
            JobShopMachineOrderStatus::Infeasible
        );
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(encoding.formula()) else {
            panic!("two length-two operations cannot share a three-tick machine");
        };
        assert_eq!(check_drat(encoding.formula(), &proof), Ok(true));
    }

    #[test]
    fn precedence_closure_matches_baseline_on_all_tiny_two_machine_jobs() {
        for first_reversed in [false, true] {
            for second_reversed in [false, true] {
                for durations in 0usize..16 {
                    let duration = |bit: usize| 1 + ((durations >> bit) & 1usize);
                    let first = if first_reversed { [1, 0] } else { [0, 1] };
                    let second = if second_reversed { [1, 0] } else { [0, 1] };
                    let problem = JobShopProblem {
                        machines: 2,
                        jobs: vec![
                            vec![
                                JobShopOperation {
                                    machine: first[0],
                                    duration: duration(0),
                                },
                                JobShopOperation {
                                    machine: first[1],
                                    duration: duration(1),
                                },
                            ],
                            vec![
                                JobShopOperation {
                                    machine: second[0],
                                    duration: duration(2),
                                },
                                JobShopOperation {
                                    machine: second[1],
                                    duration: duration(3),
                                },
                            ],
                        ],
                    };
                    for bound in 0..=8 {
                        let baseline =
                            encode_job_shop(&problem, bound, JobShopEncodingLimits::default())
                                .unwrap();
                        let closed = encode_job_shop_with_precedence_closure(
                            &problem,
                            bound,
                            JobShopEncodingLimits::default(),
                        )
                        .unwrap();
                        let baseline_result = solve_with_native_core(baseline.formula()).unwrap();
                        let closed_result = solve_with_native_core(closed.formula()).unwrap();
                        assert_eq!(
                            matches!(baseline_result, SatResult::Sat(_)),
                            matches!(closed_result, SatResult::Sat(_)),
                            "mismatch for orders {first:?}/{second:?}, durations {durations:04b}, bound {bound}"
                        );
                        if let SatResult::Sat(model) = closed_result {
                            closed.lift_model(&model).unwrap();
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn semantic_mutations_are_rejected() {
        let problem = JobShopProblem::parse_orlib(TINY).unwrap();
        let mut overlap = JobShopSchedule {
            schema: JOB_SHOP_SCHEDULE_SCHEMA.to_owned(),
            makespan: 4,
            starts: vec![vec![0, 2], vec![1, 3]],
        };
        assert!(matches!(
            check_job_shop_schedule(&problem, &overlap),
            Err(JobShopError::InvalidSchedule(_))
        ));
        overlap.makespan = 3;
        overlap.starts[1] = vec![1, 0];
        assert!(matches!(
            check_job_shop_schedule(&problem, &overlap),
            Err(JobShopError::InvalidSchedule(_))
        ));
    }
}
