//! Proof-carrying bounded-makespan search for classical job-shop scheduling.
//!
//! The public instance parser, independent schedule checker, and SAT encoding
//! share only the typed problem. Search models are lifted to start times and
//! replayed against precedence, machine capacity, and the claimed makespan.

use axeyum_cnf::{CnfAssignment, CnfClause, CnfFormula, CnfLit, CnfVar};
use serde::{Deserialize, Serialize};

/// Portable schedule artifact schema.
pub const JOB_SHOP_SCHEDULE_SCHEMA: &str = "axeyum.job-shop-schedule.v1";

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
            for pair in row.chunks_exact(2) {
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

fn parse_numbers(line: &str) -> Result<Vec<usize>, JobShopError> {
    line.split_whitespace()
        .map(|word| {
            word.parse::<usize>()
                .map_err(|_| JobShopError::Parse(format!("invalid integer `{word}`")))
        })
        .collect()
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
}

/// Exact CNF question “does this instance have makespan at most `bound`?”.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JobShopEncoding {
    formula: CnfFormula,
    problem: JobShopProblem,
    bound: usize,
    layout: Vec<Vec<OperationLayout>>,
    machine_orders: Vec<JobShopMachineOrder>,
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
}

fn encode_machine_orders(
    problem: &JobShopProblem,
    layout: &[Vec<OperationLayout>],
    builder: &mut Builder,
) -> Result<Vec<JobShopMachineOrder>, JobShopError> {
    let mut orders = Vec::new();
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
                orders.push(JobShopMachineOrder {
                    machine,
                    left_job,
                    left_operation,
                    right_job,
                    right_operation,
                    selector: CnfVar::new(order)
                        .map_err(|error| JobShopError::Cnf(format!("order variable: {error:?}")))?,
                });
                let left_item = problem.jobs[left_job][left_operation];
                let right_item = problem.jobs[right_job][right_operation];
                let left_layout = &layout[left_job][left_operation];
                let right_layout = &layout[right_job][right_operation];

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
    encode_job_shop_internal(problem, bound, limits, false)
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
    encode_job_shop_internal(problem, bound, limits, true)
}

fn encode_operation_layouts(
    problem: &JobShopProblem,
    bound: usize,
    builder: &mut Builder,
    job_windows: bool,
) -> Result<Vec<Vec<OperationLayout>>, JobShopError> {
    let mut layout = Vec::with_capacity(problem.jobs.len());
    for operations in &problem.jobs {
        let total_duration = operations.iter().try_fold(0usize, |sum, operation| {
            sum.checked_add(operation.duration)
                .ok_or_else(|| JobShopError::Malformed("job duration sum overflow".to_owned()))
        })?;
        let mut preceding_duration = 0usize;
        let mut job_layout = Vec::with_capacity(operations.len());
        for operation in operations {
            if operation.machine >= problem.machines || operation.duration == 0 {
                return Err(JobShopError::Malformed(
                    "invalid operation machine or duration".to_owned(),
                ));
            }
            let earliest = if job_windows { preceding_duration } else { 0 };
            let remaining_duration = total_duration - preceding_duration;
            let latest = if job_windows {
                bound.checked_sub(remaining_duration)
            } else {
                bound.checked_sub(operation.duration)
            };
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
    let layout = encode_operation_layouts(problem, bound, &mut builder, job_windows)?;

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
    let machine_orders = encode_machine_orders(problem, &layout, &mut builder)?;
    let formula = builder.finish()?;
    Ok(JobShopEncoding {
        formula,
        problem: problem.clone(),
        bound,
        layout,
        machine_orders,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_cnf::cube::{boolean_product_cubes, covering_formula};
    use axeyum_cnf::{
        ProofSolveOutcome, SatResult, check_drat, solve_with_drat_proof, solve_with_rustsat_batsat,
    };

    const TINY: &str = "2 2\n0 2 1 1\n1 2 0 1\n";

    #[test]
    fn parser_checker_and_model_lifting_agree() {
        let problem = JobShopProblem::parse_orlib(TINY).unwrap();
        let encoding = encode_job_shop(&problem, 3, JobShopEncodingLimits::default()).unwrap();
        let SatResult::Sat(model) = solve_with_rustsat_batsat(encoding.formula()).unwrap() else {
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
            let baseline_result = solve_with_rustsat_batsat(baseline.formula()).unwrap();
            let windowed_result = solve_with_rustsat_batsat(windowed.formula()).unwrap();
            assert_eq!(
                matches!(baseline_result, SatResult::Sat(_)),
                matches!(windowed_result, SatResult::Sat(_)),
                "boundary mismatch at {bound}"
            );
            if let SatResult::Sat(model) = windowed_result {
                let schedule = windowed.lift_model(&model).unwrap();
                assert!(schedule.makespan <= bound);
            }
        }
        let baseline = encode_job_shop(&problem, 3, JobShopEncodingLimits::default()).unwrap();
        let windowed =
            encode_job_shop_with_job_windows(&problem, 3, JobShopEncodingLimits::default())
                .unwrap();
        assert!(windowed.formula().variable_count() < baseline.formula().variable_count());
        assert!(windowed.formula().clauses().len() < baseline.formula().clauses().len());
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
