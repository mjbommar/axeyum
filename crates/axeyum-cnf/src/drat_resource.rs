//! Predicting and declining the memory cost of DRAT checking (ADR-0426).
//!
//! Backward DRAT checking ([`crate::check_drat_backward`]) holds the whole proof
//! prefix in a form the walk can index, so its footprint is a multiple of the
//! proof's size on disk. That multiple was assumed to be about 1.5x; it was
//! measured at 6.6x on a 1.87 GB certificate and at 8.0-10.0x on the four
//! largest certificates this repository ships. The consequence is not
//! theoretical: a host with 26 GiB of RAM cannot re-check a 5 GB proof, and the
//! way it finds out is the OOM killer.
//!
//! **An OOM kill is indistinguishable from a refuted claim.** `SIGKILL` produces
//! exit 137 and no output, which reads exactly like a checker that rejected the
//! proof. This module exists so that the answer to "will this check fit?" is a
//! computed, typed value produced *before* any memory is committed, rather than
//! a signal produced after all of it is.
//!
//! # The three pieces
//!
//! 1. [`DratProofShape`] — how many steps, clauses and literal occurrences a
//!    proof has. Available exactly (from a parsed proof), by *sampling* the head
//!    of a proof file, or as a pure extrapolation from the file's byte length.
//! 2. [`DratMemoryModel`] — per-route cost constants that turn a shape into a
//!    predicted resident size. The constants are documented with the
//!    measurements they came from, and
//!    `tests/drat_memory_model.rs` re-derives them from the committed
//!    certificates on every run, so the model is measured continuously rather
//!    than remembered.
//! 3. [`MemoryBudget`] — what is actually available, from `/proc/meminfo`'s
//!    `MemAvailable` or from an explicit caller-supplied limit.
//!
//! Put together, [`MemoryBudget::admits`] answers the scheduling question, and
//! [`DratResourceDecline`] is the *typed* refusal — a first-class "I did not
//! check this", never confusable with "this proof is invalid" (which is
//! [`crate::DratError::StepNotVerified`]) or with "this formula is refuted".
//!
//! # Reporting the ratio
//!
//! Every budgeted check hands back a [`DratMemoryReport`] carrying both the
//! prediction and what the run actually cost, measured from the checker's own
//! allocation capacities rather than estimated. That is what keeps the constants
//! honest: a caller that logs the report is re-measuring the model on real data
//! every time it runs.

use std::io::{self, BufRead};

/// Which checking route's footprint is being predicted.
///
/// The two backward routes run the *same algorithm* over the same clause plan;
/// they differ only in whether the proof is materialised as a `Vec<DratStep>`
/// first. That difference is most of the cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DratCheckRoute {
    /// [`crate::parse_drat`] into a `Vec<DratStep>`, then
    /// [`crate::check_drat_backward`]. The step vector and the clause plan are
    /// resident at the same time.
    InMemoryBackward,
    /// [`crate::check_drat_backward_reader`]: the clause plan is built directly
    /// from the reader and no step vector ever exists.
    FileBackedBackward,
}

impl DratCheckRoute {
    /// Stable name for artifacts and diagnostics.
    pub fn name(self) -> &'static str {
        match self {
            DratCheckRoute::InMemoryBackward => "in-memory-backward",
            DratCheckRoute::FileBackedBackward => "file-backed-backward",
        }
    }
}

impl core::fmt::Display for DratCheckRoute {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.name())
    }
}

/// How a [`DratProofShape`] was obtained, which is how much to trust it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DratShapeSource {
    /// Counted from the whole proof. No extrapolation.
    Exact,
    /// Counted over the first `sampled_bytes` of the proof and scaled to the
    /// full length.
    Sampled {
        /// Bytes actually read and counted.
        sampled_bytes: u64,
    },
    /// Derived from the proof's byte length alone, using
    /// [`DratMemoryModel::TEXT_BYTES_PER_LITERAL`] and
    /// [`DratMemoryModel::LITERALS_PER_STEP`]. The coarsest input; use it when
    /// the proof cannot be read at all (a remote scheduler sizing a job from a
    /// file listing).
    ProofBytesOnly,
}

/// The counts a DRAT proof's memory cost is a function of.
///
/// Deletion steps contribute literals to the parsed step vector but never reach
/// the clause plan's arena (a deletion is resolved by literal set and then
/// discarded), so additions and deletions are counted separately.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DratProofShape {
    proof_bytes: u64,
    steps: u64,
    added_clauses: u64,
    added_literals: u64,
    total_literals: u64,
    source: DratShapeSource,
}

impl DratProofShape {
    /// Sample this fraction of a proof, at least, for
    /// [`DratProofShape::sample`] to be within a few per cent. See the table on
    /// that method for the measurements behind it.
    pub const RECOMMENDED_SAMPLE_FRACTION: f64 = 0.05;

    /// Never sample less than this, however small the fraction works out: on a
    /// small proof a percentage of it is a handful of lines.
    pub const MINIMUM_SAMPLE_BYTES: u64 = 1 << 20;

    /// The sample size [`DratProofShape::sample`] should be given for a proof of
    /// `proof_bytes`.
    pub fn recommended_sample_bytes(proof_bytes: u64) -> u64 {
        #[allow(
            clippy::cast_precision_loss,
            clippy::cast_possible_truncation,
            clippy::cast_sign_loss
        )]
        let fraction = (proof_bytes as f64 * Self::RECOMMENDED_SAMPLE_FRACTION) as u64;
        fraction.max(Self::MINIMUM_SAMPLE_BYTES)
    }

    /// Builds a shape from counts taken over a whole proof.
    ///
    /// `total_literals` counts every literal occurrence in the proof, additions
    /// and deletions alike; `added_literals` counts only those in additions.
    pub fn exact(
        proof_bytes: u64,
        steps: u64,
        added_clauses: u64,
        added_literals: u64,
        total_literals: u64,
    ) -> Self {
        Self {
            proof_bytes,
            steps,
            added_clauses,
            added_literals,
            total_literals,
            source: DratShapeSource::Exact,
        }
    }

    /// Counts a proof already held as steps.
    pub fn of_steps(proof: &[crate::DratStep]) -> Self {
        let mut shape = Self {
            proof_bytes: 0,
            steps: 0,
            added_clauses: 0,
            added_literals: 0,
            total_literals: 0,
            source: DratShapeSource::Exact,
        };
        for step in proof {
            shape.observe(step);
        }
        // The proof does not exist as text here, so its on-disk size is what
        // `write_drat` would produce; the model's per-literal text width is the
        // only estimate in this path and it is only used for the *reported*
        // ratio, never for the prediction.
        shape.proof_bytes = shape.total_literals * DratMemoryModel::TEXT_BYTES_PER_LITERAL
            + shape.steps * DratMemoryModel::TEXT_BYTES_PER_STEP;
        shape
    }

    /// Estimates a shape from the proof's byte length alone.
    pub fn from_proof_bytes(proof_bytes: u64) -> Self {
        let total_literals = proof_bytes / DratMemoryModel::TEXT_BYTES_PER_LITERAL;
        let steps = (total_literals / DratMemoryModel::LITERALS_PER_STEP).max(1);
        Self {
            proof_bytes,
            steps,
            // Additions and deletions come in near-matched pairs in every
            // solver-produced proof measured here (1.03:1 across the four
            // largest committed certificates), so half of each.
            added_clauses: steps / 2,
            added_literals: total_literals / 2,
            total_literals,
            source: DratShapeSource::ProofBytesOnly,
        }
    }

    /// Counts the first `sample_bytes` of a textual DRAT proof and scales the
    /// counts to `proof_bytes`.
    ///
    /// Reading stops at the first line boundary at or after `sample_bytes`, so
    /// no partial line is counted. When the whole proof is shorter than the
    /// sample, the result is [`DratShapeSource::Exact`].
    ///
    /// # How big a sample
    ///
    /// **The head of a DRAT proof is not representative, and a small sample is
    /// badly biased.** Measured on the four largest certificates this repository
    /// ships, as error in the estimated *added-literal* count:
    ///
    /// | sample | `F_81` | `F_103` | `F_171` | `F_256` |
    /// |---:|---:|---:|---:|---:|
    /// | 0.1% | +92% | +102% | +93% | +54% |
    /// | 1% | +87% | +23% | +9% | +4% |
    /// | 5% | +11% | +8% | +1% | -1% |
    /// | 10% | +11% | +3% | 0% | 0% |
    ///
    /// The *step* count is well estimated at any sample size (within 11%); it is
    /// the mean clause width that drifts, because a proof's early lemmas are
    /// wider than its later ones. Use [`DratProofShape::RECOMMENDED_SAMPLE_FRACTION`]
    /// unless you have a reason not to.
    ///
    /// The bias at small samples is toward *over*-estimating, which is the safe
    /// direction for a memory budget: a 0.1% sample declines checks that would
    /// have fitted, rather than admitting checks that will not.
    ///
    /// # Errors
    ///
    /// Returns whatever the reader yields.
    pub fn sample<R: BufRead>(
        mut reader: R,
        proof_bytes: u64,
        sample_bytes: u64,
    ) -> io::Result<Self> {
        let mut shape = Self {
            proof_bytes,
            steps: 0,
            added_clauses: 0,
            added_literals: 0,
            total_literals: 0,
            source: DratShapeSource::Exact,
        };
        let mut line = String::new();
        let mut read: u64 = 0;
        loop {
            line.clear();
            let count = reader.read_line(&mut line)?;
            if count == 0 {
                break;
            }
            read += count as u64;
            count_text_line(&line, &mut shape);
            if read >= sample_bytes {
                break;
            }
        }
        if read == 0 {
            return Ok(Self::from_proof_bytes(proof_bytes));
        }
        if read >= proof_bytes {
            shape.proof_bytes = read;
            return Ok(shape);
        }
        // Scale in u128 so a 20 GB proof times a 100 MB sample count cannot
        // overflow.
        let scale = |value: u64| -> u64 {
            let scaled = u128::from(value) * u128::from(proof_bytes) / u128::from(read);
            u64::try_from(scaled).unwrap_or(u64::MAX)
        };
        Ok(Self {
            proof_bytes,
            steps: scale(shape.steps),
            added_clauses: scale(shape.added_clauses),
            added_literals: scale(shape.added_literals),
            total_literals: scale(shape.total_literals),
            source: DratShapeSource::Sampled {
                sampled_bytes: read,
            },
        })
    }

    fn observe(&mut self, step: &crate::DratStep) {
        self.steps += 1;
        match step {
            crate::DratStep::Add(lits) => {
                self.added_clauses += 1;
                self.added_literals += lits.len() as u64;
                self.total_literals += lits.len() as u64;
            }
            crate::DratStep::Delete(lits) => {
                self.total_literals += lits.len() as u64;
            }
        }
    }

    /// Size of the proof on disk, in bytes.
    pub fn proof_bytes(self) -> u64 {
        self.proof_bytes
    }

    /// Number of proof steps (additions plus deletions).
    pub fn steps(self) -> u64 {
        self.steps
    }

    /// Number of clause additions.
    pub fn added_clauses(self) -> u64 {
        self.added_clauses
    }

    /// Literal occurrences in clause additions.
    pub fn added_literals(self) -> u64 {
        self.added_literals
    }

    /// Literal occurrences in the whole proof.
    pub fn total_literals(self) -> u64 {
        self.total_literals
    }

    /// How the counts were obtained.
    pub fn source(self) -> DratShapeSource {
        self.source
    }
}

/// Counts one line of textual DRAT into `shape`. Mirrors the tokenisation of
/// `parse_drat_line` closely enough to count, without building literals.
fn count_text_line(line: &str, shape: &mut DratProofShape) {
    let line = line.trim();
    if line.is_empty() || line.starts_with('c') {
        return;
    }
    let mut tokens = line.split_whitespace().peekable();
    let delete = if tokens.peek() == Some(&"d") {
        tokens.next();
        true
    } else {
        false
    };
    let mut lits: u64 = 0;
    for token in tokens {
        if token == "0" {
            break;
        }
        lits += 1;
    }
    shape.steps += 1;
    shape.total_literals += lits;
    if !delete {
        shape.added_clauses += 1;
        shape.added_literals += lits;
    }
}

/// The part of a check's footprint the *formula* contributes.
///
/// The plan holds one clause record per formula clause and one arena slot per
/// formula literal, exactly as it does for the proof's additions. On a
/// search-scale certificate the formula is a rounding error (4% of the records
/// for `rado-r4-a4-b1/F_256`), but a caller with a large formula and a short
/// proof would be under-predicted without it — and under-prediction is the
/// direction that ends in an OOM kill.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FormulaShape {
    clauses: u64,
    literals: u64,
}

impl FormulaShape {
    /// No formula: for a caller predicting from a file listing alone. Under-
    /// predicts by the formula's own size, so prefer [`FormulaShape::of`].
    pub const EMPTY: Self = Self {
        clauses: 0,
        literals: 0,
    };

    /// Counts a formula.
    pub fn of(formula: &crate::CnfFormula) -> Self {
        Self {
            clauses: formula.clauses().len() as u64,
            literals: formula
                .clauses()
                .iter()
                .map(|clause| clause.lits().len() as u64)
                .sum(),
        }
    }

    /// Builds a shape from counts a caller already has.
    pub fn new(clauses: u64, literals: u64) -> Self {
        Self { clauses, literals }
    }

    /// Number of clauses.
    pub fn clauses(self) -> u64 {
        self.clauses
    }

    /// Literal occurrences.
    pub fn literals(self) -> u64 {
        self.literals
    }
}

/// Per-route cost constants that turn a [`DratProofShape`] into a predicted
/// resident size.
///
/// # Where the constants come from
///
/// Measured on this repository's four largest committed certificates (release
/// build, Linux, glibc `malloc`, peak RSS from `/proc/self/status` `VmHWM`):
///
/// | certificate | text DRAT | steps | added literals | peak RSS | RSS / DRAT |
/// |---|---:|---:|---:|---:|---:|
/// | `rado-r4-a3-b1/F_81` | 8,862,657 | 164,538 | 1,138,646 | 88,416,256 | 9.98x |
/// | `rado-r4-a3-b2/F_103` | 74,818,033 | 1,202,198 | 8,849,656 | 608,473,088 | 8.13x |
/// | `rado-r4-a1-b2/F_171` | 131,197,778 | 2,010,887 | 16,317,546 | 1,112,662,016 | 8.48x |
/// | `rado-r4-a4-b1/F_256` | 166,982,506 | 2,555,413 | 19,652,014 | 1,335,078,912 | 8.00x |
///
/// agent-c measured 6.6x independently on a 1,873,245,421-byte proof, which is
/// the same model with the fixed per-run costs amortised away.
///
/// The constants below are *per structural item*, not a bytes-per-byte ratio,
/// because the ratio is not constant: it depends on how many literals a proof
/// packs into a byte of text, which varies with the variable count.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DratMemoryModel {
    route: DratCheckRoute,
}

impl DratMemoryModel {
    /// Mean bytes of textual DRAT per literal occurrence. Measured at 4.31,
    /// 4.30, 4.07 and 4.31 on the four certificates above; 4 is used, which
    /// *over*-estimates the literal count and therefore the memory, which is the
    /// safe direction.
    pub const TEXT_BYTES_PER_LITERAL: u64 = 4;

    /// Bytes of textual DRAT per step beyond its literals: the `0` terminator,
    /// its space, and the newline.
    pub const TEXT_BYTES_PER_STEP: u64 = 3;

    /// Mean literal occurrences per step, used only by
    /// [`DratProofShape::from_proof_bytes`]. Measured at 12.7, 14.5, 16.0 and
    /// 15.2; 15 is used.
    pub const LITERALS_PER_STEP: u64 = 15;

    /// Bytes per step held in a `Vec<DratStep>`: the enum itself (32 bytes: a
    /// discriminant plus a `Vec` header) plus one heap allocation per clause,
    /// whose glibc bookkeeping is 16 bytes.
    const STEP_VECTOR_BYTES_PER_STEP: u64 = 48;

    /// Bytes per literal held in a `Vec<DratStep>`: `size_of::<CnfLit>()` is 8,
    /// and a `Vec` grown by `push` holds a power-of-two capacity, which averages
    /// about 1.4x the length over a uniform spread of clause sizes.
    const STEP_VECTOR_BYTES_PER_LITERAL: u64 = 12;

    /// Bytes per clause record in the backward checker's plan.
    ///
    /// `size_of::<ClauseRecord>()` is 56 and the record vector grows by
    /// doubling, so its capacity runs at up to 2x its length: 112. The deletion
    /// index holds one entry per distinct clause at 33 bytes a slot, and its
    /// table is likewise power-of-two sized: 56. Measured directly on
    /// `PHP(8, 7)`, where 4,212 records occupied 458,752 bytes of record vector
    /// and 236,544 bytes of index table.
    const PLAN_BYTES_PER_CLAUSE: u64 = 168;

    /// Bytes per proof step in the plan's two step-to-record maps: 8 bytes each,
    /// with the same doubling slack. Measured at 131,072 bytes for 6,153 steps
    /// on `PHP(8, 7)`.
    const PLAN_BYTES_PER_STEP: u64 = 24;

    /// Bytes per literal occurrence in the plan's clause arena: 8 bytes per
    /// packed literal code, with doubling slack. Measured at 917,504 bytes for
    /// 62,961 literals on `PHP(8, 7)` — 1.82x over the exact 8 bytes, which is
    /// where a `Vec` that grew by `push` happened to land.
    const PLAN_BYTES_PER_LITERAL: u64 = 15;

    /// Fixed cost of a run: allocator arenas, the binary's own resident pages,
    /// and the per-variable vectors, which are negligible beside the above at
    /// any scale where this question is asked.
    ///
    /// Public because it is the difference between what
    /// [`DratMemoryEstimate::estimated_bytes`] predicts (peak *resident* size,
    /// which a scheduler compares against free memory) and what
    /// [`DratMemoryReport::observed_structure_bytes`] measures (the checker's
    /// own allocations). A caller comparing the two must subtract it, and
    /// `tests/drat_memory_model.rs` does.
    pub const FIXED_BYTES: u64 = 16 * 1024 * 1024;

    /// A model for `route`.
    pub fn new(route: DratCheckRoute) -> Self {
        Self { route }
    }

    /// The route this model predicts.
    pub fn route(self) -> DratCheckRoute {
        self.route
    }

    /// Predicted peak resident bytes for checking a proof of this shape against
    /// a formula of that shape.
    ///
    /// Pass [`FormulaShape::EMPTY`] only when the formula genuinely is not
    /// available; it under-predicts by the formula's own contribution.
    pub fn estimate(self, shape: DratProofShape, formula: FormulaShape) -> DratMemoryEstimate {
        let plan = shape
            .added_clauses
            .saturating_add(formula.clauses)
            .saturating_mul(Self::PLAN_BYTES_PER_CLAUSE)
            .saturating_add(shape.steps.saturating_mul(Self::PLAN_BYTES_PER_STEP))
            .saturating_add(
                shape
                    .added_literals
                    .saturating_add(formula.literals)
                    .saturating_mul(Self::PLAN_BYTES_PER_LITERAL),
            );
        let steps = match self.route {
            DratCheckRoute::FileBackedBackward => 0,
            DratCheckRoute::InMemoryBackward => shape
                .steps
                .saturating_mul(Self::STEP_VECTOR_BYTES_PER_STEP)
                .saturating_add(
                    shape
                        .total_literals
                        .saturating_mul(Self::STEP_VECTOR_BYTES_PER_LITERAL),
                ),
        };
        DratMemoryEstimate {
            route: self.route,
            shape,
            estimated_bytes: plan.saturating_add(steps).saturating_add(Self::FIXED_BYTES),
        }
    }
}

/// A prediction of what checking a particular proof will cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DratMemoryEstimate {
    route: DratCheckRoute,
    shape: DratProofShape,
    estimated_bytes: u64,
}

impl DratMemoryEstimate {
    /// The route predicted.
    pub fn route(self) -> DratCheckRoute {
        self.route
    }

    /// The shape the prediction was computed from.
    pub fn shape(self) -> DratProofShape {
        self.shape
    }

    /// Predicted peak resident bytes.
    pub fn estimated_bytes(self) -> u64 {
        self.estimated_bytes
    }

    /// Predicted peak resident bytes per byte of proof text — the number this
    /// module exists to make small, and the one a scheduler multiplies.
    ///
    /// Returns `None` for an empty proof.
    pub fn bytes_per_proof_byte(self) -> Option<f64> {
        if self.shape.proof_bytes == 0 {
            return None;
        }
        // Both operands are sizes in bytes; f64 represents every value below
        // 2^53 exactly, and this is a diagnostic ratio either way.
        #[allow(clippy::cast_precision_loss)]
        Some(self.estimated_bytes as f64 / self.shape.proof_bytes as f64)
    }
}

impl core::fmt::Display for DratMemoryEstimate {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} of {} proof bytes via {}",
            self.estimated_bytes, self.shape.proof_bytes, self.route
        )
    }
}

/// Where a [`MemoryBudget`] came from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BudgetSource {
    /// An explicit caller-supplied limit.
    Explicit,
    /// `MemAvailable` from `/proc/meminfo`, scaled by a headroom fraction.
    SystemAvailable {
        /// The raw `MemAvailable` value before headroom was applied.
        mem_available_bytes: u64,
    },
}

/// How much memory a check is allowed to use.
///
/// # Why `MemAvailable` and not `MemFree`
///
/// `MemFree` ignores reclaimable page cache and so wildly understates what is
/// usable; `MemAvailable` is the kernel's own estimate of what a new allocation
/// can obtain without swapping. Critically, `MemAvailable` **excludes** `tmpfs`
/// (`Shmem`), which is not reclaimable — and `/tmp` on this project's hosts is a
/// 62 GiB tmpfs whose contents are RAM. `df` on that mount reports disk and is
/// the wrong instrument; `MemAvailable` already has it right.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemoryBudget {
    limit_bytes: u64,
    source: BudgetSource,
}

impl MemoryBudget {
    /// Fraction of `MemAvailable` [`MemoryBudget::from_system`] will commit,
    /// leaving room for the rest of the machine and for the allocator's own
    /// fragmentation.
    pub const DEFAULT_HEADROOM_NUMERATOR: u64 = 4;
    /// Denominator of [`MemoryBudget::DEFAULT_HEADROOM_NUMERATOR`].
    pub const DEFAULT_HEADROOM_DENOMINATOR: u64 = 5;

    /// An explicit budget of `limit_bytes`.
    pub fn bytes(limit_bytes: u64) -> Self {
        Self {
            limit_bytes,
            source: BudgetSource::Explicit,
        }
    }

    /// Four fifths of the system's `MemAvailable`, or `None` where that cannot
    /// be read (any non-Linux target, or a sandbox without `/proc`).
    ///
    /// A `None` here is a *missing measurement*, and the caller must decide what
    /// to do about it. It is deliberately not defaulted to "unlimited": that is
    /// the behaviour this module exists to replace.
    pub fn from_system() -> Option<Self> {
        let mem_available_bytes = system_mem_available_bytes()?;
        Some(Self {
            limit_bytes: mem_available_bytes / Self::DEFAULT_HEADROOM_DENOMINATOR
                * Self::DEFAULT_HEADROOM_NUMERATOR,
            source: BudgetSource::SystemAvailable {
                mem_available_bytes,
            },
        })
    }

    /// The limit in bytes.
    pub fn limit_bytes(self) -> u64 {
        self.limit_bytes
    }

    /// Where the limit came from.
    pub fn source(self) -> BudgetSource {
        self.source
    }

    /// Decides whether a check predicted to cost `estimate` may proceed.
    ///
    /// # Errors
    ///
    /// Returns [`DratResourceDecline`] when the prediction exceeds the budget.
    /// That is not a checking failure and says nothing about the proof.
    pub fn admits(
        self,
        estimate: DratMemoryEstimate,
    ) -> Result<DratMemoryEstimate, Box<DratResourceDecline>> {
        if estimate.estimated_bytes <= self.limit_bytes {
            Ok(estimate)
        } else {
            Err(Box::new(DratResourceDecline {
                estimate,
                budget: self,
            }))
        }
    }
}

/// Reads `MemAvailable` from `/proc/meminfo`, in bytes.
fn system_mem_available_bytes() -> Option<u64> {
    let meminfo = std::fs::read_to_string("/proc/meminfo").ok()?;
    parse_mem_available_bytes(&meminfo)
}

/// Parses `MemAvailable` out of `/proc/meminfo` text. Split out so it is
/// testable without a `/proc`.
fn parse_mem_available_bytes(meminfo: &str) -> Option<u64> {
    let line = meminfo
        .lines()
        .find(|line| line.starts_with("MemAvailable:"))?;
    let kib: u64 = line.split_whitespace().nth(1)?.parse().ok()?;
    kib.checked_mul(1024)
}

/// A refusal to check on resource grounds (ADR-0426).
///
/// This is the type that replaces exit 137. It is **not** an error about the
/// proof: nothing was read, nothing was verified, and nothing was rejected. A
/// caller that turns this into "the claim is refuted" has made a category error,
/// which is exactly the confusion the OOM killer used to create for free.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DratResourceDecline {
    estimate: DratMemoryEstimate,
    budget: MemoryBudget,
}

impl DratResourceDecline {
    /// The prediction that exceeded the budget.
    pub fn estimate(self) -> DratMemoryEstimate {
        self.estimate
    }

    /// The budget it exceeded.
    pub fn budget(self) -> MemoryBudget {
        self.budget
    }

    /// Bytes by which the prediction exceeds the budget.
    pub fn shortfall_bytes(self) -> u64 {
        self.estimate
            .estimated_bytes
            .saturating_sub(self.budget.limit_bytes)
    }
}

impl core::fmt::Display for DratResourceDecline {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "declined to check a {} byte DRAT proof: the {} route is predicted to need \
             {} bytes of resident memory ({:.2}x the proof) against a budget of {} bytes, \
             a shortfall of {} bytes. Nothing was checked; this is not a verdict on the proof.",
            self.estimate.shape.proof_bytes,
            self.estimate.route,
            self.estimate.estimated_bytes,
            self.estimate.bytes_per_proof_byte().unwrap_or(0.0),
            self.budget.limit_bytes,
            self.shortfall_bytes(),
        )
    }
}

impl core::error::Error for DratResourceDecline {}

/// What a budgeted check predicted, and what it actually cost.
///
/// `observed_structure_bytes` is not an estimate: it is the sum of the
/// allocation capacities the checker actually held, read off the live data
/// structures at their peak. Logging this is how the constants in
/// [`DratMemoryModel`] stay measured rather than remembered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DratMemoryReport {
    estimate: DratMemoryEstimate,
    observed_structure_bytes: u64,
    observed_shape: DratProofShape,
}

impl DratMemoryReport {
    /// Builds a report. Crate-internal: only a checker can supply an honest
    /// observation.
    pub(crate) fn new(
        estimate: DratMemoryEstimate,
        observed_structure_bytes: u64,
        observed_shape: DratProofShape,
    ) -> Self {
        Self {
            estimate,
            observed_structure_bytes,
            observed_shape,
        }
    }

    /// What was predicted before the run.
    pub fn estimate(self) -> DratMemoryEstimate {
        self.estimate
    }

    /// Bytes the checker's own data structures held at their peak, summed from
    /// their allocation capacities.
    pub fn observed_structure_bytes(self) -> u64 {
        self.observed_structure_bytes
    }

    /// The proof's shape as actually counted during the run.
    pub fn observed_shape(self) -> DratProofShape {
        self.observed_shape
    }

    /// Observed structure bytes per byte of proof text. `None` when the proof's
    /// byte length is unknown or zero.
    pub fn observed_bytes_per_proof_byte(self) -> Option<f64> {
        if self.observed_shape.proof_bytes == 0 {
            return None;
        }
        #[allow(clippy::cast_precision_loss)]
        Some(self.observed_structure_bytes as f64 / self.observed_shape.proof_bytes as f64)
    }
}

impl core::fmt::Display for DratMemoryReport {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} route: {} proof bytes, {} steps, {} added literals; \
             predicted {} bytes, held {} bytes ({:.2}x observed vs {:.2}x predicted)",
            self.estimate.route,
            self.observed_shape.proof_bytes,
            self.observed_shape.steps,
            self.observed_shape.added_literals,
            self.estimate.estimated_bytes,
            self.observed_structure_bytes,
            self.observed_bytes_per_proof_byte().unwrap_or(0.0),
            self.estimate.bytes_per_proof_byte().unwrap_or(0.0),
        )
    }
}

/// The outcome of a budgeted backward DRAT check (ADR-0426).
///
/// Three outcomes, deliberately distinct, because two of them used to be the
/// same exit code:
///
/// - [`BackwardCheckOutcome::Refuted`] — the proof establishes UNSAT.
/// - [`BackwardCheckOutcome::NoRefutation`] — the proof verifies but contains no
///   empty clause, so UNSAT is *not* established.
/// - [`BackwardCheckOutcome::Declined`] — the check was not attempted, because
///   it was predicted not to fit. Says nothing whatever about the proof.
///
/// A proof that fails to verify is not an outcome here at all: it is
/// [`crate::DratError::StepNotVerified`], an error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BackwardCheckOutcome {
    /// The formula is refuted by the proof.
    Refuted(DratMemoryReport),
    /// The proof verifies but derives no empty clause.
    NoRefutation(DratMemoryReport),
    /// Not attempted: the predicted footprint exceeded the budget.
    Declined(Box<DratResourceDecline>),
}

impl BackwardCheckOutcome {
    /// `true` only for [`BackwardCheckOutcome::Refuted`].
    ///
    /// Named for what it means rather than for a bare `bool`, so that a
    /// declined check cannot be silently read as an established refutation.
    pub fn is_refuted(&self) -> bool {
        matches!(self, BackwardCheckOutcome::Refuted(_))
    }

    /// The memory report, for the two outcomes that ran.
    pub fn report(&self) -> Option<DratMemoryReport> {
        match self {
            BackwardCheckOutcome::Refuted(report) | BackwardCheckOutcome::NoRefutation(report) => {
                Some(*report)
            }
            BackwardCheckOutcome::Declined(_) => None,
        }
    }

    /// The decline, when the check was not attempted.
    pub fn decline(&self) -> Option<DratResourceDecline> {
        match self {
            BackwardCheckOutcome::Declined(decline) => Some(**decline),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CnfLit, CnfVar, DratStep};

    fn lit(dimacs: i32) -> CnfLit {
        let var = CnfVar::new(dimacs.unsigned_abs() as usize - 1).expect("small variable");
        let positive = CnfLit::positive(var);
        if dimacs < 0 {
            positive.negated()
        } else {
            positive
        }
    }

    #[test]
    fn parses_mem_available() {
        let meminfo =
            "MemTotal:       129000000 kB\nMemFree:  100 kB\nMemAvailable:   75497472 kB\n";
        assert_eq!(parse_mem_available_bytes(meminfo), Some(75_497_472 * 1024));
    }

    #[test]
    fn missing_mem_available_is_none_not_unlimited() {
        assert_eq!(parse_mem_available_bytes("MemTotal: 100 kB\n"), None);
    }

    #[test]
    fn exact_shape_counts_additions_and_deletions_separately() {
        let proof = vec![
            DratStep::Add(vec![lit(1), lit(-2)]),
            DratStep::Delete(vec![lit(1), lit(-2), lit(3)]),
            DratStep::Add(vec![]),
        ];
        let shape = DratProofShape::of_steps(&proof);
        assert_eq!(shape.steps(), 3);
        assert_eq!(shape.added_clauses(), 2);
        assert_eq!(shape.added_literals(), 2);
        assert_eq!(shape.total_literals(), 5);
        assert_eq!(shape.source(), DratShapeSource::Exact);
    }

    #[test]
    fn sampling_a_whole_short_proof_is_exact() {
        let text = "1 -2 0\nd 1 -2 3 0\n0\n";
        let shape = DratProofShape::sample(std::io::Cursor::new(text), text.len() as u64, 1 << 20)
            .expect("cursor cannot fail");
        assert_eq!(shape.source(), DratShapeSource::Exact);
        assert_eq!(shape.steps(), 3);
        assert_eq!(shape.added_clauses(), 2);
        assert_eq!(shape.added_literals(), 2);
        assert_eq!(shape.total_literals(), 5);
    }

    #[test]
    fn sampling_scales_a_prefix_to_the_whole_file() {
        // Ten identical two-literal additions; sampling the first ~half must
        // extrapolate back to ten.
        let mut text = String::new();
        for _ in 0..10 {
            text.push_str("1 -2 0\n");
        }
        let shape = DratProofShape::sample(
            std::io::Cursor::new(text.clone()),
            text.len() as u64,
            (text.len() / 2) as u64,
        )
        .expect("cursor cannot fail");
        assert!(matches!(
            shape.source(),
            DratShapeSource::Sampled { sampled_bytes } if sampled_bytes < text.len() as u64
        ));
        assert_eq!(shape.steps(), 10);
        assert_eq!(shape.added_literals(), 20);
    }

    #[test]
    fn comments_and_blank_lines_are_not_steps() {
        let text = "c a comment\n\n1 0\n";
        let shape = DratProofShape::sample(std::io::Cursor::new(text), text.len() as u64, 1 << 20)
            .expect("cursor cannot fail");
        assert_eq!(shape.steps(), 1);
        assert_eq!(shape.added_literals(), 1);
    }

    #[test]
    fn file_backed_route_is_cheaper_than_in_memory_on_the_same_shape() {
        let shape = DratProofShape::from_proof_bytes(1_000_000_000);
        let in_memory = DratMemoryModel::new(DratCheckRoute::InMemoryBackward)
            .estimate(shape, FormulaShape::EMPTY);
        let file_backed = DratMemoryModel::new(DratCheckRoute::FileBackedBackward)
            .estimate(shape, FormulaShape::EMPTY);
        assert!(file_backed.estimated_bytes() < in_memory.estimated_bytes());
    }

    #[test]
    fn a_budget_declines_and_says_so_without_a_verdict() {
        let shape = DratProofShape::from_proof_bytes(20_000_000_000);
        let estimate = DratMemoryModel::new(DratCheckRoute::InMemoryBackward)
            .estimate(shape, FormulaShape::EMPTY);
        let budget = MemoryBudget::bytes(26 * 1024 * 1024 * 1024);
        let decline = budget
            .admits(estimate)
            .expect_err("20 GB must not fit in 26 GiB");
        assert!(decline.shortfall_bytes() > 0);
        let rendered = decline.to_string();
        assert!(rendered.contains("declined"));
        assert!(rendered.contains("not a verdict"));
    }

    #[test]
    fn a_budget_admits_what_fits() {
        let shape = DratProofShape::from_proof_bytes(1_000_000);
        let estimate = DratMemoryModel::new(DratCheckRoute::InMemoryBackward)
            .estimate(shape, FormulaShape::EMPTY);
        assert!(MemoryBudget::bytes(1 << 30).admits(estimate).is_ok());
    }

    #[test]
    fn declined_is_not_refuted() {
        let shape = DratProofShape::from_proof_bytes(20_000_000_000);
        let estimate = DratMemoryModel::new(DratCheckRoute::InMemoryBackward)
            .estimate(shape, FormulaShape::EMPTY);
        let decline = MemoryBudget::bytes(1 << 20)
            .admits(estimate)
            .expect_err("must decline");
        let outcome = BackwardCheckOutcome::Declined(decline);
        assert!(!outcome.is_refuted());
        assert!(outcome.report().is_none());
        assert!(outcome.decline().is_some());
    }
}
