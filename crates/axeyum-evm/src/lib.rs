//! # axeyum-evm — EVM bytecode symbolic bug-hunter
//!
//! Symbolically execute raw EVM runtime bytecode over symbolic calldata to find
//! arithmetic-overflow / assertion-violation (`REVERT`/`INVALID`/`Panic(0x11)`)
//! bugs, emitting a **replayable calldata witness** on a bug and a re-checked
//! (Lean-checkable, when in fragment) **no-bug certificate** when a function is
//! proven safe up to a bound.
//!
//! The decidable EVM core is `QF_BV`/`QF_ABV` — axeyum's strongest fragments:
//! 256-bit words = `BV256`, byte memory + word storage, keccak / external `CALL` /
//! gas are **havoc'd** to a sound `Unknown` (never wrong-pruned, exactly as
//! halmos/hevm defer). Built on the `SymbolicExecutor` path explorer.
//!
//! ## Soundness discipline (DISAGREE = 0)
//!
//! Every witness is re-checked by *concrete* re-execution ([`concrete::run`]): the
//! solver's calldata is run through a from-scratch concrete interpreter and the
//! bug must actually fire. A witness that does not reproduce is a defect in the
//! lowering, never a reported finding. See `docs/consumer-track/evm/PLAN.md`.
//!
//! ## At a glance
//!
//! ```rust
//! use axeyum_evm::{analyze, AnalyzeConfig};
//!
//! // PUSH1 0x05 PUSH1 0x05 ... a tiny contract; see the crate tests for real ones.
//! let bytecode = [0x60, 0x00, 0x00]; // PUSH1 0; STOP
//! let report = analyze(&bytecode, &AnalyzeConfig::default());
//! assert!(report.findings.is_empty());
//! ```
#![forbid(unsafe_code)]

pub mod concrete;
pub mod keccak;
pub mod opcode;
pub mod reproduce;
pub mod symbolic;
pub mod word;

use axeyum_ir::Value;
use axeyum_solver::{EvidenceReport, SolverConfig, SolverError};

use crate::concrete::{Env, Halt};
use crate::symbolic::BugKind;
use crate::word::Word;

/// How symbolic-key storage reads/writes are lowered to the solver.
///
/// Both encodings are denotation-equivalent (last-write-wins, cold slots read 0);
/// they differ only in *how* the read-over-write is expressed, which is the
/// warm-array vs frontend-`ite`-fold trade-off the capability scoreboard measures
/// (see `docs/consumer-track/evm/SCOREBOARD.md`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum MemoryEncoding {
    /// Frontend read-over-write: `SLOAD(k)` folds `ite(k = kᵢ, vᵢ, …)` over the
    /// write list (pure `QF_BV`). The original Phase-2 encoding.
    #[default]
    IteFold,
    /// Real SMT arrays: storage is a `const_array(0)` advanced by `store` on each
    /// `SSTORE`, and `SLOAD(k)` is `select`. Feasibility auto-routes through the
    /// solver's warm/memory-aware path (`SymbolicMemory` + `assume_auto`).
    WarmArray,
}

/// Configuration for an [`analyze`] run.
#[derive(Debug, Clone)]
pub struct AnalyzeConfig {
    /// Look for unsigned `ADD`/`MUL` overflow on tracked arithmetic ops.
    pub detect_overflow: bool,
    /// Treat reachable `REVERT`/`INVALID` as bugs.
    pub detect_assertions: bool,
    /// Maximum opcodes executed per path (loop / runaway bound).
    pub max_steps: usize,
    /// How symbolic-key storage is lowered (warm arrays vs `ite`-fold).
    pub memory: MemoryEncoding,
    /// Maximum number of transactions in a sequence to explore (persistent
    /// storage between them, fresh symbolic calldata each). `1` = single-tx
    /// (the default); `>1` searches for bugs reachable only across calls.
    pub max_txs: usize,
    /// The solver configuration threaded into the feasibility checks.
    pub solver: SolverConfig,
}

impl Default for AnalyzeConfig {
    fn default() -> Self {
        Self {
            detect_overflow: true,
            detect_assertions: true,
            max_steps: 10_000,
            memory: MemoryEncoding::default(),
            max_txs: 1,
            solver: SolverConfig::default(),
        }
    }
}

/// What kind of bug a [`Finding`] reports (mirrors [`BugKind`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FindingKind {
    /// A reachable `REVERT` (require/assert failure, `Panic(0x11)`, …).
    Revert,
    /// A reachable `INVALID` opcode.
    Invalid,
    /// A reachable unsigned `ADD` overflow.
    AddOverflow,
    /// A reachable unsigned `MUL` overflow.
    MulOverflow,
}

impl From<BugKind> for FindingKind {
    fn from(k: BugKind) -> Self {
        match k {
            BugKind::Revert => FindingKind::Revert,
            BugKind::Invalid => FindingKind::Invalid,
            BugKind::AddOverflow => FindingKind::AddOverflow,
            BugKind::MulOverflow => FindingKind::MulOverflow,
        }
    }
}

/// The concrete inputs of one transaction in a multi-tx witness sequence.
#[derive(Debug, Clone)]
pub struct TxCall {
    /// The concrete calldata for this transaction.
    pub calldata: Vec<u8>,
    /// The concrete `CALLVALUE` (msg.value) for this transaction.
    pub callvalue: [u8; 32],
    /// The concrete `CALLER` (msg.sender) for this transaction.
    pub caller: [u8; 32],
}

/// A discovered bug plus the concrete inputs that trigger it.
#[derive(Debug, Clone)]
pub struct Finding {
    /// The kind of bug.
    pub kind: FindingKind,
    /// The byte offset (pc) of the offending opcode.
    pub pc: usize,
    /// The concrete calldata that drives the **bug's transaction** to the bug —
    /// the **replayable witness** (validated by concrete re-execution before being
    /// reported). For a single-tx bug this is the whole witness.
    pub calldata_witness: Vec<u8>,
    /// The concrete `CALLVALUE` (msg.value) in the bug's transaction.
    pub callvalue: [u8; 32],
    /// The concrete `CALLER` (msg.sender) in the bug's transaction.
    pub caller: [u8; 32],
    /// Transactions that must run first (storage persisting) to reach the bug —
    /// empty for a single-tx bug. The full replay sequence is
    /// `prior_txs` followed by `(calldata_witness, callvalue, caller)`.
    pub prior_txs: Vec<TxCall>,
    /// Concrete values for the environment opcodes (`GAS`/`BALANCE`/context/…)
    /// encountered on the path, in execution order — replayed by the concrete
    /// oracle so the bug reproduces deterministically. Empty when the path used no
    /// environment opcodes.
    pub env_inputs: Vec<[u8; 32]>,
    /// How the concrete re-execution of the full sequence halted — the independent
    /// confirmation that the bug is real.
    pub concrete_halt: Halt,
}

/// The no-bug verdict (when no [`Finding`] was produced).
#[derive(Debug)]
pub enum Verdict {
    /// No bug was found and no path was undecided within the explored sub-tree —
    /// a sound "no bug up to the step bound" result. Carries a best-effort
    /// re-checked evidence report when one could be produced.
    SafeUpToBound {
        /// A re-checked safety certificate, when the safety query lay in a
        /// fragment `produce_evidence` could certify (boxed: an
        /// [`EvidenceReport`] is large relative to the other variant).
        evidence: Option<Box<EvidenceReport>>,
    },
    /// No bug was found, but some explored path ended in `Unknown` (a havoc'd
    /// keccak/CALL/gas op, an unresolved symbolic offset, or a solver limit) — so
    /// the absence of a finding is **not** a soundness claim. Honest `unknown`.
    InconclusiveDueToUnknown,
}

/// The result of analysing a contract.
#[derive(Debug)]
pub struct AnalysisReport {
    /// Bugs found (Phase-1 reports the first feasible bug; the list is the
    /// extension point).
    pub findings: Vec<Finding>,
    /// The no-bug verdict (only meaningful when `findings` is empty).
    pub verdict: Option<Verdict>,
}

impl AnalysisReport {
    /// Whether any bug was reported.
    #[must_use]
    pub fn has_findings(&self) -> bool {
        !self.findings.is_empty()
    }
}

/// Analyses EVM runtime `bytecode` for overflow / assertion-violation bugs over
/// symbolic calldata. Returns concrete, **concretely-revalidated** witnesses for
/// any bug, or a no-bug verdict.
///
/// # Panics
///
/// Never panics in normal operation; an internal solver error is folded into an
/// inconclusive verdict (sound: an error never becomes a wrong "no bug").
#[must_use]
pub fn analyze(bytecode: &[u8], cfg: &AnalyzeConfig) -> AnalysisReport {
    match analyze_inner(bytecode, cfg) {
        Ok(report) => report,
        // A genuine solver/IR error is folded into an honest inconclusive verdict
        // rather than a wrong "safe": never report safety we did not establish.
        Err(_) => AnalysisReport {
            findings: Vec::new(),
            verdict: Some(Verdict::InconclusiveDueToUnknown),
        },
    }
}

fn analyze_inner(bytecode: &[u8], cfg: &AnalyzeConfig) -> Result<AnalysisReport, SolverError> {
    let program = opcode::decode(bytecode);
    let track_overflow = cfg.detect_overflow;

    let exploration = symbolic::explore(
        &program,
        &cfg.solver,
        cfg.max_steps,
        track_overflow,
        cfg.memory,
        cfg.max_txs,
    )?;

    if let Some(bug) = &exploration.bug {
        // Only report assertion bugs if assertion detection is on; overflow bugs
        // are already gated by `track_overflow` in the explorer.
        let report_it = match bug.kind {
            BugKind::Revert | BugKind::Invalid => cfg.detect_assertions,
            BugKind::AddOverflow | BugKind::MulOverflow => true,
        };
        if report_it {
            if let Some(finding) = revalidate(&program, bug, cfg) {
                return Ok(AnalysisReport {
                    findings: vec![finding],
                    verdict: None,
                });
            }
            // Witness did not reproduce concretely: this is a lowering defect, not
            // a finding. Surface as inconclusive rather than a false positive.
            return Ok(AnalysisReport {
                findings: Vec::new(),
                verdict: Some(Verdict::InconclusiveDueToUnknown),
            });
        }
    }

    // No reported bug.
    let verdict = if exploration.saw_unknown {
        Verdict::InconclusiveDueToUnknown
    } else {
        // The path tree was fully decided and bug free. Tie the certificate to the
        // explorer's *real* refutation (item #3): the disjunction of every
        // bug-reachability obligation it proved infeasible is UNSAT, and that is
        // the "no bad state is path-reachable up to the bound" proof — no longer a
        // fabricated `0==1`.
        Verdict::SafeUpToBound {
            evidence: safety_evidence(exploration.refuted_obligations, &cfg.solver),
        }
    };
    Ok(AnalysisReport {
        findings: Vec::new(),
        verdict: Some(verdict),
    })
}

/// Produces a re-checked evidence report for the **real** safety claim: the
/// disjunction of the bug-reachability obligations the explorer refuted is UNSAT
/// (item #3). Each obligation `pathᵢ ∧ bug_predicateᵢ` was individually proved
/// infeasible during exploration, so their disjunction is unsatisfiable — a
/// genuine "no bad state is reachable up to the bound" certificate, re-checked
/// before it is handed out. When the explored program had **no** bug site at all
/// the obligation set is empty and the claim is vacuously the unsatisfiable
/// `false` — still derived from the real structure (nothing reachable to refute),
/// not an invented contradiction.
fn safety_evidence(
    refuted: symbolic::RefutedSafety,
    config: &SolverConfig,
) -> Option<Box<EvidenceReport>> {
    let symbolic::RefutedSafety {
        mut arena,
        obligations,
    } = refuted;

    // The safety formula = OR of the refuted obligations (each individually
    // infeasible ⇒ the disjunction is UNSAT). Empty ⇒ `false` (vacuous safety).
    let formula = match obligations.split_first() {
        None => arena.bool_const(false),
        Some((&first, rest)) => {
            let mut acc = first;
            for &ob in rest {
                acc = arena.or(acc, ob).ok()?;
            }
            acc
        }
    };

    let report = axeyum_solver::produce_evidence(&mut arena, &[formula], config).ok()?;
    // Re-check before handing it out (DISAGREE=0 discipline for the cert path too).
    if report.evidence.check(&arena, &[formula]).ok()? {
        Some(Box::new(report))
    } else {
        None
    }
}

/// Re-executes the lifted witness **concretely** to confirm the bug reproduces.
/// Returns `None` if the witness fails to reproduce (a lowering defect → no
/// finding, never a false positive). This is the DISAGREE=0 gate.
fn revalidate(
    program: &opcode::Program,
    bug: &symbolic::PathBug,
    cfg: &AnalyzeConfig,
) -> Option<Finding> {
    let here = Env {
        calldata: bug.calldata.clone(),
        callvalue: bug.callvalue.clone(),
        caller: bug.caller.clone(),
    };

    let env_inputs: Vec<[u8; 32]> = bug.env_inputs.iter().map(Word::to_be_bytes).collect();

    // Single-tx bug: the original concrete revalidation (replaying any env opcodes).
    if bug.prior_txs.is_empty() {
        let halt = concrete::run_with_env(program, &here, cfg.max_steps, &bug.env_inputs);
        let reproduces = match bug.kind {
            BugKind::Revert => matches!(halt, Halt::Revert(_)),
            BugKind::Invalid => matches!(halt, Halt::Invalid),
            // For an overflow bug the concrete run need not revert; instead we
            // confirm the tracked arithmetic op at `bug.pc` concretely overflows.
            BugKind::AddOverflow | BugKind::MulOverflow => concrete::overflow_reproduces(
                program,
                &here,
                bug.pc,
                bug.kind == BugKind::MulOverflow,
                cfg.max_steps,
            ),
        };
        if !reproduces {
            return None;
        }
        return Some(Finding {
            kind: bug.kind.into(),
            pc: bug.pc,
            calldata_witness: bug.calldata.clone(),
            callvalue: bug.callvalue.to_be_bytes(),
            caller: bug.caller.to_be_bytes(),
            prior_txs: Vec::new(),
            env_inputs,
            concrete_halt: halt,
        });
    }

    // Multi-tx bug: replay the witness transaction sequence with persistent
    // storage and confirm the final tx reaches the bug. Cross-tx *overflow* is not
    // revalidated here (conservatively rejected → Unknown, never a wrong finding).
    if matches!(bug.kind, BugKind::AddOverflow | BugKind::MulOverflow) {
        return None;
    }
    let mut envs: Vec<Env> = bug
        .prior_txs
        .iter()
        .map(|t| Env {
            calldata: t.calldata.clone(),
            callvalue: t.callvalue.clone(),
            caller: t.caller.clone(),
        })
        .collect();
    envs.push(here);
    let halt = concrete::run_sequence(program, &envs, cfg.max_steps, &bug.env_inputs);
    let reproduces = match bug.kind {
        BugKind::Revert => matches!(halt, Halt::Revert(_)),
        BugKind::Invalid => matches!(halt, Halt::Invalid),
        BugKind::AddOverflow | BugKind::MulOverflow => false,
    };
    if !reproduces {
        return None;
    }
    let prior_txs = bug
        .prior_txs
        .iter()
        .map(|t| TxCall {
            calldata: t.calldata.clone(),
            callvalue: t.callvalue.to_be_bytes(),
            caller: t.caller.to_be_bytes(),
        })
        .collect();
    Some(Finding {
        kind: bug.kind.into(),
        pc: bug.pc,
        calldata_witness: bug.calldata.clone(),
        callvalue: bug.callvalue.to_be_bytes(),
        caller: bug.caller.to_be_bytes(),
        prior_txs,
        env_inputs,
        concrete_halt: halt,
    })
}

/// Lifts a model `Value` for a byte symbol to a `u8`.
pub(crate) fn value_to_u8(value: &Value) -> u8 {
    match value {
        Value::Bool(b) => u8::from(*b),
        Value::Bv { value, .. } => u8::try_from(*value & 0xff).unwrap_or(0),
        Value::WideBv(w) => w
            .to_lsb_bits()
            .iter()
            .take(8)
            .enumerate()
            .fold(0u8, |acc, (i, &b)| if b { acc | (1 << i) } else { acc }),
        _ => 0,
    }
}

/// Lifts a model `Value` for a 256-bit word symbol to a [`Word`].
pub(crate) fn value_to_word(value: &Value) -> Word {
    match value {
        Value::Bool(b) => Word::from_u128(u128::from(*b)),
        Value::Bv { value, .. } => Word::from_u128(*value),
        Value::WideBv(w) if w.width() == word::WIDTH => Word(w.clone()),
        Value::WideBv(w) => {
            // Re-fit to 256 bits from its bits (defensive; widths should match).
            let bits = w.to_lsb_bits();
            let mut adj = vec![false; 256];
            for (i, slot) in adj.iter_mut().enumerate() {
                *slot = bits.get(i).copied().unwrap_or(false);
            }
            Word(axeyum_ir::WideUint::from_lsb_bits(&adj))
        }
        _ => Word::zero(),
    }
}
