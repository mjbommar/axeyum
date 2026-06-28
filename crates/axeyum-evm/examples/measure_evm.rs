//! EVM / symbolic-execution capability scoreboard — the consumer-track
//! measurement deliverable (integration I3).
//!
//! Runs a **construction-known** EVM corpus through [`axeyum_evm::analyze`] and
//! emits a committed scoreboard grouped by *memory-shape class*: how many bugs
//! were found (each carrying a concretely-revalidated calldata witness) and how
//! many safe contracts were proved `SafeUpToBound`, with the soundness floor
//! `DISAGREE = 0`.
//!
//! This is the symbolic-execution-engine analogue of the SMT `DOMINANCE.md`
//! scoreboard: the warm-incremental memory/array work that powers symbolic
//! storage now carries a *number* (decided rate + per-shape coverage) instead of
//! being asserted. Every reported finding is independently re-confirmed here by
//! re-running the witness through the concrete interpreter — a separate oracle
//! from the one `analyze` uses internally.
//!
//! Run: `cargo run -p axeyum-evm --example measure_evm`
//! Writes: `docs/consumer-track/evm/SCOREBOARD.md` and `.../corpus.json`.

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

use axeyum_evm::concrete::{self, Env, Halt};
use axeyum_evm::opcode::{Program, decode};
use axeyum_evm::word::Word;
use axeyum_evm::{AnalyzeConfig, FindingKind, MemoryEncoding, Verdict, analyze};

// ----- opcode byte helpers -------------------------------------------------
const STOP: u8 = 0x00;
const ADD: u8 = 0x01;
const EQ: u8 = 0x14;
const ISZERO: u8 = 0x15;
const AND: u8 = 0x16;
const SHA3: u8 = 0x20;
const CALLDATALOAD: u8 = 0x35;
const POP: u8 = 0x50;
const MLOAD: u8 = 0x51;
const MSTORE: u8 = 0x52;
const SLOAD: u8 = 0x54;
const SSTORE: u8 = 0x55;
const JUMPI: u8 = 0x57;
const GAS: u8 = 0x5a;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const PUSH2: u8 = 0x61;
const RETURN: u8 = 0xf3;
const REVERT: u8 = 0xfd;
const INVALID: u8 = 0xfe;

const STEP_LIMIT: usize = 10_000;

/// The symbolic-execution memory-shape a case exercises (the capability axis the
/// warm-incremental engine work targets).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Shape {
    /// Pure arithmetic over calldata, no memory.
    Arith,
    /// Concrete-offset `MSTORE`/`MLOAD`.
    ConcreteMem,
    /// Control flow / reachable `REVERT` guard.
    Control,
    /// Symbolic-key `SLOAD`/`SSTORE` (read-over-write storage).
    SymbolicStorage,
    /// `keccak256`-keyed mapping storage (injectivity reasoning).
    KeccakMapping,
    /// Environment / context opcodes (`GAS`/`BALANCE`/block-context) as witnessed
    /// symbolic inputs.
    Environment,
}

impl Shape {
    fn label(self) -> &'static str {
        match self {
            Shape::Arith => "arith",
            Shape::ConcreteMem => "concrete-mem",
            Shape::Control => "control-flow",
            Shape::SymbolicStorage => "symbolic-storage",
            Shape::KeccakMapping => "keccak-mapping",
            Shape::Environment => "environment",
        }
    }
}

/// What the contract was *constructed* to be — the oracle.
#[derive(Clone, Copy)]
enum Expect {
    /// A bug of this kind is reachable.
    Bug(FindingKind),
    /// No bug is reachable up to the step bound.
    Safe,
}

struct Case {
    name: &'static str,
    shape: Shape,
    expect: Expect,
    bytecode: Vec<u8>,
}

/// The decided outcome of a case, reconciled against its construction-known label.
enum Outcome {
    /// A bug was found and its witness independently reproduced.
    BugFound,
    /// The contract was proved `SafeUpToBound`.
    SafeProved,
    /// Honest `unknown` (havoc / solver limit) — a decide-incompleteness, not a
    /// soundness failure.
    Unknown,
    /// A wrong verdict against the construction-known label, or a witness that did
    /// not reproduce. Must never happen (the soundness floor).
    Disagree(String),
}

impl Outcome {
    fn tag(&self) -> &'static str {
        match self {
            Outcome::BugFound => "bug-found",
            Outcome::SafeProved => "safe-proved",
            Outcome::Unknown => "unknown",
            Outcome::Disagree(_) => "DISAGREE",
        }
    }
}

/// Independently re-confirm a reported finding by re-running its witness through
/// the concrete interpreter — a separate oracle from `analyze`'s internal one.
fn witness_reproduces(program: &Program, f: &axeyum_evm::Finding) -> bool {
    let env = Env {
        calldata: f.calldata_witness.clone(),
        callvalue: Word::from_be_bytes(&f.callvalue),
        caller: Word::from_be_bytes(&f.caller),
    };
    let env_inputs: Vec<Word> = f
        .env_inputs
        .iter()
        .map(|b| Word::from_be_bytes(b))
        .collect();
    // Multi-tx witness: replay the full transaction sequence (storage persisting,
    // env values consumed in global order) and confirm the bug fires in the final
    // tx — the independent multi-tx oracle.
    if !f.prior_txs.is_empty() {
        let mut envs: Vec<Env> = f
            .prior_txs
            .iter()
            .map(|t| Env {
                calldata: t.calldata.clone(),
                callvalue: Word::from_be_bytes(&t.callvalue),
                caller: Word::from_be_bytes(&t.caller),
            })
            .collect();
        envs.push(env);
        let halt = concrete::run_sequence(program, &envs, STEP_LIMIT, &env_inputs);
        return match f.kind {
            FindingKind::Revert => matches!(halt, Halt::Revert(_)),
            FindingKind::Invalid => matches!(halt, Halt::Invalid),
            FindingKind::AddOverflow | FindingKind::MulOverflow => false,
        };
    }
    match f.kind {
        FindingKind::AddOverflow => {
            concrete::overflow_reproduces(program, &env, f.pc, false, STEP_LIMIT)
        }
        FindingKind::MulOverflow => {
            concrete::overflow_reproduces(program, &env, f.pc, true, STEP_LIMIT)
        }
        FindingKind::Revert => {
            matches!(
                concrete::run_with_env(program, &env, STEP_LIMIT, &env_inputs),
                Halt::Revert(_)
            )
        }
        FindingKind::Invalid => {
            matches!(
                concrete::run_with_env(program, &env, STEP_LIMIT, &env_inputs),
                Halt::Invalid
            )
        }
    }
}

fn evaluate(case: &Case) -> Outcome {
    evaluate_with(case, MemoryEncoding::default())
}

fn evaluate_with(case: &Case, memory: MemoryEncoding) -> Outcome {
    let cfg = AnalyzeConfig {
        memory,
        ..AnalyzeConfig::default()
    };
    let report = analyze(&case.bytecode, &cfg);
    evaluate_report(case, report)
}

/// Reconcile an already-computed report against the case's construction-known
/// label (shared by the default sweep and the multi-tx / encoding comparisons).
fn evaluate_report(case: &Case, report: axeyum_evm::AnalysisReport) -> Outcome {
    let program = decode(&case.bytecode);

    if let Some(f) = report.findings.first() {
        // A finding exists. It was concretely revalidated inside `analyze`; we
        // re-confirm independently here too.
        if !witness_reproduces(&program, f) {
            return Outcome::Disagree(format!(
                "reported {:?} finding did not reproduce concretely",
                f.kind
            ));
        }
        return match case.expect {
            // The witness genuinely reaches the bug. On a contract we labelled
            // safe, the witness is ground truth — the disagreement is real.
            Expect::Safe => {
                Outcome::Disagree(format!("witnessed {:?} bug on a safe contract", f.kind))
            }
            Expect::Bug(_) => Outcome::BugFound,
        };
    }

    match (&case.expect, report.verdict) {
        (Expect::Safe, Some(Verdict::SafeUpToBound { .. })) => Outcome::SafeProved,
        // Proving safety on a contract with a reachable bug is a soundness failure.
        (Expect::Bug(kind), Some(Verdict::SafeUpToBound { .. })) => Outcome::Disagree(format!(
            "proved SafeUpToBound but a {kind:?} bug is reachable"
        )),
        // Honest unknown either way — decide-incompleteness, not unsoundness.
        (_, Some(Verdict::InconclusiveDueToUnknown) | None) => Outcome::Unknown,
    }
}

#[derive(Default)]
struct Tally {
    total: usize,
    bug_found: usize,
    safe_proved: usize,
    unknown: usize,
    disagree: usize,
}

impl Tally {
    fn record(&mut self, outcome: &Outcome) {
        self.total += 1;
        match outcome {
            Outcome::BugFound => self.bug_found += 1,
            Outcome::SafeProved => self.safe_proved += 1,
            Outcome::Unknown => self.unknown += 1,
            Outcome::Disagree(_) => self.disagree += 1,
        }
    }

    fn decided(&self) -> usize {
        self.bug_found + self.safe_proved
    }
}

#[rustfmt::skip]
fn corpus() -> Vec<Case> {
    use Expect::{Bug, Safe};
    use FindingKind::{AddOverflow, Invalid, Revert};
    use Shape::{Arith, ConcreteMem, Control, Environment, KeccakMapping, SymbolicStorage};
    vec![
        Case {
            name: "add-overflow-unguarded", shape: Arith, expect: Bug(AddOverflow),
            bytecode: vec![
                PUSH1, 0x00, CALLDATALOAD, PUSH1, 0x20, CALLDATALOAD, ADD, PUSH1, 0x00, MSTORE,
                PUSH1, 0x20, PUSH1, 0x00, RETURN,
            ],
        },
        Case {
            name: "mask-then-store-safe", shape: ConcreteMem, expect: Safe,
            bytecode: vec![
                PUSH1, 0x00, CALLDATALOAD, PUSH1, 0xff, AND, PUSH1, 0x00, MSTORE, PUSH1, 0x20,
                PUSH1, 0x00, RETURN,
            ],
        },
        Case {
            name: "require-nonzero-revert", shape: Control, expect: Bug(Revert),
            bytecode: vec![
                PUSH1, 0x00, CALLDATALOAD, ISZERO, PUSH1, 0x0a, JUMPI, STOP, STOP, STOP, JUMPDEST,
                PUSH1, 0x00, PUSH1, 0x00, REVERT,
            ],
        },
        Case {
            name: "reachable-invalid-opcode", shape: Control, expect: Bug(Invalid),
            bytecode: vec![
                PUSH1, 0x00, CALLDATALOAD, ISZERO, PUSH1, 0x0a, JUMPI, STOP, STOP, STOP, JUMPDEST,
                INVALID,
            ],
        },
        Case {
            name: "mem-roundtrip-safe", shape: ConcreteMem, expect: Safe,
            bytecode: vec![
                PUSH1, 0x00, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x00, MLOAD, PUSH1, 0x20,
                PUSH1, 0x00, RETURN,
            ],
        },
        Case {
            name: "symbolic-storage-roundtrip-revert", shape: SymbolicStorage, expect: Bug(Revert),
            bytecode: vec![
                PUSH1, 0x20, CALLDATALOAD, PUSH1, 0x00, CALLDATALOAD, SSTORE, PUSH1, 0x40,
                CALLDATALOAD, SLOAD, PUSH2, 0xde, 0xad, EQ, PUSH1, 0x13, JUMPI, STOP, JUMPDEST,
                PUSH1, 0x00, PUSH1, 0x00, REVERT,
            ],
        },
        Case {
            name: "cold-slot-load-safe", shape: SymbolicStorage, expect: Safe,
            bytecode: vec![
                PUSH1, 0x99, SLOAD, PUSH2, 0xde, 0xad, EQ, PUSH1, 0x0b, JUMPI, STOP, JUMPDEST,
                PUSH1, 0x00, PUSH1, 0x00, REVERT,
            ],
        },
        Case {
            name: "gas-branch-revert", shape: Environment, expect: Bug(Revert),
            bytecode: vec![
                GAS, ISZERO, PUSH1, 0x07, JUMPI, STOP, STOP, JUMPDEST, PUSH1, 0x00, PUSH1, 0x00,
                REVERT,
            ],
        },
        Case {
            name: "reads-gas-safe", shape: Environment, expect: Safe,
            bytecode: vec![GAS, POP, STOP],
        },
        Case {
            name: "keccak-mapping-alias-revert", shape: KeccakMapping, expect: Bug(Revert),
            bytecode: vec![
                PUSH1, 0x00, CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x00, PUSH1, 0x20, MSTORE,
                PUSH2, 0xde, 0xad, PUSH1, 0x40, PUSH1, 0x00, SHA3, SSTORE, PUSH1, 0x20,
                CALLDATALOAD, PUSH1, 0x00, MSTORE, PUSH1, 0x40, PUSH1, 0x00, SHA3, SLOAD, PUSH2,
                0xde, 0xad, EQ, PUSH1, 0x29, JUMPI, STOP, STOP, JUMPDEST, PUSH1, 0x00, PUSH1, 0x00,
                REVERT,
            ],
        },
    ]
}

/// One case decided under both storage encodings, with wall-clock timings.
struct EncCompare {
    name: &'static str,
    shape: &'static str,
    ite_tag: String,
    ite_us: u128,
    warm_tag: String,
    warm_us: u128,
    agree: bool,
}

/// Decide the symbolic-storage / keccak rows under both `ite`-fold and warm-array
/// encodings. The two must agree (denotation equivalence); the timings are the
/// warm-vs-`ite`-fold signal that informs the U6 special-case-vs-general decision.
fn compare_encodings(cases: &[Case]) -> Vec<EncCompare> {
    let mut out = Vec::new();
    for case in cases {
        if !matches!(case.shape, Shape::SymbolicStorage | Shape::KeccakMapping) {
            continue;
        }
        let t0 = Instant::now();
        let ite = evaluate_with(case, MemoryEncoding::IteFold);
        let ite_us = t0.elapsed().as_micros();
        let t1 = Instant::now();
        let warm = evaluate_with(case, MemoryEncoding::WarmArray);
        let warm_us = t1.elapsed().as_micros();
        out.push(EncCompare {
            name: case.name,
            shape: case.shape.label(),
            agree: ite.tag() == warm.tag(),
            ite_tag: ite.tag().to_string(),
            ite_us,
            warm_tag: warm.tag().to_string(),
            warm_us,
        });
    }
    out
}

fn render_compare(cmp: &[EncCompare]) -> String {
    let mut out = String::new();
    out.push_str("\n## Warm-array vs `ite`-fold (symbolic-storage rows)\n\n");
    out.push_str(
        "Both storage encodings are denotation-equivalent, so **cross-encoding \
         agreement must hold on every row** (a disagreement counts against the \
         DISAGREE floor above). Times are a single wall-clock `analyze()` run — \
         indicative of the encoding cost, not a tuned benchmark.\n\n",
    );
    out.push_str("| Case | Shape | `ite`-fold | t µs | warm-array | t µs | agree |\n");
    out.push_str("|---|---|---|---|---|---|---|\n");
    for c in cmp {
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} | {} | {} | {} |",
            c.name,
            c.shape,
            c.ite_tag,
            c.ite_us,
            c.warm_tag,
            c.warm_us,
            if c.agree { "yes" } else { "**NO**" },
        );
    }
    out
}

fn render_markdown(
    rows: &[(&Case, Outcome)],
    overall: &Tally,
    by_shape: &[(Shape, Tally)],
) -> String {
    let mut out = String::new();
    out.push_str("# EVM / symbolic-execution capability scoreboard\n\n");
    out.push_str(
        "Generated by `cargo run -p axeyum-evm --example measure_evm`. A \
         construction-known EVM corpus through `axeyum_evm::analyze`, grouped by \
         memory-shape class. Every reported bug carries a calldata witness that \
         reproduces under the concrete interpreter (re-confirmed here, \
         independently of `analyze`'s internal revalidation).\n\n",
    );

    let _ = writeln!(
        out,
        "## Headline\n\n- **{} cases**, **{} decided** ({} bugs found + {} safe \
         proved), {} honest unknown.\n- **DISAGREE = {}** — the soundness floor \
         (a wrong verdict against a construction-known label, or a witness that \
         did not reproduce).\n",
        overall.total,
        overall.decided(),
        overall.bug_found,
        overall.safe_proved,
        overall.unknown,
        overall.disagree,
    );

    out.push_str("## By memory-shape class\n\n");
    out.push_str("| Shape | Cases | Bug-found | Safe-proved | Unknown | DISAGREE |\n");
    out.push_str("|---|---|---|---|---|---|\n");
    for (shape, t) in by_shape {
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} | {} | {} |",
            shape.label(),
            t.total,
            t.bug_found,
            t.safe_proved,
            t.unknown,
            t.disagree,
        );
    }

    out.push_str("\n## Per case\n\n");
    out.push_str("| Case | Shape | Expected | Outcome |\n|---|---|---|---|\n");
    for (case, outcome) in rows {
        let expected = match case.expect {
            Expect::Bug(k) => format!("bug:{k:?}"),
            Expect::Safe => "safe".to_string(),
        };
        let note = match outcome {
            Outcome::Disagree(why) => format!("{} ({why})", outcome.tag()),
            _ => outcome.tag().to_string(),
        };
        let _ = writeln!(
            out,
            "| {} | {} | {expected} | {note} |",
            case.name,
            case.shape.label()
        );
    }
    out
}

fn render_json(rows: &[(&Case, Outcome)], overall: &Tally) -> String {
    let mut out = String::new();
    out.push_str("{\n");
    let _ = writeln!(
        out,
        "  \"total\": {}, \"bug_found\": {}, \"safe_proved\": {}, \"unknown\": {}, \"disagree\": {},",
        overall.total, overall.bug_found, overall.safe_proved, overall.unknown, overall.disagree,
    );
    out.push_str("  \"cases\": [\n");
    for (i, (case, outcome)) in rows.iter().enumerate() {
        let comma = if i + 1 == rows.len() { "" } else { "," };
        let _ = writeln!(
            out,
            "    {{ \"name\": \"{}\", \"shape\": \"{}\", \"outcome\": \"{}\" }}{comma}",
            case.name,
            case.shape.label(),
            outcome.tag(),
        );
    }
    out.push_str("  ]\n}\n");
    out
}

/// Builds a contract that does `n` concrete-key `SSTORE`s (`storage[i] = i`) then
/// `SLOAD`s a symbolic calldata key and reverts iff it equals `0xdead`. The
/// revert is unreachable (every stored value and the cold default are `< 0xdead`),
/// so both encodings must prove it safe — while reasoning over a store-chain of
/// depth `n`. This is the read-over-write depth knob the warm-vs-`ite` cost turns
/// on. `n <= 48` keeps the `JUMPDEST` within a `PUSH1`.
fn deep_chain_bytecode(n: u8) -> Vec<u8> {
    let mut code = Vec::new();
    for i in 0..n {
        code.extend_from_slice(&[PUSH1, i, PUSH1, i, SSTORE]); // storage[i] = i
    }
    let dest = u8::try_from(5 * usize::from(n) + 12).expect("dest fits a PUSH1");
    code.extend_from_slice(&[PUSH1, 0x00, CALLDATALOAD, SLOAD]); // loaded = storage[calldata[0:32]]
    code.extend_from_slice(&[PUSH2, 0xde, 0xad, EQ, PUSH1, dest, JUMPI, STOP]);
    code.extend_from_slice(&[JUMPDEST, PUSH1, 0x00, PUSH1, 0x00, REVERT]);
    code
}

/// One depth point of the store-chain scaling sweep.
struct ScaleRow {
    depth: u8,
    ite_tag: String,
    ite_us: u128,
    warm_tag: String,
    warm_us: u128,
    agree: bool,
}

/// Decide the deep store-chain at increasing depths under both encodings.
fn scaling_sweep() -> Vec<ScaleRow> {
    let mut out = Vec::new();
    for &depth in &[2_u8, 4, 8, 16, 32] {
        let case = Case {
            name: "deep-store-chain",
            shape: Shape::SymbolicStorage,
            expect: Expect::Safe,
            bytecode: deep_chain_bytecode(depth),
        };
        let t0 = Instant::now();
        let ite = evaluate_with(&case, MemoryEncoding::IteFold);
        let ite_us = t0.elapsed().as_micros();
        let t1 = Instant::now();
        let warm = evaluate_with(&case, MemoryEncoding::WarmArray);
        let warm_us = t1.elapsed().as_micros();
        out.push(ScaleRow {
            depth,
            agree: ite.tag() == warm.tag(),
            ite_tag: ite.tag().to_string(),
            ite_us,
            warm_tag: warm.tag().to_string(),
            warm_us,
        });
    }
    out
}

fn render_scaling(rows: &[ScaleRow]) -> String {
    let mut out = String::new();
    out.push_str("\n## Storage-depth scaling (warm-array vs `ite`-fold)\n\n");
    out.push_str(
        "A safe contract that `SSTORE`s `n` distinct concrete slots then `SLOAD`s a \
         symbolic key — the read-over-write depth knob. Both encodings prove it \
         safe at every depth (agreement = soundness); the times show how each \
         encoding's cost grows with chain depth.\n\n",
    );
    out.push_str("| Store-chain depth | `ite`-fold | t µs | warm-array | t µs | agree |\n");
    out.push_str("|---|---|---|---|---|---|\n");
    for r in rows {
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} | {} | {} |",
            r.depth,
            r.ite_tag,
            r.ite_us,
            r.warm_tag,
            r.warm_us,
            if r.agree { "yes" } else { "**NO**" },
        );
    }
    out
}

/// One multi-transaction case: a construction-known sequence outcome.
struct MultiTxRow {
    name: &'static str,
    max_txs: usize,
    expect: Expect,
    outcome: Outcome,
    txs_in_witness: usize,
}

/// Decide a couple of construction-known multi-transaction contracts: a bug that
/// is reachable only across calls (and must carry a replay-validated sequence
/// witness), and a contract safe under any number of calls.
fn multitx_sweep() -> Vec<MultiTxRow> {
    // `if storage[0]==0 { storage[0]=1 } else { revert }` — safe in 1 call, the
    // revert is reachable in 2 (storage persists). The reported finding must carry
    // a 2-tx witness (revalidated by the persistent-storage concrete replay).
    let cross_tx_bug = vec![
        PUSH1, 0x00, SLOAD, ISZERO, PUSH1, 0x0c, JUMPI, PUSH1, 0x00, PUSH1, 0x00, REVERT, JUMPDEST,
        PUSH1, 0x01, PUSH1, 0x00, SSTORE, STOP,
    ];
    // Loads a cold slot vs a sentinel — safe regardless of call count.
    let multi_safe = vec![
        PUSH1, 0x99, SLOAD, PUSH2, 0xde, 0xad, EQ, PUSH1, 0x0b, JUMPI, STOP, JUMPDEST, PUSH1, 0x00,
        PUSH1, 0x00, REVERT,
    ];
    let mut rows = Vec::new();
    for (name, max_txs, expect, bytecode) in [
        (
            "cross-tx-init-then-revert",
            2,
            Expect::Bug(FindingKind::Revert),
            cross_tx_bug,
        ),
        ("safe-under-any-tx-count", 3, Expect::Safe, multi_safe),
    ] {
        let case = Case {
            name,
            shape: Shape::SymbolicStorage,
            expect,
            bytecode,
        };
        let report = analyze(
            &case.bytecode,
            &AnalyzeConfig {
                max_txs,
                ..AnalyzeConfig::default()
            },
        );
        let txs_in_witness = report.findings.first().map_or(0, |f| f.prior_txs.len() + 1);
        rows.push(MultiTxRow {
            name,
            max_txs,
            expect,
            outcome: evaluate_report(&case, report),
            txs_in_witness,
        });
    }
    rows
}

fn render_multitx(rows: &[MultiTxRow]) -> String {
    let mut out = String::new();
    out.push_str("\n## Multi-transaction invariants (A1)\n\n");
    out.push_str(
        "Bugs reachable only across a call sequence (persistent storage between \
         txs). A reported cross-tx bug carries a replay-validated multi-tx witness \
         (the persistent-storage concrete oracle); DISAGREE stays 0.\n\n",
    );
    out.push_str("| Case | max_txs | expected | outcome | txs in witness |\n");
    out.push_str("|---|---|---|---|---|\n");
    for r in rows {
        let expected = match r.expect {
            Expect::Bug(k) => format!("bug:{k:?}"),
            Expect::Safe => "safe".to_string(),
        };
        let _ = writeln!(
            out,
            "| {} | {} | {expected} | {} | {} |",
            r.name,
            r.max_txs,
            r.outcome.tag(),
            r.txs_in_witness,
        );
    }
    out
}

/// Aggregate per-case outcomes into an overall tally and a per-shape breakdown.
fn aggregate(rows: &[(&Case, Outcome)]) -> (Tally, Vec<(Shape, Tally)>) {
    let shapes = [
        Shape::Arith,
        Shape::ConcreteMem,
        Shape::Control,
        Shape::SymbolicStorage,
        Shape::KeccakMapping,
        Shape::Environment,
    ];
    let mut overall = Tally::default();
    let mut by_shape: Vec<(Shape, Tally)> = shapes.iter().map(|s| (*s, Tally::default())).collect();
    for (case, outcome) in rows {
        overall.record(outcome);
        if let Some(entry) = by_shape.iter_mut().find(|(s, _)| *s == case.shape) {
            entry.1.record(outcome);
        }
    }
    (overall, by_shape)
}

fn main() -> ExitCode {
    let cases = corpus();
    let mut rows: Vec<(&Case, Outcome)> = Vec::new();
    for case in &cases {
        let outcome = evaluate(case);
        if let Outcome::Disagree(why) = &outcome {
            eprintln!("DISAGREE on {}: {why}", case.name);
        }
        rows.push((case, outcome));
    }

    let (mut overall, by_shape) = aggregate(&rows);

    // Warm-array vs ite-fold on the symbolic-storage rows. A cross-encoding
    // disagreement is a soundness concern and counts against the DISAGREE floor.
    let cmp = compare_encodings(&cases);
    for c in &cmp {
        if !c.agree {
            eprintln!(
                "CROSS-ENCODING DISAGREE on {}: {} vs {}",
                c.name, c.ite_tag, c.warm_tag
            );
            overall.disagree += 1;
        }
    }

    let scale = scaling_sweep();
    for r in &scale {
        if !r.agree {
            eprintln!(
                "SCALING DISAGREE at depth {}: {} vs {}",
                r.depth, r.ite_tag, r.warm_tag
            );
            overall.disagree += 1;
        }
    }

    let multitx = multitx_sweep();
    for r in &multitx {
        if let Outcome::Disagree(why) = &r.outcome {
            eprintln!("MULTI-TX DISAGREE on {}: {why}", r.name);
            overall.disagree += 1;
        }
    }

    let md = format!(
        "{}{}{}{}",
        render_markdown(&rows, &overall, &by_shape),
        render_compare(&cmp),
        render_scaling(&scale),
        render_multitx(&multitx),
    );
    let json = render_json(&rows, &overall);

    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../docs/consumer-track/evm");
    std::fs::create_dir_all(&dir).expect("create scoreboard dir");
    std::fs::write(dir.join("SCOREBOARD.md"), &md).expect("write SCOREBOARD.md");
    std::fs::write(dir.join("corpus.json"), &json).expect("write corpus.json");

    print!("{md}");

    if overall.disagree == 0 {
        eprintln!("DISAGREE = 0 over {} cases.", overall.total);
        ExitCode::SUCCESS
    } else {
        eprintln!(
            "FAIL: {} disagreement(s) — soundness floor breached.",
            overall.disagree
        );
        ExitCode::FAILURE
    }
}
