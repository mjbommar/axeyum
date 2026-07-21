//! Compiler-reflected handshake FSM refinement (ADR-0321).

use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value, eval, render};
use axeyum_solver::{
    BmcOutcome, PdrOutcome, ProofOutcome, SolverConfig, SolverError, TransitionSystem,
    bounded_model_check, prove, prove_safety_pdr,
};
use axeyum_verify::reflect::mir::checked::{MirScalarConfig, reflect_scalar_into_checked};
use sha2::{Digest, Sha256};

#[path = "fixtures/mir-fsm-target/src/lib.rs"]
mod target_fixture;

const MIR: &str = include_str!("fixtures/mir-fsm-target/artifacts/handshake.mir");
const CLOSED: u8 = 0;
const SYN_SENT: u8 = 1;
const ESTABLISHED: u8 = 2;
const BAD_ESTABLISHED: u8 = 3;
const SEND_SYN: u8 = 0;
const RECV_SYNACK: u8 = 1;
const CLOSE: u8 = 2;
const DATA: u8 = 3;
const EVENTS: [u8; 4] = [SEND_SYN, RECV_SYNACK, CLOSE, DATA];

#[derive(Clone, Copy)]
enum StepSource {
    Spec,
    Reflected,
}

#[derive(Clone, Copy)]
struct HandshakeSystem {
    source: StepSource,
    buggy: bool,
    init: u8,
    bad: u8,
}

impl HandshakeSystem {
    const fn spec(buggy: bool) -> Self {
        Self {
            source: StepSource::Spec,
            buggy,
            init: CLOSED,
            bad: BAD_ESTABLISHED,
        }
    }

    const fn reflected(buggy: bool) -> Self {
        Self {
            source: StepSource::Reflected,
            buggy,
            init: CLOSED,
            bad: BAD_ESTABLISHED,
        }
    }

    fn next(
        self,
        arena: &mut TermArena,
        state: TermId,
        event: u8,
    ) -> Result<(TermId, TermId), SolverError> {
        match self.source {
            StepSource::Spec => Ok((
                spec_next(arena, state, event, self.buggy)?,
                arena.bool_const(false),
            )),
            StepSource::Reflected => reflected_next(arena, state, event, self.buggy),
        }
    }
}

impl TransitionSystem for HandshakeSystem {
    fn state_vars(&self, arena: &mut TermArena, step: usize) -> Result<Vec<SymbolId>, SolverError> {
        Ok(vec![arena.declare(
            &format!("handshake.state@{step}"),
            Sort::BitVec(8),
        )?])
    }

    fn init(&self, arena: &mut TermArena, state: &[SymbolId]) -> Result<TermId, SolverError> {
        let current = arena.var(state[0]);
        let initial = arena.bv_const(8, u128::from(self.init))?;
        Ok(arena.eq(current, initial)?)
    }

    fn trans(
        &self,
        arena: &mut TermArena,
        pre: &[SymbolId],
        post: &[SymbolId],
    ) -> Result<TermId, SolverError> {
        let state = arena.var(pre[0]);
        let next_state = arena.var(post[0]);
        let mut relation = arena.bool_const(false);
        for event in EVENTS {
            let (next, panic) = self.next(arena, state, event)?;
            let matches = arena.eq(next_state, next)?;
            let no_panic = arena.not(panic)?;
            let transition = arena.and(no_panic, matches)?;
            relation = arena.or(relation, transition)?;
        }
        Ok(relation)
    }

    fn bad(&self, arena: &mut TermArena, state: &[SymbolId]) -> Result<TermId, SolverError> {
        let current = arena.var(state[0]);
        let bad = arena.bv_const(8, u128::from(self.bad))?;
        Ok(arena.eq(current, bad)?)
    }
}

fn spec_next(
    arena: &mut TermArena,
    state: TermId,
    event: u8,
    buggy: bool,
) -> Result<TermId, SolverError> {
    let zero = arena.bv_const(8, u128::from(CLOSED))?;
    let one = arena.bv_const(8, u128::from(SYN_SENT))?;
    let two = arena.bv_const(8, u128::from(ESTABLISHED))?;
    let three = arena.bv_const(8, u128::from(BAD_ESTABLISHED))?;
    match event {
        CLOSE => Ok(zero),
        SEND_SYN => {
            let closed = arena.eq(state, zero)?;
            Ok(arena.ite(closed, one, state)?)
        }
        RECV_SYNACK => {
            let syn_sent = arena.eq(state, one)?;
            let normal = arena.ite(syn_sent, two, state)?;
            if buggy {
                let closed = arena.eq(state, zero)?;
                Ok(arena.ite(closed, three, normal)?)
            } else {
                Ok(normal)
            }
        }
        DATA => Ok(state),
        other => Err(SolverError::Unsupported(format!(
            "event {other} is outside the frozen alphabet"
        ))),
    }
}

fn reflected_symbolic(
    arena: &mut TermArena,
    state: TermId,
    event: TermId,
    buggy: bool,
) -> Result<(TermId, TermId), SolverError> {
    let function = if buggy {
        "handshake_step_bug"
    } else {
        "handshake_step"
    };
    let reflected = reflect_scalar_into_checked(
        arena,
        &[state, event],
        MIR,
        &MirScalarConfig::new(function, 64),
    )
    .map_err(|error| SolverError::Unsupported(error.to_string()))?;
    Ok((reflected.result.value, reflected.panic))
}

fn reflected_next(
    arena: &mut TermArena,
    state: TermId,
    event: u8,
    buggy: bool,
) -> Result<(TermId, TermId), SolverError> {
    let event = arena.bv_const(8, u128::from(event))?;
    reflected_symbolic(arena, state, event, buggy)
}

fn assert_proved(arena: &mut TermArena, goal: TermId, label: &str) {
    let outcome = prove(arena, &[], goal, &SolverConfig::default())
        .unwrap_or_else(|error| panic!("{label}: solver error: {error}"));
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "{label}: expected proof, got {outcome:?}"
    );
}

fn assert_disproved(arena: &mut TermArena, goal: TermId, label: &str) {
    let outcome = prove(arena, &[], goal, &SolverConfig::default())
        .unwrap_or_else(|error| panic!("{label}: solver error: {error}"));
    assert!(
        matches!(outcome, ProofOutcome::Disproved(_)),
        "{label}: expected replayed countermodel, got {outcome:?}"
    );
}

fn concrete_spec(state: u8, event: u8, buggy: bool) -> u8 {
    match (state, event) {
        (CLOSED, RECV_SYNACK) if buggy => BAD_ESTABLISHED,
        (_, CLOSE) => CLOSED,
        (CLOSED, SEND_SYN) => SYN_SENT,
        (SYN_SENT, RECV_SYNACK) => ESTABLISHED,
        _ => state,
    }
}

fn eval_u8(arena: &TermArena, term: TermId, assignment: &Assignment) -> u8 {
    match eval(arena, term, assignment).unwrap() {
        Value::Bv { width: 8, value } => u8::try_from(value).unwrap(),
        other => panic!("expected BV8, got {other:?}"),
    }
}

fn eval_bool(arena: &TermArena, term: TermId, assignment: &Assignment) -> bool {
    match eval(arena, term, assignment).unwrap() {
        Value::Bool(value) => value,
        other => panic!("expected Bool, got {other:?}"),
    }
}

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mir-fsm-target")
}

fn sha256_bytes(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(output, "{byte:02x}").expect("writing to a String cannot fail");
    }
    output
}

fn sha256(path: &Path) -> String {
    sha256_bytes(&fs::read(path).unwrap())
}

#[test]
fn artifact_inventory_and_typed_projections_are_authenticated() {
    let root = fixture_root();
    let expected = [
        (
            "Cargo.toml",
            "00fc7c2e8bbfc6369fb25cc6203e94c390d17d481a2065be0dff25369b8b4cb5",
        ),
        (
            "Cargo.lock",
            "13f2c1533b0f32898bf372690b199a808e97c297884821c0e6373e0d2ab7b6e5",
        ),
        (
            "src/lib.rs",
            "62a01c1e6d574680d8acd81e71ae7b769c951be5c640b417dadbe2313e1ad65c",
        ),
        (
            "artifacts/handshake.mir",
            "4fd05de856b6921cd02f0b253119646e9078769cbd21a491fbc6332b2e784f8b",
        ),
        (
            "artifacts/handshake-step-summary.json",
            "aa2ee3b712d4b3026677b688e074192920303f6f411926e70827d2aeea87a855",
        ),
        (
            "artifacts/handshake-step-bug-summary.json",
            "ebb6f9621a800d8effa544b163f45f2d56fccdc8a380813db9a1204b91a492ec",
        ),
        (
            "artifacts/evidence.json",
            "7aa7e969869b8c0f41fb8a803b24f36b4fbcafb553a57138c1b9431bf3bae081",
        ),
        (
            "artifacts/provenance.json",
            "76bbebdc5a1d21a2911444d65c3e1fad8e83ff7c6d50fe210d04fd994d0db531",
        ),
    ];
    let inventory = expected
        .iter()
        .map(|(relative, hash)| format!("{hash}  {relative}"))
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    assert_eq!(
        fs::read_to_string(root.join("artifacts/SHA256SUMS")).unwrap(),
        inventory
    );
    for (relative, hash) in expected {
        assert_eq!(sha256(&root.join(relative)), hash, "{relative}");
    }
    assert_eq!(MIR.len(), 2_691);

    for (function, buggy, result_hash, panic_hash) in [
        (
            "handshake_step",
            false,
            "27bbbf185a55531ce1378c0c0b723b45a8d29b8e835e45d4536414d38ad21712",
            "1f3c24e146a378cc7d651636a0aff2df5e3ccae23ecec6244040bdbf4d1fcd69",
        ),
        (
            "handshake_step_bug",
            true,
            "4854dea71534186367e81083cbef9c337e0fca9c58b0cec5f91a16d72132715a",
            "ab60c82259de51cc9f2eae40309d804df8cc6d9c013d77ca0926238ad32a4091",
        ),
    ] {
        let mut arena = TermArena::new();
        let state = arena
            .declare(&format!("mir.build.{function}.arg0"), Sort::BitVec(8))
            .unwrap();
        let event = arena
            .declare(&format!("mir.build.{function}.arg1"), Sort::BitVec(8))
            .unwrap();
        let state = arena.var(state);
        let event = arena.var(event);
        let (result, panic) = reflected_symbolic(&mut arena, state, event, buggy).unwrap();
        assert_eq!(sha256_bytes(render(&arena, result).as_bytes()), result_hash);
        assert_eq!(sha256_bytes(render(&arena, panic).as_bytes()), panic_hash);
    }

    for relative in [
        "artifacts/handshake.mir",
        "artifacts/handshake-step-summary.json",
        "artifacts/handshake-step-bug-summary.json",
        "artifacts/evidence.json",
        "artifacts/provenance.json",
    ] {
        let bytes = fs::read(root.join(relative)).unwrap();
        let mut mutated = bytes.clone();
        mutated[0] ^= 1;
        assert_ne!(sha256_bytes(&mutated), sha256_bytes(&bytes), "{relative}");
    }
}

#[test]
fn per_event_identity_refinement_and_panic_freedom_are_universal() {
    let started = Instant::now();
    for event in EVENTS {
        let mut arena = TermArena::new();
        let state_symbol = arena.declare("state", Sort::BitVec(8)).unwrap();
        let state = arena.var(state_symbol);
        let expected = spec_next(&mut arena, state, event, false).unwrap();
        let (actual, panic) = reflected_next(&mut arena, state, event, false).unwrap();
        let exact = arena.eq(actual, expected).unwrap();
        assert_proved(&mut arena, exact, &format!("event {event} result"));
        let no_panic = arena.not(panic).unwrap();
        assert_proved(&mut arena, no_panic, &format!("event {event} panic"));
    }
    eprintln!(
        "ADR0321_EVENT_PROOFS groups=8 wall_ms={}",
        started.elapsed().as_millis()
    );
}

#[test]
fn complete_relation_refines_and_transports_pdr_safety() {
    let started = Instant::now();
    let mut arena = TermArena::new();
    let pre = [arena.declare("relation.pre", Sort::BitVec(8)).unwrap()];
    let post = [arena.declare("relation.post", Sort::BitVec(8)).unwrap()];
    let spec = HandshakeSystem::spec(false);
    let implementation = HandshakeSystem::reflected(false);
    let spec_relation = spec.trans(&mut arena, &pre, &post).unwrap();
    let implementation_relation = implementation.trans(&mut arena, &pre, &post).unwrap();
    let relation_equal = arena.eq(spec_relation, implementation_relation).unwrap();
    assert_proved(&mut arena, relation_equal, "complete transition relation");
    let spec_init = spec.init(&mut arena, &pre).unwrap();
    let implementation_init = implementation.init(&mut arena, &pre).unwrap();
    assert_eq!(spec_init, implementation_init);
    let spec_bad = spec.bad(&mut arena, &pre).unwrap();
    let implementation_bad = implementation.bad(&mut arena, &pre).unwrap();
    assert_eq!(spec_bad, implementation_bad);

    let mut spec_arena = TermArena::new();
    let spec_outcome = prove_safety_pdr(&mut spec_arena, &spec, &SolverConfig::default()).unwrap();
    assert!(matches!(spec_outcome, PdrOutcome::Safe { .. }));
    let mut implementation_arena = TermArena::new();
    let implementation_outcome = prove_safety_pdr(
        &mut implementation_arena,
        &implementation,
        &SolverConfig::default(),
    )
    .unwrap();
    assert!(matches!(implementation_outcome, PdrOutcome::Safe { .. }));
    eprintln!(
        "ADR0321_RELATION_PDR relations=1 safe_systems=2 wall_ms={}",
        started.elapsed().as_millis()
    );
}

#[test]
fn blind_injection_control_is_reachable_and_source_replayed() {
    let started = Instant::now();
    let buggy = HandshakeSystem::reflected(true);
    let mut pdr_arena = TermArena::new();
    let pdr = prove_safety_pdr(&mut pdr_arena, &buggy, &SolverConfig::default()).unwrap();
    assert!(matches!(pdr, PdrOutcome::Reachable { .. }));
    let mut bmc_arena = TermArena::new();
    let bmc = bounded_model_check(&mut bmc_arena, &buggy, 1, &SolverConfig::default()).unwrap();
    assert!(matches!(bmc, BmcOutcome::Reachable { .. }));

    let mut arena = TermArena::new();
    let state_symbol = arena.declare("witness.state", Sort::BitVec(8)).unwrap();
    let event_symbol = arena.declare("witness.event", Sort::BitVec(8)).unwrap();
    let state = arena.var(state_symbol);
    let event = arena.var(event_symbol);
    let (result, panic) = reflected_symbolic(&mut arena, state, event, true).unwrap();
    let mut assignment = Assignment::new();
    assignment.set(
        state_symbol,
        Value::Bv {
            width: 8,
            value: u128::from(CLOSED),
        },
    );
    assignment.set(
        event_symbol,
        Value::Bv {
            width: 8,
            value: u128::from(RECV_SYNACK),
        },
    );
    assert!(!eval_bool(&arena, panic, &assignment));
    assert_eq!(eval_u8(&arena, result, &assignment), BAD_ESTABLISHED);
    assert_eq!(
        target_fixture::handshake_step_bug(CLOSED, RECV_SYNACK),
        BAD_ESTABLISHED
    );
    assert_eq!(concrete_spec(CLOSED, RECV_SYNACK, true), BAD_ESTABLISHED);
    assert_ne!(
        target_fixture::handshake_step(CLOSED, RECV_SYNACK),
        BAD_ESTABLISHED
    );
    eprintln!(
        "ADR0321_BUG pdr=reachable bmc=reachable source_replay=pass wall_ms={}",
        started.elapsed().as_millis()
    );
}

#[test]
fn exhaustive_2048_rows_match_reflection_spec_and_rust() {
    let started = Instant::now();
    let mut rows = 0_u32;
    for buggy in [false, true] {
        let mut arena = TermArena::new();
        let state_symbol = arena.declare("sample.state", Sort::BitVec(8)).unwrap();
        let event_symbol = arena.declare("sample.event", Sort::BitVec(8)).unwrap();
        let state = arena.var(state_symbol);
        let event = arena.var(event_symbol);
        let (result, panic) = reflected_symbolic(&mut arena, state, event, buggy).unwrap();
        for state_value in u8::MIN..=u8::MAX {
            for event_value in EVENTS {
                let mut assignment = Assignment::new();
                assignment.set(
                    state_symbol,
                    Value::Bv {
                        width: 8,
                        value: u128::from(state_value),
                    },
                );
                assignment.set(
                    event_symbol,
                    Value::Bv {
                        width: 8,
                        value: u128::from(event_value),
                    },
                );
                assert!(!eval_bool(&arena, panic, &assignment));
                let reflected = eval_u8(&arena, result, &assignment);
                let specified = concrete_spec(state_value, event_value, buggy);
                let source = if buggy {
                    target_fixture::handshake_step_bug(state_value, event_value)
                } else {
                    target_fixture::handshake_step(state_value, event_value)
                };
                assert_eq!(reflected, specified);
                assert_eq!(reflected, source);
                rows += 1;
            }
        }
    }
    assert_eq!(rows, 2_048);
    eprintln!(
        "ADR0321_SAMPLE rows={rows} disagreements=0 errors=0 panics=0 dropped=0 wall_ms={}",
        started.elapsed().as_millis()
    );
}

#[test]
fn semantic_mutations_are_refuted_or_change_safety() {
    let mut arena = TermArena::new();
    let state_symbol = arena.declare("mutation.state", Sort::BitVec(8)).unwrap();
    let state = arena.var(state_symbol);
    let good_spec = spec_next(&mut arena, state, RECV_SYNACK, false).unwrap();
    let (blind, _) = reflected_next(&mut arena, state, RECV_SYNACK, true).unwrap();
    let blind_equal = arena.eq(blind, good_spec).unwrap();
    assert_disproved(&mut arena, blind_equal, "added blind-injection arm");

    let mut arena = TermArena::new();
    let state_symbol = arena.declare("mutation.state", Sort::BitVec(8)).unwrap();
    let state = arena.var(state_symbol);
    let buggy_spec = spec_next(&mut arena, state, RECV_SYNACK, true).unwrap();
    let (removed, _) = reflected_next(&mut arena, state, RECV_SYNACK, false).unwrap();
    let removed_equal = arena.eq(removed, buggy_spec).unwrap();
    assert_disproved(&mut arena, removed_equal, "removed blind-injection arm");

    for (label, mutated) in [
        (
            "flipped close target",
            MIR.replacen("_0 = const 0_u8;", "_0 = const 1_u8;", 1),
        ),
        (
            "deleted send transition",
            MIR.replacen("_0 = const 1_u8;", "_0 = copy _1;", 1),
        ),
        (
            "altered synack source",
            MIR.replacen(
                "_6 = Eq(copy _1, const 1_u8);",
                "_6 = Eq(copy _1, const 0_u8);",
                1,
            ),
        ),
        (
            "swapped close event",
            MIR.replacen(
                "_3 = Eq(copy _2, const 2_u8);",
                "_3 = Eq(copy _2, const 3_u8);",
                1,
            ),
        ),
    ] {
        let mut arena = TermArena::new();
        let state_symbol = arena.declare("mutation.state", Sort::BitVec(8)).unwrap();
        let event_symbol = arena.declare("mutation.event", Sort::BitVec(8)).unwrap();
        let state = arena.var(state_symbol);
        let event = arena.var(event_symbol);
        let expected = reflected_symbolic(&mut arena, state, event, false)
            .unwrap()
            .0;
        let actual = reflect_scalar_into_checked(
            &mut arena,
            &[state, event],
            &mutated,
            &MirScalarConfig::new("handshake_step", 64),
        )
        .unwrap()
        .result
        .value;
        let equal = arena.eq(actual, expected).unwrap();
        assert_disproved(&mut arena, equal, label);
    }

    let wrong_bad = HandshakeSystem {
        bad: ESTABLISHED,
        ..HandshakeSystem::reflected(false)
    };
    let mut arena = TermArena::new();
    let outcome = prove_safety_pdr(&mut arena, &wrong_bad, &SolverConfig::default()).unwrap();
    assert!(matches!(outcome, PdrOutcome::Reachable { .. }));

    let wrong_init = HandshakeSystem {
        init: BAD_ESTABLISHED,
        ..HandshakeSystem::reflected(false)
    };
    let mut arena = TermArena::new();
    let state = [arena.declare("mutated.init", Sort::BitVec(8)).unwrap()];
    let correct_init = HandshakeSystem::reflected(false)
        .init(&mut arena, &state)
        .unwrap();
    let mutated_init = wrong_init.init(&mut arena, &state).unwrap();
    let init_equal = arena.eq(correct_init, mutated_init).unwrap();
    assert_disproved(&mut arena, init_equal, "mutated init predicate");

    let mut arena = TermArena::new();
    let state = arena.declare("wide.state", Sort::BitVec(16)).unwrap();
    let event = arena.declare("wide.event", Sort::BitVec(8)).unwrap();
    let state = arena.var(state);
    let event = arena.var(event);
    assert!(
        reflect_scalar_into_checked(
            &mut arena,
            &[state, event],
            MIR,
            &MirScalarConfig::new("handshake_step", 64),
        )
        .is_err()
    );
}
