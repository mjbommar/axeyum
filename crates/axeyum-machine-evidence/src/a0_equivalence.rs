//! Executable finite A0 equivalence queries with decoded counterexample replay.

use std::{fs, path::Path};

use axeyum_machine::a0::{
    Conditions, Instruction, Memory, Outcome, Program, State, Word, decode_state, encode,
    encode_state, step,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{EvidenceError, load_semantic_package};

const SCHEMA: &str = "axeyum.a0.equivalence.v1";
const QUERY_SCHEMA: &str = "axeyum.a0.equivalence-query.v1";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Observation {
    ResultOnly,
    FullState,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Precondition {
    RunningFamily,
    ClearResultFlags,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RightProgram {
    XorR0,
    XorR1,
}

/// One canonical architectural counterexample and both replayed successors.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct A0EquivalenceCounterexample {
    /// Complete canonical initial-state bytes returned by the finite query.
    pub initial_state: Vec<u8>,
    /// Complete canonical left successor produced by replay.
    pub left_final_state: Vec<u8>,
    /// Complete canonical right successor produced by replay.
    pub right_final_state: Vec<u8>,
    /// First unequal observed component in canonical comparison order.
    pub first_difference: String,
    /// Whether decoding the saved model and rerunning both programs reproduced
    /// the same successors and observation mismatch.
    pub replayed: bool,
}

/// Result of one serialized finite equivalence query.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct A0EquivalenceQueryResult {
    /// Stable query label.
    pub label: String,
    /// SHA-256 of the canonical serialized query contract.
    pub query_sha256: String,
    /// Architectural word width.
    pub width: u8,
    /// Exact left program bytes.
    pub left_program: Vec<u8>,
    /// Exact right program bytes.
    pub right_program: Vec<u8>,
    /// Named initial-state family.
    pub precondition: String,
    /// Named endpoint observation.
    pub observation: String,
    /// Complete finite domain described by the query.
    pub domain: String,
    /// Number of admitted initial states evaluated through both programs.
    pub cases_checked: u64,
    /// `equivalent` or `counterexample`.
    pub verdict: String,
    /// Canonical witness when the mismatch query is satisfiable.
    pub counterexample: Option<A0EquivalenceCounterexample>,
}

/// Source-bound report for the first A0 equivalence and counterexample route.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct A0EquivalenceReport {
    /// Report schema.
    pub schema: String,
    /// SHA-256 of the canonical A0 semantic-package file.
    pub semantic_package_sha256: String,
    /// Result-only equivalence for the canonical clear-register pair.
    pub result_only: A0EquivalenceQueryResult,
    /// Destination-mutation query and replayed value witness.
    pub destination_mutation: A0EquivalenceQueryResult,
    /// Full-state query without a condition premise and replayed flag witness.
    pub full_state_without_premise: A0EquivalenceQueryResult,
    /// Full-state equivalence under the exact clear-result condition premise.
    pub full_state_with_premise: A0EquivalenceQueryResult,
}

#[derive(Serialize)]
struct QueryContract<'a> {
    schema: &'static str,
    label: &'a str,
    width: u8,
    left_program: &'a [u8],
    right_program: &'a [u8],
    precondition: &'a str,
    observation: &'a str,
    max_steps: u8,
    domain: &'a str,
}

/// Produces the four first-book A0 equivalence queries and replayed models.
///
/// # Errors
///
/// Returns a categorized error for a stale semantic package, invalid encoded
/// program, failed finite query, or counterexample that does not replay.
pub fn a0_equivalence_report(package_path: &Path) -> Result<A0EquivalenceReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    Ok(A0EquivalenceReport {
        schema: SCHEMA.to_owned(),
        semantic_package_sha256: sha256_hex(&package_bytes),
        result_only: run_query(
            "clear-r0-result-only",
            Observation::ResultOnly,
            Precondition::RunningFamily,
            RightProgram::XorR0,
        )?,
        destination_mutation: run_query(
            "clear-r0-destination-mutation",
            Observation::ResultOnly,
            Precondition::RunningFamily,
            RightProgram::XorR1,
        )?,
        full_state_without_premise: run_query(
            "clear-r0-full-state-without-condition-premise",
            Observation::FullState,
            Precondition::RunningFamily,
            RightProgram::XorR0,
        )?,
        full_state_with_premise: run_query(
            "clear-r0-full-state-with-condition-premise",
            Observation::FullState,
            Precondition::ClearResultFlags,
            RightProgram::XorR0,
        )?,
    })
}

/// Rebuilds every query, decodes every saved model, and replays both programs.
///
/// # Errors
///
/// Returns `semantic-mismatch` for malformed, stale, or nonreplaying evidence.
pub fn check_a0_equivalence(
    package_path: &Path,
    report_path: &Path,
) -> Result<A0EquivalenceReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let saved: A0EquivalenceReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let expected = a0_equivalence_report(package_path)?;
    if saved != expected {
        return Err(EvidenceError::SemanticMismatch(
            "A0 equivalence report differs from decoded finite-query replay".to_owned(),
        ));
    }
    for query in [
        &saved.destination_mutation,
        &saved.full_state_without_premise,
    ] {
        replay_saved_counterexample(query)?;
    }
    Ok(saved)
}

/// Requires the destination mutation to produce a replayed value witness.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the mutation is distinguished and
/// `control-failure` if it is accepted or lacks a replayed model.
pub fn check_a0_equivalence_destination_control(
    package_path: &Path,
    report_path: &Path,
) -> Result<(), EvidenceError> {
    let report = check_a0_equivalence(package_path, report_path)?;
    let Some(counterexample) = report.destination_mutation.counterexample else {
        return Err(EvidenceError::ControlFailure(
            "destination mutation returned no counterexample".to_owned(),
        ));
    };
    if report.destination_mutation.verdict == "counterexample"
        && counterexample.replayed
        && counterexample.first_difference == "r0"
    {
        return Err(EvidenceError::SemanticMismatch(
            "mutated destination has a decoded and replayed r0 witness".to_owned(),
        ));
    }
    Err(EvidenceError::ControlFailure(
        "destination mutation did not produce the declared witness".to_owned(),
    ))
}

/// Corrupts one byte of a saved satisfying model and requires replay rejection.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the corrupted model no longer reproduces
/// the saved successors, and `control-failure` if the corruption is accepted.
pub fn check_a0_equivalence_corrupt_model_control(
    package_path: &Path,
    report_path: &Path,
) -> Result<(), EvidenceError> {
    let report = check_a0_equivalence(package_path, report_path)?;
    let mut query = report.destination_mutation;
    let counterexample = query.counterexample.as_mut().ok_or_else(|| {
        EvidenceError::ControlFailure("destination mutation lacks a saved model".to_owned())
    })?;
    let register_offset = 8_usize;
    let byte = counterexample
        .initial_state
        .get_mut(register_offset)
        .ok_or_else(|| EvidenceError::ControlFailure("saved state is too short".to_owned()))?;
    *byte ^= 1;
    match replay_saved_counterexample(&query) {
        Err(EvidenceError::SemanticMismatch(_)) => Err(EvidenceError::SemanticMismatch(
            "corrupted decoded model was rejected by concrete replay".to_owned(),
        )),
        Err(error) => Err(EvidenceError::ControlFailure(format!(
            "corrupt-model control failed for the wrong reason: {error}"
        ))),
        Ok(()) => Err(EvidenceError::ControlFailure(
            "corrupted decoded model reproduced the saved trace".to_owned(),
        )),
    }
}

fn run_query(
    label: &str,
    observation: Observation,
    precondition: Precondition,
    right: RightProgram,
) -> Result<A0EquivalenceQueryResult, EvidenceError> {
    let left_instruction = Instruction::MovImmediate {
        rd: 0,
        immediate: 0,
    };
    let right_instruction = Instruction::Xor {
        rd: match right {
            RightProgram::XorR0 => 0,
            RightProgram::XorR1 => 1,
        },
        rs1: 0,
        rs2: 0,
    };
    let left_program = encode(left_instruction).map_err(machine_error)?.to_vec();
    let right_program = encode(right_instruction).map_err(machine_error)?.to_vec();
    let precondition_name = match precondition {
        Precondition::RunningFamily => "running-width8-r0-and-flags-free",
        Precondition::ClearResultFlags => "running-width8-z1-n0-c0-v0-r0-free",
    };
    let observation_name = match observation {
        Observation::ResultOnly => "r0-pc-outcome",
        Observation::FullState => "complete-state",
    };
    let domain = match precondition {
        Precondition::RunningFamily => {
            "all 256 r0 words and all 16 Z/N/C/V assignments; r1..r7 zero; empty memory; pc=0; running"
        }
        Precondition::ClearResultFlags => {
            "all 256 r0 words; Z=true and N=C=V=false; r1..r7 zero; empty memory; pc=0; running"
        }
    };
    let contract = QueryContract {
        schema: QUERY_SCHEMA,
        label,
        width: 8,
        left_program: &left_program,
        right_program: &right_program,
        precondition: precondition_name,
        observation: observation_name,
        max_steps: 1,
        domain,
    };
    let query_sha256 = sha256_hex(&serde_json::to_vec(&contract)?);
    let left = program(&left_program)?;
    let right_program_value = program(&right_program)?;
    let mut cases_checked = 0_u64;
    let mut witnesses = Vec::new();
    for value in 0_u64..=u64::from(u8::MAX) {
        for conditions in admitted_conditions(precondition) {
            let initial = initial_state(value, conditions)?;
            let left_final = step(&left, &initial);
            let right_final = step(&right_program_value, &initial);
            cases_checked += 1;
            if let Some(first_difference) = first_difference(observation, &left_final, &right_final)
            {
                witnesses.push(counterexample(
                    &initial,
                    &left_final,
                    &right_final,
                    first_difference,
                )?);
            }
        }
    }
    let counterexample = minimize_witness(witnesses);
    let result = A0EquivalenceQueryResult {
        label: label.to_owned(),
        query_sha256,
        width: 8,
        left_program,
        right_program,
        precondition: precondition_name.to_owned(),
        observation: observation_name.to_owned(),
        domain: domain.to_owned(),
        cases_checked,
        verdict: if counterexample.is_some() {
            "counterexample"
        } else {
            "equivalent"
        }
        .to_owned(),
        counterexample,
    };
    if result.counterexample.is_some() {
        replay_saved_counterexample(&result)?;
    }
    Ok(result)
}

fn admitted_conditions(precondition: Precondition) -> Vec<Conditions> {
    match precondition {
        Precondition::ClearResultFlags => vec![Conditions {
            zero: true,
            negative: false,
            carry: false,
            overflow: false,
        }],
        Precondition::RunningFamily => (0_u8..16)
            .map(|bits| Conditions {
                zero: bits & 1 != 0,
                negative: bits & 2 != 0,
                carry: bits & 4 != 0,
                overflow: bits & 8 != 0,
            })
            .collect(),
    }
}

fn initial_state(value: u64, conditions: Conditions) -> Result<State, EvidenceError> {
    let mut state = State::new(8, Memory::zeroed(0), word(0)?).map_err(machine_error)?;
    state.registers[0] = word(value)?;
    state.conditions = conditions;
    Ok(state)
}

fn program(bytes: &[u8]) -> Result<Program, EvidenceError> {
    let instruction_bytes: [u8; 4] = bytes.try_into().map_err(|_| {
        EvidenceError::SemanticMismatch("equivalence program is not one A0 instruction".to_owned())
    })?;
    axeyum_machine::a0::decode(instruction_bytes).map_err(machine_error)?;
    Program::new(8, word(0)?, bytes.to_vec()).map_err(machine_error)
}

fn first_difference(observation: Observation, left: &State, right: &State) -> Option<String> {
    if left.registers[0] != right.registers[0] {
        return Some("r0".to_owned());
    }
    if left.pc != right.pc {
        return Some("pc".to_owned());
    }
    if left.outcome != right.outcome {
        return Some("outcome".to_owned());
    }
    if observation == Observation::ResultOnly {
        return None;
    }
    for index in 1..left.registers.len() {
        if left.registers[index] != right.registers[index] {
            return Some(format!("r{index}"));
        }
    }
    for (name, lhs, rhs) in [
        ("zero", left.conditions.zero, right.conditions.zero),
        (
            "negative",
            left.conditions.negative,
            right.conditions.negative,
        ),
        ("carry", left.conditions.carry, right.conditions.carry),
        (
            "overflow",
            left.conditions.overflow,
            right.conditions.overflow,
        ),
    ] {
        if lhs != rhs {
            return Some(name.to_owned());
        }
    }
    if left.memory != right.memory {
        return Some("memory".to_owned());
    }
    None
}

fn counterexample(
    initial: &State,
    left_final: &State,
    right_final: &State,
    first_difference: String,
) -> Result<A0EquivalenceCounterexample, EvidenceError> {
    Ok(A0EquivalenceCounterexample {
        initial_state: encode_state(initial).map_err(machine_error)?,
        left_final_state: encode_state(left_final).map_err(machine_error)?,
        right_final_state: encode_state(right_final).map_err(machine_error)?,
        first_difference,
        replayed: true,
    })
}

fn minimize_witness(
    mut witnesses: Vec<A0EquivalenceCounterexample>,
) -> Option<A0EquivalenceCounterexample> {
    witnesses.sort_by_key(|witness| {
        let state = decode_state(&witness.initial_state).expect("generated state decodes");
        let flag_count = [
            state.conditions.zero,
            state.conditions.negative,
            state.conditions.carry,
            state.conditions.overflow,
        ]
        .into_iter()
        .filter(|value| *value)
        .count();
        (
            witness.first_difference != "carry",
            flag_count,
            state.registers[0].unsigned(),
        )
    });
    witnesses.into_iter().next()
}

fn replay_saved_counterexample(query: &A0EquivalenceQueryResult) -> Result<(), EvidenceError> {
    let saved = query.counterexample.as_ref().ok_or_else(|| {
        EvidenceError::SemanticMismatch("counterexample verdict lacks a saved model".to_owned())
    })?;
    let initial = decode_state(&saved.initial_state).map_err(machine_error)?;
    if initial.outcome != Outcome::Running || initial.pc != word(0)? {
        return Err(EvidenceError::SemanticMismatch(
            "decoded counterexample violates the query entry contract".to_owned(),
        ));
    }
    let left_final = step(&program(&query.left_program)?, &initial);
    let right_final = step(&program(&query.right_program)?, &initial);
    if encode_state(&left_final).map_err(machine_error)? != saved.left_final_state
        || encode_state(&right_final).map_err(machine_error)? != saved.right_final_state
    {
        return Err(EvidenceError::SemanticMismatch(
            "decoded counterexample does not reproduce the saved successors".to_owned(),
        ));
    }
    let observation = if query.observation == "complete-state" {
        Observation::FullState
    } else {
        Observation::ResultOnly
    };
    if first_difference(observation, &left_final, &right_final).as_deref()
        != Some(saved.first_difference.as_str())
    {
        return Err(EvidenceError::SemanticMismatch(
            "decoded counterexample does not reproduce the saved observation mismatch".to_owned(),
        ));
    }
    Ok(())
}

fn word(value: u64) -> Result<Word, EvidenceError> {
    Word::new(8, value).map_err(machine_error)
}

fn machine_error(error: impl core::fmt::Debug) -> EvidenceError {
    EvidenceError::SemanticMismatch(format!("{error:?}"))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(digest.len() * 2);
    for byte in digest {
        use core::fmt::Write as _;
        write!(&mut output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}
