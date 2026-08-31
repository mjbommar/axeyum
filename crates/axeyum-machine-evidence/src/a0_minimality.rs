//! Exhaustive bounded minimality for the book's tiny A0 `x + 2` language.

use std::{collections::BTreeSet, fs, path::Path};

use axeyum_machine::a0::{Instruction, Memory, Outcome, Program, State, Word, encode, step};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{EvidenceError, load_semantic_package};

const SCHEMA: &str = "axeyum.a0.scalar-minimality.v1";
const WIDTH: u8 = 8;

/// One admitted decoded instruction and its canonical A0 bytes.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CandidateRecord {
    /// Stable book-facing instruction spelling.
    pub label: String,
    /// Canonical four-byte A0 encoding.
    pub bytes: Vec<u8>,
}

/// Complete serialized candidate-language contract.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CandidateLanguageRecord {
    /// Exact six-instance alphabet in enumeration order.
    pub alphabet: Vec<CandidateRecord>,
    /// Writable registers.
    pub writable_registers: Vec<u8>,
    /// Read-only resource registers and entry values.
    pub read_only_registers: Vec<(u8, u64)>,
    /// Maximum candidate length.
    pub maximum_instructions: u8,
    /// Cost definition.
    pub cost: String,
    /// Endpoint observation.
    pub observation: String,
    /// SHA-256 of the canonical contract fields above.
    pub language_sha256: String,
}

/// Complete coverage and rejection summary for one instruction-count stratum.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MinimalityStratum {
    /// Instruction count and cost.
    pub cost: u8,
    /// Cardinality predicted by the language product.
    pub candidates_expected: u64,
    /// Syntactic candidates actually enumerated.
    pub candidates_checked: u64,
    /// Distinct complete truth tables reached.
    pub behavior_classes: u64,
    /// Candidates meeting the specification on every width-eight input.
    pub correct_candidates: u64,
    /// Least separating input for every rejected syntactic candidate.
    pub first_counterexamples: Vec<u64>,
    /// SHA-256 over candidates, truth tables, and separating inputs in order.
    pub coverage_sha256: String,
}

/// Source-bound minimality result for the six-instance A0 language.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct A0MinimalityReport {
    /// Report schema.
    pub schema: String,
    /// SHA-256 of the canonical A0 semantic-package file.
    pub semantic_package_sha256: String,
    /// Architectural word width of the exhaustive input domain.
    pub width: u8,
    /// Complete candidate-language contract.
    pub language: CandidateLanguageRecord,
    /// Mathematical specification.
    pub specification: String,
    /// Zero-, one-, and two-instruction coverage.
    pub strata: Vec<MinimalityStratum>,
    /// Selected minimum-cost witness.
    pub witness: Vec<CandidateRecord>,
    /// Complete witness truth table in input order.
    pub witness_results: Vec<u64>,
    /// Established minimum instruction count in the declared language.
    pub minimum_cost: u8,
    /// SHA-256 over the canonical language, strata, witness, and results.
    pub result_sha256: String,
}

/// Produces the exhaustive tiny-language A0 minimality report.
///
/// # Errors
///
/// Returns a categorized error for a stale semantic package, malformed
/// candidate encoding, incomplete enumeration, or missing witness.
pub fn a0_minimality_report(package_path: &Path) -> Result<A0MinimalityReport, EvidenceError> {
    load_semantic_package(package_path)?;
    compute_report(package_path, LanguageControl::Declared)
}

/// Recomputes the language product, every candidate behavior, and the witness.
///
/// # Errors
///
/// Returns `semantic-mismatch` for malformed, stale, or changed evidence.
pub fn check_a0_minimality(
    package_path: &Path,
    report_path: &Path,
) -> Result<A0MinimalityReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let saved: A0MinimalityReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let expected = compute_report(package_path, LanguageControl::Declared)?;
    if saved != expected {
        return Err(EvidenceError::SemanticMismatch(
            "A0 scalar-minimality report differs from complete replay".to_owned(),
        ));
    }
    Ok(saved)
}

/// Replaces the witness's second increment with doubling and requires failure.
///
/// # Errors
///
/// Returns `semantic-mismatch` when a concrete input rejects the faulty
/// witness and `control-failure` if it still satisfies the specification.
pub fn check_a0_minimality_witness_control(
    package_path: &Path,
    report_path: &Path,
) -> Result<(), EvidenceError> {
    check_a0_minimality(package_path, report_path)?;
    let alphabet = alphabet(LanguageControl::Declared)?;
    let mutated = vec![alphabet[3].clone(), alphabet[2].clone()];
    let results = truth_table(&mutated)?;
    if let Some(input) = first_mismatch(&results) {
        return Err(EvidenceError::SemanticMismatch(format!(
            "mutated minimum-cost witness fails at input {input}"
        )));
    }
    Err(EvidenceError::ControlFailure(
        "mutated minimum-cost witness was accepted".to_owned(),
    ))
}

/// Removes one printed alphabet member and requires the language digest and
/// stratum cardinalities to disagree with the saved report.
///
/// # Errors
///
/// Returns `semantic-mismatch` when closure is load-bearing and
/// `control-failure` if the smaller language is accepted as the printed one.
pub fn check_a0_minimality_language_omission_control(
    package_path: &Path,
    report_path: &Path,
) -> Result<(), EvidenceError> {
    let saved = check_a0_minimality(package_path, report_path)?;
    let omitted = compute_report(package_path, LanguageControl::OmitLast)?;
    if saved.language.language_sha256 != omitted.language.language_sha256
        && saved.strata[1].candidates_checked != omitted.strata[1].candidates_checked
    {
        return Err(EvidenceError::SemanticMismatch(
            "omitted alphabet member changed language identity and coverage".to_owned(),
        ));
    }
    Err(EvidenceError::ControlFailure(
        "omitted alphabet member was not load-bearing".to_owned(),
    ))
}

#[derive(Clone, Copy)]
enum LanguageControl {
    Declared,
    OmitLast,
}

fn compute_report(
    package_path: &Path,
    control: LanguageControl,
) -> Result<A0MinimalityReport, EvidenceError> {
    let package_bytes = fs::read(package_path)?;
    let alphabet = alphabet(control)?;
    let language = language_record(&alphabet)?;
    let programs = (0_u8..=2)
        .map(|cost| programs_of_cost(&alphabet, cost))
        .collect::<Vec<_>>();
    let strata = programs
        .iter()
        .enumerate()
        .map(|(cost, candidates)| {
            stratum(
                u8::try_from(cost).expect("three strata fit u8"),
                alphabet.len(),
                candidates,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    if strata[0].correct_candidates != 0 || strata[1].correct_candidates != 0 {
        return Err(EvidenceError::SemanticMismatch(
            "a cheaper candidate satisfies x+2 in the declared language".to_owned(),
        ));
    }
    let mut correct = Vec::new();
    for candidate in &programs[2] {
        let results = truth_table(candidate)?;
        if first_mismatch(&results).is_none() {
            correct.push(candidate);
        }
    }
    let witness = (*correct
        .iter()
        .find(|candidate| candidate[0].label == "add r0,r0,r1" && candidate[1] == candidate[0])
        .ok_or_else(|| {
            EvidenceError::SemanticMismatch("printed two-add witness was not enumerated".to_owned())
        })?)
    .clone();
    let witness_results = truth_table(&witness)?;
    if first_mismatch(&witness_results).is_some() {
        return Err(EvidenceError::SemanticMismatch(
            "printed witness does not implement x+2".to_owned(),
        ));
    }
    let payload = serde_json::to_vec(&(&language, &strata, &witness, &witness_results))?;
    Ok(A0MinimalityReport {
        schema: SCHEMA.to_owned(),
        semantic_package_sha256: sha256_hex(&package_bytes),
        width: WIDTH,
        language,
        specification: "r0_out = (r0_in + 2) mod 2^8; running completion".to_owned(),
        strata,
        witness,
        witness_results,
        minimum_cost: 2,
        result_sha256: sha256_hex(&payload),
    })
}

fn alphabet(control: LanguageControl) -> Result<Vec<CandidateRecord>, EvidenceError> {
    let instructions = [
        ("mov r0,r0", Instruction::Mov { rd: 0, rs1: 0 }),
        ("mov r0,r1", Instruction::Mov { rd: 0, rs1: 1 }),
        (
            "add r0,r0,r0",
            Instruction::Add {
                rd: 0,
                rs1: 0,
                rs2: 0,
            },
        ),
        (
            "add r0,r0,r1",
            Instruction::Add {
                rd: 0,
                rs1: 0,
                rs2: 1,
            },
        ),
        (
            "add r0,r1,r0",
            Instruction::Add {
                rd: 0,
                rs1: 1,
                rs2: 0,
            },
        ),
        (
            "add r0,r1,r1",
            Instruction::Add {
                rd: 0,
                rs1: 1,
                rs2: 1,
            },
        ),
    ];
    let take = match control {
        LanguageControl::Declared => instructions.len(),
        LanguageControl::OmitLast => instructions.len() - 1,
    };
    instructions[..take]
        .iter()
        .map(|(label, instruction)| {
            Ok(CandidateRecord {
                label: (*label).to_owned(),
                bytes: encode(*instruction).map_err(machine_error)?.to_vec(),
            })
        })
        .collect()
}

fn language_record(alphabet: &[CandidateRecord]) -> Result<CandidateLanguageRecord, EvidenceError> {
    #[derive(Serialize)]
    struct Contract<'a> {
        alphabet: &'a [CandidateRecord],
        writable_registers: [u8; 1],
        read_only_registers: [(u8, u64); 1],
        maximum_instructions: u8,
        cost: &'static str,
        observation: &'static str,
    }
    let contract = Contract {
        alphabet,
        writable_registers: [0],
        read_only_registers: [(1, 1)],
        maximum_instructions: 2,
        cost: "instruction-count",
        observation: "r0-and-running-completion",
    };
    Ok(CandidateLanguageRecord {
        alphabet: alphabet.to_vec(),
        writable_registers: vec![0],
        read_only_registers: vec![(1, 1)],
        maximum_instructions: 2,
        cost: contract.cost.to_owned(),
        observation: contract.observation.to_owned(),
        language_sha256: sha256_hex(&serde_json::to_vec(&contract)?),
    })
}

fn programs_of_cost(alphabet: &[CandidateRecord], cost: u8) -> Vec<Vec<CandidateRecord>> {
    match cost {
        0 => vec![Vec::new()],
        1 => alphabet
            .iter()
            .cloned()
            .map(|instruction| vec![instruction])
            .collect(),
        2 => alphabet
            .iter()
            .flat_map(|first| {
                alphabet
                    .iter()
                    .map(move |second| vec![first.clone(), second.clone()])
            })
            .collect(),
        _ => Vec::new(),
    }
}

fn stratum(
    cost: u8,
    alphabet_size: usize,
    candidates: &[Vec<CandidateRecord>],
) -> Result<MinimalityStratum, EvidenceError> {
    let expected = u64::try_from(alphabet_size.pow(u32::from(cost)))
        .expect("tiny language cardinality fits u64");
    let checked = u64::try_from(candidates.len()).expect("tiny language cardinality fits u64");
    if checked != expected {
        return Err(EvidenceError::SemanticMismatch(format!(
            "cost-{cost} enumeration visited {checked}, expected {expected}"
        )));
    }
    let mut behaviors = BTreeSet::new();
    let mut correct = 0_u64;
    let mut first_counterexamples = Vec::new();
    let mut coverage = Vec::new();
    for candidate in candidates {
        let results = truth_table(candidate)?;
        behaviors.insert(results.clone());
        let mismatch = first_mismatch(&results);
        if let Some(input) = mismatch {
            if cost < 2 {
                first_counterexamples.push(input);
            }
        } else {
            correct += 1;
        }
        coverage.extend_from_slice(&serde_json::to_vec(&(candidate, &results, mismatch))?);
    }
    Ok(MinimalityStratum {
        cost,
        candidates_expected: expected,
        candidates_checked: checked,
        behavior_classes: u64::try_from(behaviors.len()).expect("tiny class count fits u64"),
        correct_candidates: correct,
        first_counterexamples,
        coverage_sha256: sha256_hex(&coverage),
    })
}

fn truth_table(candidate: &[CandidateRecord]) -> Result<Vec<u64>, EvidenceError> {
    let code = candidate
        .iter()
        .flat_map(|instruction| instruction.bytes.iter().copied())
        .collect::<Vec<_>>();
    for instruction in candidate {
        let bytes: [u8; 4] = instruction.bytes.as_slice().try_into().map_err(|_| {
            EvidenceError::SemanticMismatch("candidate instruction is not four bytes".to_owned())
        })?;
        axeyum_machine::a0::decode(bytes).map_err(machine_error)?;
    }
    let program = Program::new(WIDTH, word(0)?, code).map_err(machine_error)?;
    (0_u64..(1_u64 << WIDTH))
        .map(|input| {
            let mut state =
                State::new(WIDTH, Memory::zeroed(0), word(0)?).map_err(machine_error)?;
            state.registers[0] = word(input)?;
            state.registers[1] = word(1)?;
            for _ in candidate {
                state = step(&program, &state);
            }
            if state.outcome != Outcome::Running || state.registers[1].unsigned() != 1 {
                return Err(EvidenceError::SemanticMismatch(
                    "candidate violated running completion or read-only r1".to_owned(),
                ));
            }
            Ok(state.registers[0].unsigned())
        })
        .collect()
}

fn first_mismatch(results: &[u64]) -> Option<u64> {
    results.iter().enumerate().find_map(|(input, result)| {
        let input = u64::try_from(input).expect("width-four input fits u64");
        (*result != (input + 2) & 0xff).then_some(input)
    })
}

fn word(value: u64) -> Result<Word, EvidenceError> {
    Word::new(WIDTH, value).map_err(machine_error)
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
