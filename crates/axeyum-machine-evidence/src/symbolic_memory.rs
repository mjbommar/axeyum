//! Source-derived symbolic evidence for the A0 load/store frame laws.

use std::{fs, path::Path};

use axeyum_ir::{TermArena, TermId, render};
use axeyum_machine::a0::{
    Instruction, Memory, MemoryDomain, Outcome, Program, State, Word, encode, memory_load,
    memory_store, step,
};
use axeyum_solver::{
    UnsatProof, UnsatProofOutcome, certify_array_elim_unsat, export_qf_abv_unsat_proof,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{EvidenceError, load_semantic_package};

const SCHEMA: &str = "axeyum.a0.symbolic-memory-frame.v1";
const WIDTHS: [u8; 8] = [8, 16, 24, 32, 40, 48, 56, 64];

/// Saved clausal and array-elimination evidence for one architectural width.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicMemoryWidthProof {
    /// Fixed word and address width.
    pub width: u8,
    /// SHA-256 of the exact negated frame assertion rebuilt by the checker.
    pub assertion_sha256: String,
    /// Number of select-congruence constraints in the checked elimination.
    pub array_congruence_constraints: usize,
    /// DIMACS for the deterministically array-eliminated assertion.
    pub dimacs: String,
    /// DRAT refutation of that DIMACS.
    pub drat: String,
    /// Elaborated LRAT refutation, when available.
    pub lrat: Option<String>,
}

/// Concrete counterexample to a store that commits its valid prefix on trap.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PartialStoreCounterexample {
    /// Architectural width used by the replay.
    pub width: u8,
    /// Wrapped store base.
    pub base: u64,
    /// Stored word.
    pub value: u64,
    /// Byte present before and after the correct trapped store.
    pub original_first_byte: u8,
    /// Byte left by the deliberately non-atomic implementation.
    pub mutated_first_byte: u8,
    /// Whether the correct shared implementation trapped and preserved memory.
    pub correct_store_preserved_memory: bool,
    /// Whether committing the tentative map on failure makes the negated
    /// symbolic frame theorem satisfiable.
    pub symbolic_mutation_satisfiable: bool,
}

/// Source-bound symbolic A0 memory-frame report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicMemoryReport {
    /// Report schema identifier.
    pub schema: String,
    /// SHA-256 of the canonical semantic-package JSON bytes.
    pub semantic_package_sha256: String,
    /// One checked proof for every supported A0 width.
    pub proofs: Vec<SymbolicMemoryWidthProof>,
    /// Replayed negative control for non-atomic trapped stores.
    pub partial_store_counterexample: PartialStoreCounterexample,
}

#[derive(Clone)]
struct SymbolicMemory {
    bytes: TermId,
    present: TermId,
}

struct SymbolicDomain<'a> {
    arena: &'a mut TermArena,
    width: u32,
    commit_on_failure: bool,
}

impl MemoryDomain for SymbolicDomain<'_> {
    type Memory = SymbolicMemory;
    type Address = TermId;
    type Byte = TermId;
    type Word = TermId;
    type Bit = TermId;

    fn word_bytes(&self) -> usize {
        usize::try_from(self.width / 8).expect("A0 byte count fits usize")
    }

    fn true_bit(&mut self) -> TermId {
        self.arena.bool_const(true)
    }

    fn and(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.arena
            .and(lhs, rhs)
            .expect("validity terms are Boolean")
    }

    fn address_offset(&mut self, base: TermId, offset: usize) -> TermId {
        let offset = self
            .arena
            .bv_const(
                self.width,
                u128::try_from(offset).expect("byte offset fits u128"),
            )
            .expect("A0 width is valid");
        self.arena
            .bv_add(base, offset)
            .expect("address terms have one width")
    }

    fn present(&mut self, memory: &SymbolicMemory, address: TermId) -> TermId {
        let bit = self
            .arena
            .select(memory.present, address)
            .expect("presence memory has word indices");
        let one = self
            .arena
            .bv_const(1, 1)
            .expect("one-bit constant is valid");
        self.arena.eq(bit, one).expect("presence is one bit")
    }

    fn read_byte(&mut self, memory: &SymbolicMemory, address: TermId) -> TermId {
        self.arena
            .select(memory.bytes, address)
            .expect("byte memory has word indices")
    }

    fn join_little_endian(&mut self, bytes: &[TermId]) -> TermId {
        let mut joined = *bytes.last().expect("A0 words contain at least one byte");
        for &byte in bytes[..bytes.len() - 1].iter().rev() {
            joined = self
                .arena
                .concat(joined, byte)
                .expect("all memory elements are bytes");
        }
        joined
    }

    fn split_little_endian(&mut self, word: TermId) -> Vec<TermId> {
        (0..self.word_bytes())
            .map(|offset| {
                let low = u32::try_from(offset * 8).expect("A0 bit offset fits u32");
                self.arena
                    .extract(low + 7, low, word)
                    .expect("word contains every selected byte")
            })
            .collect()
    }

    fn write_byte(
        &mut self,
        memory: SymbolicMemory,
        address: TermId,
        byte: TermId,
    ) -> SymbolicMemory {
        SymbolicMemory {
            bytes: self
                .arena
                .store(memory.bytes, address, byte)
                .expect("byte store has matching sorts"),
            present: memory.present,
        }
    }

    fn choose_memory(
        &mut self,
        valid: TermId,
        success: SymbolicMemory,
        failure: SymbolicMemory,
    ) -> SymbolicMemory {
        if self.commit_on_failure {
            return success;
        }
        SymbolicMemory {
            bytes: self
                .arena
                .ite(valid, success.bytes, failure.bytes)
                .expect("memory alternatives have one array sort"),
            present: self
                .arena
                .ite(valid, success.present, failure.present)
                .expect("presence alternatives have one array sort"),
        }
    }
}

struct Query {
    arena: TermArena,
    assertion: TermId,
}

#[allow(clippy::too_many_lines)]
fn build_query(width: u8, commit_on_failure: bool) -> Query {
    let width32 = u32::from(width);
    let mut arena = TermArena::new();
    let memory = SymbolicMemory {
        bytes: arena
            .array_var("memory_bytes", width32, 8)
            .expect("A0 byte memory has valid sorts"),
        present: arena
            .array_var("memory_present", width32, 1)
            .expect("A0 presence memory has valid sorts"),
    };
    let address = arena
        .bv_var("address", width32)
        .expect("A0 address width is valid");
    let probe = arena
        .bv_var("probe", width32)
        .expect("A0 probe width is valid");
    let value = arena
        .bv_var("value", width32)
        .expect("A0 value width is valid");

    let load = memory_load(
        &mut SymbolicDomain {
            arena: &mut arena,
            width: width32,
            commit_on_failure,
        },
        &memory,
        address,
    );
    let store = memory_store(
        &mut SymbolicDomain {
            arena: &mut arena,
            width: width32,
            commit_on_failure,
        },
        &memory,
        address,
        value,
    );

    let old_probe = arena
        .select(memory.bytes, probe)
        .expect("probe reads one old byte");
    let old_probe_present = arena
        .select(memory.present, probe)
        .expect("probe reads one old presence bit");
    let actual_probe = arena
        .select(store.memory.bytes, probe)
        .expect("probe reads one successor byte");
    let actual_probe_present = arena
        .select(store.memory.present, probe)
        .expect("probe reads one successor presence bit");

    let mut expected_valid = arena.bool_const(true);
    let mut expected_loaded_bytes = Vec::with_capacity(usize::from(width / 8));
    let mut expected_success_probe = old_probe;
    for offset in 0..usize::from(width / 8) {
        let offset_term = arena
            .bv_const(
                width32,
                u128::try_from(offset).expect("byte offset fits u128"),
            )
            .expect("A0 width is valid");
        let candidate = arena
            .bv_add(address, offset_term)
            .expect("candidate address has A0 width");
        let present = arena
            .select(memory.present, candidate)
            .expect("candidate presence read is valid");
        let one = arena.bv_const(1, 1).expect("one bit is valid");
        let present = arena.eq(present, one).expect("presence is one bit");
        expected_valid = arena
            .and(expected_valid, present)
            .expect("validity conjunction is Boolean");
        expected_loaded_bytes.push(
            arena
                .select(memory.bytes, candidate)
                .expect("candidate byte read is valid"),
        );
        let low = u32::try_from(offset * 8).expect("A0 bit offset fits u32");
        let value_byte = arena
            .extract(low + 7, low, value)
            .expect("stored word contains selected byte");
        let at_probe = arena.eq(candidate, probe).expect("addresses have one sort");
        expected_success_probe = arena
            .ite(at_probe, value_byte, expected_success_probe)
            .expect("probe alternatives are bytes");
    }
    let expected_loaded = join_bytes(&mut arena, &expected_loaded_bytes);
    let expected_probe = arena
        .ite(expected_valid, expected_success_probe, old_probe)
        .expect("atomic store alternatives are bytes");

    let equalities = [
        arena
            .eq(load.valid, expected_valid)
            .expect("validity is Boolean"),
        arena
            .eq(load.value, expected_loaded)
            .expect("loaded words have one width"),
        arena
            .eq(store.valid, expected_valid)
            .expect("validity is Boolean"),
        arena
            .eq(actual_probe, expected_probe)
            .expect("probe bytes have one sort"),
        arena
            .eq(actual_probe_present, old_probe_present)
            .expect("store preserves the finite domain"),
    ];
    let mut theorem = arena.bool_const(true);
    for equality in equalities {
        theorem = arena
            .and(theorem, equality)
            .expect("frame clauses are Boolean");
    }
    let assertion = arena.not(theorem).expect("the frame theorem is Boolean");
    Query { arena, assertion }
}

fn join_bytes(arena: &mut TermArena, bytes: &[TermId]) -> TermId {
    let mut joined = *bytes.last().expect("A0 words contain at least one byte");
    for &byte in bytes[..bytes.len() - 1].iter().rev() {
        joined = arena
            .concat(joined, byte)
            .expect("all selected memory elements are bytes");
    }
    joined
}

/// Produces array-elimination and clausal certificates for every A0 width.
///
/// # Errors
///
/// Returns a categorized error if the semantic package is stale, a width is
/// not certified, or either the array-elimination witness or clausal proof
/// fails independent replay.
pub fn symbolic_memory_report(package_path: &Path) -> Result<SymbolicMemoryReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let package_bytes = fs::read(package_path)?;
    let mut proofs = Vec::with_capacity(WIDTHS.len());
    for width in WIDTHS {
        let query = build_query(width, false);
        let certificate = certify_array_elim_unsat(&query.arena, &[query.assertion])
            .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?
            .ok_or_else(|| {
                EvidenceError::SemanticMismatch(format!(
                    "symbolic memory frame was not certified at width {width}"
                ))
            })?;
        if !certificate
            .recheck(&query.arena, &[query.assertion])
            .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?
        {
            return Err(EvidenceError::SemanticMismatch(format!(
                "width-{width} array-elimination certificate did not recheck"
            )));
        }
        let proof = certificate.bv_proof();
        proofs.push(SymbolicMemoryWidthProof {
            width,
            assertion_sha256: assertion_digest(&query.arena, query.assertion),
            array_congruence_constraints: certificate.congruence_constraint_count(),
            dimacs: proof.dimacs.clone(),
            drat: proof.drat.clone(),
            lrat: proof.lrat.clone(),
        });
    }
    Ok(SymbolicMemoryReport {
        schema: SCHEMA.to_owned(),
        semantic_package_sha256: sha256_hex(&package_bytes),
        proofs,
        partial_store_counterexample: partial_store_counterexample()?,
    })
}

/// Rebuilds the source-derived terms and checks every saved certificate.
///
/// # Errors
///
/// Returns a categorized error for stale metadata, malformed evidence, a
/// changed source assertion, or a failed array, DRAT, LRAT, or concrete replay.
pub fn check_symbolic_memory(
    package_path: &Path,
    report_path: &Path,
) -> Result<SymbolicMemoryReport, EvidenceError> {
    load_semantic_package(package_path)?;
    let report: SymbolicMemoryReport = serde_json::from_slice(&fs::read(report_path)?)?;
    if report.schema != SCHEMA
        || report.semantic_package_sha256 != sha256_hex(&fs::read(package_path)?)
        || report.proofs.len() != WIDTHS.len()
    {
        return Err(EvidenceError::SemanticMismatch(
            "symbolic memory metadata does not match the semantic package".to_owned(),
        ));
    }
    for (&width, saved) in WIDTHS.iter().zip(&report.proofs) {
        if saved.width != width {
            return Err(EvidenceError::SemanticMismatch(
                "symbolic memory widths are not canonical".to_owned(),
            ));
        }
        let query = build_query(width, false);
        if saved.assertion_sha256 != assertion_digest(&query.arena, query.assertion) {
            return Err(EvidenceError::SemanticMismatch(format!(
                "width-{width} memory assertion digest differs"
            )));
        }
        let certificate = certify_array_elim_unsat(&query.arena, &[query.assertion])
            .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?
            .ok_or_else(|| {
                EvidenceError::SemanticMismatch(format!(
                    "width-{width} memory assertion is not certified"
                ))
            })?;
        if certificate.congruence_constraint_count() != saved.array_congruence_constraints
            || !certificate
                .recheck(&query.arena, &[query.assertion])
                .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?
        {
            return Err(EvidenceError::SemanticMismatch(format!(
                "width-{width} array-elimination witness differs"
            )));
        }
        let fresh = certificate.bv_proof();
        if fresh.dimacs != saved.dimacs {
            return Err(EvidenceError::SemanticMismatch(format!(
                "width-{width} eliminated DIMACS differs"
            )));
        }
        let proof = UnsatProof {
            dimacs: saved.dimacs.clone(),
            drat: saved.drat.clone(),
            lrat: saved.lrat.clone(),
        };
        if !proof
            .recheck()
            .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?
        {
            return Err(EvidenceError::SemanticMismatch(format!(
                "width-{width} memory DRAT failed"
            )));
        }
        if proof
            .recheck_lrat()
            .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?
            != Some(true)
        {
            return Err(EvidenceError::SemanticMismatch(format!(
                "width-{width} memory certificate lacks valid LRAT"
            )));
        }
    }
    if report.partial_store_counterexample != partial_store_counterexample()? {
        return Err(EvidenceError::SemanticMismatch(
            "partial-store counterexample did not replay".to_owned(),
        ));
    }
    Ok(report)
}

/// Requires the non-atomic trapped-store mutation to change mapped memory.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the intended mutation is detected and
/// `control-failure` if the faulty partial store is unexpectedly accepted.
pub fn check_symbolic_memory_partial_store_control(
    package_path: &Path,
    report_path: &Path,
) -> Result<(), EvidenceError> {
    let report = check_symbolic_memory(package_path, report_path)?;
    let counterexample = &report.partial_store_counterexample;
    if counterexample.correct_store_preserved_memory
        && counterexample.symbolic_mutation_satisfiable
        && counterexample.original_first_byte != counterexample.mutated_first_byte
    {
        return Err(EvidenceError::SemanticMismatch(
            "non-atomic trapped store has a replayed counterexample".to_owned(),
        ));
    }
    Err(EvidenceError::ControlFailure(
        "partial trapped store was unexpectedly accepted".to_owned(),
    ))
}

struct PartialStoreDomain;

impl MemoryDomain for PartialStoreDomain {
    type Memory = Memory;
    type Address = Word;
    type Byte = u8;
    type Word = Word;
    type Bit = bool;

    fn word_bytes(&self) -> usize {
        2
    }
    fn true_bit(&mut self) -> bool {
        true
    }
    fn and(&mut self, lhs: bool, rhs: bool) -> bool {
        lhs && rhs
    }
    fn address_offset(&mut self, base: Word, offset: usize) -> Word {
        Word::new(
            16,
            base.unsigned()
                .wrapping_add(u64::try_from(offset).expect("small offset")),
        )
        .expect("value is reduced to width")
    }
    fn present(&mut self, memory: &Memory, address: Word) -> bool {
        memory.byte_at(address.unsigned()).is_some()
    }
    fn read_byte(&mut self, memory: &Memory, address: Word) -> u8 {
        memory.byte_at(address.unsigned()).unwrap_or(0)
    }
    fn join_little_endian(&mut self, bytes: &[u8]) -> Word {
        Word::from_little_endian(bytes).expect("two bytes make a word")
    }
    fn split_little_endian(&mut self, word: Word) -> Vec<u8> {
        word.little_endian_bytes()
    }
    fn write_byte(&mut self, memory: Memory, address: Word, byte: u8) -> Memory {
        let entries = memory
            .entries()
            .map(|(candidate, old)| {
                (
                    candidate,
                    if candidate == address.unsigned() {
                        byte
                    } else {
                        old
                    },
                )
            })
            .collect();
        Memory::from_entries(entries).expect("updating preserves unique addresses")
    }
    fn choose_memory(&mut self, _valid: bool, success: Memory, _failure: Memory) -> Memory {
        success
    }
}

fn partial_store_counterexample() -> Result<PartialStoreCounterexample, EvidenceError> {
    let base = Word::new(16, 65_535).map_err(machine_error)?;
    let value = Word::new(16, 0xabcd).map_err(machine_error)?;
    let original = Memory::from_entries(vec![(65_535, 0)]).map_err(machine_error)?;
    let mutated = memory_store(&mut PartialStoreDomain, &original, base, value);
    let original_first_byte = original.byte_at(65_535).expect("declared byte is present");
    let mutated_first_byte = mutated
        .memory
        .byte_at(65_535)
        .expect("mutation preserves the domain");

    let instruction = Instruction::Store {
        base: 0,
        source: 1,
        offset: 0,
    };
    let program = Program::new(
        16,
        Word::new(16, 0).map_err(machine_error)?,
        encode(instruction).map_err(machine_error)?.to_vec(),
    )
    .map_err(machine_error)?;
    let mut state = State::new(
        16,
        original.clone(),
        Word::new(16, 0).map_err(machine_error)?,
    )
    .map_err(machine_error)?;
    state.registers[0] = base;
    state.registers[1] = value;
    let correct = step(&program, &state);
    let correct_store_preserved_memory = !mutated.valid
        && matches!(correct.outcome, Outcome::Trapped(_))
        && correct.memory == original;
    let mut mutated_query = build_query(16, true);
    let symbolic_mutation_satisfiable =
        match export_qf_abv_unsat_proof(&mut mutated_query.arena, &[mutated_query.assertion])
            .map_err(|error| EvidenceError::SemanticMismatch(error.to_string()))?
        {
            UnsatProofOutcome::Satisfiable => true,
            UnsatProofOutcome::Proved(_) => {
                return Err(EvidenceError::ControlFailure(
                    "partial-store symbolic mutation was unexpectedly proved".to_owned(),
                ));
            }
            UnsatProofOutcome::Inconclusive => {
                return Err(EvidenceError::ControlFailure(
                    "partial-store symbolic mutation was inconclusive".to_owned(),
                ));
            }
        };

    // The correct public transition is already exercised by the source-bound
    // memory route. Here the shared generic orchestration is instantiated with
    // the one deliberate mutation: choose the tentative map even when invalid.
    Ok(PartialStoreCounterexample {
        width: 16,
        base: base.unsigned(),
        value: value.unsigned(),
        original_first_byte,
        mutated_first_byte,
        correct_store_preserved_memory,
        symbolic_mutation_satisfiable,
    })
}

fn machine_error(error: impl core::fmt::Debug) -> EvidenceError {
    EvidenceError::SemanticMismatch(format!("{error:?}"))
}

fn assertion_digest(arena: &TermArena, assertion: TermId) -> String {
    sha256_hex(render(arena, assertion).as_bytes())
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(64);
    for byte in digest {
        use core::fmt::Write as _;
        write!(&mut output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}
