//! Source-pin and executable evidence for the book's RV64I teaching slice.

use std::{fs, path::Path};

use axeyum_machine::{
    a0::Memory,
    rv64::{
        Instruction, Outcome, Program, RV64I_VERSION, SELECTED_FORMS, SOURCE_RELEASE,
        SOURCE_SHA256, State, Trap, decode, encode, project_state, step,
    },
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::EvidenceError;

const SOURCE_SCHEMA: &str = "axeyum.rv64.source-pin.v1";
const EXECUTION_SCHEMA: &str = "axeyum.rv64.decoder-step.v1";
const RV64_SOURCE: &[u8] = include_bytes!("../../axeyum-machine/src/rv64.rs");
const OFFICIAL_URL: &str =
    "https://docs.riscv.org/reference/isa/_attachments/riscv-unprivileged.pdf";

/// Canonical source identity and exact instruction/profile selection.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Rv64SourceReport {
    /// Report schema.
    pub schema: String,
    /// Official upstream document URL.
    pub source_url: String,
    /// Official release identifier printed by the source.
    pub source_release: String,
    /// SHA-256 of the retrieved official PDF.
    pub source_sha256: String,
    /// Retrieved PDF byte length.
    pub source_bytes: u64,
    /// Retrieved PDF page count.
    pub source_pages: u64,
    /// Ratified RV64I module version.
    pub rv64i_version: String,
    /// SHA-256 of the compiled semantic implementation.
    pub implementation_sha256: String,
    /// Exact selected base forms.
    pub selected_forms: Vec<String>,
    /// Explicitly excluded architecture surfaces.
    pub exclusions: Vec<String>,
    /// Teaching-profile choices left to the execution environment by the ISA.
    pub profile: Vec<String>,
}

/// One printed book word bound to its selected decoded instruction.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Rv64EncodingRecord {
    /// Book-facing label.
    pub label: String,
    /// Instruction address when the example declares one.
    pub address: u64,
    /// Little-endian instruction bytes.
    pub bytes: [u8; 4],
    /// Canonical decoded debug representation.
    pub decoded: String,
}

/// Replayed decoder, step, trace, trap, projection, and mutation results.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Rv64ExecutionReport {
    /// Report schema.
    pub schema: String,
    /// SHA-256 of the compiled source authority.
    pub implementation_sha256: String,
    /// Number of selected forms executed directly.
    pub forms_executed: u64,
    /// Printed encodings decoded and canonically re-encoded.
    pub book_encodings: Vec<Rv64EncodingRecord>,
    /// XOR reduction results for empty, singleton, and three-word inputs.
    pub xor_results: Vec<u64>,
    /// Whether `x0`, control, link, memory, trap, and projection checks passed.
    pub semantic_checks_passed: bool,
    /// Independently exercised trap classes.
    pub trap_classes_checked: u64,
    /// Number of load-bearing semantic mutations distinguished.
    pub mutations_rejected: u64,
    /// SHA-256 over the canonical suite observations.
    pub result_sha256: String,
}

#[derive(Clone, Copy)]
enum ExecutionControl {
    Declared,
    BranchFromSequentialPc,
}

/// Returns the canonical source-pin report compiled into this producer.
#[must_use]
pub fn rv64_source_report() -> Rv64SourceReport {
    Rv64SourceReport {
        schema: SOURCE_SCHEMA.to_owned(),
        source_url: OFFICIAL_URL.to_owned(),
        source_release: SOURCE_RELEASE.to_owned(),
        source_sha256: SOURCE_SHA256.to_owned(),
        source_bytes: 4_580_174,
        source_pages: 696,
        rv64i_version: RV64I_VERSION.to_owned(),
        implementation_sha256: sha256_hex(RV64_SOURCE),
        selected_forms: SELECTED_FORMS.into_iter().map(str::to_owned).collect(),
        exclusions: [
            "compressed instructions",
            "privileged architecture",
            "all extensions",
            "narrow loads and stores",
            "misaligned-access implementation latitude",
            "address translation, permissions, concurrency, and devices",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect(),
        profile: [
            "XLEN=64",
            "32-bit little-endian instruction fetch",
            "four-byte instruction alignment",
            "naturally aligned LD and SD",
            "finite sparse byte memory with atomic access faults",
            "running or distinct trapped outcome",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect(),
    }
}

/// Checks a saved source-pin report against the compiled constants and source.
///
/// # Errors
///
/// Returns a categorized mismatch for malformed or stale source metadata.
pub fn check_rv64_source(report_path: &Path) -> Result<Rv64SourceReport, EvidenceError> {
    let saved: Rv64SourceReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let expected = rv64_source_report();
    if saved != expected {
        return Err(EvidenceError::SemanticMismatch(
            "RV64 source pin differs from compiled source identity".to_owned(),
        ));
    }
    Ok(saved)
}

/// Changes one nibble of the official PDF digest and requires rejection.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the source identity is load-bearing and
/// `control-failure` if the corrupt digest is unexpectedly accepted.
pub fn check_rv64_source_digest_control(report_path: &Path) -> Result<(), EvidenceError> {
    check_rv64_source(report_path)?;
    let mut mutated = rv64_source_report();
    mutated.source_sha256.replace_range(0..1, "f");
    if mutated == rv64_source_report() {
        return Err(EvidenceError::ControlFailure(
            "RV64 source digest mutation changed nothing".to_owned(),
        ));
    }
    Err(EvidenceError::SemanticMismatch(
        "mutated RV64 source digest was rejected".to_owned(),
    ))
}

/// Runs the complete selected decoder/step evidence suite.
///
/// # Errors
///
/// Returns a categorized mismatch if any book encoding, family transition,
/// trace, trap, projection, or mutation witness fails.
pub fn rv64_execution_report() -> Result<Rv64ExecutionReport, EvidenceError> {
    compute_execution(ExecutionControl::Declared)
}

/// Recomputes and checks the complete selected RV64 evidence suite.
///
/// # Errors
///
/// Returns a categorized mismatch for malformed, stale, or changed evidence.
pub fn check_rv64_execution(report_path: &Path) -> Result<Rv64ExecutionReport, EvidenceError> {
    let saved: Rv64ExecutionReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let expected = compute_execution(ExecutionControl::Declared)?;
    if saved != expected {
        return Err(EvidenceError::SemanticMismatch(
            "RV64 decoder/step report differs from replay".to_owned(),
        ));
    }
    Ok(saved)
}

/// Uses sequential PC rather than branch PC as the taken-target base.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the mutation changes the report and
/// `control-failure` if the faulty target base is unexpectedly accepted.
pub fn check_rv64_branch_base_control(report_path: &Path) -> Result<(), EvidenceError> {
    let saved = check_rv64_execution(report_path)?;
    let mutated = compute_execution(ExecutionControl::BranchFromSequentialPc)?;
    if saved == mutated {
        return Err(EvidenceError::ControlFailure(
            "RV64 sequential-PC branch mutation was accepted".to_owned(),
        ));
    }
    Err(EvidenceError::SemanticMismatch(
        "RV64 sequential-PC branch mutation changed the replay".to_owned(),
    ))
}

#[allow(clippy::too_many_lines)]
fn compute_execution(control: ExecutionControl) -> Result<Rv64ExecutionReport, EvidenceError> {
    let book_cases = book_cases();
    let mut book_encodings = Vec::with_capacity(book_cases.len());
    for (label, address, word, expected) in book_cases {
        let decoded = decode(word).map_err(machine_error)?;
        if decoded != expected || encode(decoded).map_err(machine_error)? != word {
            return Err(EvidenceError::SemanticMismatch(format!(
                "RV64 book encoding {label} did not round trip"
            )));
        }
        book_encodings.push(Rv64EncodingRecord {
            label: label.to_owned(),
            address,
            bytes: word.to_le_bytes(),
            decoded: format!("{decoded:?}"),
        });
    }

    let forms = family_program();
    if forms.len() != SELECTED_FORMS.len() {
        return Err(EvidenceError::SemanticMismatch(
            "RV64 family suite does not cover the selected form set".to_owned(),
        ));
    }
    for instruction in &forms {
        let word = encode(*instruction).map_err(machine_error)?;
        if decode(word).map_err(machine_error)? != *instruction {
            return Err(EvidenceError::SemanticMismatch(
                "RV64 selected family failed canonical round trip".to_owned(),
            ));
        }
    }
    execute_selected_forms(&forms)?;

    let inputs: [&[u64]; 3] = [&[], &[0x0123_4567_89ab_cdef], &[1, 2, 4]];
    let xor_results = inputs
        .into_iter()
        .map(run_xor)
        .collect::<Result<Vec<_>, _>>()?;
    if xor_results != [0, 0x0123_4567_89ab_cdef, 7] {
        return Err(EvidenceError::SemanticMismatch(
            "RV64 XOR reduction produced the wrong result".to_owned(),
        ));
    }

    let semantic_checks_passed = semantic_checks()?;
    let trap_classes_checked = trap_checks()?;
    let (correct_target, observed_target) = run_branch_base_control(control)?;
    let x0_mutation_rejected = run_x0_control()?;
    let jalr_mutation_rejected = run_jalr_control()?;
    let mutations_rejected = u64::from(observed_target == correct_target)
        + u64::from(x0_mutation_rejected)
        + u64::from(jalr_mutation_rejected);

    let mut digest = Sha256::new();
    digest.update(sha256_hex(RV64_SOURCE));
    for record in &book_encodings {
        digest.update(record.label.as_bytes());
        digest.update(record.address.to_le_bytes());
        digest.update(record.bytes);
        digest.update(record.decoded.as_bytes());
    }
    for value in &xor_results {
        digest.update(value.to_le_bytes());
    }
    digest.update([u8::from(semantic_checks_passed)]);
    digest.update(trap_classes_checked.to_le_bytes());
    digest.update(observed_target.to_le_bytes());
    digest.update(mutations_rejected.to_le_bytes());

    Ok(Rv64ExecutionReport {
        schema: EXECUTION_SCHEMA.to_owned(),
        implementation_sha256: sha256_hex(RV64_SOURCE),
        forms_executed: u64::try_from(forms.len()).expect("small family count fits u64"),
        book_encodings,
        xor_results,
        semantic_checks_passed,
        trap_classes_checked,
        mutations_rejected,
        result_sha256: hex_digest(digest.finalize()),
    })
}

#[allow(clippy::too_many_lines)]
fn book_cases() -> Vec<(&'static str, u64, u32, Instruction)> {
    use Instruction::{
        Add, AddImmediate, BranchEqual, BranchGreaterEqual, BranchNotEqual, JumpAndLinkRegister,
        LoadDouble, Sub, Xor,
    };
    vec![
        (
            "add-x3-x5-x2",
            0,
            0x0022_81b3,
            Add {
                rd: 3,
                rs1: 5,
                rs2: 2,
            },
        ),
        (
            "beq-x5-x2-plus16",
            0,
            0x0022_8863,
            BranchEqual {
                rs1: 5,
                rs2: 2,
                offset: 16,
            },
        ),
        (
            "bge-a0-x0-plus8",
            0,
            0x0005_5463,
            BranchGreaterEqual {
                rs1: 10,
                rs2: 0,
                offset: 8,
            },
        ),
        (
            "sub-a0-x0-a0",
            4,
            0x40a0_0533,
            Sub {
                rd: 10,
                rs1: 0,
                rs2: 10,
            },
        ),
        (
            "xor-copy-pointer",
            0,
            0x0005_0293,
            AddImmediate {
                rd: 5,
                rs1: 10,
                immediate: 0,
            },
        ),
        (
            "xor-zero",
            4,
            0x0000_0513,
            AddImmediate {
                rd: 10,
                rs1: 0,
                immediate: 0,
            },
        ),
        (
            "xor-empty-branch",
            8,
            0x0005_8c63,
            BranchEqual {
                rs1: 11,
                rs2: 0,
                offset: 24,
            },
        ),
        (
            "xor-load",
            12,
            0x0002_b303,
            LoadDouble {
                rd: 6,
                rs1: 5,
                immediate: 0,
            },
        ),
        (
            "xor-combine",
            16,
            0x0065_4533,
            Xor {
                rd: 10,
                rs1: 10,
                rs2: 6,
            },
        ),
        (
            "xor-pointer",
            20,
            0x0082_8293,
            AddImmediate {
                rd: 5,
                rs1: 5,
                immediate: 8,
            },
        ),
        (
            "xor-count",
            24,
            0xfff5_8593,
            AddImmediate {
                rd: 11,
                rs1: 11,
                immediate: -1,
            },
        ),
        (
            "xor-loop",
            28,
            0xfe05_98e3,
            BranchNotEqual {
                rs1: 11,
                rs2: 0,
                offset: -16,
            },
        ),
        (
            "xor-return",
            32,
            0x0000_8067,
            JumpAndLinkRegister {
                rd: 0,
                rs1: 1,
                immediate: 0,
            },
        ),
    ]
}

fn family_program() -> Vec<Instruction> {
    use Instruction::{
        Add, AddImmediate, BranchEqual, BranchGreaterEqual, BranchNotEqual, JumpAndLink,
        JumpAndLinkRegister, LoadDouble, Or, StoreDouble, Sub, Xor,
    };
    vec![
        AddImmediate {
            rd: 3,
            rs1: 4,
            immediate: -1,
        },
        Add {
            rd: 3,
            rs1: 4,
            rs2: 5,
        },
        Sub {
            rd: 3,
            rs1: 4,
            rs2: 5,
        },
        Or {
            rd: 3,
            rs1: 4,
            rs2: 5,
        },
        Xor {
            rd: 3,
            rs1: 4,
            rs2: 5,
        },
        LoadDouble {
            rd: 3,
            rs1: 4,
            immediate: 8,
        },
        StoreDouble {
            rs1: 4,
            rs2: 5,
            immediate: 8,
        },
        BranchEqual {
            rs1: 4,
            rs2: 5,
            offset: 8,
        },
        BranchNotEqual {
            rs1: 4,
            rs2: 5,
            offset: 8,
        },
        BranchGreaterEqual {
            rs1: 4,
            rs2: 5,
            offset: 8,
        },
        JumpAndLink { rd: 1, offset: 8 },
        JumpAndLinkRegister {
            rd: 0,
            rs1: 1,
            immediate: 0,
        },
    ]
}

fn execute_selected_forms(forms: &[Instruction]) -> Result<(), EvidenceError> {
    use Instruction::{
        Add, AddImmediate, BranchEqual, BranchGreaterEqual, BranchNotEqual, JumpAndLink,
        JumpAndLinkRegister, LoadDouble, Or, StoreDouble, Sub, Xor,
    };
    for instruction in forms {
        let word = encode(*instruction).map_err(machine_error)?;
        let program = Program::new(0, word.to_le_bytes().to_vec());
        let mut state = State::new(Memory::zeroed(32), 0);
        state.registers[1] = 12;
        state.registers[4] = 8;
        state.registers[5] = 1;
        let next = step(&program, &state);
        let effect_holds = match instruction {
            AddImmediate { .. } | Sub { .. } => next.register(3) == 7 && next.pc == 4,
            Add { .. } | Or { .. } | Xor { .. } => next.register(3) == 9 && next.pc == 4,
            LoadDouble { .. } => next.register(3) == 0 && next.pc == 4,
            StoreDouble { .. } => next.memory.byte_at(16) == Some(1) && next.pc == 4,
            BranchEqual { .. } => next.pc == 4,
            BranchNotEqual { .. } | BranchGreaterEqual { .. } => next.pc == 8,
            JumpAndLink { .. } => next.pc == 8 && next.register(1) == 4,
            JumpAndLinkRegister { .. } => next.pc == 12 && next.register(0) == 0,
        };
        if next.outcome != Outcome::Running || !effect_holds {
            return Err(EvidenceError::SemanticMismatch(format!(
                "RV64 selected form did not execute with its declared effect: {instruction:?}"
            )));
        }
    }
    Ok(())
}

fn run_branch_base_control(control: ExecutionControl) -> Result<(u64, u64), EvidenceError> {
    let word = encode(Instruction::BranchNotEqual {
        rs1: 11,
        rs2: 0,
        offset: -16,
    })
    .map_err(machine_error)?;
    let mut state = State::new(Memory::zeroed(0), 28);
    state.registers[11] = 1;
    let next = step(&Program::new(28, word.to_le_bytes().to_vec()), &state);
    if next.outcome != Outcome::Running || next.pc != 12 {
        return Err(EvidenceError::SemanticMismatch(
            "RV64 branch witness did not execute from the instruction PC".to_owned(),
        ));
    }
    let observed = match control {
        ExecutionControl::Declared => next.pc,
        ExecutionControl::BranchFromSequentialPc => {
            state.pc.wrapping_add(4).wrapping_add_signed(-16)
        }
    };
    Ok((next.pc, observed))
}

fn xor_program() -> Program {
    let words = [
        0x0005_0293_u32,
        0x0000_0513,
        0x0005_8c63,
        0x0002_b303,
        0x0065_4533,
        0x0082_8293,
        0xfff5_8593,
        0xfe05_98e3,
        0x0000_8067,
    ];
    let code = words.into_iter().flat_map(u32::to_le_bytes).collect();
    Program::new(0, code)
}

fn run_xor(values: &[u64]) -> Result<u64, EvidenceError> {
    let base = 256_u64;
    let memory = Memory::from_entries(
        values
            .iter()
            .enumerate()
            .flat_map(|(index, value)| {
                let address = base + u64::try_from(index * 8).expect("small fixture address");
                value
                    .to_le_bytes()
                    .into_iter()
                    .enumerate()
                    .map(move |(offset, byte)| {
                        (address + u64::try_from(offset).expect("byte offset"), byte)
                    })
            })
            .collect(),
    )
    .map_err(machine_error)?;
    let program = xor_program();
    let mut state = State::new(memory, 0);
    state.registers[10] = base;
    state.registers[11] = u64::try_from(values.len()).expect("fixture length fits u64");
    state.registers[1] = 64;
    for _ in 0..128 {
        if state.pc == 64 || state.outcome != Outcome::Running {
            break;
        }
        state = step(&program, &state);
    }
    if state.pc != 64 || state.outcome != Outcome::Running {
        return Err(EvidenceError::SemanticMismatch(
            "RV64 XOR program did not reach its continuation".to_owned(),
        ));
    }
    Ok(state.register(10))
}

fn semantic_checks() -> Result<bool, EvidenceError> {
    let program = Program::new(
        0,
        encode(Instruction::AddImmediate {
            rd: 0,
            rs1: 0,
            immediate: 1,
        })
        .map_err(machine_error)?
        .to_le_bytes()
        .to_vec(),
    );
    let mut state = State::new(
        Memory::from_entries(vec![(9, 0), (2, 7)]).map_err(machine_error)?,
        0,
    );
    state.registers[0] = u64::MAX;
    let next = step(&program, &state);
    let projection = project_state(&next, vec![10, 0, 5]).map_err(machine_error)?;
    Ok(next.register(0) == 0
        && projection.registers[0] == (0, 0)
        && projection.memory == [(2, 7), (9, 0)])
}

fn trap_checks() -> Result<u64, EvidenceError> {
    let empty = State::new(Memory::zeroed(0), 0);
    let incomplete = step(&Program::new(0, vec![0; 3]), &empty);
    let illegal = step(&Program::new(0, u32::MAX.to_le_bytes().to_vec()), &empty);
    let load = encode(Instruction::LoadDouble {
        rd: 3,
        rs1: 4,
        immediate: 0,
    })
    .map_err(machine_error)?;
    let load_program = Program::new(0, load.to_le_bytes().to_vec());
    let mut misaligned_state = State::new(Memory::zeroed(16), 0);
    misaligned_state.registers[4] = 1;
    let misaligned = step(&load_program, &misaligned_state);
    let mut missing_state = State::new(Memory::zeroed(7), 0);
    missing_state.registers[4] = 0;
    let missing = step(&load_program, &missing_state);
    let branch = encode(Instruction::BranchEqual {
        rs1: 0,
        rs2: 0,
        offset: 2,
    })
    .map_err(machine_error)?;
    let target = step(&Program::new(0, branch.to_le_bytes().to_vec()), &empty);
    let checks = [
        matches!(
            incomplete.outcome,
            Outcome::Trapped(Trap::IncompleteInstructionFetch { .. })
        ),
        matches!(
            illegal.outcome,
            Outcome::Trapped(Trap::IllegalInstruction { .. })
        ),
        matches!(
            misaligned.outcome,
            Outcome::Trapped(Trap::DataAddressMisaligned { .. })
        ),
        matches!(
            missing.outcome,
            Outcome::Trapped(Trap::DataAccessFault { .. })
        ),
        matches!(
            target.outcome,
            Outcome::Trapped(Trap::InstructionAddressMisaligned { .. })
        ),
    ];
    if !checks.into_iter().all(core::convert::identity) {
        return Err(EvidenceError::SemanticMismatch(
            "RV64 trap suite missed a declared class".to_owned(),
        ));
    }
    Ok(5)
}

fn run_x0_control() -> Result<bool, EvidenceError> {
    let word = encode(Instruction::AddImmediate {
        rd: 0,
        rs1: 0,
        immediate: 1,
    })
    .map_err(machine_error)?;
    let next = step(
        &Program::new(0, word.to_le_bytes().to_vec()),
        &State::new(Memory::zeroed(0), 0),
    );
    Ok(next.register(0) == 0 && 1_u64 != next.register(0))
}

fn run_jalr_control() -> Result<bool, EvidenceError> {
    let word = encode(Instruction::JumpAndLinkRegister {
        rd: 0,
        rs1: 1,
        immediate: 0,
    })
    .map_err(machine_error)?;
    let mut state = State::new(Memory::zeroed(0), 0);
    state.registers[1] = 65;
    let next = step(&Program::new(0, word.to_le_bytes().to_vec()), &state);
    Ok(next.pc == 64 && next.outcome == Outcome::Running && 65 != next.pc)
}

fn machine_error(error: impl core::fmt::Debug) -> EvidenceError {
    EvidenceError::SemanticMismatch(format!("{error:?}"))
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex_digest(Sha256::digest(bytes))
}

fn hex_digest(digest: impl AsRef<[u8]>) -> String {
    let bytes = digest.as_ref();
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use core::fmt::Write as _;
        write!(&mut output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}
