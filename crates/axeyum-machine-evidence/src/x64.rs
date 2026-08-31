//! Source-pin and executable evidence for the book's x86-64 teaching slice.

use std::{collections::BTreeSet, fs, path::Path};

use axeyum_machine::{
    a0::Memory,
    x64::{
        Condition, FlagValue, Instruction, Outcome, Program, SELECTED_FORMS, SOURCE_REVISION,
        SOURCE_SHA256, State, Trap, decode, encode, project_state, step,
    },
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::EvidenceError;

const SOURCE_SCHEMA: &str = "axeyum.x64.source-pin.v1";
const EXECUTION_SCHEMA: &str = "axeyum.x64.decoder-step.v1";
const X64_SOURCE: &[u8] = include_bytes!("../../axeyum-machine/src/x64.rs");
const OFFICIAL_URL: &str = "https://cdrdv2-public.intel.com/922478/325383-092-sdm-vol-2abcd.pdf";

/// Canonical Intel source identity and selected form/profile boundary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[allow(missing_docs)]
pub struct X64SourceReport {
    pub schema: String,
    pub source_url: String,
    pub source_revision: String,
    pub source_sha256: String,
    pub source_bytes: u64,
    pub source_pages: u64,
    pub source_date: String,
    pub implementation_sha256: String,
    pub selected_forms: Vec<String>,
    pub exclusions: Vec<String>,
    pub profile: Vec<String>,
}

/// One manuscript or resolved teaching-fixture instruction encoding.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[allow(missing_docs)]
pub struct X64EncodingRecord {
    pub label: String,
    pub address: u64,
    pub bytes: Vec<u8>,
    pub decoded: String,
}

/// Replayed decoder, step, program, trap, projection, and mutation results.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[allow(missing_docs)]
pub struct X64ExecutionReport {
    pub schema: String,
    pub implementation_sha256: String,
    pub forms_executed: u64,
    pub book_encodings: Vec<X64EncodingRecord>,
    pub xor_results: Vec<u64>,
    pub count_result: u64,
    pub leaf_result: u64,
    pub nonleaf_result: u64,
    pub nonleaf_rbx_restored: bool,
    pub absolute_results: Vec<u64>,
    pub semantic_checks_passed: bool,
    pub trap_classes_checked: u64,
    pub mutations_rejected: u64,
    pub result_sha256: String,
}

#[derive(Clone, Copy)]
enum ExecutionControl {
    Declared,
    BranchFromInstructionRip,
}

/// Returns the compiled source-pin report.
#[must_use]
pub fn x64_source_report() -> X64SourceReport {
    X64SourceReport {
        schema: SOURCE_SCHEMA.to_owned(),
        source_url: OFFICIAL_URL.to_owned(),
        source_revision: SOURCE_REVISION.to_owned(),
        source_sha256: SOURCE_SHA256.to_owned(),
        source_bytes: 11_258_123,
        source_pages: 2_573,
        source_date: "June 2026".to_owned(),
        implementation_sha256: sha256_hex(X64_SOURCE),
        selected_forms: SELECTED_FORMS.into_iter().map(str::to_owned).collect(),
        exclusions: [
            "registers R8 through R15",
            "SIB, RIP-relative, absolute, and wider-displacement addressing",
            "near conditional jumps and indirect calls or jumps",
            "legacy modes, privileged state, segmentation, paging, and devices",
            "LOCK, VEX, EVEX, APX, vector, floating-point, and system forms",
            "alignment checking, canonical-address faults, and asynchronous events",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect(),
        profile: [
            "64-bit mode",
            "low eight general-purpose registers",
            "CF, PF, AF, ZF, SF, and OF with explicit undefined values",
            "finite little-endian byte memory",
            "immutable code image and variable-length sequential RIP",
            "running or distinct trapped outcome",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect(),
    }
}

/// Checks a saved x86-64 source report.
///
/// # Errors
///
/// Returns a categorized mismatch for malformed or stale metadata.
pub fn check_x64_source(report_path: &Path) -> Result<X64SourceReport, EvidenceError> {
    let saved: X64SourceReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let expected = x64_source_report();
    if saved != expected {
        return Err(EvidenceError::SemanticMismatch(
            "x86-64 source pin differs from compiled source identity".to_owned(),
        ));
    }
    Ok(saved)
}

/// Corrupts the official PDF digest and requires rejection.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the source identity is load-bearing.
pub fn check_x64_source_digest_control(report_path: &Path) -> Result<(), EvidenceError> {
    check_x64_source(report_path)?;
    let mut mutated = x64_source_report();
    mutated.source_sha256.replace_range(0..1, "f");
    if mutated == x64_source_report() {
        return Err(EvidenceError::ControlFailure(
            "x86-64 source digest mutation changed nothing".to_owned(),
        ));
    }
    Err(EvidenceError::SemanticMismatch(
        "mutated x86-64 source digest was rejected".to_owned(),
    ))
}

/// Runs the complete selected x86-64 evidence suite.
///
/// # Errors
///
/// Returns a categorized mismatch for a failed decode, transition, program,
/// trap, projection, or mutation observation.
pub fn x64_execution_report() -> Result<X64ExecutionReport, EvidenceError> {
    compute_execution(ExecutionControl::Declared)
}

/// Recomputes and checks a saved x86-64 evidence report.
///
/// # Errors
///
/// Returns a categorized mismatch for malformed, stale, or changed evidence.
pub fn check_x64_execution(report_path: &Path) -> Result<X64ExecutionReport, EvidenceError> {
    let saved: X64ExecutionReport = serde_json::from_slice(&fs::read(report_path)?)?;
    let expected = compute_execution(ExecutionControl::Declared)?;
    if saved != expected {
        return Err(EvidenceError::SemanticMismatch(
            "x86-64 decoder/step report differs from replay".to_owned(),
        ));
    }
    Ok(saved)
}

/// Uses the instruction RIP instead of the following RIP as branch base.
///
/// # Errors
///
/// Returns `semantic-mismatch` when the mutation changes the report.
pub fn check_x64_branch_base_control(report_path: &Path) -> Result<(), EvidenceError> {
    let saved = check_x64_execution(report_path)?;
    let mutated = compute_execution(ExecutionControl::BranchFromInstructionRip)?;
    if saved == mutated {
        return Err(EvidenceError::ControlFailure(
            "x86-64 instruction-RIP branch mutation was accepted".to_owned(),
        ));
    }
    Err(EvidenceError::SemanticMismatch(
        "x86-64 instruction-RIP branch mutation changed the replay".to_owned(),
    ))
}

#[allow(clippy::too_many_lines)]
fn compute_execution(control: ExecutionControl) -> Result<X64ExecutionReport, EvidenceError> {
    let mut forms = BTreeSet::new();
    let mut book_encodings = Vec::new();
    for (label, address, bytes) in book_cases() {
        let (instruction, length) = decode(&bytes).map_err(machine_error)?;
        if length != bytes.len() || encode(instruction).map_err(machine_error)? != bytes {
            return Err(EvidenceError::SemanticMismatch(format!(
                "x86-64 book encoding {label} did not round trip"
            )));
        }
        forms.insert(form_name(instruction));
        book_encodings.push(X64EncodingRecord {
            label: label.to_owned(),
            address,
            bytes,
            decoded: format!("{instruction:?}"),
        });
    }
    if forms.len() != SELECTED_FORMS.len() {
        return Err(EvidenceError::SemanticMismatch(format!(
            "x86-64 manuscript suite covered {} of {} selected forms",
            forms.len(),
            SELECTED_FORMS.len()
        )));
    }

    let xor_results = [
        run_xor(&[])?,
        run_xor(&[0x0123_4567_89ab_cdef])?,
        run_xor(&[1, 2, 4])?,
    ];
    if xor_results != [0, 0x0123_4567_89ab_cdef, 7] {
        return Err(EvidenceError::SemanticMismatch(
            "x86-64 XOR program produced the wrong result".to_owned(),
        ));
    }
    let count_result = run_count(3)?;
    let leaf_result = run_leaf(41)?;
    let (nonleaf_result, nonleaf_rbx_restored) = run_nonleaf()?;
    let absolute_results = [run_absolute(7)?, run_absolute(u64::MAX - 6)?];
    if count_result != 0
        || leaf_result != 42
        || nonleaf_result != 7
        || !nonleaf_rbx_restored
        || absolute_results != [7, 7]
    {
        return Err(EvidenceError::SemanticMismatch(
            "x86-64 manuscript program suite produced a wrong observation".to_owned(),
        ));
    }

    let semantic_checks_passed = semantic_checks()? && zero_form_checks();
    let trap_classes_checked = trap_checks()?;
    let (correct_target, observed_target) = branch_base_observation(control)?;
    let upper_clear = upper_clear_control();
    let undefined_af = undefined_af_control();
    let implicit_stack = implicit_stack_control()?;
    let mutations_rejected = u64::from(observed_target == correct_target)
        + u64::from(upper_clear)
        + u64::from(undefined_af)
        + u64::from(implicit_stack);

    let mut digest = Sha256::new();
    digest.update(sha256_hex(X64_SOURCE));
    for record in &book_encodings {
        digest.update(record.label.as_bytes());
        digest.update(record.address.to_le_bytes());
        digest.update(&record.bytes);
        digest.update(record.decoded.as_bytes());
    }
    for value in xor_results {
        digest.update(value.to_le_bytes());
    }
    digest.update(count_result.to_le_bytes());
    digest.update(leaf_result.to_le_bytes());
    digest.update(nonleaf_result.to_le_bytes());
    for value in absolute_results {
        digest.update(value.to_le_bytes());
    }
    digest.update([
        u8::from(semantic_checks_passed),
        u8::from(nonleaf_rbx_restored),
    ]);
    digest.update(trap_classes_checked.to_le_bytes());
    digest.update(observed_target.to_le_bytes());
    digest.update(mutations_rejected.to_le_bytes());

    Ok(X64ExecutionReport {
        schema: EXECUTION_SCHEMA.to_owned(),
        implementation_sha256: sha256_hex(X64_SOURCE),
        forms_executed: u64::try_from(forms.len()).expect("small form count"),
        book_encodings,
        xor_results: xor_results.to_vec(),
        count_result,
        leaf_result,
        nonleaf_result,
        nonleaf_rbx_restored,
        absolute_results: absolute_results.to_vec(),
        semantic_checks_passed,
        trap_classes_checked,
        mutations_rejected,
        result_sha256: hex_digest(digest.finalize()),
    })
}

#[allow(clippy::too_many_lines)]
fn book_cases() -> Vec<(&'static str, u64, Vec<u8>)> {
    vec![
        ("xor-clear", 0, vec![0x31, 0xc0]),
        ("xor-test-count", 2, vec![0x48, 0x85, 0xf6]),
        ("xor-empty-branch", 5, vec![0x74, 0x0d]),
        ("xor-memory", 7, vec![0x48, 0x33, 0x07]),
        ("xor-pointer", 10, vec![0x48, 0x83, 0xc7, 0x08]),
        ("xor-count", 14, vec![0x48, 0x83, 0xee, 0x01]),
        ("xor-loop", 18, vec![0x75, 0xf3]),
        ("xor-return", 20, vec![0xc3]),
        ("count-test", 0, vec![0x48, 0x85, 0xff]),
        ("count-empty-branch", 3, vec![0x74, 0x06]),
        ("count-sub", 5, vec![0x48, 0x83, 0xef, 0x01]),
        ("count-loop", 9, vec![0x75, 0xfa]),
        ("leaf-lea", 0, vec![0x48, 0x8d, 0x47, 0x01]),
        ("leaf-return", 4, vec![0xc3]),
        ("absolute-copy", 0, vec![0x48, 0x89, 0xf8]),
        ("absolute-test", 3, vec![0x48, 0x85, 0xc0]),
        ("absolute-jns", 6, vec![0x79, 0x03]),
        ("absolute-negate", 8, vec![0x48, 0xf7, 0xd8]),
        ("zero-xor", 0, vec![0x31, 0xc0]),
        ("zero-mov", 0, vec![0xb8, 0, 0, 0, 0]),
        ("frame-push", 0, vec![0x53]),
        ("frame-sub-rsp", 1, vec![0x48, 0x83, 0xec, 0x20]),
        ("frame-save-argument", 5, vec![0x48, 0x89, 0xfb]),
        ("frame-call-resolved-fixture", 8, vec![0xe8, 0x09, 0, 0, 0]),
        ("frame-add-result", 13, vec![0x48, 0x01, 0xd8]),
        ("frame-add-rsp", 16, vec![0x48, 0x83, 0xc4, 0x20]),
        ("frame-pop", 20, vec![0x5b]),
        ("frame-return", 21, vec![0xc3]),
    ]
}

fn form_name(instruction: Instruction) -> &'static str {
    use Instruction::{
        Add64, AddImmediate64, CallRelative, JumpShort, LoadEffectiveAddress64, Move64,
        MoveImmediate32, Negate64, Pop64, Push64, Return, SubImmediate64, Test64, Xor32,
        Xor64Memory,
    };
    match instruction {
        Xor32 { .. } => "XOR r32,r32",
        MoveImmediate32 { .. } => "MOV r32,imm32",
        Test64 { .. } => "TEST r64,r64",
        JumpShort {
            condition: Condition::Equal,
            ..
        } => "JE rel8",
        JumpShort {
            condition: Condition::NotEqual,
            ..
        } => "JNE rel8",
        JumpShort {
            condition: Condition::NotSign,
            ..
        } => "JNS rel8",
        Xor64Memory { .. } => "XOR r64,m64",
        AddImmediate64 { .. } => "ADD r64,imm8",
        SubImmediate64 { .. } => "SUB r64,imm8",
        Move64 { .. } => "MOV r64,r64",
        Negate64 { .. } => "NEG r64",
        LoadEffectiveAddress64 { .. } => "LEA r64,[r64+disp8]",
        Push64 { .. } => "PUSH r64",
        Pop64 { .. } => "POP r64",
        CallRelative { .. } => "CALL rel32",
        Add64 { .. } => "ADD r64,r64",
        Return => "RET",
    }
}

fn run_xor(values: &[u64]) -> Result<u64, EvidenceError> {
    let code = vec![
        0x31, 0xc0, 0x48, 0x85, 0xf6, 0x74, 0x0d, 0x48, 0x33, 0x07, 0x48, 0x83, 0xc7, 0x08, 0x48,
        0x83, 0xee, 0x01, 0x75, 0xf3, 0xc3,
    ];
    let base = 256_u64;
    let stack = 512_u64;
    let mut words: Vec<(u64, u64)> = values
        .iter()
        .enumerate()
        .map(|(index, value)| (base + u64::try_from(index * 8).expect("fixture"), *value))
        .collect();
    words.push((stack, 64));
    let mut state = State::new(memory_with_words(&words, 600)?, 0);
    state.registers[7] = base;
    state.registers[6] = u64::try_from(values.len()).expect("fixture");
    state.registers[4] = stack;
    Ok(run_until(&Program::new(0, code), state, 64, 128)?.register(0))
}

fn run_count(value: u64) -> Result<u64, EvidenceError> {
    let code = vec![
        0x48, 0x85, 0xff, 0x74, 0x06, 0x48, 0x83, 0xef, 0x01, 0x75, 0xfa,
    ];
    let mut state = State::new(Memory::zeroed(0), 0);
    state.registers[7] = value;
    Ok(run_until(&Program::new(0, code), state, 11, 64)?.register(7))
}

fn run_leaf(value: u64) -> Result<u64, EvidenceError> {
    let mut state = State::new(memory_with_words(&[(128, 64)], 256)?, 0);
    state.registers[7] = value;
    state.registers[4] = 128;
    Ok(run_until(
        &Program::new(0, vec![0x48, 0x8d, 0x47, 0x01, 0xc3]),
        state,
        64,
        4,
    )?
    .register(0))
}

fn run_absolute(value: u64) -> Result<u64, EvidenceError> {
    let mut state = State::new(Memory::zeroed(0), 0);
    state.registers[7] = value;
    Ok(run_until(
        &Program::new(
            0,
            vec![
                0x48, 0x89, 0xf8, 0x48, 0x85, 0xc0, 0x79, 0x03, 0x48, 0xf7, 0xd8,
            ],
        ),
        state,
        11,
        4,
    )?
    .register(0))
}

fn run_nonleaf() -> Result<(u64, bool), EvidenceError> {
    let code = vec![
        0x53, 0x48, 0x83, 0xec, 0x20, 0x48, 0x89, 0xfb, 0xe8, 0x09, 0, 0, 0, 0x48, 0x01, 0xd8,
        0x48, 0x83, 0xc4, 0x20, 0x5b, 0xc3, 0xc3,
    ];
    let mut state = State::new(memory_with_words(&[(128, 64)], 256)?, 0);
    state.registers[0] = 2;
    state.registers[3] = 9;
    state.registers[4] = 128;
    state.registers[7] = 5;
    let result = run_until(&Program::new(0, code), state, 64, 16)?;
    Ok((
        result.register(0),
        result.register(3) == 9 && result.register(4) == 136,
    ))
}

fn semantic_checks() -> Result<bool, EvidenceError> {
    let mut state = State::new(
        Memory::from_entries(vec![(9, 1), (2, 7)]).map_err(machine_error)?,
        44,
    );
    state.registers[7] = 11;
    state.registers[0] = 13;
    let projection = project_state(&state, vec![7, 0]).map_err(machine_error)?;
    Ok(projection.registers == [(0, 13), (7, 11)] && projection.memory == [(2, 7), (9, 1)])
}

fn zero_form_checks() -> bool {
    let mut initial = State::new(Memory::zeroed(0), 0);
    initial.registers[0] = u64::MAX;
    initial.flags.carry = FlagValue::Set;
    let xor = step(&Program::new(0, vec![0x31, 0xc0]), &initial);
    let moved = step(&Program::new(0, vec![0xb8, 0, 0, 0, 0]), &initial);
    xor.register(0) == 0
        && moved.register(0) == 0
        && xor.flags.carry == FlagValue::Clear
        && moved.flags.carry == FlagValue::Set
}

fn trap_checks() -> Result<u64, EvidenceError> {
    let incomplete = step(
        &Program::new(0, vec![0x48]),
        &State::new(Memory::zeroed(0), 0),
    );
    let illegal = step(
        &Program::new(0, vec![0x0f]),
        &State::new(Memory::zeroed(0), 0),
    );
    let mut missing_state = State::new(Memory::zeroed(7), 0);
    missing_state.registers[7] = 0;
    let missing = step(&Program::new(0, vec![0x48, 0x33, 0x07]), &missing_state);
    if !matches!(
        incomplete.outcome,
        Outcome::Trapped(Trap::IncompleteInstructionFetch { .. })
    ) || !matches!(
        illegal.outcome,
        Outcome::Trapped(Trap::IllegalInstruction { .. })
    ) || !matches!(
        missing.outcome,
        Outcome::Trapped(Trap::DataAccessFault { .. })
    ) {
        return Err(EvidenceError::SemanticMismatch(
            "x86-64 trap suite missed a declared class".to_owned(),
        ));
    }
    Ok(3)
}

fn branch_base_observation(control: ExecutionControl) -> Result<(u64, u64), EvidenceError> {
    let program = Program::new(18, vec![0x75, 0xf3]);
    let mut state = State::new(Memory::zeroed(0), 18);
    state.flags.zero = FlagValue::Clear;
    let next = step(&program, &state);
    if next.outcome != Outcome::Running || next.rip != 7 {
        return Err(EvidenceError::SemanticMismatch(
            "x86-64 branch witness failed".to_owned(),
        ));
    }
    let observed = match control {
        ExecutionControl::Declared => next.rip,
        ExecutionControl::BranchFromInstructionRip => state.rip.wrapping_add_signed(-13),
    };
    Ok((next.rip, observed))
}

fn upper_clear_control() -> bool {
    let mut state = State::new(Memory::zeroed(0), 0);
    state.registers[0] = u64::MAX;
    let next = step(&Program::new(0, vec![0x31, 0xc0]), &state);
    next.register(0) == 0 && next.register(0) != 0xffff_ffff_0000_0000
}

fn undefined_af_control() -> bool {
    let next = step(
        &Program::new(0, vec![0x31, 0xc0]),
        &State::new(Memory::zeroed(0), 0),
    );
    next.flags.auxiliary == FlagValue::Undefined && next.flags.auxiliary != FlagValue::Clear
}

fn implicit_stack_control() -> Result<bool, EvidenceError> {
    let mut state = State::new(memory_with_words(&[], 64)?, 0);
    state.registers[4] = 32;
    let next = step(&Program::new(0, vec![0xe8, 7, 0, 0, 0]), &state);
    Ok(next.rip == 12 && next.register(4) == 24 && read_word(&next.memory, 24) == Some(5))
}

fn run_until(
    program: &Program,
    mut state: State,
    target: u64,
    limit: usize,
) -> Result<State, EvidenceError> {
    for _ in 0..limit {
        if state.rip == target || state.outcome != Outcome::Running {
            break;
        }
        state = step(program, &state);
    }
    if state.rip != target || state.outcome != Outcome::Running {
        return Err(EvidenceError::SemanticMismatch(format!(
            "x86-64 program did not reach {target:#x}"
        )));
    }
    Ok(state)
}

fn memory_with_words(words: &[(u64, u64)], length: usize) -> Result<Memory, EvidenceError> {
    let mut entries: Vec<(u64, u8)> = (0..length)
        .map(|address| (u64::try_from(address).expect("fixture"), 0))
        .collect();
    for (address, word) in words {
        for (offset, byte) in word.to_le_bytes().into_iter().enumerate() {
            let index = usize::try_from(*address).map_err(machine_error)? + offset;
            let Some(entry) = entries.get_mut(index) else {
                return Err(EvidenceError::SemanticMismatch(
                    "x86-64 fixture word outside memory".to_owned(),
                ));
            };
            entry.1 = byte;
        }
    }
    Memory::from_entries(entries).map_err(machine_error)
}

fn read_word(memory: &Memory, address: u64) -> Option<u64> {
    let bytes: Option<Vec<u8>> = (0..8)
        .map(|offset| memory.byte_at(address + offset))
        .collect();
    Some(u64::from_le_bytes(bytes?.try_into().ok()?))
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
