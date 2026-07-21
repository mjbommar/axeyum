//! Authenticated bounded page-table-shaped evidence (ADR-0320).

use std::fmt::Write as _;
use std::fs;
use std::panic::catch_unwind;
use std::path::{Path, PathBuf};
use std::time::Instant;

use axeyum_ir::{Assignment, TermArena, TermId, Value, eval, render};
use axeyum_solver::{Model, ProofOutcome, SolverConfig, prove};
use axeyum_verify::reflect::mir::checked::{
    CheckedMirMemory, MirMemoryConfig, ReflectErrorKind, reflect_bounded_memory_checked,
};
use axeyum_verify::reflect::mir::syntax::parse_function;
use sha2::{Digest, Sha256};

#[path = "fixtures/mir-target-crate/src/lib.rs"]
mod target_fixture;

const MIR: &str = include_str!("fixtures/mir-target-crate/artifacts/page_table_walks.mir");
const TABLES: [[u8; 4]; 8] = [
    [0x00, 0x00, 0x00, 0x00],
    [0xff, 0xff, 0xff, 0xff],
    [0x00, 0x01, 0x02, 0x03],
    [0x40, 0x81, 0xc2, 0x03],
    [0x01, 0x01, 0x00, 0x00],
    [0x01, 0x02, 0x00, 0x00],
    [0x03, 0x42, 0x81, 0xc0],
    [0xfc, 0x81, 0x42, 0x03],
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AuthError {
    HashMismatch,
    InventoryMismatch,
}

#[derive(Clone, Copy)]
struct WalkSpec {
    parent: TermId,
    leaf: TermId,
    frame: TermId,
    permissions: TermId,
}

fn fixture_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/mir-target-crate")
}

fn sha256_bytes(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(output, "{byte:02x}").expect("writing to a String cannot fail");
    }
    output
}

fn sha256(path: &Path) -> String {
    sha256_bytes(
        &fs::read(path)
            .unwrap_or_else(|error| panic!("read {} for authentication: {error}", path.display())),
    )
}

fn authenticate_blob(bytes: &[u8], expected: &str) -> Result<(), AuthError> {
    if sha256_bytes(bytes) == expected {
        Ok(())
    } else {
        Err(AuthError::HashMismatch)
    }
}

fn authenticate_inventory(actual: &str, expected: &str) -> Result<(), AuthError> {
    if actual == expected {
        Ok(())
    } else {
        Err(AuthError::InventoryMismatch)
    }
}

fn reflect(function: &str) -> CheckedMirMemory {
    reflect_bounded_memory_checked(MIR, &MirMemoryConfig::new(function, 64))
        .unwrap_or_else(|error| panic!("reflect {function}: {error}"))
}

fn param(reflected: &CheckedMirMemory, local: u32) -> axeyum_ir::SymbolId {
    reflected
        .params
        .iter()
        .find(|parameter| parameter.local == local)
        .unwrap_or_else(|| panic!("missing reflected parameter _{local}"))
        .symbol
}

fn select4(arena: &mut TermArena, bytes: &[TermId; 4], index: TermId) -> TermId {
    let mut selected = bytes[3];
    for offset in (0_usize..3).rev() {
        let offset_term = arena.bv_const(8, offset as u128).unwrap();
        let at_offset = arena.eq(index, offset_term).unwrap();
        selected = arena.ite(at_offset, bytes[offset], selected).unwrap();
    }
    selected
}

fn walk_spec(reflected: &mut CheckedMirMemory) -> WalkSpec {
    let address_symbol = param(reflected, 2);
    let address = reflected.arena.var(address_symbol);
    let input = &reflected.region.input;
    assert_eq!(input.len(), 4);
    let bytes = [
        reflected.arena.var(input[0]),
        reflected.arena.var(input[1]),
        reflected.arena.var(input[2]),
        reflected.arena.var(input[3]),
    ];
    let six = reflected.arena.bv_const(8, 6).unwrap();
    let three = reflected.arena.bv_const(8, 3).unwrap();
    let shifted = reflected.arena.bv_lshr(address, six).unwrap();
    let level1 = reflected.arena.bv_and(shifted, three).unwrap();
    let parent = select4(&mut reflected.arena, &bytes, level1);
    let level2 = reflected.arena.bv_and(parent, three).unwrap();
    let leaf = select4(&mut reflected.arena, &bytes, level2);
    let frame_mask = reflected.arena.bv_const(8, 0xfc).unwrap();
    let frame = reflected.arena.bv_and(leaf, frame_mask).unwrap();
    let intersection = reflected.arena.bv_and(parent, leaf).unwrap();
    let permissions = reflected.arena.bv_and(intersection, three).unwrap();
    WalkSpec {
        parent,
        leaf,
        frame,
        permissions,
    }
}

fn assignment(reflected: &CheckedMirMemory, table: [u8; 4], address: u8) -> Assignment {
    let mut assignment = Assignment::new();
    assignment.set(
        param(reflected, 2),
        Value::Bv {
            width: 8,
            value: u128::from(address),
        },
    );
    for (symbol, byte) in reflected.region.input.iter().zip(table) {
        assignment.set(
            *symbol,
            Value::Bv {
                width: 8,
                value: u128::from(byte),
            },
        );
    }
    assignment
}

fn assignment_from_model(model: &Model) -> Assignment {
    let mut assignment = Assignment::new();
    for (symbol, value) in model.iter() {
        assignment.set(symbol, value);
    }
    assignment
}

fn inputs_from_model(reflected: &CheckedMirMemory, model: &Model) -> ([u8; 4], u8) {
    let mut table = [0_u8; 4];
    for (slot, symbol) in table.iter_mut().zip(reflected.region.input.iter().copied()) {
        *slot = match model.get(symbol) {
            Some(Value::Bv { width: 8, value }) => u8::try_from(value).unwrap(),
            other => panic!("countermodel has no byte for {symbol:?}: {other:?}"),
        };
    }
    let address = match model.get(param(reflected, 2)) {
        Some(Value::Bv { width: 8, value }) => u8::try_from(value).unwrap(),
        other => panic!("countermodel has no virtual address: {other:?}"),
    };
    (table, address)
}

fn eval_bool(arena: &TermArena, term: TermId, assignment: &Assignment) -> bool {
    match eval(arena, term, assignment).unwrap() {
        Value::Bool(value) => value,
        other => panic!("expected Bool, got {other:?}"),
    }
}

fn eval_u8(arena: &TermArena, term: TermId, assignment: &Assignment) -> u8 {
    match eval(arena, term, assignment).unwrap() {
        Value::Bv { width: 8, value } => u8::try_from(value).unwrap(),
        other => panic!("expected BV8, got {other:?}"),
    }
}

fn assert_proved(arena: &mut TermArena, goal: TermId, label: &str) {
    let outcome = prove(arena, &[], goal, &SolverConfig::default())
        .unwrap_or_else(|error| panic!("{label}: solver error: {error}"));
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "{label}: expected proof, got {outcome:?}"
    );
}

fn assert_disproved(arena: &mut TermArena, goal: TermId, label: &str) -> Model {
    let outcome = prove(arena, &[], goal, &SolverConfig::default())
        .unwrap_or_else(|error| panic!("{label}: solver error: {error}"));
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("{label}: expected replayed countermodel, got {outcome:?}");
    };
    assert!(
        !eval_bool(arena, goal, &assignment_from_model(&model)),
        "{label}: returned countermodel must falsify the original goal"
    );
    model
}

fn spec_frame(table: [u8; 4], address: u8) -> u8 {
    let level1 = usize::from((address >> 6) & 3);
    let level2 = usize::from(table[level1] & 3);
    table[level2] & 0xfc
}

fn spec_permissions(table: [u8; 4], address: u8) -> u8 {
    let level1 = usize::from((address >> 6) & 3);
    let parent = table[level1];
    let level2 = usize::from(parent & 3);
    (parent & table[level2]) & 3
}

#[test]
fn committed_artifact_and_typed_projections_are_authenticated() {
    let root = fixture_root();
    let expected = [
        (
            "Cargo.toml",
            "bc93ff6420e999c5a58a26ef43ef7da2e6f83379596fdd846d26d3908982c2b3",
        ),
        (
            "Cargo.lock",
            "e5cb6201eb08b7e5c879584e7ef9141191b6b966aa476ba0c9a76b78323fb6ad",
        ),
        (
            "src/lib.rs",
            "dda67bd8e005568bcae7a3c1fe30fc8bb79d010d35e1aa88cedffc8d9a708642",
        ),
        (
            "artifacts/page_table_walks.mir",
            "6a1e7c82ad14de2355d5e7039422933b99c410e3ca4bff89b1704ee53f5b5c43",
        ),
        (
            "artifacts/walk-frame-summary.json",
            "c5e886633528ee3d775b1c2dc110e6df4126afd3e799b90619894fe2ae7ee1ab",
        ),
        (
            "artifacts/walk-permissions-summary.json",
            "6d7769e213eef6016cd12b3b09b060f96751edc9d10d0c6c09090f172e19277f",
        ),
        (
            "artifacts/evidence.json",
            "c0314cee438f687370b4a28e5eb37f96008b8843a676f2d3c9c48655e1516367",
        ),
        (
            "artifacts/provenance.json",
            "ee8c44cd94d8b4aa305a680471031e9f2c60dc9ee9c1235283201628c0b8d374",
        ),
    ];
    let inventory = expected
        .iter()
        .map(|(relative, hash)| format!("{hash}  {relative}"))
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    let committed_inventory = fs::read_to_string(root.join("artifacts/SHA256SUMS")).unwrap();
    assert_eq!(
        authenticate_inventory(&committed_inventory, &inventory),
        Ok(())
    );
    for (relative, hash) in expected {
        assert_eq!(sha256(&root.join(relative)), hash, "{relative}");
    }
    assert_eq!(MIR.len(), 8_218);

    for (function, expected_result) in [
        (
            "walk_frame",
            "393eeb2d75b20fc7277a43cd0b25dfca73eaf9c2a0fc03fff1f6382e2945080c",
        ),
        (
            "walk_permissions",
            "ad22dde91686cabf7316214a8c029e4b9f078a1963f4c18c14b867d0fe1704b1",
        ),
    ] {
        let reflected = reflect(function);
        assert_eq!(reflected.region.input.len(), 4);
        assert_eq!(
            sha256_bytes(render(&reflected.arena, reflected.result.value).as_bytes()),
            expected_result
        );
        assert_eq!(
            sha256_bytes(render(&reflected.arena, reflected.panic).as_bytes()),
            "d9664f625df0a48a05861ac5e9c7a99ff15fafbc0ea7f5a758b6993ac2ad8261"
        );
        assert_eq!(parse_function(MIR, function).unwrap().blocks.len(), 4);
        let repeated = reflect(function);
        assert_eq!(
            render(&reflected.arena, reflected.result.value),
            render(&repeated.arena, repeated.result.value)
        );
        assert_eq!(
            render(&reflected.arena, reflected.panic),
            render(&repeated.arena, repeated.panic)
        );
        assert_eq!(reflected.region.input, repeated.region.input);
    }
}

#[test]
fn good_walks_have_universal_reflected_proofs() {
    let started = Instant::now();
    let mut frame = reflect("walk_frame");
    let frame_spec = walk_spec(&mut frame);
    let no_frame_panic = frame.arena.not(frame.panic).unwrap();
    let exact_frame = frame
        .arena
        .eq(frame.result.value, frame_spec.frame)
        .unwrap();
    let three = frame.arena.bv_const(8, 3).unwrap();
    let low_bits = frame.arena.bv_and(frame.result.value, three).unwrap();
    let zero = frame.arena.bv_const(8, 0).unwrap();
    let aligned = frame.arena.eq(low_bits, zero).unwrap();
    let frame_goal = frame.arena.and(no_frame_panic, exact_frame).unwrap();
    let frame_goal = frame.arena.and(frame_goal, aligned).unwrap();
    assert_proved(&mut frame.arena, frame_goal, "frame walk invariants");

    let mut permissions = reflect("walk_permissions");
    let permission_spec = walk_spec(&mut permissions);
    let no_permission_panic = permissions.arena.not(permissions.panic).unwrap();
    let exact_permissions = permissions
        .arena
        .eq(permissions.result.value, permission_spec.permissions)
        .unwrap();
    let parent_bits = permissions
        .arena
        .bv_and(permissions.result.value, permission_spec.parent)
        .unwrap();
    let parent_subset = permissions
        .arena
        .eq(parent_bits, permissions.result.value)
        .unwrap();
    let leaf_bits = permissions
        .arena
        .bv_and(permissions.result.value, permission_spec.leaf)
        .unwrap();
    let leaf_subset = permissions
        .arena
        .eq(leaf_bits, permissions.result.value)
        .unwrap();
    let permission_goal = permissions
        .arena
        .and(no_permission_panic, exact_permissions)
        .unwrap();
    let permission_goal = permissions
        .arena
        .and(permission_goal, parent_subset)
        .unwrap();
    let permission_goal = permissions.arena.and(permission_goal, leaf_subset).unwrap();
    assert_proved(
        &mut permissions.arena,
        permission_goal,
        "permission walk invariants",
    );
    eprintln!("ADR0320_PROOF wall_ms={}", started.elapsed().as_millis());
}

#[test]
fn broken_walks_have_replayed_source_witnesses() {
    let mut index = reflect("broken_walk_index");
    let no_panic = index.arena.not(index.panic).unwrap();
    let model = assert_disproved(&mut index.arena, no_panic, "unmasked index");
    let address = match model.get(param(&index, 2)) {
        Some(Value::Bv { width: 8, value }) => u8::try_from(value).unwrap(),
        other => panic!("countermodel has no unmasked address: {other:?}"),
    };
    assert!(address >= 4);
    let reflected_assignment = assignment(&index, [0; 4], address);
    assert!(eval_bool(&index.arena, index.panic, &reflected_assignment));
    assert!(catch_unwind(|| target_fixture::broken_walk_index([0; 4], address)).is_err());
    assert!(catch_unwind(|| target_fixture::walk_frame([0; 4], address)).is_ok());

    let mut frame = reflect("broken_frame_unaligned");
    let three = frame.arena.bv_const(8, 3).unwrap();
    let low = frame.arena.bv_and(frame.result.value, three).unwrap();
    let zero = frame.arena.bv_const(8, 0).unwrap();
    let aligned = frame.arena.eq(low, zero).unwrap();
    let model = assert_disproved(&mut frame.arena, aligned, "unaligned frame");
    let (table, address) = inputs_from_model(&frame, &model);
    let reflected_assignment = assignment(&frame, table, address);
    let broken = eval_u8(&frame.arena, frame.result.value, &reflected_assignment);
    assert_ne!(broken & 3, 0);
    assert_eq!(
        target_fixture::broken_frame_unaligned(table, address),
        broken
    );
    assert_eq!(target_fixture::walk_frame(table, address) & 3, 0);

    let mut permissions = reflect("broken_permissions_escalate");
    let spec = walk_spec(&mut permissions);
    let retained = permissions
        .arena
        .bv_and(permissions.result.value, spec.parent)
        .unwrap();
    let subset = permissions
        .arena
        .eq(retained, permissions.result.value)
        .unwrap();
    let model = assert_disproved(&mut permissions.arena, subset, "permission escalation");
    let (table, address) = inputs_from_model(&permissions, &model);
    let reflected_assignment = assignment(&permissions, table, address);
    let broken = eval_u8(
        &permissions.arena,
        permissions.result.value,
        &reflected_assignment,
    );
    assert_eq!(
        target_fixture::broken_permissions_escalate(table, address),
        broken
    );
    let level1 = usize::from((address >> 6) & 3);
    assert_ne!(broken & !table[level1], 0);
    assert_eq!(
        target_fixture::walk_permissions(table, address) & !table[level1],
        0
    );
}

#[test]
fn frozen_sampler_has_exact_4096_row_agreement() {
    let started = Instant::now();
    let frame = reflect("walk_frame");
    let permissions = reflect("walk_permissions");
    let mut rows = 0_u32;
    for table in TABLES {
        for address in u8::MIN..=u8::MAX {
            let frame_assignment = assignment(&frame, table, address);
            assert!(!eval_bool(&frame.arena, frame.panic, &frame_assignment));
            let reflected_frame = eval_u8(&frame.arena, frame.result.value, &frame_assignment);
            assert_eq!(reflected_frame, spec_frame(table, address));
            assert_eq!(reflected_frame, target_fixture::walk_frame(table, address));
            rows += 1;

            let permission_assignment = assignment(&permissions, table, address);
            assert!(!eval_bool(
                &permissions.arena,
                permissions.panic,
                &permission_assignment,
            ));
            let reflected_permissions = eval_u8(
                &permissions.arena,
                permissions.result.value,
                &permission_assignment,
            );
            assert_eq!(reflected_permissions, spec_permissions(table, address));
            assert_eq!(
                reflected_permissions,
                target_fixture::walk_permissions(table, address)
            );
            rows += 1;
        }
    }
    assert_eq!(rows, 4_096);
    eprintln!(
        "ADR0320_SAMPLE rows={rows} disagreements=0 errors=0 panics=0 dropped=0 wall_ms={}",
        started.elapsed().as_millis()
    );
}

#[test]
fn semantic_mutations_have_teeth() {
    let raw_hash = "6a1e7c82ad14de2355d5e7039422933b99c410e3ca4bff89b1704ee53f5b5c43";
    let redundant_level1 = MIR.replacen("_4 = BitAnd(move _5, const 3_u8);", "_4 = move _5;", 1);
    assert_eq!(
        authenticate_blob(redundant_level1.as_bytes(), raw_hash),
        Err(AuthError::HashMismatch)
    );
    let mut redundant =
        reflect_bounded_memory_checked(&redundant_level1, &MirMemoryConfig::new("walk_frame", 64))
            .unwrap();
    let spec = walk_spec(&mut redundant);
    let exact = redundant
        .arena
        .eq(redundant.result.value, spec.frame)
        .unwrap();
    assert_proved(
        &mut redundant.arena,
        exact,
        "redundant level-one mask removal remains semantically equal",
    );

    let missing_level2 = MIR.replacen("_9 = BitAnd(move _10, const 3_u8);", "_9 = move _10;", 1);
    let mut missing_level2 =
        reflect_bounded_memory_checked(&missing_level2, &MirMemoryConfig::new("walk_frame", 64))
            .unwrap();
    let no_panic = missing_level2.arena.not(missing_level2.panic).unwrap();
    assert_disproved(
        &mut missing_level2.arena,
        no_panic,
        "missing level-two index mask",
    );

    let missing_frame_mask = MIR.replace("_0 = BitAnd(move _12, const 252_u8);", "_0 = move _12;");
    let mut missing_frame = reflect_bounded_memory_checked(
        &missing_frame_mask,
        &MirMemoryConfig::new("walk_frame", 64),
    )
    .unwrap();
    let three = missing_frame.arena.bv_const(8, 3).unwrap();
    let low = missing_frame
        .arena
        .bv_and(missing_frame.result.value, three)
        .unwrap();
    let zero = missing_frame.arena.bv_const(8, 0).unwrap();
    let aligned = missing_frame.arena.eq(low, zero).unwrap();
    assert_disproved(&mut missing_frame.arena, aligned, "missing frame mask");

    for (label, mutated) in [
        (
            "missing parent intersection",
            MIR.replace("_12 = BitAnd(copy _8, move _13);", "_12 = move _13;"),
        ),
        (
            "parent-for-leaf selection swap",
            MIR.replace("_13 = copy _1[_10];", "_13 = copy _1[_3];"),
        ),
    ] {
        let mut reflected =
            reflect_bounded_memory_checked(&mutated, &MirMemoryConfig::new("walk_permissions", 64))
                .unwrap();
        let spec = walk_spec(&mut reflected);
        let exact = reflected
            .arena
            .eq(reflected.result.value, spec.permissions)
            .unwrap();
        assert_disproved(&mut reflected.arena, exact, label);
    }
}

#[test]
fn configuration_assertion_and_metadata_mutations_fail_closed() {
    let wrong_region = MIR.replacen("fn walk_frame(_1: [u8; 4]", "fn walk_frame(_1: [u8; 0]", 1);
    assert_eq!(
        reflect_bounded_memory_checked(&wrong_region, &MirMemoryConfig::new("walk_frame", 64))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::RegionSize
    );
    assert_eq!(
        reflect_bounded_memory_checked(MIR, &MirMemoryConfig::new("walk_frame", 32))
            .unwrap_err()
            .kind(),
        ReflectErrorKind::TargetWidth
    );

    let broken_assert = MIR.replacen(
        "assert(move _4, \"index out of bounds: the length is {} but the index is {}\", const 4_usize, copy _3)",
        "assert(const true, \"corrupted compiler assertion\")",
        1,
    );
    let mut broken = reflect_bounded_memory_checked(
        &broken_assert,
        &MirMemoryConfig::new("broken_walk_index", 64),
    )
    .unwrap();
    let no_panic = broken.arena.not(broken.panic).unwrap();
    assert_disproved(
        &mut broken.arena,
        no_panic,
        "corrupt assertion cannot suppress access panic",
    );

    let root = fixture_root();
    for (relative, expected) in [
        (
            "artifacts/walk-frame-summary.json",
            "c5e886633528ee3d775b1c2dc110e6df4126afd3e799b90619894fe2ae7ee1ab",
        ),
        (
            "artifacts/walk-permissions-summary.json",
            "6d7769e213eef6016cd12b3b09b060f96751edc9d10d0c6c09090f172e19277f",
        ),
        (
            "artifacts/evidence.json",
            "c0314cee438f687370b4a28e5eb37f96008b8843a676f2d3c9c48655e1516367",
        ),
        (
            "artifacts/provenance.json",
            "ee8c44cd94d8b4aa305a680471031e9f2c60dc9ee9c1235283201628c0b8d374",
        ),
    ] {
        let mut bytes = fs::read(root.join(relative)).unwrap();
        bytes[0] ^= 1;
        assert_eq!(
            authenticate_blob(&bytes, expected),
            Err(AuthError::HashMismatch),
            "{relative} tamper"
        );
    }
    let inventory = fs::read_to_string(root.join("artifacts/SHA256SUMS")).unwrap();
    let mutated_inventory = inventory.replacen('6', "7", 1);
    assert_eq!(
        authenticate_inventory(&mutated_inventory, &inventory),
        Err(AuthError::InventoryMismatch)
    );
}
