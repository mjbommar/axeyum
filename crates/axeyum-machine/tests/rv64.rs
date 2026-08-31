//! Direct controls for the source-pinned RV64I teaching slice.

use axeyum_machine::{
    a0::Memory,
    rv64::{
        EncodingError, Instruction, Outcome, Program, RV64I_VERSION, SELECTED_FORMS,
        SOURCE_RELEASE, SOURCE_SHA256, State, Trap, decode, encode, project_state, step,
    },
};

#[test]
fn source_identity_and_exact_form_set_are_pinned() {
    assert_eq!(SOURCE_RELEASE, "20260120");
    assert_eq!(RV64I_VERSION, "2.1");
    assert_eq!(
        SOURCE_SHA256,
        "06bb3c23074f72060a0ec061a80933af948cae7ceafdcd9d1fe177b05fd150bc"
    );
    assert_eq!(
        SELECTED_FORMS,
        [
            "ADDI", "ADD", "SUB", "OR", "XOR", "LD", "SD", "BEQ", "BNE", "BGE", "JAL", "JALR"
        ]
    );
}

#[test]
fn known_book_encodings_decode_and_round_trip() {
    let cases = [
        (
            0x0022_81b3,
            Instruction::Add {
                rd: 3,
                rs1: 5,
                rs2: 2,
            },
        ),
        (
            0x0022_8863,
            Instruction::BranchEqual {
                rs1: 5,
                rs2: 2,
                offset: 16,
            },
        ),
        (
            0xfe05_1ee3,
            Instruction::BranchNotEqual {
                rs1: 10,
                rs2: 0,
                offset: -4,
            },
        ),
        (
            0x0005_5463,
            Instruction::BranchGreaterEqual {
                rs1: 10,
                rs2: 0,
                offset: 8,
            },
        ),
        (
            0x40a0_0533,
            Instruction::Sub {
                rd: 10,
                rs1: 0,
                rs2: 10,
            },
        ),
        (
            0x0000_8067,
            Instruction::JumpAndLinkRegister {
                rd: 0,
                rs1: 1,
                immediate: 0,
            },
        ),
    ];
    for (word, instruction) in cases {
        assert_eq!(decode(word), Ok(instruction));
        assert_eq!(encode(instruction), Ok(word));
    }
    assert!(matches!(
        decode(0xffff_ffff),
        Err(EncodingError::IllegalInstruction(_))
    ));
}

#[test]
fn xor_reduction_table_decodes_at_every_printed_address() {
    let words = [
        0x0005_0293,
        0x0000_0513,
        0x0005_8c63,
        0x0002_b303,
        0x0065_4533,
        0x0082_8293,
        0xfff5_8593,
        0xfe05_98e3,
        0x0000_8067,
    ];
    let expected = [
        Instruction::AddImmediate {
            rd: 5,
            rs1: 10,
            immediate: 0,
        },
        Instruction::AddImmediate {
            rd: 10,
            rs1: 0,
            immediate: 0,
        },
        Instruction::BranchEqual {
            rs1: 11,
            rs2: 0,
            offset: 24,
        },
        Instruction::LoadDouble {
            rd: 6,
            rs1: 5,
            immediate: 0,
        },
        Instruction::Xor {
            rd: 10,
            rs1: 10,
            rs2: 6,
        },
        Instruction::AddImmediate {
            rd: 5,
            rs1: 5,
            immediate: 8,
        },
        Instruction::AddImmediate {
            rd: 11,
            rs1: 11,
            immediate: -1,
        },
        Instruction::BranchNotEqual {
            rs1: 11,
            rs2: 0,
            offset: -16,
        },
        Instruction::JumpAndLinkRegister {
            rd: 0,
            rs1: 1,
            immediate: 0,
        },
    ];
    for ((index, word), instruction) in words.into_iter().enumerate().zip(expected) {
        assert_eq!(decode(word), Ok(instruction), "address {:#x}", index * 4);
        assert_eq!(encode(instruction), Ok(word));
    }
}

#[test]
fn arithmetic_x0_and_branch_pc_rules_execute() {
    let instructions = [
        Instruction::AddImmediate {
            rd: 0,
            rs1: 10,
            immediate: 1,
        },
        Instruction::AddImmediate {
            rd: 10,
            rs1: 10,
            immediate: -1,
        },
        Instruction::BranchNotEqual {
            rs1: 10,
            rs2: 0,
            offset: -4,
        },
    ];
    let program = program(&instructions);
    let mut state = State::new(Memory::zeroed(0), 0);
    state.registers[0] = u64::MAX;
    state.registers[10] = 2;
    state = step(&program, &state);
    assert_eq!(state.register(0), 0);
    assert_eq!(state.pc, 4);
    state = step(&program, &state);
    assert_eq!(state.register(10), 1);
    assert_eq!(state.pc, 8);
    state = step(&program, &state);
    assert_eq!(state.pc, 4, "taken branch uses its own PC as base");
}

#[test]
fn doubleword_memory_is_little_endian_aligned_and_atomic() {
    let instructions = [
        Instruction::StoreDouble {
            rs1: 5,
            rs2: 6,
            immediate: 0,
        },
        Instruction::LoadDouble {
            rd: 7,
            rs1: 5,
            immediate: 0,
        },
    ];
    let program = program(&instructions);
    let mut state = State::new(Memory::zeroed(16), 0);
    state.registers[5] = 8;
    state.registers[6] = 0x0123_4567_89ab_cdef;
    state = step(&program, &state);
    assert_eq!(
        (8..16)
            .map(|address| state.memory.byte(address).unwrap())
            .collect::<Vec<_>>(),
        [0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01]
    );
    state = step(&program, &state);
    assert_eq!(state.register(7), 0x0123_4567_89ab_cdef);

    let before = Memory::from_entries((0..7).map(|address| (address, 0)).collect()).unwrap();
    let mut missing = State::new(before.clone(), 0);
    missing.registers[5] = 0;
    missing.registers[6] = u64::MAX;
    let trapped = step(&program, &missing);
    assert_eq!(trapped.memory, before);
    assert!(matches!(
        trapped.outcome,
        Outcome::Trapped(Trap::DataAccessFault {
            address: 0,
            bytes: 8
        })
    ));

    let mut misaligned = State::new(Memory::zeroed(16), 0);
    misaligned.registers[5] = 1;
    assert!(matches!(
        step(&program, &misaligned).outcome,
        Outcome::Trapped(Trap::DataAddressMisaligned { address: 1 })
    ));
}

#[test]
fn links_targets_and_instruction_alignment_are_explicit() {
    let image = program(&[
        Instruction::JumpAndLink { rd: 1, offset: 8 },
        Instruction::AddImmediate {
            rd: 10,
            rs1: 0,
            immediate: 99,
        },
        Instruction::JumpAndLinkRegister {
            rd: 0,
            rs1: 5,
            immediate: 1,
        },
    ]);
    let mut state = State::new(Memory::zeroed(0), 0);
    state.registers[5] = 16;
    state = step(&image, &state);
    assert_eq!(state.register(1), 4);
    assert_eq!(state.pc, 8);
    state = step(&image, &state);
    assert_eq!(state.pc, 16);
    assert_eq!(state.register(0), 0);

    let bad = program(&[Instruction::JumpAndLink { rd: 1, offset: 2 }]);
    let entry = State::new(Memory::zeroed(0), 0);
    let trapped = step(&bad, &entry);
    assert_eq!(
        trapped.register(1),
        0,
        "faulting jump does not write its link"
    );
    assert_eq!(trapped.pc, 0);
    assert!(matches!(
        trapped.outcome,
        Outcome::Trapped(Trap::InstructionAddressMisaligned { pc: 2 })
    ));
}

#[test]
fn refinement_projection_is_canonical_and_preserves_complete_memory() {
    let mut state = State::new(Memory::from_entries(vec![(9, 0), (2, 7)]).unwrap(), 44);
    state.registers[10] = 99;
    state.registers[5] = 42;
    state.registers[0] = u64::MAX;
    let projected = project_state(&state, vec![10, 0, 5]).unwrap();
    assert_eq!(projected.registers, [(0, 0), (5, 42), (10, 99)]);
    assert_eq!(projected.memory, [(2, 7), (9, 0)]);
    assert_eq!(projected.pc, 44);
    assert_eq!(projected.outcome, Outcome::Running);
    assert!(project_state(&state, vec![5, 5]).is_err());
    assert!(project_state(&state, vec![32]).is_err());
}

fn program(instructions: &[Instruction]) -> Program {
    let code = instructions
        .iter()
        .flat_map(|instruction| encode(*instruction).unwrap().to_le_bytes())
        .collect();
    Program::new(0, code)
}
