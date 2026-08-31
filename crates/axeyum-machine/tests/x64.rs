//! Direct controls for the source-pinned x86-64 teaching slice.

use axeyum_machine::{
    a0::Memory,
    x64::{
        Condition, EncodingError, FlagValue, Instruction, Outcome, Program, SELECTED_FORMS,
        SOURCE_REVISION, SOURCE_SHA256, State, Trap, decode, encode, project_state, step,
    },
};

#[test]
fn source_identity_and_exact_form_set_are_pinned() {
    assert_eq!(SOURCE_REVISION, "325383-092US");
    assert_eq!(
        SOURCE_SHA256,
        "db01e5918a710c16487e27a9e71a19af201f39b3311c55550559baaf0805160b"
    );
    assert_eq!(SELECTED_FORMS.len(), 17);
    assert_eq!(SELECTED_FORMS[0], "XOR r32,r32");
    assert_eq!(SELECTED_FORMS[16], "RET");
}

#[test]
fn every_selected_form_round_trips_canonically() {
    let forms = [
        Instruction::Xor32 {
            destination: 0,
            source: 0,
        },
        Instruction::MoveImmediate32 {
            destination: 0,
            immediate: 0,
        },
        Instruction::Test64 { lhs: 6, rhs: 6 },
        Instruction::JumpShort {
            condition: Condition::Equal,
            displacement: 13,
        },
        Instruction::JumpShort {
            condition: Condition::NotEqual,
            displacement: -13,
        },
        Instruction::JumpShort {
            condition: Condition::NotSign,
            displacement: 3,
        },
        Instruction::Xor64Memory {
            destination: 0,
            base: 7,
        },
        Instruction::AddImmediate64 {
            destination: 7,
            immediate: 8,
        },
        Instruction::SubImmediate64 {
            destination: 6,
            immediate: 1,
        },
        Instruction::Move64 {
            destination: 0,
            source: 7,
        },
        Instruction::Negate64 { destination: 0 },
        Instruction::LoadEffectiveAddress64 {
            destination: 0,
            base: 7,
            displacement: 1,
        },
        Instruction::Push64 { source: 3 },
        Instruction::Pop64 { destination: 3 },
        Instruction::CallRelative { displacement: 17 },
        Instruction::Add64 {
            destination: 0,
            source: 3,
        },
        Instruction::Return,
    ];
    assert_eq!(forms.len(), SELECTED_FORMS.len());
    for instruction in forms {
        let bytes = encode(instruction).unwrap();
        assert_eq!(decode(&bytes), Ok((instruction, bytes.len())));
    }
}

#[test]
fn printed_absolute_value_and_zero_forms_decode_exactly() {
    let cases: &[(&[u8], Instruction)] = &[
        (
            &[0x48, 0x89, 0xf8],
            Instruction::Move64 {
                destination: 0,
                source: 7,
            },
        ),
        (&[0x48, 0x85, 0xc0], Instruction::Test64 { lhs: 0, rhs: 0 }),
        (
            &[0x79, 0x03],
            Instruction::JumpShort {
                condition: Condition::NotSign,
                displacement: 3,
            },
        ),
        (
            &[0x48, 0xf7, 0xd8],
            Instruction::Negate64 { destination: 0 },
        ),
        (
            &[0x31, 0xc0],
            Instruction::Xor32 {
                destination: 0,
                source: 0,
            },
        ),
        (
            &[0xb8, 0, 0, 0, 0],
            Instruction::MoveImmediate32 {
                destination: 0,
                immediate: 0,
            },
        ),
    ];
    for (bytes, instruction) in cases {
        assert_eq!(decode(bytes), Ok((*instruction, bytes.len())));
        assert_eq!(encode(*instruction).unwrap(), *bytes);
    }
}

#[test]
fn all_six_printed_x86_listings_have_executable_witnesses() {
    let count = vec![
        0x48, 0x85, 0xff, 0x74, 0x06, 0x48, 0x83, 0xef, 0x01, 0x75, 0xfa,
    ];
    let mut count_state = State::new(Memory::zeroed(0), 0);
    count_state.registers[7] = 3;
    count_state = run_until(&Program::new(0, count), count_state, 11, 16);
    assert_eq!(count_state.register(7), 0);

    let leaf = Program::new(0, vec![0x48, 0x8d, 0x47, 0x01, 0xc3]);
    let mut leaf_state = State::new(memory_with_words(&[(128, 64)]), 0);
    leaf_state.registers[7] = 41;
    leaf_state.registers[4] = 128;
    leaf_state = run_until(&leaf, leaf_state, 64, 4);
    assert_eq!(leaf_state.register(0), 42);

    let absolute = Program::new(
        0,
        vec![
            0x48, 0x89, 0xf8, 0x48, 0x85, 0xc0, 0x79, 0x03, 0x48, 0xf7, 0xd8,
        ],
    );
    for (input, expected) in [(7_u64, 7_u64), (u64::MAX - 6, 7)] {
        let mut state = State::new(Memory::zeroed(0), 0);
        state.registers[7] = input;
        state = run_until(&absolute, state, 11, 4);
        assert_eq!(state.register(0), expected);
    }

    let nonleaf = Program::new(
        0,
        vec![
            0x53, 0x48, 0x83, 0xec, 0x20, 0x48, 0x89, 0xfb, 0xe8, 0x09, 0, 0, 0, 0x48, 0x01, 0xd8,
            0x48, 0x83, 0xc4, 0x20, 0x5b, 0xc3, 0xc3,
        ],
    );
    let mut nonleaf_state = State::new(memory_with_words(&[(128, 64)]), 0);
    nonleaf_state.registers[0] = 2;
    nonleaf_state.registers[3] = 9;
    nonleaf_state.registers[4] = 128;
    nonleaf_state.registers[7] = 5;
    nonleaf_state = run_until(&nonleaf, nonleaf_state, 64, 16);
    assert_eq!(nonleaf_state.register(0), 7);
    assert_eq!(nonleaf_state.register(3), 9);
    assert_eq!(nonleaf_state.register(4), 136);

    let xor_zero = step(
        &Program::new(0, vec![0x31, 0xc0]),
        &State::new(Memory::zeroed(0), 0),
    );
    let mut move_state = State::new(Memory::zeroed(0), 0);
    move_state.flags.carry = FlagValue::Set;
    let move_zero = step(&Program::new(0, vec![0xb8, 0, 0, 0, 0]), &move_state);
    assert_eq!(xor_zero.register(0), move_zero.register(0));
    assert_ne!(xor_zero.flags, move_zero.flags);
}

#[test]
fn printed_xor_program_runs_empty_singleton_and_three_word_cases() {
    assert_eq!(run_xor(&[]), 0);
    assert_eq!(run_xor(&[0x0123_4567_89ab_cdef]), 0x0123_4567_89ab_cdef);
    assert_eq!(run_xor(&[1, 2, 4]), 7);
}

#[test]
fn flags_partial_registers_and_relative_base_are_explicit() {
    let program = Program::new(100, vec![0x31, 0xc0, 0x75, 0xfc]);
    let mut state = State::new(Memory::zeroed(0), 100);
    state.registers[0] = u64::MAX;
    let cleared = step(&program, &state);
    assert_eq!(cleared.register(0), 0);
    assert_eq!(cleared.flags.zero, FlagValue::Set);
    assert_eq!(cleared.flags.carry, FlagValue::Clear);
    assert_eq!(cleared.flags.overflow, FlagValue::Clear);
    assert_eq!(cleared.flags.auxiliary, FlagValue::Undefined);
    let fallthrough = step(&program, &cleared);
    assert_eq!(fallthrough.rip, 104);

    let mut taken_state = cleared;
    taken_state.flags.zero = FlagValue::Clear;
    taken_state.rip = 102;
    let taken = step(&program, &taken_state);
    assert_eq!(taken.rip, 100);
}

#[test]
fn stack_control_and_memory_faults_are_atomic() {
    let memory = Memory::zeroed(64);
    let mut call_state = State::new(memory, 0);
    call_state.registers[4] = 32;
    let called = step(&Program::new(0, vec![0xe8, 7, 0, 0, 0]), &call_state);
    assert_eq!(called.rip, 12);
    assert_eq!(called.register(4), 24);
    assert_eq!(read_word(&called.memory, 24), 5);

    let returned = step(&Program::new(12, vec![0xc3]), &called);
    assert_eq!(returned.rip, 5);
    assert_eq!(returned.register(4), 32);

    let mut failed_state = State::new(Memory::zeroed(7), 0);
    failed_state.registers[4] = 8;
    failed_state.registers[3] = 0xfeed;
    let failed = step(&Program::new(0, vec![0x53]), &failed_state);
    assert!(matches!(
        failed.outcome,
        Outcome::Trapped(Trap::DataAccessFault {
            address: 0,
            bytes: 8
        })
    ));
    assert_eq!(failed.memory, failed_state.memory);
    assert_eq!(failed.register(4), 8);
}

#[test]
fn decode_traps_and_projection_preserve_declared_state() {
    assert_eq!(decode(&[0x48]), Err(EncodingError::IncompleteInstruction));
    assert_eq!(decode(&[0x0f]), Err(EncodingError::IllegalInstruction));
    let incomplete = step(
        &Program::new(0, vec![0x48]),
        &State::new(Memory::zeroed(0), 0),
    );
    assert!(matches!(
        incomplete.outcome,
        Outcome::Trapped(Trap::IncompleteInstructionFetch { rip: 0 })
    ));
    let illegal = step(
        &Program::new(0, vec![0x0f]),
        &State::new(Memory::zeroed(0), 0),
    );
    assert!(matches!(
        illegal.outcome,
        Outcome::Trapped(Trap::IllegalInstruction { rip: 0 })
    ));

    let mut state = State::new(Memory::from_entries(vec![(9, 1), (2, 7)]).unwrap(), 44);
    state.registers[7] = 11;
    state.registers[0] = 13;
    let projection = project_state(&state, vec![7, 0]).unwrap();
    assert_eq!(projection.registers, [(0, 13), (7, 11)]);
    assert_eq!(projection.memory, [(2, 7), (9, 1)]);
}

fn run_xor(values: &[u64]) -> u64 {
    let code = vec![
        0x31, 0xc0, 0x48, 0x85, 0xf6, 0x74, 0x0d, 0x48, 0x33, 0x07, 0x48, 0x83, 0xc7, 0x08, 0x48,
        0x83, 0xee, 0x01, 0x75, 0xf3, 0xc3,
    ];
    let base = 256_u64;
    let stack = 512_u64;
    let continuation = 64_u64;
    let mut entries = Vec::new();
    for (index, value) in values.iter().enumerate() {
        let address = base + u64::try_from(index * 8).unwrap();
        entries.extend(
            value
                .to_le_bytes()
                .into_iter()
                .enumerate()
                .map(|(offset, byte)| (address + u64::try_from(offset).unwrap(), byte)),
        );
    }
    entries.extend(
        continuation
            .to_le_bytes()
            .into_iter()
            .enumerate()
            .map(|(offset, byte)| (stack + u64::try_from(offset).unwrap(), byte)),
    );
    let mut state = State::new(Memory::from_entries(entries).unwrap(), 0);
    state.registers[7] = base;
    state.registers[6] = u64::try_from(values.len()).unwrap();
    state.registers[4] = stack;
    let program = Program::new(0, code);
    for _ in 0..128 {
        if state.rip == continuation || state.outcome != Outcome::Running {
            break;
        }
        state = step(&program, &state);
    }
    assert_eq!(state.outcome, Outcome::Running);
    assert_eq!(state.rip, continuation);
    assert_eq!(state.register(4), stack + 8);
    state.register(0)
}

fn read_word(memory: &Memory, address: u64) -> u64 {
    u64::from_le_bytes(
        (0..8)
            .map(|offset| memory.byte_at(address + offset).unwrap())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap(),
    )
}

fn memory_with_words(words: &[(u64, u64)]) -> Memory {
    let mut entries: Vec<(u64, u8)> = (0..256).map(|address| (address, 0)).collect();
    for (address, word) in words {
        for (offset, byte) in word.to_le_bytes().into_iter().enumerate() {
            entries[usize::try_from(*address).unwrap() + offset].1 = byte;
        }
    }
    Memory::from_entries(entries).unwrap()
}

fn run_until(program: &Program, mut state: State, target: u64, limit: usize) -> State {
    for _ in 0..limit {
        if state.rip == target || state.outcome != Outcome::Running {
            break;
        }
        state = step(program, &state);
    }
    assert_eq!(state.outcome, Outcome::Running);
    assert_eq!(state.rip, target);
    state
}
