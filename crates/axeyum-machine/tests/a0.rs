#![allow(missing_docs)]

use axeyum_machine::a0::{
    A0Error, Conditions, Instruction, Memory, MemorySpan, Observation, ObservationError, Outcome,
    Program, State, StateComponent, StopReason, Trap, Word, decode, decode_state, encode,
    encode_state, run, run_prefix, step,
};

fn word(width: u8, value: u64) -> Word {
    Word::new(width, value).unwrap()
}
fn program(bytes: Vec<u8>) -> Program {
    Program::new(8, word(8, 0), bytes).unwrap()
}
fn state(memory: usize) -> State {
    State::new(8, Memory::zeroed(memory), word(8, 0)).unwrap()
}

#[test]
fn word_roundtrip_and_signed_reading() {
    let value = word(16, 0x80ff);
    assert_eq!(value.little_endian_bytes(), [0xff, 0x80]);
    assert_eq!(Word::from_little_endian(&[0xff, 0x80]).unwrap(), value);
    assert_eq!(value.signed(), -32_513);
    assert_eq!(word(8, 0x1ff).unsigned(), 0xff);
    assert_eq!(Word::new(7, 0), Err(A0Error::InvalidWordWidth(7)));
}

#[test]
fn word_extension_and_truncation_are_explicit() {
    let positive = word(8, 0x7f);
    let negative = word(8, 0x80);

    assert_eq!(positive.zero_extend(16), Ok(word(16, 0x007f)));
    assert_eq!(negative.zero_extend(16), Ok(word(16, 0x0080)));
    assert_eq!(positive.sign_extend(16), Ok(word(16, 0x007f)));
    assert_eq!(negative.sign_extend(16), Ok(word(16, 0xff80)));
    assert_eq!(word(16, 0xabcd).truncate(8), Ok(word(8, 0xcd)));

    assert_eq!(negative.zero_extend(8), Ok(negative));
    assert_eq!(negative.sign_extend(8), Ok(negative));
    assert_eq!(negative.truncate(8), Ok(negative));
    assert_eq!(
        word(16, 0).zero_extend(8),
        Err(A0Error::InvalidWidthConversion { from: 16, to: 8 })
    );
    assert_eq!(
        word(8, 0).truncate(16),
        Err(A0Error::InvalidWidthConversion { from: 8, to: 16 })
    );
    assert_eq!(negative.sign_extend(12), Err(A0Error::InvalidWordWidth(12)));
}

#[test]
fn canonical_state_encoding_roundtrips_every_outcome() {
    let mut base = State::new(
        16,
        Memory::from_bytes(vec![0x10, 0x20, 0x30, 0x40]),
        word(16, 0x1234),
    )
    .unwrap();
    for (index, register) in base.registers.iter_mut().enumerate() {
        *register = word(16, u64::try_from(index).unwrap() * 0x1111);
    }
    base.conditions = Conditions {
        zero: true,
        negative: false,
        carry: true,
        overflow: true,
    };
    let outcomes = [
        Outcome::Running,
        Outcome::Halted,
        Outcome::Trapped(Trap::MisalignedProgramCounter { pc: 2 }),
        Outcome::Trapped(Trap::IncompleteCodeFetch { pc: 0xfffc }),
        Outcome::Trapped(Trap::IllegalEncoding {
            pc: 4,
            bytes: [0x99, 1, 2, 3],
        }),
        Outcome::Trapped(Trap::DataRange {
            address: 3,
            bytes: 2,
            memory_len: 4,
        }),
    ];
    for outcome in outcomes {
        let mut state = base.clone();
        state.outcome = outcome;
        let encoded = encode_state(&state).unwrap();
        let decoded = decode_state(&encoded).unwrap();
        assert_eq!(decoded, state);
        assert_eq!(encode_state(&decoded).unwrap(), encoded);
    }
}

#[test]
fn canonical_state_decoder_rejects_noncanonical_mutations() {
    let mut state = State::new(
        16,
        Memory::from_bytes(vec![0x10, 0x20, 0x30, 0x40]),
        word(16, 0x1234),
    )
    .unwrap();
    state.outcome = Outcome::Trapped(Trap::DataRange {
        address: 3,
        bytes: 2,
        memory_len: 4,
    });
    let encoded = encode_state(&state).unwrap();
    let mut mutations = Vec::new();

    let mut bad_magic = encoded.clone();
    bad_magic[0] ^= 1;
    mutations.push(bad_magic);
    let mut bad_version = encoded.clone();
    bad_version[4] = 2;
    mutations.push(bad_version);
    let mut bad_width = encoded.clone();
    bad_width[5] = 7;
    mutations.push(bad_width);
    let mut high_register = encoded.clone();
    high_register[16] = 1;
    mutations.push(high_register);
    let mut reserved_condition = encoded.clone();
    reserved_condition[122] = 0x80;
    mutations.push(reserved_condition);
    let mut unknown_outcome = encoded.clone();
    unknown_outcome[123] = 0xff;
    mutations.push(unknown_outcome);
    let mut unknown_trap = encoded.clone();
    unknown_trap[124] = 0xff;
    mutations.push(unknown_trap);
    let mut wrong_trap_memory = encoded.clone();
    let last = wrong_trap_memory.len() - 8;
    wrong_trap_memory[last..].copy_from_slice(&5_u64.to_le_bytes());
    mutations.push(wrong_trap_memory);
    let mut trailing = encoded.clone();
    trailing.push(0);
    mutations.push(trailing);
    mutations.push(encoded[..encoded.len() - 1].to_vec());

    for mutation in mutations {
        assert!(decode_state(&mutation).is_err());
    }

    let mut wrong_register_width = state.clone();
    wrong_register_width.registers[0] = word(8, 0);
    assert!(matches!(
        encode_state(&wrong_register_width),
        Err(A0Error::StateWidthMismatch { .. })
    ));
    let mut wrong_trap_length = state;
    wrong_trap_length.outcome = Outcome::Trapped(Trap::DataRange {
        address: 3,
        bytes: 2,
        memory_len: 5,
    });
    assert!(matches!(
        encode_state(&wrong_trap_length),
        Err(A0Error::InvalidStateEncoding(_))
    ));
}

#[test]
fn decoder_rejects_reserved_and_unused_fields() {
    assert_eq!(
        decode([0x10, 0x0a, 0x03, 0]),
        Ok(Instruction::Add {
            rd: 2,
            rs1: 1,
            rs2: 3
        })
    );
    assert!(matches!(
        decode([0x10, 0x4a, 0x03, 0]),
        Err(A0Error::IllegalEncoding(_))
    ));
    assert!(matches!(
        decode([0x10, 0x0a, 0x0b, 0]),
        Err(A0Error::IllegalEncoding(_))
    ));
    assert!(matches!(
        decode([0x00, 0x0a, 0, 1]),
        Err(A0Error::IllegalEncoding(_))
    ));
    assert!(matches!(
        decode([0x99, 0, 0, 0]),
        Err(A0Error::IllegalEncoding(_))
    ));
}

#[test]
fn encoder_is_canonical_and_rejects_invalid_registers() {
    let instruction = Instruction::Add {
        rd: 2,
        rs1: 1,
        rs2: 3,
    };
    assert_eq!(encode(instruction), Ok([0x10, 0x0a, 0x03, 0]));
    assert_eq!(decode(encode(instruction).unwrap()), Ok(instruction));
    assert_eq!(
        encode(Instruction::Mov { rd: 8, rs1: 0 }),
        Err(A0Error::InvalidRegister(8))
    );
}

#[test]
fn add_writes_destination_flags_and_pc() {
    let code = program(vec![0x10, 0x0a, 0x03, 0]);
    let mut before = state(0);
    before.registers[1] = word(8, 0x7f);
    before.registers[3] = word(8, 1);
    let after = step(&code, &before);
    assert_eq!(after.registers[2].unsigned(), 0x80);
    assert_eq!(after.registers[1], before.registers[1]);
    assert_eq!(after.pc.unsigned(), 4);
    assert_eq!(
        after.conditions,
        Conditions {
            zero: false,
            negative: true,
            carry: false,
            overflow: true
        }
    );
}

#[test]
fn carry_and_no_borrow_are_distinct_contracts() {
    let add = program(vec![0x10, 0x0a, 0x03, 0]);
    let mut before = state(0);
    before.registers[1] = word(8, 0xff);
    before.registers[3] = word(8, 1);
    let added = step(&add, &before);
    assert_eq!(added.registers[2].unsigned(), 0);
    assert!(added.conditions.carry);
    assert!(added.conditions.zero);

    let sub = program(vec![0x11, 0x0a, 0x03, 0]);
    let subtracted = step(&sub, &before);
    assert_eq!(subtracted.registers[2].unsigned(), 0xfe);
    assert!(subtracted.conditions.carry);
}

#[test]
fn store_then_load_is_little_endian() {
    let code = program(vec![0x03, 0x08, 0x02, 1, 0x02, 0x0b, 0, 1]);
    let mut before = state(8);
    before.registers[1] = word(8, 2);
    before.registers[2] = word(8, 0xab);
    let stored = step(&code, &before);
    assert_eq!(stored.memory.byte(3), Some(0xab));
    let loaded = step(&code, &stored);
    assert_eq!(loaded.registers[3].unsigned(), 0xab);
}

#[test]
fn invalid_data_range_traps_without_partial_write() {
    let code = program(vec![0x03, 0x08, 0x02, 0]);
    let mut before = state(2);
    before.registers[1] = word(8, 2);
    before.registers[2] = word(8, 0xab);
    let after = step(&code, &before);
    assert_eq!(after.memory, before.memory);
    assert!(matches!(
        after.outcome,
        Outcome::Trapped(Trap::DataRange { address: 2, .. })
    ));
}

#[test]
fn branch_uses_sequential_pc_as_its_base() {
    let code = program(vec![0x30, 0, 0, 1, 0xff, 0, 0, 0, 0xff, 0, 0, 0]);
    let mut before = state(0);
    before.conditions.zero = true;
    let taken = step(&code, &before);
    assert_eq!(taken.pc.unsigned(), 8);
    before.conditions.zero = false;
    let not_taken = step(&code, &before);
    assert_eq!(not_taken.pc.unsigned(), 4);
}

#[test]
fn halt_and_trap_have_no_successor() {
    let halt = program(vec![0xff, 0, 0, 0]);
    let halted = step(&halt, &state(0));
    assert_eq!(halted.outcome, Outcome::Halted);
    assert_eq!(halted.pc.unsigned(), 0);
    assert_eq!(step(&halt, &halted), halted);

    let illegal = program(vec![0x99, 0, 0, 0]);
    let trapped = step(&illegal, &state(0));
    assert!(matches!(
        trapped.outcome,
        Outcome::Trapped(Trap::IllegalEncoding { .. })
    ));
    assert_eq!(step(&illegal, &trapped), trapped);
}

#[test]
fn bounded_trace_classifies_halt_trap_and_exhaustion() {
    let halt = program(vec![0xff, 0, 0, 0]);
    let halted = run(&halt, state(0), 4);
    assert_eq!(halted.stop, StopReason::Halted);
    assert_eq!(halted.states.len(), 2);

    let jump = program(vec![0x31, 0, 0, 0xff]);
    let exhausted = run(&jump, state(0), 3);
    assert_eq!(exhausted.stop, StopReason::BoundExhausted);
    assert_eq!(exhausted.states.len(), 4);

    let short = program(vec![0x00]);
    let trapped = run(&short, state(0), 1);
    assert_eq!(trapped.stop, StopReason::Trapped);
}

#[test]
fn returned_prefix_is_distinct_and_can_be_resumed() {
    let jump = program(vec![0x31, 0, 0, 0xff]);
    let initial = state(0);

    let zero_bound = run(&jump, initial.clone(), 0);
    assert_eq!(zero_bound.stop, StopReason::BoundExhausted);
    assert_eq!(zero_bound.states.len(), 1);
    assert_eq!(zero_bound.states[0], initial);

    let first = run_prefix(&jump, initial.clone(), 2);
    assert_eq!(first.stop, StopReason::PrefixReturned);
    assert_eq!(first.states.len(), 3);
    assert_eq!(first.states.last().unwrap().outcome, Outcome::Running);

    let second = run_prefix(&jump, first.states.last().unwrap().clone(), 3);
    let whole = run_prefix(&jump, initial, 5);
    let mut concatenated = first.states;
    concatenated.extend(second.states.into_iter().skip(1));
    assert_eq!(concatenated, whole.states);

    let halt = program(vec![0xff, 0, 0, 0]);
    assert_eq!(run_prefix(&halt, state(0), 4).stop, StopReason::Halted);
}

#[test]
fn immediate_is_sign_extended_at_every_supported_width() {
    for width in (8..=64).step_by(8) {
        let code = Program::new(width, word(width, 0), vec![0x01, 0x03, 0, 0x80]).unwrap();
        let before = State::new(width, Memory::zeroed(0), word(width, 0)).unwrap();
        let after = step(&code, &before);
        assert_eq!(after.registers[3].signed(), -128, "width {width}");
        assert_eq!(after.conditions, Conditions::default(), "width {width}");
    }
}

#[test]
fn all_data_movement_and_logic_instructions_obey_the_contract() {
    let mut before = state(0);
    before.registers[1] = word(8, 0b1010_0101);
    before.registers[2] = word(8, 0b1100_0011);
    before.conditions = Conditions {
        zero: true,
        negative: true,
        carry: true,
        overflow: true,
    };

    let moved = step(&program(vec![0x00, 0x0b, 0, 0]), &before);
    assert_eq!(moved.registers[3], before.registers[1]);
    assert_eq!(moved.conditions, before.conditions);

    let cases = [
        ([0x12, 0x0b, 0x02, 0], 0x81),
        ([0x13, 0x0b, 0x02, 0], 0xe7),
        ([0x14, 0x0b, 0x02, 0], 0x66),
        ([0x15, 0x0b, 0, 0], 0x5a),
    ];
    for (bytes, expected) in cases {
        let after = step(&program(bytes.to_vec()), &before);
        assert_eq!(after.registers[3].unsigned(), expected);
        assert_eq!(
            after.conditions,
            Conditions {
                zero: false,
                negative: expected & 0x80 != 0,
                carry: false,
                overflow: false,
            }
        );
    }
}

#[test]
fn shifts_cover_zero_count_last_bit_and_sign_extension() {
    let cases = [
        ([0x18, 0x0b, 0x02, 0], 0b1001_0100, false),
        ([0x19, 0x0b, 0x02, 0], 0b0010_1001, false),
        ([0x1a, 0x0b, 0x02, 0], 0b1110_1001, false),
    ];
    for (bytes, expected, carry) in cases {
        let mut before = state(0);
        before.registers[1] = word(8, 0b1010_0101);
        before.registers[2] = word(8, 2);
        let after = step(&program(bytes.to_vec()), &before);
        assert_eq!(after.registers[3].unsigned(), expected);
        assert_eq!(after.conditions.carry, carry);
        assert_eq!(after.conditions.negative, expected & 0x80 != 0);
        assert!(!after.conditions.overflow);
    }

    let mut before = state(0);
    before.registers[1] = word(8, 0x80);
    before.registers[2] = word(8, 8);
    before.conditions.carry = true;
    let after = step(&program(vec![0x1a, 0x0b, 0x02, 0]), &before);
    assert_eq!(after.registers[3].unsigned(), 0x80);
    assert!(!after.conditions.carry);
}

#[test]
fn add_and_sub_flags_are_exhaustive_for_eight_bit_words() {
    let add = program(vec![0x10, 0x0a, 0x03, 0]);
    let sub = program(vec![0x11, 0x0a, 0x03, 0]);
    for lhs in 0_u16..=255 {
        for rhs in 0_u16..=255 {
            let mut before = state(0);
            before.registers[1] = word(8, u64::from(lhs));
            before.registers[3] = word(8, u64::from(rhs));

            let added = step(&add, &before);
            let add_result = lhs.wrapping_add(rhs) & 0xff;
            let add_overflow = (lhs & 0x80) == (rhs & 0x80) && (add_result & 0x80) != (lhs & 0x80);
            assert_eq!(added.registers[2].unsigned(), u64::from(add_result));
            assert_eq!(added.conditions.zero, add_result == 0);
            assert_eq!(added.conditions.negative, add_result & 0x80 != 0);
            assert_eq!(added.conditions.carry, lhs + rhs >= 256);
            assert_eq!(added.conditions.overflow, add_overflow);

            let subtracted = step(&sub, &before);
            let sub_result = lhs.wrapping_sub(rhs) & 0xff;
            let sub_overflow = (lhs & 0x80) != (rhs & 0x80) && (sub_result & 0x80) != (lhs & 0x80);
            assert_eq!(subtracted.registers[2].unsigned(), u64::from(sub_result));
            assert_eq!(subtracted.conditions.zero, sub_result == 0);
            assert_eq!(subtracted.conditions.negative, sub_result & 0x80 != 0);
            assert_eq!(subtracted.conditions.carry, lhs >= rhs);
            assert_eq!(subtracted.conditions.overflow, sub_overflow);
        }
    }
}

#[test]
fn compare_updates_flags_without_writing_registers() {
    let mut before = state(0);
    before.registers[1] = word(8, 0x80);
    before.registers[2] = word(8, 1);
    let after = step(&program(vec![0x20, 0x08, 0x02, 0]), &before);
    assert_eq!(after.registers, before.registers);
    assert!(after.conditions.overflow);
    assert!(after.conditions.carry);
    assert_eq!(after.pc.unsigned(), 4);
}

#[test]
fn every_branch_condition_has_taken_and_untaken_controls() {
    let witnesses = [
        (
            0_u8,
            Conditions {
                zero: true,
                ..Conditions::default()
            },
        ),
        (
            1,
            Conditions {
                zero: false,
                ..Conditions::default()
            },
        ),
        (
            2,
            Conditions {
                negative: true,
                overflow: false,
                ..Conditions::default()
            },
        ),
        (
            3,
            Conditions {
                negative: true,
                overflow: true,
                ..Conditions::default()
            },
        ),
        (
            4,
            Conditions {
                carry: false,
                ..Conditions::default()
            },
        ),
        (
            5,
            Conditions {
                carry: true,
                ..Conditions::default()
            },
        ),
        (
            6,
            Conditions {
                carry: true,
                zero: false,
                ..Conditions::default()
            },
        ),
        (
            7,
            Conditions {
                carry: false,
                zero: false,
                ..Conditions::default()
            },
        ),
    ];
    for (condition, flags) in witnesses {
        let branch = program(vec![0x30, 0, condition << 3, 1]);
        let mut before = state(0);
        before.conditions = flags;
        assert_eq!(
            step(&branch, &before).pc.unsigned(),
            8,
            "condition {condition}"
        );

        before.conditions = Conditions {
            zero: !flags.zero,
            negative: !flags.negative,
            carry: !flags.carry,
            overflow: flags.overflow,
        };
        if condition == 3 {
            before.conditions.overflow = !before.conditions.negative;
        } else if condition == 7 {
            before.conditions.carry = true;
            before.conditions.zero = false;
        }
        assert_eq!(
            step(&branch, &before).pc.unsigned(),
            4,
            "condition {condition}"
        );
    }
}

#[test]
fn sixteen_bit_memory_access_is_little_endian_and_may_be_unaligned() {
    let code = Program::new(16, word(16, 0), vec![0x03, 0x08, 0x02, 1, 0x02, 0x0b, 0, 1]).unwrap();
    let mut before = State::new(16, Memory::zeroed(5), word(16, 0)).unwrap();
    before.registers[1] = word(16, 0);
    before.registers[2] = word(16, 0xabcd);
    let stored = step(&code, &before);
    assert_eq!(stored.memory.byte(1), Some(0xcd));
    assert_eq!(stored.memory.byte(2), Some(0xab));
    let loaded = step(&code, &stored);
    assert_eq!(loaded.registers[3].unsigned(), 0xabcd);
}

#[test]
fn sparse_memory_checks_each_wrapped_word_address_atomically() {
    let memory = Memory::from_entries(vec![(u64::from(u16::MAX), 0), (0, 0), (7, 0x77)]).unwrap();
    let mut before = State::new(16, memory, word(16, 0)).unwrap();
    before.registers[1] = word(16, u64::from(u16::MAX));
    before.registers[2] = word(16, 0xabcd);
    let store = Program::new(16, word(16, 0), vec![0x03, 0x08, 0x02, 0]).unwrap();
    let stored = step(&store, &before);
    assert_eq!(stored.memory.byte_at(u64::from(u16::MAX)), Some(0xcd));
    assert_eq!(stored.memory.byte_at(0), Some(0xab));
    assert_eq!(stored.memory.byte_at(7), Some(0x77));

    let mut missing = before.clone();
    missing.memory = Memory::from_entries(vec![(u64::from(u16::MAX), 0), (7, 0x77)]).unwrap();
    let trapped = step(&store, &missing);
    assert!(matches!(
        trapped.outcome,
        Outcome::Trapped(Trap::DataRange { .. })
    ));
    assert_eq!(trapped.memory, missing.memory);

    assert_eq!(
        Memory::from_entries(vec![(1, 0), (1, 1)]),
        Err(A0Error::DuplicateMemoryAddress(1))
    );
    assert_eq!(
        State::new(8, Memory::from_entries(vec![(256, 0)]).unwrap(), word(8, 0)),
        Err(A0Error::InvalidMemoryAddress {
            width: 8,
            address: 256
        })
    );
}

#[test]
fn fetch_traps_are_precise_and_code_can_cross_word_wrap() {
    let code = program(vec![0xff, 0, 0, 0]);
    let misaligned = State::new(8, Memory::zeroed(0), word(8, 2)).unwrap();
    assert_eq!(
        step(&code, &misaligned).outcome,
        Outcome::Trapped(Trap::MisalignedProgramCounter { pc: 2 })
    );

    let incomplete = State::new(8, Memory::zeroed(0), word(8, 4)).unwrap();
    assert_eq!(
        step(&code, &incomplete).outcome,
        Outcome::Trapped(Trap::IncompleteCodeFetch { pc: 4 })
    );

    let wrapping = Program::new(8, word(8, 252), vec![0x31, 0, 0, 0, 0xff, 0, 0, 0]).unwrap();
    let initial = State::new(8, Memory::zeroed(0), word(8, 252)).unwrap();
    let trace = run(&wrapping, initial, 2);
    assert_eq!(trace.stop, StopReason::Halted);
    assert_eq!(trace.states[1].pc.unsigned(), 0);
}

#[test]
fn observations_are_canonical_pure_and_range_checked() {
    let mut left = state(4);
    left.registers[0] = word(8, 7);
    left.registers[3] = word(8, 19);
    left.memory = Memory::from_bytes(vec![0xaa, 0xbb, 0xcc, 0xdd]);
    let mut right = left.clone();
    right.registers[3] = word(8, 20);

    let result = Observation::new(vec![0], vec![]).unwrap().with_outcome();
    assert_eq!(result.apply(&left).unwrap(), result.apply(&right).unwrap());

    let broad = Observation::new(
        vec![3, 0],
        vec![
            MemorySpan { start: 2, len: 2 },
            MemorySpan { start: 0, len: 1 },
        ],
    )
    .unwrap()
    .with_program_counter()
    .with_conditions()
    .with_outcome();
    let before = left.clone();
    let observed = broad.apply(&left).unwrap();
    assert_eq!(left, before, "observation must not mutate complete state");
    assert_eq!(observed.registers[0].index, 0);
    assert_eq!(observed.registers[1].index, 3);
    assert_eq!(observed.memory[0].start, 0);
    assert_eq!(observed.memory[1].bytes, vec![0xcc, 0xdd]);
    assert_ne!(observed, broad.apply(&right).unwrap());

    assert_eq!(
        Observation::new(vec![0, 0], vec![]),
        Err(ObservationError::DuplicateRegister(0))
    );
    assert!(matches!(
        Observation::new(
            vec![],
            vec![
                MemorySpan { start: 0, len: 2 },
                MemorySpan { start: 1, len: 2 }
            ]
        ),
        Err(ObservationError::OverlappingMemorySpans { .. })
    ));
    let out_of_range = Observation::new(vec![], vec![MemorySpan { start: 3, len: 2 }]).unwrap();
    assert!(matches!(
        out_of_range.apply(&left),
        Err(ObservationError::MemoryRange { .. })
    ));
}

#[test]
#[allow(clippy::too_many_lines)]
fn every_instruction_exposes_implicit_effects_without_duplicates() {
    use StateComponent::{
        Conditions as C, Memory as M, Outcome as O, ProgramCounter as P, Register as R,
    };

    let mut before = state(16);
    before.registers[1] = word(8, 5);
    let cases = [
        (
            Instruction::Mov { rd: 3, rs1: 1 },
            vec![P, O, R(1)],
            vec![P, R(3)],
        ),
        (
            Instruction::MovImmediate {
                rd: 3,
                immediate: -1,
            },
            vec![P, O],
            vec![P, R(3)],
        ),
        (
            Instruction::Load {
                rd: 3,
                base: 1,
                offset: -1,
            },
            vec![
                P,
                O,
                R(1),
                M {
                    address: word(8, 4),
                    bytes: 1,
                },
            ],
            vec![P, R(3), O],
        ),
        (
            Instruction::Store {
                base: 1,
                source: 2,
                offset: 1,
            },
            vec![P, O, R(1), R(2)],
            vec![
                P,
                M {
                    address: word(8, 6),
                    bytes: 1,
                },
                O,
            ],
        ),
        (
            Instruction::Add {
                rd: 3,
                rs1: 1,
                rs2: 2,
            },
            vec![P, O, R(1), R(2)],
            vec![P, R(3), C],
        ),
        (
            Instruction::Sub {
                rd: 3,
                rs1: 1,
                rs2: 2,
            },
            vec![P, O, R(1), R(2)],
            vec![P, R(3), C],
        ),
        (
            Instruction::And {
                rd: 3,
                rs1: 1,
                rs2: 2,
            },
            vec![P, O, R(1), R(2)],
            vec![P, R(3), C],
        ),
        (
            Instruction::Or {
                rd: 3,
                rs1: 1,
                rs2: 2,
            },
            vec![P, O, R(1), R(2)],
            vec![P, R(3), C],
        ),
        (
            Instruction::Xor {
                rd: 3,
                rs1: 1,
                rs2: 2,
            },
            vec![P, O, R(1), R(2)],
            vec![P, R(3), C],
        ),
        (
            Instruction::Not { rd: 3, rs1: 1 },
            vec![P, O, R(1)],
            vec![P, R(3), C],
        ),
        (
            Instruction::ShiftLeft {
                rd: 3,
                rs1: 1,
                rs2: 2,
            },
            vec![P, O, R(1), R(2)],
            vec![P, R(3), C],
        ),
        (
            Instruction::ShiftRight {
                rd: 3,
                rs1: 1,
                rs2: 2,
            },
            vec![P, O, R(1), R(2)],
            vec![P, R(3), C],
        ),
        (
            Instruction::ArithmeticShiftRight {
                rd: 3,
                rs1: 1,
                rs2: 2,
            },
            vec![P, O, R(1), R(2)],
            vec![P, R(3), C],
        ),
        (
            Instruction::Compare { rs1: 1, rs2: 2 },
            vec![P, O, R(1), R(2)],
            vec![P, C],
        ),
        (
            Instruction::Branch {
                condition: axeyum_machine::a0::BranchCondition::Eq,
                offset: 1,
            },
            vec![P, O, C],
            vec![P],
        ),
        (Instruction::Jump { offset: 1 }, vec![P, O], vec![P]),
        (Instruction::Halt, vec![O], vec![O]),
    ];
    for (instruction, reads, writes) in cases {
        let effects = instruction.effects(&before);
        assert_eq!(effects.reads, reads, "reads for {instruction:?}");
        assert_eq!(effects.writes, writes, "writes for {instruction:?}");
        for (index, component) in effects.reads.iter().enumerate() {
            assert!(!effects.reads[..index].contains(component));
        }
        for (index, component) in effects.writes.iter().enumerate() {
            assert!(!effects.writes[..index].contains(component));
        }
    }

    let aliased = Instruction::Add {
        rd: 1,
        rs1: 1,
        rs2: 1,
    }
    .effects(&before);
    assert_eq!(aliased.reads, vec![P, O, R(1)]);
    assert_eq!(aliased.writes, vec![P, R(1), C]);
}
