//! Direct checks for the Chapter 15 three-machine XOR relation.

use axeyum_machine::xor_reduction::{
    A0_XOR_REDUCTION_BYTES, RV64_XOR_REDUCTION_BYTES, X64_XOR_REDUCTION_BYTES, XorReductionClause,
    XorReductionError, XorReductionPoint, XorReductionPrograms, simulate_xor_reduction,
    simulate_xor_reduction_with_programs,
};

#[test]
fn exact_three_machine_programs_replay_edge_shaped_cases() {
    let cases: &[&[u64]] = &[
        &[],
        &[0],
        &[u64::MAX],
        &[0x8000_0000_0000_0000],
        &[0x0102_0304_0506_0708],
        &[0xfeed_face_cafe_beef, 0xfeed_face_cafe_beef],
        &[0x0f0f, 0x00ff],
        &[0, u64::MAX, 0x8000_0000_0000_0000],
    ];
    for words in cases {
        let simulation = simulate_xor_reduction(words).unwrap();
        assert!(
            simulation
                .snapshots
                .iter()
                .all(|item| item.relation.holds())
        );
        assert_eq!(
            simulation.expected,
            words.iter().copied().fold(0, core::ops::BitXor::bitxor)
        );
        assert_eq!(simulation.a0_steps, 6 + 5 * words.len() as u64);
        assert_eq!(simulation.rv64_steps, 4 + 5 * words.len() as u64);
        assert_eq!(simulation.x64_steps, 4 + 4 * words.len() as u64);
    }
}

#[test]
fn exact_printed_byte_lengths_are_stable() {
    assert_eq!(A0_XOR_REDUCTION_BYTES.len(), 44);
    assert_eq!(RV64_XOR_REDUCTION_BYTES.len(), 36);
    assert_eq!(X64_XOR_REDUCTION_BYTES.len(), 21);
}

#[test]
fn wrong_rv64_pointer_step_fails_at_the_next_loop_head() {
    let programs = XorReductionPrograms::with_rv64_pointer_step(1).unwrap();
    assert_eq!(
        simulate_xor_reduction_with_programs(&[0x0f0f, 0x00ff], &programs),
        Err(XorReductionError::FailedClause {
            point: XorReductionPoint::LoopHead { iteration: 1 },
            clause: XorReductionClause::Pointer,
        })
    );
}

#[test]
fn harness_rejects_input_that_would_overlap_its_return_stack() {
    assert_eq!(
        simulate_xor_reduction(&vec![0; 97]),
        Err(XorReductionError::InputTooLong {
            words: 97,
            maximum: 96,
        })
    );
}
