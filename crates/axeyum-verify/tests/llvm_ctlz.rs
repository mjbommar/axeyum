//! Checked LLVM `ctlz` and call-result range semantics (T5.1.2, ADR-0327).

use axeyum_ir::{Assignment, TermArena, TermId, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};
use axeyum_verify::reflect::llvm::checked::{
    DefinedValue, reflect_scalar_checked, reflect_scalar_into_checked,
};

fn scalar_input(width: u32, value: u128) -> Value {
    if width == 1 {
        Value::Bool(value != 0)
    } else {
        Value::Bv { width, value }
    }
}

fn scalar_value(value: Value) -> u128 {
    match value {
        Value::Bool(value) => u128::from(value),
        Value::Bv { value, .. } => value,
        other => panic!("expected scalar value, got {other:?}"),
    }
}

fn native_ctlz(value: u128, width: u32) -> u128 {
    u128::from(value.leading_zeros() - (u128::BITS - width))
}

fn ctlz_source(width: u32, zero_is_poison: bool, range: Option<(u128, u128)>) -> String {
    let range = range.map_or_else(String::new, |(lower, upper)| {
        format!("range(i{width} {lower}, {upper}) ")
    });
    format!(
        "define i{width} @f(i{width} %x) {{\n%r = tail call {range}i{width} @llvm.ctlz.i{width}(i{width} %x, i1 {zero_is_poison})\nret i{width} %r\n}}\n"
    )
}

fn evaluate(
    reflected: &axeyum_verify::reflect::llvm::checked::CheckedReflected,
    value: u128,
) -> (u128, bool) {
    let (.., symbol, width) = reflected.params[0];
    let mut assignment = Assignment::new();
    assignment.set(symbol, scalar_input(width, value));
    let actual_value =
        scalar_value(eval(&reflected.arena, reflected.result.value, &assignment).unwrap());
    let Value::Bool(defined) =
        eval(&reflected.arena, reflected.result.defined, &assignment).unwrap()
    else {
        panic!("definedness must be Boolean");
    };
    (actual_value, defined)
}

#[test]
fn widths_one_through_eight_match_an_independent_native_oracle_exhaustively() {
    for width in 1..=8 {
        let ranges = if width == 1 {
            vec![None, Some((0, 1))]
        } else {
            vec![
                None,
                Some((0, u128::from(width + 1))),
                Some((1, u128::from(width + 1))),
            ]
        };
        for zero_is_poison in [false, true] {
            for range in &ranges {
                let source = ctlz_source(width, zero_is_poison, *range);
                let reflected = reflect_scalar_checked(&source).unwrap();
                for input in 0..(1_u128 << width) {
                    let expected = native_ctlz(input, width);
                    let range_defined =
                        range.is_none_or(|(lower, upper)| lower <= expected && expected < upper);
                    let expected_defined = (!zero_is_poison || input != 0) && range_defined;
                    let (actual, actual_defined) = evaluate(&reflected, input);
                    assert_eq!(actual, expected, "i{width} input={input} range={range:?}");
                    assert_eq!(
                        actual_defined, expected_defined,
                        "i{width} input={input} poison={zero_is_poison} range={range:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn deterministic_wide_rows_cover_boundaries_and_seeded_values() {
    let mut seed = 0x9e37_79b9_7f4a_7c15_u64;
    for width in [32, 64] {
        let mut rows = vec![
            0,
            1,
            2,
            3,
            (1_u128 << (width - 1)) - 1,
            1_u128 << (width - 1),
        ];
        rows.push((1_u128 << width) - 1);
        for _ in 0..128 {
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            rows.push(u128::from(seed) & ((1_u128 << width) - 1));
        }
        for zero_is_poison in [false, true] {
            let reflected = reflect_scalar_checked(&ctlz_source(
                width,
                zero_is_poison,
                Some((0, u128::from(width + 1))),
            ))
            .unwrap();
            for &input in &rows {
                let (actual, defined) = evaluate(&reflected, input);
                assert_eq!(actual, native_ctlz(input, width), "i{width} input={input}");
                assert_eq!(defined, !zero_is_poison || input != 0);
            }
        }
    }
}

fn bv_const(arena: &mut TermArena, width: u32, value: u128) -> TermId {
    arena.bv_const(width, value).unwrap()
}

/// Independent threshold-partition specification: progressively narrower
/// unsigned intervals overwrite the count from one through the full width.
fn threshold_ctlz(
    arena: &mut TermArena,
    input: TermId,
    width: u32,
    mutation: Option<(u32, u128)>,
) -> TermId {
    let mut count = bv_const(arena, width, 0);
    for leading_zeros in 1..=width {
        let threshold = 1_u128 << (width - leading_zeros);
        let threshold = bv_const(arena, width, threshold);
        let below = arena.bv_ult(input, threshold).unwrap();
        let encoded = mutation
            .filter(|(partition, _)| *partition == leading_zeros)
            .map_or(u128::from(leading_zeros), |(_, replacement)| replacement);
        let encoded = bv_const(arena, width, encoded);
        count = arena.ite(below, encoded, count).unwrap();
    }
    count
}

fn prove_outcome(arena: &mut TermArena, goal: TermId) -> ProofOutcome {
    prove(arena, &[], goal, &SolverConfig::default()).unwrap()
}

fn reflected_ctlz(arena: &mut TermArena, width: u32, source: &str) -> (TermId, DefinedValue) {
    let input = arena.bv_var("x", width).unwrap();
    let reflected = reflect_scalar_into_checked(arena, &[input], source).unwrap();
    (input, reflected)
}

#[test]
fn thirty_two_and_sixty_four_bit_values_prove_against_threshold_partitions() {
    for width in [32, 64] {
        let source = ctlz_source(width, false, Some((0, u128::from(width + 1))));
        let mut arena = TermArena::new();
        let (input, reflected) = reflected_ctlz(&mut arena, width, &source);
        let expected = threshold_ctlz(&mut arena, input, width, None);
        let same = arena.eq(reflected.value, expected).unwrap();
        assert!(
            matches!(prove_outcome(&mut arena, same), ProofOutcome::Proved(_)),
            "i{width} ctlz must equal the independent threshold partition"
        );
        assert!(matches!(
            prove_outcome(&mut arena, reflected.defined),
            ProofOutcome::Proved(_)
        ));
    }
}

#[test]
fn zero_index_range_and_high_partition_mutations_replay() {
    let width = 32;
    let source = ctlz_source(width, false, Some((0, 33)));
    let mut arena = TermArena::new();
    let (input, reflected) = reflected_ctlz(&mut arena, width, &source);
    let expected = threshold_ctlz(&mut arena, input, width, None);

    let zero = bv_const(&mut arena, width, 0);
    let is_zero = arena.eq(input, zero).unwrap();
    let wrong_zero_value = bv_const(&mut arena, width, 0);
    let wrong_zero = arena.ite(is_zero, wrong_zero_value, expected).unwrap();
    let zero_goal = arena.eq(reflected.value, wrong_zero).unwrap();
    assert!(matches!(
        prove_outcome(&mut arena, zero_goal),
        ProofOutcome::Disproved(_)
    ));

    let index_mutation = (7, 8);
    let mutated = threshold_ctlz(&mut arena, input, width, Some(index_mutation));
    let goal = arena.eq(reflected.value, mutated).unwrap();
    assert!(
        matches!(prove_outcome(&mut arena, goal), ProofOutcome::Disproved(_)),
        "mutation {index_mutation:?} must have a replayed countermodel"
    );

    let high_threshold = bv_const(&mut arena, width, 1_u128 << (width - 1));
    let in_high_partition = arena.bv_uge(input, high_threshold).unwrap();
    let wrong_high_count = bv_const(&mut arena, width, 1);
    let wrong_high_partition = arena
        .ite(in_high_partition, wrong_high_count, expected)
        .unwrap();
    let high_goal = arena.eq(reflected.value, wrong_high_partition).unwrap();
    assert!(matches!(
        prove_outcome(&mut arena, high_goal),
        ProofOutcome::Disproved(_)
    ));

    let ranged = ctlz_source(width, false, Some((1, 33)));
    let mut range_arena = TermArena::new();
    let (_, ranged) = reflected_ctlz(&mut range_arena, width, &ranged);
    assert!(matches!(
        prove_outcome(&mut range_arena, ranged.defined),
        ProofOutcome::Disproved(_)
    ));
}

#[test]
fn poison_from_zero_is_not_eager_across_select() {
    let source = r"
define i32 @log2(i32 %x) {
  %iszero = icmp eq i32 %x, 0
  %count = tail call range(i32 0, 33) i32 @llvm.ctlz.i32(i32 %x, i1 true)
  %index = xor i32 %count, 31
  %result = select i1 %iszero, i32 0, i32 %index
  ret i32 %result
}
";
    let mut reflected = reflect_scalar_checked(source).unwrap();
    assert!(matches!(
        prove_outcome(&mut reflected.arena, reflected.result.defined),
        ProofOutcome::Proved(_)
    ));
    assert_eq!(evaluate(&reflected, 0), (0, true));
    for input in [1, 2, 3, 4, 7, 8, u128::from(u32::MAX)] {
        assert_eq!(
            evaluate(&reflected, input),
            (u128::from(u32::try_from(input).unwrap().ilog2()), true)
        );
    }
}

#[test]
fn result_range_also_applies_to_existing_minmax_intrinsics() {
    let source = "define i8 @f(i8 %x) {\n%r = call range(i8 2, 5) i8 @llvm.umin.i8(i8 %x, i8 7)\nret i8 %r\n}\n";
    let reflected = reflect_scalar_checked(source).unwrap();
    assert_eq!(evaluate(&reflected, 1), (1, false));
    assert_eq!(evaluate(&reflected, 2), (2, true));
    assert_eq!(evaluate(&reflected, 4), (4, true));
    assert_eq!(evaluate(&reflected, 5), (5, false));
}
