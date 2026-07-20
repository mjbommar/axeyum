//! Source-independent scalar specification and exhaustive-fuzz cells for T5.1.6.

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};
use axeyum_verify::reflect::llvm::checked::reflect_scalar_into_checked;
use axeyum_verify::reflect::mir::checked::{MirMemoryConfig, reflect_bounded_memory_checked};

const WIDTH: u32 = 4;
type MirScalarCase = (&'static str, fn(u128) -> u128);

#[derive(Clone, Copy)]
struct Expected {
    defined: bool,
    value: u128,
}

fn mask(width: u32) -> u128 {
    (1_u128 << width) - 1
}

fn signed(value: u128, width: u32) -> i128 {
    let value = value & mask(width);
    let sign = 1_u128 << (width - 1);
    if value & sign == 0 {
        value.cast_signed()
    } else {
        value.cast_signed() - (1_i128 << width)
    }
}

fn bits(value: i128, width: u32) -> u128 {
    value.cast_unsigned() & mask(width)
}

fn scalar_value(value: &Value) -> u128 {
    match value {
        Value::Bool(value) => u128::from(*value),
        Value::Bv { value, .. } => *value,
        other => panic!("expected scalar value, got {other:?}"),
    }
}

fn scalar_const(arena: &mut TermArena, width: u32, value: u128) -> TermId {
    if width == 1 {
        arena.bool_const(value & 1 == 1)
    } else {
        arena.bv_const(width, value).unwrap()
    }
}

fn input_value(width: u32, value: u128) -> Value {
    if width == 1 {
        Value::Bool(value & 1 == 1)
    } else {
        Value::Bv { width, value }
    }
}

fn tuples(widths: &[u32]) -> Vec<Vec<u128>> {
    fn extend(widths: &[u32], prefix: &mut Vec<u128>, result: &mut Vec<Vec<u128>>) {
        if let Some((&width, tail)) = widths.split_first() {
            for value in 0..(1_u128 << width) {
                prefix.push(value);
                extend(tail, prefix, result);
                prefix.pop();
            }
        } else {
            result.push(prefix.clone());
        }
    }

    let mut result = Vec::new();
    extend(widths, &mut Vec::new(), &mut result);
    result
}

fn prove_goal(arena: &mut TermArena, goal: TermId, label: &str) {
    let outcome = prove(arena, &[], goal, &SolverConfig::default())
        .expect("semantics-gate proof must not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "{label}: specification must be proved, got {outcome:?}"
    );
}

fn check_scalar(
    label: &str,
    ll: &str,
    input_widths: &[u32],
    output_width: u32,
    oracle: impl Fn(&[u128]) -> Expected,
) {
    let mut arena = TermArena::new();
    let mut symbols = Vec::new();
    let mut inputs = Vec::new();
    for (index, &width) in input_widths.iter().enumerate() {
        let sort = if width == 1 {
            Sort::Bool
        } else {
            Sort::BitVec(width)
        };
        let name = format!("input_{index}");
        let symbol = arena.declare(&name, sort).unwrap();
        symbols.push(symbol);
        inputs.push(arena.var(symbol));
    }
    let reflected = reflect_scalar_into_checked(&mut arena, &inputs, ll)
        .unwrap_or_else(|error| panic!("{label}: checked reflection failed: {error}"));
    assert_eq!(reflected.width, output_width, "{label}: result width");

    let rows = tuples(input_widths)
        .into_iter()
        .map(|values| {
            let expected = oracle(&values);
            let mut assignment = Assignment::new();
            for ((&symbol, &width), &value) in symbols.iter().zip(input_widths).zip(&values) {
                assignment.set(symbol, input_value(width, value));
            }
            let actual_defined = eval(&arena, reflected.defined, &assignment).unwrap();
            assert_eq!(
                actual_defined,
                Value::Bool(expected.defined),
                "{label}: definedness disagrees at {values:?}"
            );
            if expected.defined {
                let actual = eval(&arena, reflected.value, &assignment).unwrap();
                assert_eq!(
                    scalar_value(&actual),
                    expected.value & mask(output_width),
                    "{label}: value disagrees at {values:?}"
                );
            }
            (values, expected)
        })
        .collect::<Vec<_>>();

    // Build an independent finite truth-table specification in the term arena,
    // then prove the reflected value/definedness equivalent for every input.
    let mut expected_defined = arena.bool_const(false);
    let mut expected_value = scalar_const(&mut arena, output_width, 0);
    for (values, expected) in rows.iter().rev() {
        let mut condition = arena.bool_const(true);
        for ((&input, &width), &value) in inputs.iter().zip(input_widths).zip(values) {
            let constant = scalar_const(&mut arena, width, value);
            let same = arena.eq(input, constant).unwrap();
            condition = arena.and(condition, same).unwrap();
        }
        let defined = arena.bool_const(expected.defined);
        expected_defined = arena.ite(condition, defined, expected_defined).unwrap();
        let value = scalar_const(&mut arena, output_width, expected.value);
        expected_value = arena.ite(condition, value, expected_value).unwrap();
    }

    let defined_same = arena.eq(reflected.defined, expected_defined).unwrap();
    prove_goal(&mut arena, defined_same, &format!("{label} definedness"));
    let value_same = arena.eq(reflected.value, expected_value).unwrap();
    let guarded_value = arena.implies(expected_defined, value_same).unwrap();
    prove_goal(&mut arena, guarded_value, &format!("{label} value"));
}

fn binary_expected(opcode: &str, lhs: u128, rhs: u128) -> Expected {
    let modulus_mask = mask(WIDTH);
    let shift_defined = rhs < u128::from(WIDTH);
    let nonzero = rhs != 0;
    let signed_overflow =
        signed(lhs, WIDTH) == -(1_i128 << (WIDTH - 1)) && signed(rhs, WIDTH) == -1;
    let (defined, value) = match opcode {
        "add" => (true, lhs.wrapping_add(rhs)),
        "sub" => (true, lhs.wrapping_sub(rhs)),
        "mul" => (true, lhs.wrapping_mul(rhs)),
        "and" => (true, lhs & rhs),
        "or" => (true, lhs | rhs),
        "xor" => (true, lhs ^ rhs),
        "shl" => (shift_defined, if shift_defined { lhs << rhs } else { 0 }),
        "lshr" => (shift_defined, if shift_defined { lhs >> rhs } else { 0 }),
        "ashr" => (
            shift_defined,
            if shift_defined {
                bits(signed(lhs, WIDTH) >> rhs, WIDTH)
            } else {
                0
            },
        ),
        "udiv" => (nonzero, if nonzero { lhs / rhs } else { 0 }),
        "urem" => (nonzero, if nonzero { lhs % rhs } else { 0 }),
        "sdiv" => (
            nonzero && !signed_overflow,
            if nonzero {
                bits(signed(lhs, WIDTH) / signed(rhs, WIDTH), WIDTH)
            } else {
                0
            },
        ),
        "srem" => (
            nonzero && !signed_overflow,
            if nonzero {
                bits(signed(lhs, WIDTH) % signed(rhs, WIDTH), WIDTH)
            } else {
                0
            },
        ),
        _ => panic!("unknown binary opcode {opcode}"),
    };
    Expected {
        defined,
        value: value & modulus_mask,
    }
}

#[test]
fn llvm_binary_opcode_specs_and_exhaustive_fuzz() {
    for opcode in [
        "add", "sub", "mul", "and", "or", "xor", "shl", "lshr", "ashr", "udiv", "sdiv", "urem",
        "srem",
    ] {
        let ll = format!(
            "define i{WIDTH} @f(i{WIDTH} %a, i{WIDTH} %b) {{\n%r = {opcode} i{WIDTH} %a, %b\nret i{WIDTH} %r\n}}\n"
        );
        check_scalar(opcode, &ll, &[WIDTH, WIDTH], WIDTH, |values| {
            binary_expected(opcode, values[0], values[1])
        });
    }
}

fn predicate_expected(predicate: &str, lhs: u128, rhs: u128) -> bool {
    match predicate {
        "eq" => lhs == rhs,
        "ne" => lhs != rhs,
        "ult" => lhs < rhs,
        "ule" => lhs <= rhs,
        "ugt" => lhs > rhs,
        "uge" => lhs >= rhs,
        "slt" => signed(lhs, WIDTH) < signed(rhs, WIDTH),
        "sle" => signed(lhs, WIDTH) <= signed(rhs, WIDTH),
        "sgt" => signed(lhs, WIDTH) > signed(rhs, WIDTH),
        "sge" => signed(lhs, WIDTH) >= signed(rhs, WIDTH),
        _ => panic!("unknown predicate {predicate}"),
    }
}

#[test]
fn llvm_integer_predicate_specs_and_exhaustive_fuzz() {
    for predicate in [
        "eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge",
    ] {
        let ll = format!(
            "define i1 @f(i{WIDTH} %a, i{WIDTH} %b) {{\n%r = icmp {predicate} i{WIDTH} %a, %b\nret i1 %r\n}}\n"
        );
        check_scalar(predicate, &ll, &[WIDTH, WIDTH], 1, |values| Expected {
            defined: true,
            value: u128::from(predicate_expected(predicate, values[0], values[1])),
        });
    }
}

#[test]
fn llvm_cast_and_intrinsic_specs_and_exhaustive_fuzz() {
    let casts = [
        ("zext", 4, 6, false),
        ("sext", 4, 6, true),
        ("trunc", 6, 4, false),
    ];
    for (opcode, source_width, target_width, sign_extend) in casts {
        let ll = format!(
            "define i{target_width} @f(i{source_width} %a) {{\n%r = {opcode} i{source_width} %a to i{target_width}\nret i{target_width} %r\n}}\n"
        );
        check_scalar(opcode, &ll, &[source_width], target_width, |values| {
            let value = if sign_extend {
                bits(signed(values[0], source_width), target_width)
            } else {
                values[0] & mask(target_width)
            };
            Expected {
                defined: true,
                value,
            }
        });
    }

    for intrinsic in ["umin", "umax"] {
        let ll = format!(
            "define i{WIDTH} @f(i{WIDTH} %a, i{WIDTH} %b) {{\n%r = call i{WIDTH} @llvm.{intrinsic}.i{WIDTH}(i{WIDTH} %a, i{WIDTH} %b)\nret i{WIDTH} %r\n}}\n"
        );
        check_scalar(intrinsic, &ll, &[WIDTH, WIDTH], WIDTH, |values| Expected {
            defined: true,
            value: if intrinsic == "umin" {
                values[0].min(values[1])
            } else {
                values[0].max(values[1])
            },
        });
    }
}

#[derive(Clone, Copy)]
enum FlagCase {
    AddNuw,
    AddNsw,
    SubNuw,
    SubNsw,
    MulNuw,
    MulNsw,
    ShlNuw,
    ShlNsw,
    LshrExact,
    AshrExact,
    UdivExact,
    SdivExact,
    OrDisjoint,
    ZextNneg,
    TruncNuw,
    TruncNsw,
}

impl FlagCase {
    fn label(self) -> &'static str {
        match self {
            Self::AddNuw => "add-nuw",
            Self::AddNsw => "add-nsw",
            Self::SubNuw => "sub-nuw",
            Self::SubNsw => "sub-nsw",
            Self::MulNuw => "mul-nuw",
            Self::MulNsw => "mul-nsw",
            Self::ShlNuw => "shl-nuw",
            Self::ShlNsw => "shl-nsw",
            Self::LshrExact => "lshr-exact",
            Self::AshrExact => "ashr-exact",
            Self::UdivExact => "udiv-exact",
            Self::SdivExact => "sdiv-exact",
            Self::OrDisjoint => "or-disjoint",
            Self::ZextNneg => "zext-nneg",
            Self::TruncNuw => "trunc-nuw",
            Self::TruncNsw => "trunc-nsw",
        }
    }

    fn llvm(self) -> (String, Vec<u32>, u32) {
        let label = self.label();
        let (instruction, widths, output) = match self {
            Self::AddNuw => (
                format!("add nuw i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::AddNsw => (
                format!("add nsw i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::SubNuw => (
                format!("sub nuw i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::SubNsw => (
                format!("sub nsw i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::MulNuw => (
                format!("mul nuw i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::MulNsw => (
                format!("mul nsw i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::ShlNuw => (
                format!("shl nuw i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::ShlNsw => (
                format!("shl nsw i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::LshrExact => (
                format!("lshr exact i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::AshrExact => (
                format!("ashr exact i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::UdivExact => (
                format!("udiv exact i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::SdivExact => (
                format!("sdiv exact i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::OrDisjoint => (
                format!("or disjoint i{WIDTH} %a, %b"),
                vec![WIDTH, WIDTH],
                WIDTH,
            ),
            Self::ZextNneg => ("zext nneg i4 %a to i6".to_owned(), vec![4], 6),
            Self::TruncNuw => ("trunc nuw i6 %a to i4".to_owned(), vec![6], 4),
            Self::TruncNsw => ("trunc nsw i6 %a to i4".to_owned(), vec![6], 4),
        };
        let parameters = widths
            .iter()
            .enumerate()
            .map(|(index, width)| format!("i{width} %{}", ["a", "b"][index]))
            .collect::<Vec<_>>()
            .join(", ");
        (
            format!(
                "define i{output} @{label}({parameters}) {{\n%r = {instruction}\nret i{output} %r\n}}\n"
            ),
            widths,
            output,
        )
    }

    fn expected(self, values: &[u128]) -> Expected {
        let lhs = values[0];
        let rhs = values.get(1).copied().unwrap_or(0);
        let unsigned_limit = 1_u128 << WIDTH;
        let signed_min = -(1_i128 << (WIDTH - 1));
        let signed_max = (1_i128 << (WIDTH - 1)) - 1;
        let signed_in_range = |value: i128| (signed_min..=signed_max).contains(&value);
        let shifted = rhs < u128::from(WIDTH);
        let low_mask = if rhs == 0 { 0 } else { (1_u128 << rhs) - 1 };
        let base = match self {
            Self::AddNuw | Self::AddNsw => binary_expected("add", lhs, rhs),
            Self::SubNuw | Self::SubNsw => binary_expected("sub", lhs, rhs),
            Self::MulNuw | Self::MulNsw => binary_expected("mul", lhs, rhs),
            Self::ShlNuw | Self::ShlNsw => binary_expected("shl", lhs, rhs),
            Self::LshrExact => binary_expected("lshr", lhs, rhs),
            Self::AshrExact => binary_expected("ashr", lhs, rhs),
            Self::UdivExact => binary_expected("udiv", lhs, rhs),
            Self::SdivExact => binary_expected("sdiv", lhs, rhs),
            Self::OrDisjoint => binary_expected("or", lhs, rhs),
            Self::ZextNneg => Expected {
                defined: true,
                value: lhs,
            },
            Self::TruncNuw | Self::TruncNsw => Expected {
                defined: true,
                value: lhs & mask(4),
            },
        };
        let flag_defined = match self {
            Self::AddNuw => lhs + rhs < unsigned_limit,
            Self::AddNsw => signed_in_range(signed(lhs, WIDTH) + signed(rhs, WIDTH)),
            Self::SubNuw => lhs >= rhs,
            Self::SubNsw => signed_in_range(signed(lhs, WIDTH) - signed(rhs, WIDTH)),
            Self::MulNuw => lhs * rhs < unsigned_limit,
            Self::MulNsw => signed_in_range(signed(lhs, WIDTH) * signed(rhs, WIDTH)),
            Self::ShlNuw => shifted && (lhs << rhs) < unsigned_limit,
            Self::ShlNsw => shifted && signed_in_range(signed(lhs, WIDTH) * (1_i128 << rhs)),
            Self::LshrExact | Self::AshrExact => shifted && lhs & low_mask == 0,
            Self::UdivExact => rhs != 0 && lhs.is_multiple_of(rhs),
            Self::SdivExact => base.defined && signed(lhs, WIDTH) % signed(rhs, WIDTH) == 0,
            Self::OrDisjoint => lhs & rhs == 0,
            Self::ZextNneg => signed(lhs, 4) >= 0,
            Self::TruncNuw => lhs <= mask(4),
            Self::TruncNsw => (-8..=7).contains(&signed(lhs, 6)),
        };
        Expected {
            defined: base.defined && flag_defined,
            value: base.value,
        }
    }
}

#[test]
fn llvm_semantic_flag_specs_and_exhaustive_fuzz() {
    for case in [
        FlagCase::AddNuw,
        FlagCase::AddNsw,
        FlagCase::SubNuw,
        FlagCase::SubNsw,
        FlagCase::MulNuw,
        FlagCase::MulNsw,
        FlagCase::ShlNuw,
        FlagCase::ShlNsw,
        FlagCase::LshrExact,
        FlagCase::AshrExact,
        FlagCase::UdivExact,
        FlagCase::SdivExact,
        FlagCase::OrDisjoint,
        FlagCase::ZextNneg,
        FlagCase::TruncNuw,
        FlagCase::TruncNsw,
    ] {
        let (ll, widths, output) = case.llvm();
        check_scalar(case.label(), &ll, &widths, output, |values| {
            case.expected(values)
        });
    }
}

#[test]
fn llvm_select_spec_and_exhaustive_fuzz() {
    let ll =
        "define i4 @select(i1 %c, i4 %a, i4 %b) {\n%r = select i1 %c, i4 %a, i4 %b\nret i4 %r\n}\n";
    check_scalar("select", ll, &[1, 4, 4], 4, |values| Expected {
        defined: true,
        value: if values[0] == 1 { values[1] } else { values[2] },
    });
}

const MIR_SCALAR_OPS: &str = r"
fn eq_zero(_1: [u8; 1], _2: u8) -> u8 {
    let mut _0: u8;
    let mut _3: bool;

    bb0: {
        StorageLive(_3);
        _3 = Eq(copy _2, const 0_u8);
        switchInt(copy _3) -> [0: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = const 1_u8;
        goto -> bb3;
    }

    bb2: {
        _0 = const 0_u8;
        goto -> bb3;
    }

    bb3: {
        StorageDead(_3);
        return;
    }
}

fn less_than_four(_1: [u8; 1], _2: u8) -> u8 {
    let mut _0: u8;
    let mut _3: bool;

    bb0: {
        _3 = Lt(copy _2, const 4_u8);
        switchInt(copy _3) -> [0: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = const 1_u8;
        goto -> bb3;
    }

    bb2: {
        _0 = const 0_u8;
        goto -> bb3;
    }

    bb3: {
        return;
    }
}

fn low_bits(_1: [u8; 1], _2: u8) -> u8 {
    let mut _0: u8;

    bb0: {
        _0 = BitAnd(copy _2, const 3_u8);
        return;
    }
}
";

#[test]
fn mir_scalar_opcode_specs_and_exhaustive_fuzz() {
    let cases: [MirScalarCase; 3] = [
        ("eq_zero", |value| u128::from(value == 0)),
        ("less_than_four", |value| u128::from(value < 4)),
        ("low_bits", |value| value & 3),
    ];
    for (function, expected) in cases {
        let mut reflected =
            reflect_bounded_memory_checked(MIR_SCALAR_OPS, &MirMemoryConfig::new(function, 64))
                .unwrap_or_else(|error| {
                    panic!("{function}: checked MIR reflection failed: {error}")
                });
        let input_symbol = reflected
            .params
            .iter()
            .find(|parameter| parameter.local == 2)
            .expect("_2 scalar parameter")
            .symbol;
        let input_term = reflected.arena.var(input_symbol);
        let expected_term = match function {
            "eq_zero" => {
                let zero = reflected.arena.bv_const(8, 0).unwrap();
                let one = reflected.arena.bv_const(8, 1).unwrap();
                let is_zero = reflected.arena.eq(input_term, zero).unwrap();
                reflected.arena.ite(is_zero, one, zero).unwrap()
            }
            "less_than_four" => {
                let four = reflected.arena.bv_const(8, 4).unwrap();
                let one = reflected.arena.bv_const(8, 1).unwrap();
                let zero = reflected.arena.bv_const(8, 0).unwrap();
                let less = reflected.arena.bv_ult(input_term, four).unwrap();
                reflected.arena.ite(less, one, zero).unwrap()
            }
            "low_bits" => {
                let three = reflected.arena.bv_const(8, 3).unwrap();
                reflected.arena.bv_and(input_term, three).unwrap()
            }
            _ => unreachable!(),
        };
        let same = reflected
            .arena
            .eq(reflected.result.value, expected_term)
            .unwrap();
        prove_goal(&mut reflected.arena, same, function);
        let no_panic = reflected.arena.not(reflected.panic).unwrap();
        prove_goal(&mut reflected.arena, no_panic, &format!("{function} panic"));

        for value in 0..=u8::MAX {
            let mut assignment = Assignment::new();
            assignment.set(
                input_symbol,
                Value::Bv {
                    width: 8,
                    value: u128::from(value),
                },
            );
            let actual = eval(&reflected.arena, reflected.result.value, &assignment).unwrap();
            assert_eq!(
                scalar_value(&actual),
                expected(u128::from(value)),
                "{function}: value disagrees at {value}"
            );
            assert_eq!(
                eval(&reflected.arena, reflected.panic, &assignment).unwrap(),
                Value::Bool(false),
                "{function}: unexpected panic at {value}"
            );
        }
    }
}
