//! Canonical rendering for the validated scalar LLVM CFG slice.

use std::fmt::Write as _;

use super::{
    BinaryOpcode, BlockId, CastOpcode, CfgBlock, IntPredicate, Intrinsic, Operand, ScalarCfg,
    ScalarInstructionKind, SemanticFlag, TerminatorKind,
};

/// Render one validated scalar CFG into deterministic canonical LLVM text.
///
/// The renderer owns only the typed ADR-0284 projection. It deliberately omits
/// source whitespace, comments, parameter attributes, and source spans.
#[must_use]
pub fn render_scalar_cfg(cfg: &ScalarCfg) -> String {
    let mut output = String::new();
    write!(
        output,
        "define i{} @{}(",
        cfg.return_width,
        quoted_name(&cfg.name)
    )
    .expect("writing to a String cannot fail");
    for (index, parameter) in cfg.params.iter().enumerate() {
        if index != 0 {
            output.push_str(", ");
        }
        write!(output, "{} %{}", parameter.ty, quoted_name(&parameter.name))
            .expect("writing to a String cannot fail");
    }
    output.push_str(") {\n");

    for block in &cfg.blocks {
        render_block(&mut output, block);
    }
    output.push_str("}\n");
    output
}

fn render_block(output: &mut String, block: &CfgBlock) {
    if let BlockId::Label(label) = &block.id {
        writeln!(output, "{}:", quoted_name(label)).expect("writing to a String cannot fail");
    }
    for phi in &block.phis {
        write!(
            output,
            "  %{} = phi i{} ",
            quoted_name(&phi.dest),
            phi.width
        )
        .expect("writing to a String cannot fail");
        for (index, incoming) in phi.incomings.iter().enumerate() {
            if index != 0 {
                output.push_str(", ");
            }
            write!(
                output,
                "[ {}, {} ]",
                operand(&incoming.value),
                block_ref(&incoming.predecessor)
            )
            .expect("writing to a String cannot fail");
        }
        output.push('\n');
    }
    for instruction in &block.instructions {
        output.push_str("  ");
        render_instruction(output, &instruction.kind);
        output.push('\n');
    }
    output.push_str("  ");
    render_terminator(output, block);
    for metadata in &block.terminator.metadata {
        write!(output, ", {metadata}").expect("writing to a String cannot fail");
    }
    output.push('\n');
}

fn render_instruction(output: &mut String, instruction: &ScalarInstructionKind) {
    match instruction {
        ScalarInstructionKind::Binary {
            dest,
            opcode,
            flags,
            width,
            lhs,
            rhs,
        } => render_binary(output, dest, *opcode, flags, *width, lhs, rhs),
        ScalarInstructionKind::Icmp {
            dest,
            predicate,
            width,
            lhs,
            rhs,
        } => render_icmp(output, dest, *predicate, *width, lhs, rhs),
        ScalarInstructionKind::Select {
            dest,
            condition,
            width,
            then_value,
            else_value,
        } => render_select(output, dest, condition, *width, then_value, else_value),
        ScalarInstructionKind::Cast {
            dest,
            opcode,
            flags,
            source_width,
            operand: source,
            target_width,
        } => render_cast(
            output,
            dest,
            *opcode,
            flags,
            *source_width,
            source,
            *target_width,
        ),
        ScalarInstructionKind::Intrinsic {
            dest,
            intrinsic,
            width,
            lhs,
            rhs,
        } => render_intrinsic(output, dest, *intrinsic, *width, lhs, rhs),
        ScalarInstructionKind::Return { width, value } => {
            write!(output, "ret i{width} {}", operand(value))
                .expect("writing to a String cannot fail");
        }
    }
}

fn render_binary(
    output: &mut String,
    dest: &str,
    opcode: BinaryOpcode,
    flags: &[SemanticFlag],
    width: u32,
    lhs: &Operand,
    rhs: &Operand,
) {
    write!(
        output,
        "%{} = {}{} i{} {}, {}",
        quoted_name(dest),
        binary_opcode(opcode),
        rendered_flags(flags),
        width,
        operand(lhs),
        operand(rhs)
    )
    .expect("writing to a String cannot fail");
}

fn render_icmp(
    output: &mut String,
    dest: &str,
    predicate: IntPredicate,
    width: u32,
    lhs: &Operand,
    rhs: &Operand,
) {
    write!(
        output,
        "%{} = icmp {} i{} {}, {}",
        quoted_name(dest),
        predicate_name(predicate),
        width,
        operand(lhs),
        operand(rhs)
    )
    .expect("writing to a String cannot fail");
}

fn render_select(
    output: &mut String,
    dest: &str,
    condition: &Operand,
    width: u32,
    then_value: &Operand,
    else_value: &Operand,
) {
    write!(
        output,
        "%{} = select i1 {}, i{} {}, i{} {}",
        quoted_name(dest),
        operand(condition),
        width,
        operand(then_value),
        width,
        operand(else_value)
    )
    .expect("writing to a String cannot fail");
}

fn render_cast(
    output: &mut String,
    dest: &str,
    opcode: CastOpcode,
    flags: &[SemanticFlag],
    source_width: u32,
    source: &Operand,
    target_width: u32,
) {
    write!(
        output,
        "%{} = {}{} i{} {} to i{}",
        quoted_name(dest),
        cast_opcode(opcode),
        rendered_flags(flags),
        source_width,
        operand(source),
        target_width
    )
    .expect("writing to a String cannot fail");
}

fn render_intrinsic(
    output: &mut String,
    dest: &str,
    intrinsic: Intrinsic,
    width: u32,
    lhs: &Operand,
    rhs: &Operand,
) {
    write!(
        output,
        "%{} = call i{} @{}(i{} {}, i{} {})",
        quoted_name(dest),
        width,
        quoted_name(&format!("llvm.{}.i{width}", intrinsic_name(intrinsic))),
        width,
        operand(lhs),
        width,
        operand(rhs)
    )
    .expect("writing to a String cannot fail");
}

fn render_terminator(output: &mut String, block: &CfgBlock) {
    match &block.terminator.kind {
        TerminatorKind::Return { width, value } => {
            write!(output, "ret i{width} {}", operand(value))
                .expect("writing to a String cannot fail");
        }
        TerminatorKind::Branch { target } => {
            write!(output, "br {}", label_ref(target)).expect("writing to a String cannot fail");
        }
        TerminatorKind::CondBranch {
            condition,
            true_target,
            false_target,
        } => {
            write!(
                output,
                "br i1 {}, {}, {}",
                operand(condition),
                label_ref(true_target),
                label_ref(false_target)
            )
            .expect("writing to a String cannot fail");
        }
        TerminatorKind::Switch {
            width,
            value,
            default_target,
            cases,
        } => {
            write!(
                output,
                "switch i{} {}, {} [",
                width,
                operand(value),
                label_ref(default_target)
            )
            .expect("writing to a String cannot fail");
            for case in cases {
                write!(
                    output,
                    "\n    i{} {}, {}",
                    width,
                    case.value,
                    label_ref(&case.target)
                )
                .expect("writing to a String cannot fail");
            }
            if !cases.is_empty() {
                output.push_str("\n  ");
            }
            output.push(']');
        }
        TerminatorKind::Unreachable => output.push_str("unreachable"),
    }
}

fn quoted_name(name: &str) -> String {
    let mut result = String::from("\"");
    for byte in name.bytes() {
        if (0x20..=0x7e).contains(&byte) && !matches!(byte, b'"' | b'\\') {
            result.push(char::from(byte));
        } else {
            write!(result, "\\{byte:02X}").expect("writing to a String cannot fail");
        }
    }
    result.push('"');
    result
}

fn operand(value: &Operand) -> String {
    match value {
        Operand::Local(name) => format!("%{}", quoted_name(name)),
        Operand::Constant(value) => value.clone(),
    }
}

fn label_ref(block: &BlockId) -> String {
    format!("label {}", block_ref(block))
}

fn block_ref(block: &BlockId) -> String {
    match block {
        BlockId::Entry => "%\"<entry>\"".to_owned(),
        BlockId::Label(label) => format!("%{}", quoted_name(label)),
    }
}

fn rendered_flags(flags: &[SemanticFlag]) -> String {
    let mut rendered = String::new();
    for flag in flags {
        write!(rendered, " {}", flag_name(*flag)).expect("writing to a String cannot fail");
    }
    rendered
}

const fn binary_opcode(opcode: BinaryOpcode) -> &'static str {
    match opcode {
        BinaryOpcode::Add => "add",
        BinaryOpcode::Sub => "sub",
        BinaryOpcode::Mul => "mul",
        BinaryOpcode::And => "and",
        BinaryOpcode::Or => "or",
        BinaryOpcode::Xor => "xor",
        BinaryOpcode::Shl => "shl",
        BinaryOpcode::Lshr => "lshr",
        BinaryOpcode::Ashr => "ashr",
        BinaryOpcode::Udiv => "udiv",
        BinaryOpcode::Sdiv => "sdiv",
        BinaryOpcode::Urem => "urem",
        BinaryOpcode::Srem => "srem",
    }
}

const fn predicate_name(predicate: IntPredicate) -> &'static str {
    match predicate {
        IntPredicate::Eq => "eq",
        IntPredicate::Ne => "ne",
        IntPredicate::Ult => "ult",
        IntPredicate::Ule => "ule",
        IntPredicate::Ugt => "ugt",
        IntPredicate::Uge => "uge",
        IntPredicate::Slt => "slt",
        IntPredicate::Sle => "sle",
        IntPredicate::Sgt => "sgt",
        IntPredicate::Sge => "sge",
    }
}

const fn cast_opcode(opcode: CastOpcode) -> &'static str {
    match opcode {
        CastOpcode::Zext => "zext",
        CastOpcode::Sext => "sext",
        CastOpcode::Trunc => "trunc",
    }
}

const fn intrinsic_name(intrinsic: Intrinsic) -> &'static str {
    match intrinsic {
        Intrinsic::UnsignedMin => "umin",
        Intrinsic::UnsignedMax => "umax",
    }
}

const fn flag_name(flag: SemanticFlag) -> &'static str {
    match flag {
        SemanticFlag::Nuw => "nuw",
        SemanticFlag::Nsw => "nsw",
        SemanticFlag::Exact => "exact",
        SemanticFlag::Disjoint => "disjoint",
        SemanticFlag::Nneg => "nneg",
    }
}
