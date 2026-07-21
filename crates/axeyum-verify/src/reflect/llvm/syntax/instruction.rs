//! Typed syntax for the straight-line scalar integer LLVM fragment.

use super::{
    Instruction, ParseError, ParseErrorKind, SourceSpan, Token, TokenKind, from_span, lex,
};

/// Supported scalar integer binary operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOpcode {
    /// Modular addition.
    Add,
    /// Modular subtraction.
    Sub,
    /// Modular multiplication.
    Mul,
    /// Bitwise conjunction.
    And,
    /// Bitwise disjunction.
    Or,
    /// Bitwise exclusive disjunction.
    Xor,
    /// Left shift.
    Shl,
    /// Logical right shift.
    Lshr,
    /// Arithmetic right shift.
    Ashr,
    /// Unsigned division.
    Udiv,
    /// Signed division.
    Sdiv,
    /// Unsigned remainder.
    Urem,
    /// Signed remainder.
    Srem,
}

/// Supported integer comparison predicates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntPredicate {
    /// Equality.
    Eq,
    /// Disequality.
    Ne,
    /// Unsigned less-than.
    Ult,
    /// Unsigned less-than-or-equal.
    Ule,
    /// Unsigned greater-than.
    Ugt,
    /// Unsigned greater-than-or-equal.
    Uge,
    /// Signed less-than.
    Slt,
    /// Signed less-than-or-equal.
    Sle,
    /// Signed greater-than.
    Sgt,
    /// Signed greater-than-or-equal.
    Sge,
}

/// Supported integer cast operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CastOpcode {
    /// Zero extension.
    Zext,
    /// Sign extension.
    Sext,
    /// Truncation.
    Trunc,
}

/// Supported direct scalar intrinsics.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Intrinsic {
    /// `llvm.umin.iN`.
    UnsignedMin,
    /// `llvm.umax.iN`.
    UnsignedMax,
}

/// LLVM flags with poison-producing scalar semantics in this slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SemanticFlag {
    /// No unsigned wrap.
    Nuw,
    /// No signed wrap.
    Nsw,
    /// Exact division/right shift.
    Exact,
    /// Bitwise-OR operands are disjoint.
    Disjoint,
    /// Zero-extension source is non-negative.
    Nneg,
}

/// LLVM pointer-arithmetic promises admitted by the bounded byte-memory profile.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum GepFlag {
    /// Every intermediate/result pointer remains within the allocation or one-past.
    InBounds,
    /// Unsigned pointer-index arithmetic does not wrap.
    Nuw,
}

/// One scalar LLVM operand.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operand {
    /// SSA local name without `%` or surrounding quotes.
    Local(String),
    /// Integer or Boolean constant retained exactly as printed.
    Constant(String),
}

/// One scalar argument to an explicitly resolved direct call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DirectCallArgument {
    /// Declared LLVM integer width.
    pub width: u32,
    /// Whether the call site requires a non-poison argument.
    pub noundef: bool,
    /// Scalar argument value.
    pub value: Operand,
}

/// One non-wrapping half-open integer range attached to a scalar call result.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CallResultRange {
    /// Integer width carried by the `range` attribute.
    pub width: u32,
    /// Inclusive lower bound.
    pub lower: u128,
    /// Exclusive upper bound.
    pub upper: u128,
}

/// Typed syntax for one supported scalar instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarInstruction {
    /// Parsed operation and operands.
    pub kind: ScalarInstructionKind,
    /// Original source span of the entire instruction.
    pub span: SourceSpan,
}

/// Supported scalar instruction families.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarInstructionKind {
    /// Assigned integer binary operation.
    Binary {
        /// Destination SSA name.
        dest: String,
        /// Operation.
        opcode: BinaryOpcode,
        /// Semantic flags in source order.
        flags: Vec<SemanticFlag>,
        /// Operand/result width.
        width: u32,
        /// Left operand.
        lhs: Operand,
        /// Right operand.
        rhs: Operand,
    },
    /// Assigned integer comparison.
    Icmp {
        /// Destination SSA name.
        dest: String,
        /// Comparison predicate.
        predicate: IntPredicate,
        /// Input width.
        width: u32,
        /// Left operand.
        lhs: Operand,
        /// Right operand.
        rhs: Operand,
    },
    /// Assigned scalar conditional selection.
    Select {
        /// Destination SSA name.
        dest: String,
        /// Boolean condition.
        condition: Operand,
        /// Selected value width.
        width: u32,
        /// True-arm value.
        then_value: Operand,
        /// False-arm value.
        else_value: Operand,
    },
    /// Assigned integer cast.
    Cast {
        /// Destination SSA name.
        dest: String,
        /// Cast operation.
        opcode: CastOpcode,
        /// Semantic flags in source order.
        flags: Vec<SemanticFlag>,
        /// Source width.
        source_width: u32,
        /// Source operand.
        operand: Operand,
        /// Destination width.
        target_width: u32,
    },
    /// Assigned direct min/max intrinsic call.
    Intrinsic {
        /// Destination SSA name.
        dest: String,
        /// Whether the source used the semantically transparent `tail` marker.
        tail: bool,
        /// Optional poison-producing result range.
        result_range: Option<CallResultRange>,
        /// Intrinsic operation.
        intrinsic: Intrinsic,
        /// Argument/result width.
        width: u32,
        /// Left argument.
        lhs: Operand,
        /// Right argument.
        rhs: Operand,
    },
    /// Assigned direct `llvm.ctlz.iN` intrinsic call.
    CountLeadingZeros {
        /// Destination SSA name.
        dest: String,
        /// Whether the source used the semantically transparent `tail` marker.
        tail: bool,
        /// Optional poison-producing result range.
        result_range: Option<CallResultRange>,
        /// Argument/result width.
        width: u32,
        /// Integer whose leading zero bits are counted.
        operand: Operand,
        /// Whether a zero operand makes the result poison.
        zero_is_poison: bool,
    },
    /// Assigned direct scalar call whose body must be supplied explicitly by a
    /// checked resolver before it can receive executable semantics.
    DirectCall {
        /// Destination SSA name.
        dest: String,
        /// Whether the source used the semantically transparent `tail` marker.
        tail: bool,
        /// Declared result width.
        result_width: u32,
        /// Direct global callee name without `@` or surrounding quotes.
        callee: String,
        /// Ordered typed scalar arguments.
        args: Vec<DirectCallArgument>,
    },
    /// Byte-addressed pointer derivation in the bounded memory profile.
    GetElementPtr {
        /// Destination pointer SSA name.
        dest: String,
        /// Pointer arithmetic promises in source order.
        flags: Vec<GepFlag>,
        /// Pointee element width; the first profile accepts only eight.
        element_width: u32,
        /// Base pointer SSA name.
        base: String,
        /// Index width; the first profile accepts only 64.
        index_width: u32,
        /// Signed element index.
        index: Operand,
    },
    /// One non-atomic, non-volatile integer load.
    Load {
        /// Destination scalar SSA name.
        dest: String,
        /// Loaded integer width.
        width: u32,
        /// Source pointer SSA name.
        pointer: String,
        /// Promised byte alignment.
        align: u32,
    },
    /// One non-atomic, non-volatile integer store.
    Store {
        /// Stored integer width.
        width: u32,
        /// Stored scalar value.
        value: Operand,
        /// Destination pointer SSA name.
        pointer: String,
        /// Promised byte alignment.
        align: u32,
    },
    /// Scalar return.
    Return {
        /// Returned value width.
        width: u32,
        /// Returned operand.
        value: Operand,
    },
}

impl ScalarInstructionKind {
    pub(crate) fn destination(&self) -> Option<&str> {
        match self {
            Self::Binary { dest, .. }
            | Self::Icmp { dest, .. }
            | Self::Select { dest, .. }
            | Self::Cast { dest, .. }
            | Self::Intrinsic { dest, .. }
            | Self::CountLeadingZeros { dest, .. }
            | Self::DirectCall { dest, .. }
            | Self::GetElementPtr { dest, .. }
            | Self::Load { dest, .. } => Some(dest),
            Self::Store { .. } | Self::Return { .. } => None,
        }
    }
}

/// Parse one source instruction from [`super::parse_function`] into the typed
/// straight-line scalar subset.
///
/// # Errors
///
/// Returns a located error for malformed syntax, unsupported operations/types,
/// or recognized constructs whose semantics are outside ADR-0281.
pub fn parse_scalar_instruction(
    instruction: &Instruction,
) -> Result<ScalarInstruction, ParseError> {
    let mut tokens = lex(&instruction.text).map_err(|error| relocate_error(instruction, error))?;
    for token in &mut tokens {
        token.span = relocate_span(instruction, token.span);
    }
    let mut cursor = Cursor {
        tokens: &tokens,
        index: 0,
        fallback: instruction.span,
    };
    let kind = if cursor.peek_word("ret") {
        cursor.word("ret")?;
        let width = cursor.int_type()?;
        let value = cursor.operand()?;
        cursor.end()?;
        ScalarInstructionKind::Return { width, value }
    } else if cursor.peek_word("store") {
        parse_store(&mut cursor)?
    } else {
        let dest = cursor.local("instruction destination")?;
        cursor.punct('=')?;
        parse_assignment(&mut cursor, dest)?
    };
    Ok(ScalarInstruction {
        kind,
        span: instruction.span,
    })
}

fn parse_assignment(
    cursor: &mut Cursor<'_>,
    dest: String,
) -> Result<ScalarInstructionKind, ParseError> {
    let opcode = cursor.any_word("instruction opcode")?;
    if matches!(opcode.as_str(), "tail" | "musttail" | "notail" | "call") {
        return parse_call(cursor, dest, &opcode);
    }
    if let Some(binary) = parse_binary_opcode(&opcode) {
        return parse_binary(cursor, dest, binary);
    }
    match opcode.as_str() {
        "icmp" => parse_icmp(cursor, dest),
        "select" => parse_select(cursor, dest),
        "zext" => parse_cast(cursor, dest, CastOpcode::Zext),
        "sext" => parse_cast(cursor, dest, CastOpcode::Sext),
        "trunc" => parse_cast(cursor, dest, CastOpcode::Trunc),
        "getelementptr" => parse_gep(cursor, dest),
        "load" => parse_load(cursor, dest),
        _ => Err(cursor.error(
            ParseErrorKind::UnsupportedInstruction,
            &format!("unsupported scalar instruction `{opcode}`"),
        )),
    }
}

fn parse_gep(cursor: &mut Cursor<'_>, dest: String) -> Result<ScalarInstructionKind, ParseError> {
    let mut flags = Vec::new();
    while cursor.peek_word("inbounds") || cursor.peek_word("nuw") || cursor.peek_word("nusw") {
        let word = cursor.any_word("GEP flag")?;
        let flag = match word.as_str() {
            "inbounds" => GepFlag::InBounds,
            "nuw" => GepFlag::Nuw,
            "nusw" => {
                return Err(cursor.error(
                    ParseErrorKind::UnsupportedSemantics,
                    "standalone `getelementptr nusw` is outside the bounded memory profile",
                ));
            }
            _ => unreachable!("peek admitted only GEP flags"),
        };
        if flags.contains(&flag) {
            return Err(cursor.error(
                ParseErrorKind::MalformedInstruction,
                &format!("duplicate GEP flag `{word}`"),
            ));
        }
        flags.push(flag);
    }
    if !flags.contains(&GepFlag::InBounds) {
        return Err(cursor.error(
            ParseErrorKind::UnsupportedSemantics,
            "bounded byte memory requires `getelementptr inbounds`",
        ));
    }
    let element_width = cursor.int_type()?;
    if element_width != 8 {
        return Err(cursor.error(
            ParseErrorKind::UnsupportedInstruction,
            "bounded byte memory requires `getelementptr ... i8`",
        ));
    }
    cursor.punct(',')?;
    cursor.word("ptr")?;
    let base = cursor.local("GEP base pointer")?;
    cursor.punct(',')?;
    let index_width = cursor.int_type()?;
    if index_width != 64 {
        return Err(cursor.error(
            ParseErrorKind::UnsupportedInstruction,
            "bounded byte memory requires an i64 GEP index",
        ));
    }
    let index = cursor.operand()?;
    cursor.end()?;
    Ok(ScalarInstructionKind::GetElementPtr {
        dest,
        flags,
        element_width,
        base,
        index_width,
        index,
    })
}

fn parse_load(cursor: &mut Cursor<'_>, dest: String) -> Result<ScalarInstructionKind, ParseError> {
    if cursor.peek_word("atomic") || cursor.peek_word("volatile") {
        return Err(cursor.error(
            ParseErrorKind::UnsupportedSemantics,
            "atomic/volatile loads are outside the bounded memory profile",
        ));
    }
    let width = cursor.int_type()?;
    require_byte_access(cursor, width)?;
    cursor.punct(',')?;
    cursor.word("ptr")?;
    let pointer = cursor.local("load pointer")?;
    let align = cursor.optional_alignment()?;
    cursor.end()?;
    Ok(ScalarInstructionKind::Load {
        dest,
        width,
        pointer,
        align,
    })
}

fn parse_store(cursor: &mut Cursor<'_>) -> Result<ScalarInstructionKind, ParseError> {
    cursor.word("store")?;
    if cursor.peek_word("atomic") || cursor.peek_word("volatile") {
        return Err(cursor.error(
            ParseErrorKind::UnsupportedSemantics,
            "atomic/volatile stores are outside the bounded memory profile",
        ));
    }
    let width = cursor.int_type()?;
    require_byte_access(cursor, width)?;
    let value = cursor.operand()?;
    cursor.punct(',')?;
    cursor.word("ptr")?;
    let pointer = cursor.local("store pointer")?;
    let align = cursor.optional_alignment()?;
    cursor.end()?;
    Ok(ScalarInstructionKind::Store {
        width,
        value,
        pointer,
        align,
    })
}

fn require_byte_access(cursor: &Cursor<'_>, width: u32) -> Result<(), ParseError> {
    if width == 8 {
        Ok(())
    } else {
        Err(cursor.error(
            ParseErrorKind::UnsupportedInstruction,
            "bounded byte memory supports only i8 loads and stores",
        ))
    }
}

fn parse_binary(
    cursor: &mut Cursor<'_>,
    dest: String,
    opcode: BinaryOpcode,
) -> Result<ScalarInstructionKind, ParseError> {
    let flags = cursor.flags()?;
    validate_flags(cursor, &flags, binary_flags(opcode))?;
    let width = cursor.int_type()?;
    let lhs = cursor.operand()?;
    cursor.punct(',')?;
    let rhs = cursor.operand()?;
    cursor.end()?;
    Ok(ScalarInstructionKind::Binary {
        dest,
        opcode,
        flags,
        width,
        lhs,
        rhs,
    })
}

fn parse_icmp(cursor: &mut Cursor<'_>, dest: String) -> Result<ScalarInstructionKind, ParseError> {
    if cursor.peek_word("samesign") {
        return Err(cursor.error(
            ParseErrorKind::UnsupportedSemantics,
            "`icmp samesign` is outside the scalar definedness slice",
        ));
    }
    let predicate_word = cursor.any_word("icmp predicate")?;
    let predicate = parse_predicate(&predicate_word).ok_or_else(|| {
        cursor.error(
            ParseErrorKind::MalformedInstruction,
            &format!("unknown icmp predicate `{predicate_word}`"),
        )
    })?;
    let width = cursor.int_type()?;
    let lhs = cursor.operand()?;
    cursor.punct(',')?;
    let rhs = cursor.operand()?;
    cursor.end()?;
    Ok(ScalarInstructionKind::Icmp {
        dest,
        predicate,
        width,
        lhs,
        rhs,
    })
}

fn parse_select(
    cursor: &mut Cursor<'_>,
    dest: String,
) -> Result<ScalarInstructionKind, ParseError> {
    let condition_width = cursor.int_type()?;
    if condition_width != 1 {
        return Err(cursor.error(
            ParseErrorKind::MalformedInstruction,
            "scalar select condition must have type i1",
        ));
    }
    let condition = cursor.operand()?;
    cursor.punct(',')?;
    let width = cursor.int_type()?;
    let then_value = cursor.operand()?;
    cursor.punct(',')?;
    let else_width = cursor.int_type()?;
    if else_width != width {
        return Err(cursor.error(
            ParseErrorKind::MalformedInstruction,
            "select arms have different widths",
        ));
    }
    let else_value = cursor.operand()?;
    cursor.end()?;
    Ok(ScalarInstructionKind::Select {
        dest,
        condition,
        width,
        then_value,
        else_value,
    })
}

fn parse_cast(
    cursor: &mut Cursor<'_>,
    dest: String,
    opcode: CastOpcode,
) -> Result<ScalarInstructionKind, ParseError> {
    let flags = cursor.flags()?;
    let allowed = match opcode {
        CastOpcode::Zext => &[SemanticFlag::Nneg][..],
        CastOpcode::Sext => &[],
        CastOpcode::Trunc => &[SemanticFlag::Nuw, SemanticFlag::Nsw],
    };
    validate_flags(cursor, &flags, allowed)?;
    let source_width = cursor.int_type()?;
    let operand = cursor.operand()?;
    cursor.word("to")?;
    let target_width = cursor.int_type()?;
    match opcode {
        CastOpcode::Zext | CastOpcode::Sext if source_width >= target_width => {
            return Err(cursor.error(
                ParseErrorKind::MalformedInstruction,
                "extension target must be wider than its source",
            ));
        }
        CastOpcode::Trunc if source_width <= target_width => {
            return Err(cursor.error(
                ParseErrorKind::MalformedInstruction,
                "truncation target must be narrower than its source",
            ));
        }
        _ => {}
    }
    cursor.end()?;
    Ok(ScalarInstructionKind::Cast {
        dest,
        opcode,
        flags,
        source_width,
        operand,
        target_width,
    })
}

fn parse_call(
    cursor: &mut Cursor<'_>,
    dest: String,
    first: &str,
) -> Result<ScalarInstructionKind, ParseError> {
    if matches!(first, "musttail" | "notail") {
        return Err(cursor.error(
            ParseErrorKind::UnsupportedSemantics,
            &format!("`{first}` calls are outside the checked direct-call profile"),
        ));
    }
    let tail = first == "tail";
    if first != "call" {
        cursor.word("call")?;
    }
    let result_range = parse_result_range(cursor)?;
    if result_range.is_some() && cursor.peek_word("range") {
        return Err(cursor.error(
            ParseErrorKind::MalformedInstruction,
            "multiple call-result ranges are unsupported",
        ));
    }
    let width = cursor.int_type()?;
    if result_range.is_some_and(|range| range.width != width) {
        return Err(cursor.error(
            ParseErrorKind::MalformedInstruction,
            "call-result range and result widths differ",
        ));
    }
    let callee = cursor.global("direct callee")?;
    let intrinsic = if callee == format!("llvm.umin.i{width}") {
        Some(Intrinsic::UnsignedMin)
    } else if callee == format!("llvm.umax.i{width}") {
        Some(Intrinsic::UnsignedMax)
    } else {
        None
    };
    cursor.punct('(')?;
    if let Some(intrinsic) = intrinsic {
        return parse_minmax_call(cursor, dest, tail, result_range, intrinsic, width);
    }

    if callee == format!("llvm.ctlz.i{width}") {
        return parse_ctlz_call(cursor, dest, tail, result_range, width);
    }

    if callee.starts_with("llvm.ctlz.") {
        return Err(cursor.error(
            ParseErrorKind::MalformedInstruction,
            "`llvm.ctlz` name and result width do not match",
        ));
    }
    if callee.starts_with("llvm.cttz.") || callee.starts_with("llvm.ctpop.") {
        return Err(cursor.error(
            ParseErrorKind::UnsupportedSemantics,
            &format!("intrinsic `@{callee}` is outside the checked scalar profile"),
        ));
    }

    if result_range.is_some() {
        return Err(cursor.error(
            ParseErrorKind::UnsupportedSemantics,
            "call-result range on an unsupported call is outside the checked profile",
        ));
    }

    parse_direct_call(cursor, dest, tail, width, callee)
}

fn parse_minmax_call(
    cursor: &mut Cursor<'_>,
    dest: String,
    tail: bool,
    result_range: Option<CallResultRange>,
    intrinsic: Intrinsic,
    width: u32,
) -> Result<ScalarInstructionKind, ParseError> {
    let left_width = cursor.int_type()?;
    let lhs = cursor.operand()?;
    cursor.punct(',')?;
    let right_width = cursor.int_type()?;
    let rhs = cursor.operand()?;
    cursor.punct(')')?;
    if left_width != width || right_width != width {
        return Err(cursor.error(
            ParseErrorKind::MalformedInstruction,
            "intrinsic argument and result widths differ",
        ));
    }
    cursor.end()?;
    Ok(ScalarInstructionKind::Intrinsic {
        dest,
        tail,
        result_range,
        intrinsic,
        width,
        lhs,
        rhs,
    })
}

fn parse_ctlz_call(
    cursor: &mut Cursor<'_>,
    dest: String,
    tail: bool,
    result_range: Option<CallResultRange>,
    width: u32,
) -> Result<ScalarInstructionKind, ParseError> {
    let operand_width = cursor.int_type()?;
    let operand = cursor.operand()?;
    cursor.punct(',')?;
    let flag_width = cursor.int_type()?;
    let zero_is_poison = cursor.bool_literal("`llvm.ctlz` zero-poison flag")?;
    cursor.punct(')')?;
    if operand_width != width || flag_width != 1 {
        return Err(cursor.error(
            ParseErrorKind::MalformedInstruction,
            "`llvm.ctlz` argument widths do not match its signature",
        ));
    }
    cursor.end()?;
    Ok(ScalarInstructionKind::CountLeadingZeros {
        dest,
        tail,
        result_range,
        width,
        operand,
        zero_is_poison,
    })
}

fn parse_direct_call(
    cursor: &mut Cursor<'_>,
    dest: String,
    tail: bool,
    result_width: u32,
    callee: String,
) -> Result<ScalarInstructionKind, ParseError> {
    let mut args = Vec::new();
    while !cursor.peek_punct(')') {
        let arg_width = cursor.int_type()?;
        let noundef = if cursor.peek_word("noundef") {
            cursor.word("noundef")?;
            true
        } else {
            false
        };
        if let Some(attribute) = cursor.peek_any_word()
            && !matches!(attribute, "true" | "false")
            && !is_integer(attribute)
        {
            return Err(cursor.error(
                ParseErrorKind::UnsupportedSemantics,
                &format!("unsupported direct-call argument attribute `{attribute}`"),
            ));
        }
        let value = cursor.operand()?;
        args.push(DirectCallArgument {
            width: arg_width,
            noundef,
            value,
        });
        if cursor.peek_punct(')') {
            break;
        }
        cursor.punct(',')?;
    }
    cursor.punct(')')?;
    cursor.end()?;
    Ok(ScalarInstructionKind::DirectCall {
        dest,
        tail,
        result_width,
        callee,
        args,
    })
}

fn parse_result_range(cursor: &mut Cursor<'_>) -> Result<Option<CallResultRange>, ParseError> {
    if !cursor.peek_word("range") {
        return Ok(None);
    }
    cursor.word("range")?;
    cursor.punct('(')?;
    let width = cursor.int_type()?;
    let lower = cursor.unsigned_integer("call-result range lower bound")?;
    cursor.punct(',')?;
    let upper = cursor.unsigned_integer("call-result range upper bound")?;
    cursor.punct(')')?;
    if !integer_fits_width(lower, width) || !integer_fits_width(upper, width) {
        return Err(cursor.error(
            ParseErrorKind::MalformedInstruction,
            "call-result range bound does not fit its integer width",
        ));
    }
    if lower >= upper {
        return Err(cursor.error(
            ParseErrorKind::UnsupportedSemantics,
            "wrapped or empty call-result ranges are outside the checked profile",
        ));
    }
    Ok(Some(CallResultRange {
        width,
        lower,
        upper,
    }))
}

fn integer_fits_width(value: u128, width: u32) -> bool {
    width >= u128::BITS || value < (1_u128 << width)
}

fn parse_binary_opcode(word: &str) -> Option<BinaryOpcode> {
    Some(match word {
        "add" => BinaryOpcode::Add,
        "sub" => BinaryOpcode::Sub,
        "mul" => BinaryOpcode::Mul,
        "and" => BinaryOpcode::And,
        "or" => BinaryOpcode::Or,
        "xor" => BinaryOpcode::Xor,
        "shl" => BinaryOpcode::Shl,
        "lshr" => BinaryOpcode::Lshr,
        "ashr" => BinaryOpcode::Ashr,
        "udiv" => BinaryOpcode::Udiv,
        "sdiv" => BinaryOpcode::Sdiv,
        "urem" => BinaryOpcode::Urem,
        "srem" => BinaryOpcode::Srem,
        _ => return None,
    })
}

fn parse_predicate(word: &str) -> Option<IntPredicate> {
    Some(match word {
        "eq" => IntPredicate::Eq,
        "ne" => IntPredicate::Ne,
        "ult" => IntPredicate::Ult,
        "ule" => IntPredicate::Ule,
        "ugt" => IntPredicate::Ugt,
        "uge" => IntPredicate::Uge,
        "slt" => IntPredicate::Slt,
        "sle" => IntPredicate::Sle,
        "sgt" => IntPredicate::Sgt,
        "sge" => IntPredicate::Sge,
        _ => return None,
    })
}

fn binary_flags(opcode: BinaryOpcode) -> &'static [SemanticFlag] {
    match opcode {
        BinaryOpcode::Add | BinaryOpcode::Sub | BinaryOpcode::Mul | BinaryOpcode::Shl => {
            &[SemanticFlag::Nuw, SemanticFlag::Nsw]
        }
        BinaryOpcode::Lshr | BinaryOpcode::Ashr | BinaryOpcode::Udiv | BinaryOpcode::Sdiv => {
            &[SemanticFlag::Exact]
        }
        BinaryOpcode::Or => &[SemanticFlag::Disjoint],
        BinaryOpcode::And | BinaryOpcode::Xor | BinaryOpcode::Urem | BinaryOpcode::Srem => &[],
    }
}

fn validate_flags(
    cursor: &Cursor<'_>,
    flags: &[SemanticFlag],
    allowed: &[SemanticFlag],
) -> Result<(), ParseError> {
    for (index, flag) in flags.iter().enumerate() {
        if !allowed.contains(flag) {
            return Err(cursor.error(
                ParseErrorKind::MalformedInstruction,
                &format!("flag `{flag:?}` is invalid for this opcode"),
            ));
        }
        if flags[..index].contains(flag) {
            return Err(cursor.error(
                ParseErrorKind::MalformedInstruction,
                &format!("duplicate flag `{flag:?}`"),
            ));
        }
    }
    Ok(())
}

struct Cursor<'a> {
    tokens: &'a [Token],
    index: usize,
    fallback: SourceSpan,
}

impl Cursor<'_> {
    fn peek_word(&self, expected: &str) -> bool {
        matches!(self.tokens.get(self.index).map(|token| &token.kind), Some(TokenKind::Word(word)) if word == expected)
    }

    fn peek_any_word(&self) -> Option<&str> {
        match self.tokens.get(self.index).map(|token| &token.kind) {
            Some(TokenKind::Word(word)) => Some(word),
            _ => None,
        }
    }

    fn any_word(&mut self, expected: &str) -> Result<String, ParseError> {
        match self.next().map(|token| &token.kind) {
            Some(TokenKind::Word(word)) => Ok(word.clone()),
            _ => Err(self.error(
                ParseErrorKind::MalformedInstruction,
                &format!("expected {expected}"),
            )),
        }
    }

    fn word(&mut self, expected: &str) -> Result<(), ParseError> {
        let actual = self.any_word(&format!("`{expected}`"))?;
        if actual == expected {
            Ok(())
        } else {
            Err(self.error(
                ParseErrorKind::MalformedInstruction,
                &format!("expected `{expected}`, found `{actual}`"),
            ))
        }
    }

    fn local(&mut self, expected: &str) -> Result<String, ParseError> {
        match self.next().map(|token| &token.kind) {
            Some(TokenKind::LocalName(name)) => Ok(name.clone()),
            _ => Err(self.error(
                ParseErrorKind::MalformedInstruction,
                &format!("expected {expected}"),
            )),
        }
    }

    fn global(&mut self, expected: &str) -> Result<String, ParseError> {
        match self.next().map(|token| &token.kind) {
            Some(TokenKind::GlobalName(name)) => Ok(name.clone()),
            _ => Err(self.error(
                ParseErrorKind::MalformedInstruction,
                &format!("expected {expected}"),
            )),
        }
    }

    fn punct(&mut self, expected: char) -> Result<(), ParseError> {
        match self.next().map(|token| &token.kind) {
            Some(TokenKind::Punct(actual)) if *actual == expected => Ok(()),
            _ => Err(self.error(
                ParseErrorKind::MalformedInstruction,
                &format!("expected `{expected}`"),
            )),
        }
    }

    fn peek_punct(&self, expected: char) -> bool {
        matches!(self.tokens.get(self.index).map(|token| &token.kind), Some(TokenKind::Punct(actual)) if *actual == expected)
    }

    fn optional_alignment(&mut self) -> Result<u32, ParseError> {
        if !self.peek_punct(',') {
            return Ok(1);
        }
        self.punct(',')?;
        self.word("align")?;
        let raw = self.any_word("alignment")?;
        let align = raw.parse::<u32>().map_err(|_| {
            self.error(
                ParseErrorKind::MalformedInstruction,
                &format!("invalid memory alignment `{raw}`"),
            )
        })?;
        if align != 1 {
            return Err(self.error(
                ParseErrorKind::UnsupportedSemantics,
                "bounded byte memory supports only alignment 1",
            ));
        }
        Ok(align)
    }

    fn int_type(&mut self) -> Result<u32, ParseError> {
        let word = self.any_word("scalar integer type")?;
        let Some(digits) = word.strip_prefix('i') else {
            return Err(self.error(
                ParseErrorKind::UnsupportedInstruction,
                &format!("unsupported scalar type `{word}`"),
            ));
        };
        let width = digits.parse::<u32>().map_err(|_| {
            self.error(
                ParseErrorKind::MalformedInstruction,
                &format!("malformed integer type `{word}`"),
            )
        })?;
        if width == 0 {
            return Err(self.error(
                ParseErrorKind::MalformedInstruction,
                "integer width must be positive",
            ));
        }
        Ok(width)
    }

    fn operand(&mut self) -> Result<Operand, ParseError> {
        let kind = self.next().map(|token| token.kind.clone());
        match kind {
            Some(TokenKind::LocalName(name)) => Ok(Operand::Local(name)),
            Some(TokenKind::Word(word)) if matches!(word.as_str(), "undef" | "poison") => Err(self
                .error(
                    ParseErrorKind::UnsupportedSemantics,
                    &format!("`{word}` requires nondeterministic/poison value semantics"),
                )),
            Some(TokenKind::Word(word))
                if matches!(word.as_str(), "true" | "false") || is_integer(&word) =>
            {
                Ok(Operand::Constant(word))
            }
            _ => Err(self.error(
                ParseErrorKind::MalformedInstruction,
                "expected scalar local or integer constant",
            )),
        }
    }

    fn unsigned_integer(&mut self, expected: &str) -> Result<u128, ParseError> {
        let raw = self.any_word(expected)?;
        if raw.starts_with('-') {
            return Err(self.error(
                ParseErrorKind::MalformedInstruction,
                &format!("{expected} must be non-negative"),
            ));
        }
        raw.parse::<u128>().map_err(|_| {
            self.error(
                ParseErrorKind::MalformedInstruction,
                &format!("invalid {expected} `{raw}`"),
            )
        })
    }

    fn bool_literal(&mut self, expected: &str) -> Result<bool, ParseError> {
        match self.next().map(|token| &token.kind) {
            Some(TokenKind::Word(word)) if word == "true" => Ok(true),
            Some(TokenKind::Word(word)) if word == "false" => Ok(false),
            Some(TokenKind::LocalName(_)) => Err(self.error(
                ParseErrorKind::UnsupportedSemantics,
                &format!("{expected} must be a literal `true` or `false`"),
            )),
            _ => Err(self.error(
                ParseErrorKind::MalformedInstruction,
                &format!("expected {expected}"),
            )),
        }
    }

    fn flags(&mut self) -> Result<Vec<SemanticFlag>, ParseError> {
        let mut flags = Vec::new();
        while let Some(TokenKind::Word(word)) = self.tokens.get(self.index).map(|token| &token.kind)
        {
            if is_int_type(word) {
                break;
            }
            let flag = match word.as_str() {
                "nuw" => SemanticFlag::Nuw,
                "nsw" => SemanticFlag::Nsw,
                "exact" => SemanticFlag::Exact,
                "disjoint" => SemanticFlag::Disjoint,
                "nneg" => SemanticFlag::Nneg,
                _ => {
                    return Err(self.error(
                        ParseErrorKind::MalformedInstruction,
                        &format!("unknown instruction flag `{word}`"),
                    ));
                }
            };
            self.index += 1;
            flags.push(flag);
        }
        Ok(flags)
    }

    fn end(&self) -> Result<(), ParseError> {
        if self.index == self.tokens.len() {
            Ok(())
        } else {
            Err(self.error(
                ParseErrorKind::MalformedInstruction,
                "unexpected trailing instruction tokens",
            ))
        }
    }

    fn next(&mut self) -> Option<&Token> {
        let token = self.tokens.get(self.index);
        self.index += usize::from(token.is_some());
        token
    }

    fn error(&self, kind: ParseErrorKind, detail: &str) -> ParseError {
        let span = self
            .tokens
            .get(self.index.saturating_sub(1))
            .or_else(|| self.tokens.get(self.index))
            .map_or(self.fallback, |token| token.span);
        from_span(kind, span, detail)
    }
}

fn is_int_type(word: &str) -> bool {
    word.strip_prefix('i').is_some_and(|digits| {
        !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
    })
}

fn is_integer(word: &str) -> bool {
    let digits = word.strip_prefix('-').unwrap_or(word);
    !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
}

fn relocate_error(instruction: &Instruction, mut error: ParseError) -> ParseError {
    error.span = relocate_span(instruction, error.span);
    error
}

fn relocate_span(instruction: &Instruction, relative: SourceSpan) -> SourceSpan {
    SourceSpan {
        start: instruction.span.start + relative.start,
        end: instruction.span.start + relative.end,
        line: instruction.span.line + relative.line - 1,
        column: if relative.line == 1 {
            instruction.span.column + relative.column - 1
        } else {
            relative.column
        },
    }
}
