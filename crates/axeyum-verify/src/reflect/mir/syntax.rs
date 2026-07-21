//! Located typed syntax for the checked Rust MIR scalar and byte-memory profiles.

use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

/// Half-open byte range plus one-based source coordinates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceSpan {
    /// Inclusive byte offset.
    pub start: usize,
    /// Exclusive byte offset.
    pub end: usize,
    /// One-based source line.
    pub line: usize,
    /// One-based UTF-8 byte column.
    pub column: usize,
}

/// A scalar or fixed-byte-array MIR type in the admitted profile.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MirType {
    /// Rust `bool`.
    Bool,
    /// A fixed-width signed or unsigned integer.
    Integer {
        /// Bit width.
        width: u32,
        /// Whether the integer is signed.
        signed: bool,
    },
    /// Target-dependent `usize`.
    Usize,
    /// Target-dependent `isize`.
    Isize,
    /// One by-value `[u8; N]` object.
    ByteArray {
        /// Element count as written in MIR.
        bytes: usize,
    },
}

/// One numbered MIR parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    /// MIR local number (`_1` is `1`).
    pub local: u32,
    /// Parsed parameter type.
    pub ty: MirType,
    /// Source range of the declaration.
    pub span: SourceSpan,
}

/// One numbered MIR local declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalDecl {
    /// MIR local number.
    pub local: u32,
    /// Parsed local type.
    pub ty: MirType,
    /// Source range of the declaration.
    pub span: SourceSpan,
}

/// Whether a local operand consumes (`move`) or reads (`copy`) its place.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocalUse {
    /// `copy _N`.
    Copy,
    /// `move _N`.
    Move,
}

/// A typed integer constant without host-width coercion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntegerConstant {
    /// Whether the source literal has a leading minus sign.
    pub negative: bool,
    /// Absolute source magnitude.
    pub magnitude: u128,
    /// Declared MIR type suffix.
    pub ty: MirType,
}

/// An operand in the checked subset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operand {
    /// A numbered local.
    Local {
        /// Copy/move spelling retained for diagnostics.
        usage: LocalUse,
        /// Local number.
        local: u32,
    },
    /// A Boolean constant.
    Bool(bool),
    /// A typed integer constant.
    Integer(IntegerConstant),
}

/// A binary rvalue opcode admitted by this slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOpcode {
    /// Modular integer addition.
    Add,
    /// Equality.
    Eq,
    /// Signedness-directed less-than.
    Lt,
    /// Boolean or bit-vector AND.
    BitAnd,
    /// Logical right shift of an unsigned integer.
    Shr,
}

/// A typed right-hand side.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rvalue {
    /// Scalar copy, move, or constant.
    Use(Operand),
    /// One admitted binary operation.
    Binary {
        /// Operation.
        op: BinaryOpcode,
        /// Left operand.
        left: Operand,
        /// Right operand.
        right: Operand,
    },
    /// Integer-to-integer cast with the exact MIR `IntToInt` spelling.
    Cast {
        /// Source scalar operand.
        operand: Operand,
        /// Declared destination integer type.
        target: MirType,
    },
    /// Boolean or bit-vector complement.
    Not(Operand),
    /// Read one byte from a fixed array local at an integer local index.
    ArrayRead {
        /// Array local.
        array: u32,
        /// Index local.
        index: u32,
    },
}

/// One checked MIR statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatementKind {
    /// Assign a scalar rvalue to a local.
    Assign {
        /// Destination local.
        destination: u32,
        /// Typed source expression.
        value: Rvalue,
    },
    /// Store one byte through an indexed array place.
    ArrayStore {
        /// Array local.
        array: u32,
        /// Index local.
        index: u32,
        /// Stored scalar operand.
        value: Operand,
    },
    /// Recognized storage-lifetime noise.
    StorageMarker {
        /// Mentioned local.
        local: u32,
    },
}

/// One located statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Statement {
    /// Typed statement.
    pub kind: StatementKind,
    /// Source range.
    pub span: SourceSpan,
}

/// One `switchInt` case.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchCase {
    /// Source integer value.
    pub value: u128,
    /// Destination block.
    pub target: String,
}

/// A checked terminator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TerminatorKind {
    /// Return `_0`.
    Return,
    /// Unconditional edge.
    Goto {
        /// Destination block.
        target: String,
    },
    /// A Rust assertion with an unwind-to-panic edge.
    Assert {
        /// Boolean operand being checked.
        condition: Operand,
        /// Required Boolean value (`!x` becomes `false`).
        expected: bool,
        /// Normal-success block.
        success: String,
    },
    /// Integer/Boolean dispatch.
    Switch {
        /// Dispatch operand.
        discriminator: Operand,
        /// Explicit cases in source order.
        cases: Vec<SwitchCase>,
        /// Required default destination.
        otherwise: String,
    },
    /// One assigned direct scalar call with an exact normal-return edge.
    Call {
        /// Destination local written on normal return.
        destination: u32,
        /// Registered direct callee spelling.
        callee: String,
        /// Ordered scalar call operands.
        args: Vec<Operand>,
        /// Normal-return destination block.
        return_target: String,
    },
}

/// One located terminator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Terminator {
    /// Typed terminator.
    pub kind: TerminatorKind,
    /// Source range.
    pub span: SourceSpan,
}

/// One ordered basic block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    /// Source block label (`bbN`).
    pub label: String,
    /// Ordered statements before the terminator.
    pub statements: Vec<Statement>,
    /// Required final terminator.
    pub terminator: Terminator,
    /// Source range from label through closing brace.
    pub span: SourceSpan,
}

/// One selected function from a complete `-Zunpretty=mir` module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    /// Source function name.
    pub name: String,
    /// Ordered parameters.
    pub params: Vec<Parameter>,
    /// Declared return type.
    pub return_ty: MirType,
    /// Ordered local declarations, including `_0`.
    pub locals: Vec<LocalDecl>,
    /// Ordered blocks.
    pub blocks: Vec<Block>,
    /// Full source range.
    pub span: SourceSpan,
}

/// Stable syntax failure classes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseErrorKind {
    /// The selected function was absent.
    MissingFunction,
    /// The selected function appeared more than once.
    DuplicateFunction,
    /// A function signature was malformed.
    MalformedHeader,
    /// A type is outside the admitted profile.
    UnsupportedType,
    /// A parameter or local declaration was malformed.
    MalformedLocal,
    /// A local was declared more than once.
    DuplicateLocal,
    /// A block boundary or label was malformed.
    MalformedBlock,
    /// A block label was repeated.
    DuplicateBlock,
    /// A block had no final terminator.
    MissingTerminator,
    /// Source appeared after a block terminator.
    StatementAfterTerminator,
    /// A recognized statement was malformed.
    MalformedStatement,
    /// A statement is outside the admitted profile.
    UnsupportedStatement,
    /// A recognized terminator was malformed.
    MalformedTerminator,
    /// A terminator is outside the admitted profile.
    UnsupportedTerminator,
}

/// Located checked-MIR syntax failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    kind: ParseErrorKind,
    span: SourceSpan,
    detail: String,
}

impl ParseError {
    /// Stable error class.
    #[must_use]
    pub fn kind(&self) -> ParseErrorKind {
        self.kind
    }

    /// Source range responsible for the error.
    #[must_use]
    pub fn span(&self) -> SourceSpan {
        self.span
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} at {}:{}",
            self.detail, self.span.line, self.span.column
        )
    }
}

impl Error for ParseError {}

#[derive(Clone, Copy)]
struct Line<'a> {
    raw: &'a str,
    start: usize,
    number: usize,
}

impl<'a> Line<'a> {
    fn trimmed(self) -> &'a str {
        self.raw.trim()
    }

    fn span(self) -> SourceSpan {
        let leading = self.raw.len() - self.raw.trim_start().len();
        let trimmed = self.raw.trim();
        SourceSpan {
            start: self.start + leading,
            end: self.start + leading + trimmed.len(),
            line: self.number,
            column: leading + 1,
        }
    }
}

fn lines(input: &str) -> Vec<Line<'_>> {
    let mut result = Vec::new();
    let mut offset = 0;
    for (number, with_newline) in input.split_inclusive('\n').enumerate() {
        let raw = with_newline.strip_suffix('\n').unwrap_or(with_newline);
        let raw = raw.strip_suffix('\r').unwrap_or(raw);
        result.push(Line {
            raw,
            start: offset,
            number: number + 1,
        });
        offset += with_newline.len();
    }
    if input.is_empty() || input.ends_with('\n') {
        return result;
    }
    result
}

fn error(kind: ParseErrorKind, span: SourceSpan, detail: impl Into<String>) -> ParseError {
    ParseError {
        kind,
        span,
        detail: detail.into(),
    }
}

fn parse_local(raw: &str, span: SourceSpan) -> Result<u32, ParseError> {
    raw.strip_prefix('_')
        .and_then(|digits| digits.parse().ok())
        .ok_or_else(|| error(ParseErrorKind::MalformedLocal, span, "expected `_N` local"))
}

fn parse_type(raw: &str, span: SourceSpan) -> Result<MirType, ParseError> {
    let raw = raw.trim();
    match raw {
        "bool" => return Ok(MirType::Bool),
        "usize" => return Ok(MirType::Usize),
        "isize" => return Ok(MirType::Isize),
        _ => {}
    }
    if let Some(inner) = raw.strip_prefix("[u8; ").and_then(|v| v.strip_suffix(']')) {
        let bytes = inner.parse().map_err(|_| {
            error(
                ParseErrorKind::UnsupportedType,
                span,
                format!("invalid byte-array length `{inner}`"),
            )
        })?;
        return Ok(MirType::ByteArray { bytes });
    }
    let (signed, digits) = match raw.as_bytes().first() {
        Some(b'u') => (false, &raw[1..]),
        Some(b'i') => (true, &raw[1..]),
        _ => {
            return Err(error(
                ParseErrorKind::UnsupportedType,
                span,
                format!("unsupported MIR type `{raw}`"),
            ));
        }
    };
    let width: u32 = digits.parse().map_err(|_| {
        error(
            ParseErrorKind::UnsupportedType,
            span,
            format!("invalid integer type `{raw}`"),
        )
    })?;
    if !matches!(width, 8 | 16 | 32 | 64 | 128) {
        return Err(error(
            ParseErrorKind::UnsupportedType,
            span,
            format!("unsupported integer width {width}"),
        ));
    }
    Ok(MirType::Integer { width, signed })
}

fn parse_header(line: Line<'_>) -> Result<(String, Vec<Parameter>, MirType), ParseError> {
    let span = line.span();
    let text = line.trimmed();
    let rest = text.strip_prefix("fn ").ok_or_else(|| {
        error(
            ParseErrorKind::MalformedHeader,
            span,
            "expected `fn` header",
        )
    })?;
    let (name, after_name) = rest.split_once('(').ok_or_else(|| {
        error(
            ParseErrorKind::MalformedHeader,
            span,
            "function header has no `(`",
        )
    })?;
    if name.is_empty()
        || !name
            .chars()
            .all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
    {
        return Err(error(
            ParseErrorKind::MalformedHeader,
            span,
            "function name is outside the checked identifier subset",
        ));
    }
    let (params_raw, tail) = after_name.rsplit_once(") -> ").ok_or_else(|| {
        error(
            ParseErrorKind::MalformedHeader,
            span,
            "function header has no return type",
        )
    })?;
    let return_raw = tail.strip_suffix(" {").ok_or_else(|| {
        error(
            ParseErrorKind::MalformedHeader,
            span,
            "function header must end with ` {`",
        )
    })?;
    let return_ty = parse_type(return_raw, span)?;
    if matches!(return_ty, MirType::ByteArray { .. }) {
        return Err(error(
            ParseErrorKind::UnsupportedType,
            span,
            "byte-array returns are outside this slice",
        ));
    }
    let mut params = Vec::new();
    if !params_raw.trim().is_empty() {
        for (index, raw) in params_raw.split(',').enumerate() {
            let (local_raw, ty_raw) = raw.trim().split_once(": ").ok_or_else(|| {
                error(
                    ParseErrorKind::MalformedLocal,
                    span,
                    format!("malformed parameter `{}`", raw.trim()),
                )
            })?;
            let local = parse_local(local_raw, span)?;
            let expected = u32::try_from(index + 1)
                .map_err(|_| error(ParseErrorKind::MalformedLocal, span, "too many parameters"))?;
            if local != expected {
                return Err(error(
                    ParseErrorKind::MalformedLocal,
                    span,
                    format!("parameters must be ordered `_1..`; found _{local}"),
                ));
            }
            params.push(Parameter {
                local,
                ty: parse_type(ty_raw, span)?,
                span,
            });
        }
    }
    Ok((name.to_owned(), params, return_ty))
}

fn selected_header_name(text: &str) -> Option<&str> {
    let rest = text.strip_prefix("fn ")?;
    let end = rest
        .char_indices()
        .find_map(|(index, character)| {
            (character == '(' || character.is_whitespace()).then_some(index)
        })
        .unwrap_or(rest.len());
    let name = &rest[..end];
    (!name.is_empty()).then_some(name)
}

fn parse_local_decl(line: Line<'_>) -> Result<LocalDecl, ParseError> {
    let span = line.span();
    let text = line
        .trimmed()
        .strip_suffix(';')
        .ok_or_else(|| error(ParseErrorKind::MalformedLocal, span, "local lacks `;`"))?;
    let rest = text
        .strip_prefix("let mut ")
        .or_else(|| text.strip_prefix("let "))
        .ok_or_else(|| error(ParseErrorKind::MalformedLocal, span, "malformed local"))?;
    let (local, ty) = rest.split_once(": ").ok_or_else(|| {
        error(
            ParseErrorKind::MalformedLocal,
            span,
            "local declaration lacks type",
        )
    })?;
    Ok(LocalDecl {
        local: parse_local(local, span)?,
        ty: parse_type(ty, span)?,
        span,
    })
}

fn parse_operand(raw: &str, span: SourceSpan) -> Result<Operand, ParseError> {
    let raw = raw.trim();
    if raw == "const true" {
        return Ok(Operand::Bool(true));
    }
    if raw == "const false" {
        return Ok(Operand::Bool(false));
    }
    if let Some(rest) = raw.strip_prefix("copy ") {
        return Ok(Operand::Local {
            usage: LocalUse::Copy,
            local: parse_local(rest, span)?,
        });
    }
    if let Some(rest) = raw.strip_prefix("move ") {
        return Ok(Operand::Local {
            usage: LocalUse::Move,
            local: parse_local(rest, span)?,
        });
    }
    if let Some(rest) = raw.strip_prefix("const ") {
        let (literal, ty_raw) = rest.rsplit_once('_').ok_or_else(|| {
            error(
                ParseErrorKind::MalformedStatement,
                span,
                "integer constant lacks a type suffix",
            )
        })?;
        let ty = parse_type(ty_raw, span)?;
        if matches!(ty, MirType::Bool | MirType::ByteArray { .. }) {
            return Err(error(
                ParseErrorKind::MalformedStatement,
                span,
                "integer constant has a non-integer type",
            ));
        }
        let (negative, magnitude_raw) = literal
            .strip_prefix('-')
            .map_or((false, literal), |value| (true, value));
        let magnitude = magnitude_raw.parse().map_err(|_| {
            error(
                ParseErrorKind::MalformedStatement,
                span,
                format!("invalid integer constant `{literal}`"),
            )
        })?;
        return Ok(Operand::Integer(IntegerConstant {
            negative,
            magnitude,
            ty,
        }));
    }
    Err(error(
        ParseErrorKind::UnsupportedStatement,
        span,
        format!("unsupported operand `{raw}`"),
    ))
}

fn parse_indexed(raw: &str, span: SourceSpan) -> Result<(u32, u32), ParseError> {
    let (array, index) = raw.split_once('[').ok_or_else(|| {
        error(
            ParseErrorKind::MalformedStatement,
            span,
            "indexed place lacks `[`",
        )
    })?;
    let index = index.strip_suffix(']').ok_or_else(|| {
        error(
            ParseErrorKind::MalformedStatement,
            span,
            "indexed place lacks `]`",
        )
    })?;
    Ok((parse_local(array, span)?, parse_local(index, span)?))
}

fn parse_rvalue(raw: &str, span: SourceSpan) -> Result<Rvalue, ParseError> {
    let raw = raw.trim();
    if let Some(place) = raw
        .strip_prefix("copy ")
        .or_else(|| raw.strip_prefix("move "))
        .filter(|place| place.contains('['))
    {
        let (array, index) = parse_indexed(place, span)?;
        return Ok(Rvalue::ArrayRead { array, index });
    }
    if let Some((operand, cast)) = raw.split_once(" as ") {
        let target = cast.strip_suffix(" (IntToInt)").ok_or_else(|| {
            error(
                ParseErrorKind::UnsupportedStatement,
                span,
                "only exact `IntToInt` scalar casts are admitted",
            )
        })?;
        return Ok(Rvalue::Cast {
            operand: parse_operand(operand, span)?,
            target: parse_type(target, span)?,
        });
    }
    if let Some(operand) = raw
        .strip_prefix("Not(")
        .and_then(|rest| rest.strip_suffix(')'))
    {
        return Ok(Rvalue::Not(parse_operand(operand, span)?));
    }
    for (name, op) in [
        ("Add", BinaryOpcode::Add),
        ("Eq", BinaryOpcode::Eq),
        ("Lt", BinaryOpcode::Lt),
        ("BitAnd", BinaryOpcode::BitAnd),
        ("Shr", BinaryOpcode::Shr),
    ] {
        if let Some(args) = raw
            .strip_prefix(name)
            .and_then(|rest| rest.strip_prefix('('))
            .and_then(|rest| rest.strip_suffix(')'))
        {
            let (left, right) = args.split_once(", ").ok_or_else(|| {
                error(
                    ParseErrorKind::MalformedStatement,
                    span,
                    format!("{name} requires two operands"),
                )
            })?;
            return Ok(Rvalue::Binary {
                op,
                left: parse_operand(left, span)?,
                right: parse_operand(right, span)?,
            });
        }
    }
    Ok(Rvalue::Use(parse_operand(raw, span)?))
}

fn parse_call_terminator(text: &str, span: SourceSpan) -> Result<TerminatorKind, ParseError> {
    let (assignment, edges) = text.split_once(" -> [").ok_or_else(|| {
        error(
            ParseErrorKind::MalformedTerminator,
            span,
            "direct call lacks ` -> [` edge list",
        )
    })?;
    let edges = edges.strip_suffix(']').ok_or_else(|| {
        error(
            ParseErrorKind::MalformedTerminator,
            span,
            "direct call edge list lacks closing `]`",
        )
    })?;
    let (destination, invocation) = assignment.split_once(" = ").ok_or_else(|| {
        error(
            ParseErrorKind::MalformedTerminator,
            span,
            "direct call lacks an assigned destination",
        )
    })?;
    let destination = parse_local(destination, span)?;
    let (callee, args) = invocation.split_once('(').ok_or_else(|| {
        error(
            ParseErrorKind::MalformedTerminator,
            span,
            "direct call lacks `(`",
        )
    })?;
    let args = args.strip_suffix(')').ok_or_else(|| {
        error(
            ParseErrorKind::MalformedTerminator,
            span,
            "direct call lacks closing `)`",
        )
    })?;
    let bare_identifier = !callee.is_empty()
        && callee
            .chars()
            .all(|character| character == '_' || character.is_ascii_alphanumeric());
    let registered_intrinsic = callee == "core::num::<impl u8>::wrapping_add";
    if !bare_identifier && !registered_intrinsic {
        return Err(error(
            ParseErrorKind::UnsupportedTerminator,
            span,
            "only bare direct calls and the registered u8 wrapping-add intrinsic are admitted",
        ));
    }
    let args = if args.is_empty() {
        Vec::new()
    } else {
        args.split(", ")
            .map(|argument| parse_operand(argument, span))
            .collect::<Result<Vec<_>, _>>()?
    };
    let (normal, unwind) = edges.split_once(", ").ok_or_else(|| {
        error(
            ParseErrorKind::MalformedTerminator,
            span,
            "direct call requires normal-return and unwind edges",
        )
    })?;
    let return_target = normal.strip_prefix("return: ").ok_or_else(|| {
        error(
            ParseErrorKind::MalformedTerminator,
            span,
            "direct call lacks `return:` target",
        )
    })?;
    if return_target.is_empty() {
        return Err(error(
            ParseErrorKind::MalformedTerminator,
            span,
            "direct call has an empty return target",
        ));
    }
    if unwind != "unwind continue" {
        return Err(error(
            ParseErrorKind::UnsupportedTerminator,
            span,
            "only exact `unwind continue` direct calls are admitted",
        ));
    }
    Ok(TerminatorKind::Call {
        destination,
        callee: callee.to_owned(),
        args,
        return_target: return_target.to_owned(),
    })
}

fn parse_statement(line: Line<'_>) -> Result<Statement, ParseError> {
    let span = line.span();
    let text = line.trimmed().strip_suffix(';').ok_or_else(|| {
        error(
            ParseErrorKind::MalformedStatement,
            span,
            "statement lacks `;`",
        )
    })?;
    if let Some(local) = text
        .strip_prefix("StorageLive(")
        .or_else(|| text.strip_prefix("StorageDead("))
        .and_then(|rest| rest.strip_suffix(')'))
    {
        return Ok(Statement {
            kind: StatementKind::StorageMarker {
                local: parse_local(local, span)?,
            },
            span,
        });
    }
    let (destination, value) = text.split_once(" = ").ok_or_else(|| {
        error(
            ParseErrorKind::UnsupportedStatement,
            span,
            format!("unsupported statement `{text}`"),
        )
    })?;
    let kind = if destination.contains('[') {
        let (array, index) = parse_indexed(destination, span)?;
        StatementKind::ArrayStore {
            array,
            index,
            value: parse_operand(value, span)?,
        }
    } else {
        StatementKind::Assign {
            destination: parse_local(destination, span)?,
            value: parse_rvalue(value, span)?,
        }
    };
    Ok(Statement { kind, span })
}

#[allow(clippy::too_many_lines)]
fn parse_terminator(line: Line<'_>) -> Result<Option<Terminator>, ParseError> {
    let span = line.span();
    let text = line.trimmed().strip_suffix(';').unwrap_or(line.trimmed());
    let kind = if text == "return" {
        TerminatorKind::Return
    } else if let Some(target) = text.strip_prefix("goto -> ") {
        TerminatorKind::Goto {
            target: target.to_owned(),
        }
    } else if text.contains(" = ") && text.contains(" -> [") {
        parse_call_terminator(text, span)?
    } else if let Some(rest) = text.strip_prefix("assert(") {
        let (condition_raw, _) = rest.split_once(", \"").ok_or_else(|| {
            error(
                ParseErrorKind::MalformedTerminator,
                span,
                "assert lacks a message boundary",
            )
        })?;
        if !rest.contains("unwind continue]") {
            return Err(error(
                ParseErrorKind::UnsupportedTerminator,
                span,
                "only `unwind continue` assertions are admitted",
            ));
        }
        let (expected, condition_raw) = condition_raw
            .strip_prefix('!')
            .map_or((true, condition_raw), |inner| (false, inner));
        let success = rest
            .split("success: ")
            .nth(1)
            .and_then(|tail| tail.split([',', ']']).next())
            .filter(|target| !target.is_empty())
            .ok_or_else(|| {
                error(
                    ParseErrorKind::MalformedTerminator,
                    span,
                    "assert lacks a success target",
                )
            })?;
        TerminatorKind::Assert {
            condition: parse_operand(condition_raw, span)?,
            expected,
            success: success.to_owned(),
        }
    } else if let Some(rest) = text.strip_prefix("switchInt(") {
        let (discriminator, arms) = rest.split_once(") -> [").ok_or_else(|| {
            error(
                ParseErrorKind::MalformedTerminator,
                span,
                "malformed switchInt header",
            )
        })?;
        let arms = arms.strip_suffix(']').ok_or_else(|| {
            error(
                ParseErrorKind::MalformedTerminator,
                span,
                "switchInt lacks closing `]`",
            )
        })?;
        let mut cases = Vec::new();
        let mut otherwise = None;
        for arm in arms.split(", ") {
            let (value, target) = arm.split_once(": ").ok_or_else(|| {
                error(
                    ParseErrorKind::MalformedTerminator,
                    span,
                    "malformed switchInt arm",
                )
            })?;
            if value == "otherwise" {
                if otherwise.replace(target.to_owned()).is_some() {
                    return Err(error(
                        ParseErrorKind::MalformedTerminator,
                        span,
                        "switchInt repeats otherwise",
                    ));
                }
            } else {
                cases.push(SwitchCase {
                    value: value.parse().map_err(|_| {
                        error(
                            ParseErrorKind::MalformedTerminator,
                            span,
                            format!("invalid switch value `{value}`"),
                        )
                    })?,
                    target: target.to_owned(),
                });
            }
        }
        TerminatorKind::Switch {
            discriminator: parse_operand(discriminator, span)?,
            cases,
            otherwise: otherwise.ok_or_else(|| {
                error(
                    ParseErrorKind::MalformedTerminator,
                    span,
                    "switchInt requires otherwise",
                )
            })?,
        }
    } else if text.starts_with("drop(")
        || text.starts_with("call ")
        || text.starts_with("resume")
        || text.starts_with("unreachable")
    {
        return Err(error(
            ParseErrorKind::UnsupportedTerminator,
            span,
            format!("unsupported terminator `{text}`"),
        ));
    } else {
        return Ok(None);
    };
    Ok(Some(Terminator { kind, span }))
}

fn parse_block(lines: &[Line<'_>], start: usize) -> Result<(Block, usize), ParseError> {
    let header = lines[start];
    let header_span = header.span();
    let label = header
        .trimmed()
        .strip_suffix(": {")
        .filter(|label| {
            label.strip_prefix("bb").is_some_and(|digits| {
                !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit())
            })
        })
        .ok_or_else(|| {
            error(
                ParseErrorKind::MalformedBlock,
                header_span,
                "expected `bbN: {`",
            )
        })?
        .to_owned();
    let mut statements = Vec::new();
    let mut terminator = None;
    let mut index = start + 1;
    while index < lines.len() {
        let line = lines[index];
        let text = line.trimmed();
        if text == "}" {
            let terminator = terminator.ok_or_else(|| {
                error(
                    ParseErrorKind::MissingTerminator,
                    header_span,
                    format!("block {label} has no terminator"),
                )
            })?;
            return Ok((
                Block {
                    label,
                    statements,
                    terminator,
                    span: SourceSpan {
                        start: header_span.start,
                        end: line.span().end,
                        line: header_span.line,
                        column: header_span.column,
                    },
                },
                index + 1,
            ));
        }
        if text.is_empty() {
            index += 1;
            continue;
        }
        if terminator.is_some() {
            return Err(error(
                ParseErrorKind::StatementAfterTerminator,
                line.span(),
                format!("source follows terminator in {label}"),
            ));
        }
        if let Some(parsed) = parse_terminator(line)? {
            terminator = Some(parsed);
        } else {
            statements.push(parse_statement(line)?);
        }
        index += 1;
    }
    Err(error(
        ParseErrorKind::MalformedBlock,
        header_span,
        format!("block {label} is not closed"),
    ))
}

/// Select and parse one named function from complete raw compiler MIR.
///
/// # Errors
///
/// Returns a located error for a missing/duplicate function, malformed typed
/// declarations, or unsupported statements and terminators.
#[allow(clippy::too_many_lines)]
pub fn parse_function(input: &str, selected: &str) -> Result<Function, ParseError> {
    let source_lines = lines(input);
    let mut matches = Vec::new();
    for (index, line) in source_lines.iter().copied().enumerate() {
        if selected_header_name(line.trimmed()) == Some(selected) {
            matches.push(index);
        }
    }
    let start = match matches.as_slice() {
        [] => {
            return Err(error(
                ParseErrorKind::MissingFunction,
                SourceSpan {
                    start: 0,
                    end: 0,
                    line: 1,
                    column: 1,
                },
                format!("MIR function `{selected}` is absent"),
            ));
        }
        [one] => *one,
        [_, duplicate, ..] => {
            return Err(error(
                ParseErrorKind::DuplicateFunction,
                source_lines[*duplicate].span(),
                format!("MIR function `{selected}` appears more than once"),
            ));
        }
    };
    let (name, params, return_ty) = parse_header(source_lines[start])?;
    let mut end = start + 1;
    while end < source_lines.len() {
        let raw = source_lines[end].raw;
        if raw.trim_end() == "}" && raw.trim_start().len() == raw.len() {
            break;
        }
        end += 1;
    }
    if end == source_lines.len() {
        return Err(error(
            ParseErrorKind::MalformedHeader,
            source_lines[start].span(),
            format!("function `{name}` is not closed"),
        ));
    }

    let mut locals = Vec::new();
    let mut local_numbers = BTreeSet::new();
    let mut blocks = Vec::new();
    let mut block_labels = BTreeSet::new();
    let body = &source_lines[start + 1..end];
    let mut index = 0;
    while index < body.len() {
        let line = body[index];
        let text = line.trimmed();
        if text.is_empty() || text.starts_with("debug ") {
            index += 1;
            continue;
        }
        if text.starts_with("let ") {
            let local = parse_local_decl(line)?;
            if !local_numbers.insert(local.local) {
                return Err(error(
                    ParseErrorKind::DuplicateLocal,
                    local.span,
                    format!("local _{} is declared more than once", local.local),
                ));
            }
            locals.push(local);
            index += 1;
            continue;
        }
        if text.ends_with(": {") {
            let (block, next) = parse_block(body, index)?;
            if !block_labels.insert(block.label.clone()) {
                return Err(error(
                    ParseErrorKind::DuplicateBlock,
                    block.span,
                    format!("block {} is repeated", block.label),
                ));
            }
            blocks.push(block);
            index = next;
            continue;
        }
        return Err(error(
            ParseErrorKind::UnsupportedStatement,
            line.span(),
            format!("unsupported function-level MIR `{text}`"),
        ));
    }
    if blocks.is_empty() {
        return Err(error(
            ParseErrorKind::MalformedBlock,
            source_lines[start].span(),
            format!("function `{name}` has no blocks"),
        ));
    }
    let header_span = source_lines[start].span();
    Ok(Function {
        name,
        params,
        return_ty,
        locals,
        blocks,
        span: SourceSpan {
            start: header_span.start,
            end: source_lines[end].span().end,
            line: header_span.line,
            column: header_span.column,
        },
    })
}
