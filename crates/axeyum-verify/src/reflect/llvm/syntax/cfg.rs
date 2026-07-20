//! Typed control-flow syntax and whole-function graph validation.

use std::collections::{BTreeMap, BTreeSet};

use super::{
    Function, Instruction, Operand, Parameter, ParseError, ParseErrorKind, ScalarInstruction,
    SourceSpan, Token, TokenKind, from_span, lex, parse_scalar_instruction,
};

/// Stable identity of one basic block.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum BlockId {
    /// The source function's unlabeled entry block.
    Entry,
    /// An explicitly labeled block, without `%` or surrounding quotes.
    Label(String),
}

/// One incoming value and predecessor edge for a PHI.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PhiIncoming {
    /// Value selected when `predecessor` transferred control to this block.
    pub value: Operand,
    /// Predecessor block named by the incoming edge.
    pub predecessor: BlockId,
}

/// One typed scalar integer PHI.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Phi {
    /// Destination SSA name.
    pub dest: String,
    /// Incoming and result integer width.
    pub width: u32,
    /// Incoming pairs in source order.
    pub incomings: Vec<PhiIncoming>,
    /// Source span of the complete PHI.
    pub span: SourceSpan,
}

/// One normalized integer switch case.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SwitchCase {
    /// Case value normalized modulo the switch width.
    pub value: u128,
    /// Destination for the matching value.
    pub target: BlockId,
}

/// Supported scalar CFG terminators.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TerminatorKind {
    /// Return a scalar integer value.
    Return {
        /// Return value width.
        width: u32,
        /// Returned value.
        value: Operand,
    },
    /// Unconditional transfer.
    Branch {
        /// Destination block.
        target: BlockId,
    },
    /// Conditional transfer with explicit edge roles.
    CondBranch {
        /// Scalar `i1` condition.
        condition: Operand,
        /// Destination when the condition is true.
        true_target: BlockId,
        /// Destination when the condition is false.
        false_target: BlockId,
    },
    /// Integer multi-way transfer.
    Switch {
        /// Scrutinee and case width.
        width: u32,
        /// Integer scrutinee.
        value: Operand,
        /// Destination when no case matches.
        default_target: BlockId,
        /// Ordered normalized cases.
        cases: Vec<SwitchCase>,
    },
    /// A control point with no defined execution semantics.
    Unreachable,
}

/// One typed terminator plus non-semantic metadata attachments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Terminator {
    /// Control-flow operation.
    pub kind: TerminatorKind,
    /// Source metadata attachments retained verbatim, without leading commas.
    pub metadata: Vec<String>,
    /// Source span covering the complete terminator.
    pub span: SourceSpan,
}

/// One validated scalar basic block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CfgBlock {
    /// Block identity.
    pub id: BlockId,
    /// Leading PHIs in source order.
    pub phis: Vec<Phi>,
    /// Non-PHI scalar body instructions in source order.
    pub instructions: Vec<ScalarInstruction>,
    /// Exactly one final terminator.
    pub terminator: Terminator,
    /// Unique predecessors in deterministic source-block order.
    pub predecessors: Vec<BlockId>,
    /// Unique successors in first-occurrence terminator order.
    pub successors: Vec<BlockId>,
    /// Source span of the original block.
    pub span: SourceSpan,
}

/// A typed and structurally validated scalar LLVM control-flow graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarCfg {
    /// Function name.
    pub name: String,
    /// Function parameters.
    pub params: Vec<Parameter>,
    /// Entry block identity.
    pub entry: BlockId,
    /// Blocks in source order.
    pub blocks: Vec<CfgBlock>,
}

/// Parse and validate the scalar control-flow subset of one structured function.
///
/// # Errors
///
/// Returns a located error for malformed graph structure, unsupported
/// instructions or terminators, undefined labels, and invalid PHI predecessor
/// sets. The function never panics for source input.
pub fn parse_scalar_cfg(function: &Function) -> Result<ScalarCfg, ParseError> {
    let entry = function.blocks.first().map(block_id).ok_or_else(|| {
        from_span(
            ParseErrorKind::MalformedControlFlow,
            function.span,
            "function has no basic block",
        )
    })?;
    let mut blocks = function
        .blocks
        .iter()
        .map(parse_block)
        .collect::<Result<Vec<_>, _>>()?;
    let positions = blocks
        .iter()
        .enumerate()
        .map(|(index, block)| (block.id.clone(), index))
        .collect::<BTreeMap<_, _>>();

    for block in &blocks {
        for target in &block.successors {
            if !positions.contains_key(target) {
                return Err(from_span(
                    ParseErrorKind::UndefinedBlockLabel,
                    block.terminator.span,
                    &format!("undefined CFG target {}", display_block(target)),
                ));
            }
        }
        for phi in &block.phis {
            for incoming in &phi.incomings {
                if !positions.contains_key(&incoming.predecessor) {
                    return Err(from_span(
                        ParseErrorKind::UndefinedBlockLabel,
                        phi.span,
                        &format!(
                            "undefined PHI predecessor {}",
                            display_block(&incoming.predecessor)
                        ),
                    ));
                }
            }
        }
    }

    let block_order = blocks
        .iter()
        .map(|block| block.id.clone())
        .collect::<Vec<_>>();
    for source in &block_order {
        let source_index = positions[source];
        let successors = blocks[source_index].successors.clone();
        for target in successors {
            let target_index = positions[&target];
            push_unique(&mut blocks[target_index].predecessors, source.clone());
        }
    }

    let entry_index = positions[&entry];
    if !blocks[entry_index].predecessors.is_empty() {
        return Err(from_span(
            ParseErrorKind::MalformedControlFlow,
            blocks[entry_index].span,
            "entry block must not have a predecessor",
        ));
    }
    for block in &blocks {
        validate_phis(block)?;
    }

    Ok(ScalarCfg {
        name: function.name.clone(),
        params: function.params.clone(),
        entry,
        blocks,
    })
}

fn block_id(block: &super::Block) -> BlockId {
    block
        .label
        .as_ref()
        .map_or(BlockId::Entry, |label| BlockId::Label(label.clone()))
}

fn parse_block(block: &super::Block) -> Result<CfgBlock, ParseError> {
    if block.instructions.is_empty() {
        return Err(from_span(
            ParseErrorKind::MalformedControlFlow,
            block.span,
            "basic block is empty",
        ));
    }
    let mut phis = Vec::new();
    let mut instructions = Vec::new();
    let mut terminator = None;
    let mut body_started = false;
    let mut index = 0;
    while index < block.instructions.len() {
        let (instruction, consumed) = grouped_instruction(&block.instructions[index..])?;
        index += consumed;
        if terminator.is_some() {
            return Err(from_span(
                ParseErrorKind::MalformedControlFlow,
                instruction.span,
                "instruction appears after a terminator",
            ));
        }
        if is_phi(&instruction.text) {
            if body_started {
                return Err(from_span(
                    ParseErrorKind::InvalidPhi,
                    instruction.span,
                    "PHI instructions must be contiguous at block start",
                ));
            }
            phis.push(parse_phi(&instruction)?);
        } else if is_terminator(&instruction.text) {
            body_started = true;
            terminator = Some(parse_terminator(&instruction)?);
        } else {
            body_started = true;
            instructions.push(parse_scalar_instruction(&instruction)?);
        }
    }
    let terminator = terminator.ok_or_else(|| {
        from_span(
            ParseErrorKind::MalformedControlFlow,
            block.span,
            "basic block has no supported terminator",
        )
    })?;
    let successors = successors(&terminator.kind);
    Ok(CfgBlock {
        id: block_id(block),
        phis,
        instructions,
        terminator,
        predecessors: Vec::new(),
        successors,
        span: block.span,
    })
}

fn grouped_instruction(source: &[Instruction]) -> Result<(Instruction, usize), ParseError> {
    let first = source
        .first()
        .expect("parse_block passes a nonempty suffix");
    if !first.text.starts_with("switch ") {
        return Ok((first.clone(), 1));
    }
    let mut depth = 0_i32;
    let mut opened = false;
    for (index, line) in source.iter().enumerate() {
        for token in relocated_tokens(line, &line.text)? {
            match token.kind {
                TokenKind::Punct('[') => {
                    depth += 1;
                    opened = true;
                }
                TokenKind::Punct(']') => depth -= 1,
                _ => {}
            }
            if depth < 0 {
                return Err(from_span(
                    ParseErrorKind::MalformedControlFlow,
                    line.span,
                    "switch case list has an unmatched closing bracket",
                ));
            }
        }
        if opened && depth == 0 {
            let grouped = layout_group(&source[..=index]);
            return Ok((
                Instruction {
                    text: grouped,
                    span: SourceSpan {
                        end: line.span.end,
                        ..first.span
                    },
                },
                index + 1,
            ));
        }
    }
    Err(from_span(
        ParseErrorKind::MalformedControlFlow,
        first.span,
        "switch case list is not closed",
    ))
}

fn layout_group(lines: &[Instruction]) -> String {
    let first = lines.first().expect("group has a first source line");
    let last = lines.last().expect("group has a last source line");
    let mut bytes = vec![b' '; last.span.end - first.span.start];
    let mut previous_line = first.span.line;
    let mut previous_end = 0;
    for line in lines {
        let relative_start = line.span.start - first.span.start;
        let relative_end = relative_start + line.text.len();
        bytes[relative_start..relative_end].copy_from_slice(line.text.as_bytes());

        let newline_count = line.span.line.saturating_sub(previous_line);
        if newline_count > 0 {
            let last_newline = relative_start.saturating_sub(line.span.column);
            for offset in 0..newline_count.saturating_sub(1) {
                let position = previous_end + offset;
                if position < last_newline {
                    bytes[position] = b'\n';
                }
            }
            bytes[last_newline] = b'\n';
        }
        previous_line = line.span.line;
        previous_end = relative_end;
    }
    String::from_utf8(bytes).expect("spaces plus source UTF-8 remain UTF-8")
}

fn is_phi(text: &str) -> bool {
    text.split_once(" = ")
        .is_some_and(|(_, rhs)| rhs.starts_with("phi "))
}

fn is_terminator(text: &str) -> bool {
    const PREFIXES: &[&str] = &[
        "ret ",
        "br ",
        "switch ",
        "unreachable",
        "indirectbr ",
        "invoke ",
        "callbr ",
        "resume ",
        "catchswitch ",
        "catchret ",
        "cleanupret ",
    ];
    PREFIXES.iter().any(|prefix| text.starts_with(prefix))
}

fn parse_phi(instruction: &Instruction) -> Result<Phi, ParseError> {
    let tokens = relocated_tokens(instruction, &instruction.text)?;
    let mut cursor = Cursor::new(&tokens, instruction.span);
    let dest = cursor.local("PHI destination")?;
    cursor.punct('=')?;
    cursor.word("phi")?;
    let width = cursor.int_type()?;
    let mut incomings = Vec::new();
    let mut seen = BTreeSet::new();
    loop {
        cursor.punct('[')?;
        let value = cursor.operand()?;
        cursor.punct(',')?;
        let predecessor = BlockId::Label(cursor.local("PHI predecessor")?);
        cursor.punct(']')?;
        if !seen.insert(predecessor.clone()) {
            return Err(cursor.error(ParseErrorKind::InvalidPhi, "PHI repeats one predecessor"));
        }
        incomings.push(PhiIncoming { value, predecessor });
        if !cursor.consume_punct(',') {
            break;
        }
    }
    cursor.end(ParseErrorKind::InvalidPhi, "trailing PHI tokens")?;
    if incomings.is_empty() {
        return Err(from_span(
            ParseErrorKind::InvalidPhi,
            instruction.span,
            "PHI must have at least one incoming pair",
        ));
    }
    Ok(Phi {
        dest,
        width,
        incomings,
        span: instruction.span,
    })
}

fn parse_terminator(instruction: &Instruction) -> Result<Terminator, ParseError> {
    let (main, metadata) = split_metadata(&instruction.text, instruction.span)?;
    let tokens = relocated_tokens(instruction, main)?;
    let mut cursor = Cursor::new(&tokens, instruction.span);
    let opcode = cursor.any_word("terminator opcode")?;
    let kind = match opcode.as_str() {
        "ret" => parse_return(&mut cursor)?,
        "br" => parse_branch(&mut cursor)?,
        "switch" => parse_switch(&mut cursor)?,
        "unreachable" => {
            cursor.end(
                ParseErrorKind::MalformedControlFlow,
                "trailing `unreachable` tokens",
            )?;
            TerminatorKind::Unreachable
        }
        _ => {
            return Err(cursor.error(
                ParseErrorKind::UnsupportedInstruction,
                &format!("unsupported terminator `{opcode}`"),
            ));
        }
    };
    Ok(Terminator {
        kind,
        metadata,
        span: instruction.span,
    })
}

fn parse_return(cursor: &mut Cursor<'_>) -> Result<TerminatorKind, ParseError> {
    if cursor.peek_word("void") {
        return Err(cursor.error(
            ParseErrorKind::UnsupportedInstruction,
            "void return is outside the scalar CFG slice",
        ));
    }
    let width = cursor.int_type()?;
    let value = cursor.operand()?;
    cursor.end(
        ParseErrorKind::MalformedControlFlow,
        "trailing return tokens",
    )?;
    Ok(TerminatorKind::Return { width, value })
}

fn parse_branch(cursor: &mut Cursor<'_>) -> Result<TerminatorKind, ParseError> {
    if cursor.peek_word("label") {
        let target = cursor.label()?;
        cursor.end(
            ParseErrorKind::MalformedControlFlow,
            "trailing branch tokens",
        )?;
        return Ok(TerminatorKind::Branch { target });
    }
    let width = cursor.int_type()?;
    if width != 1 {
        return Err(cursor.error(
            ParseErrorKind::MalformedControlFlow,
            "conditional branch condition must have type i1",
        ));
    }
    let condition = cursor.operand()?;
    cursor.punct(',')?;
    let true_target = cursor.label()?;
    cursor.punct(',')?;
    let false_target = cursor.label()?;
    cursor.end(
        ParseErrorKind::MalformedControlFlow,
        "trailing branch tokens",
    )?;
    Ok(TerminatorKind::CondBranch {
        condition,
        true_target,
        false_target,
    })
}

fn parse_switch(cursor: &mut Cursor<'_>) -> Result<TerminatorKind, ParseError> {
    let width = cursor.int_type()?;
    let value = cursor.operand()?;
    cursor.punct(',')?;
    let default_target = cursor.label()?;
    cursor.punct('[')?;
    let mut cases = Vec::new();
    let mut seen = BTreeSet::new();
    while !cursor.consume_punct(']') {
        let case_type_span = cursor.current_span();
        let case_width = cursor.int_type()?;
        if case_width != width {
            return Err(from_span(
                ParseErrorKind::MalformedControlFlow,
                case_type_span,
                "switch case width does not match the scrutinee",
            ));
        }
        let raw = cursor.constant("switch case constant")?;
        let case_value = normalize_constant(&raw, width, cursor.fallback)?;
        cursor.punct(',')?;
        let target = cursor.label()?;
        if !seen.insert(case_value) {
            return Err(cursor.error(
                ParseErrorKind::MalformedControlFlow,
                "switch contains duplicate normalized case constants",
            ));
        }
        cases.push(SwitchCase {
            value: case_value,
            target,
        });
        cursor.consume_punct(',');
    }
    cursor.end(
        ParseErrorKind::MalformedControlFlow,
        "trailing switch tokens",
    )?;
    Ok(TerminatorKind::Switch {
        width,
        value,
        default_target,
        cases,
    })
}

fn split_metadata(text: &str, span: SourceSpan) -> Result<(&str, Vec<String>), ParseError> {
    let Some(start) = text.find(", !") else {
        return Ok((text, Vec::new()));
    };
    let main = text[..start].trim_end();
    let mut attachments = Vec::new();
    for raw in text[start + 1..].split(',') {
        let attachment = raw.trim();
        let mut words = attachment.split_whitespace();
        let key = words.next();
        let value = words.next();
        if !key.is_some_and(|word| word.starts_with('!'))
            || !value.is_some_and(|word| word.starts_with('!'))
            || words.next().is_some()
        {
            return Err(from_span(
                ParseErrorKind::UnsupportedSemantics,
                span,
                "unsupported terminator metadata attachment",
            ));
        }
        attachments.push(attachment.to_owned());
    }
    Ok((main, attachments))
}

fn relocated_tokens(instruction: &Instruction, text: &str) -> Result<Vec<Token>, ParseError> {
    let mut tokens = lex(text).map_err(|error| relocate_error(instruction, &error))?;
    for token in &mut tokens {
        token.span = relocate_span(instruction, token.span);
    }
    Ok(tokens)
}

fn relocate_error(instruction: &Instruction, error: &ParseError) -> ParseError {
    from_span(
        error.kind(),
        relocate_span(instruction, error.span()),
        &error.to_string(),
    )
}

fn relocate_span(instruction: &Instruction, local: SourceSpan) -> SourceSpan {
    SourceSpan {
        start: instruction.span.start + local.start,
        end: (instruction.span.start + local.end).min(instruction.span.end),
        line: instruction.span.line + local.line - 1,
        column: if local.line == 1 {
            instruction.span.column + local.column - 1
        } else {
            local.column
        },
    }
}

fn successors(kind: &TerminatorKind) -> Vec<BlockId> {
    let mut result = Vec::new();
    match kind {
        TerminatorKind::Return { .. } | TerminatorKind::Unreachable => {}
        TerminatorKind::Branch { target } => push_unique(&mut result, target.clone()),
        TerminatorKind::CondBranch {
            true_target,
            false_target,
            ..
        } => {
            push_unique(&mut result, true_target.clone());
            push_unique(&mut result, false_target.clone());
        }
        TerminatorKind::Switch {
            default_target,
            cases,
            ..
        } => {
            push_unique(&mut result, default_target.clone());
            for case in cases {
                push_unique(&mut result, case.target.clone());
            }
        }
    }
    result
}

fn push_unique(values: &mut Vec<BlockId>, value: BlockId) {
    if !values.contains(&value) {
        values.push(value);
    }
}

fn validate_phis(block: &CfgBlock) -> Result<(), ParseError> {
    let expected = block.predecessors.iter().cloned().collect::<BTreeSet<_>>();
    for phi in &block.phis {
        let actual = phi
            .incomings
            .iter()
            .map(|incoming| incoming.predecessor.clone())
            .collect::<BTreeSet<_>>();
        if actual != expected {
            return Err(from_span(
                ParseErrorKind::InvalidPhi,
                phi.span,
                "PHI incoming predecessor set does not match the CFG",
            ));
        }
    }
    Ok(())
}

fn normalize_constant(raw: &str, width: u32, span: SourceSpan) -> Result<u128, ParseError> {
    if width == 0 || width > 128 {
        return Err(from_span(
            ParseErrorKind::UnsupportedInstruction,
            span,
            "switch widths above 128 are outside the scalar CFG slice",
        ));
    }
    if raw.starts_with('-') {
        let signed = raw.parse::<i128>().map_err(|_| {
            from_span(
                ParseErrorKind::MalformedControlFlow,
                span,
                "invalid signed switch constant",
            )
        })?;
        let minimum = if width == 128 {
            i128::MIN
        } else {
            -(1_i128 << (width - 1))
        };
        if signed < minimum {
            return Err(from_span(
                ParseErrorKind::MalformedControlFlow,
                span,
                "signed switch constant does not fit its width",
            ));
        }
        Ok(if width == 128 {
            signed.cast_unsigned()
        } else {
            signed.cast_unsigned() & ((1_u128 << width) - 1)
        })
    } else {
        let unsigned = raw.parse::<u128>().map_err(|_| {
            from_span(
                ParseErrorKind::MalformedControlFlow,
                span,
                "invalid unsigned switch constant",
            )
        })?;
        if width < 128 && unsigned >= (1_u128 << width) {
            return Err(from_span(
                ParseErrorKind::MalformedControlFlow,
                span,
                "unsigned switch constant does not fit its width",
            ));
        }
        Ok(unsigned)
    }
}

fn display_block(block: &BlockId) -> String {
    match block {
        BlockId::Entry => "<entry>".to_owned(),
        BlockId::Label(label) => format!("%{label}"),
    }
}

struct Cursor<'a> {
    tokens: &'a [Token],
    index: usize,
    fallback: SourceSpan,
}

impl<'a> Cursor<'a> {
    fn new(tokens: &'a [Token], fallback: SourceSpan) -> Self {
        Self {
            tokens,
            index: 0,
            fallback,
        }
    }

    fn peek_word(&self, expected: &str) -> bool {
        matches!(
            self.tokens.get(self.index).map(|token| &token.kind),
            Some(TokenKind::Word(word)) if word == expected
        )
    }

    fn any_word(&mut self, what: &str) -> Result<String, ParseError> {
        let token = self.next(what)?;
        match &token.kind {
            TokenKind::Word(word) => Ok(word.clone()),
            _ => Err(from_span(
                ParseErrorKind::MalformedControlFlow,
                token.span,
                &format!("expected {what}"),
            )),
        }
    }

    fn word(&mut self, expected: &str) -> Result<(), ParseError> {
        let token = self.next(expected)?;
        if token.kind == TokenKind::Word(expected.to_owned()) {
            Ok(())
        } else {
            Err(from_span(
                ParseErrorKind::MalformedControlFlow,
                token.span,
                &format!("expected `{expected}`"),
            ))
        }
    }

    fn local(&mut self, what: &str) -> Result<String, ParseError> {
        let token = self.next(what)?;
        match &token.kind {
            TokenKind::LocalName(name) => Ok(name.clone()),
            _ => Err(from_span(
                ParseErrorKind::MalformedControlFlow,
                token.span,
                &format!("expected {what}"),
            )),
        }
    }

    fn label(&mut self) -> Result<BlockId, ParseError> {
        self.word("label")?;
        self.local("block label").map(BlockId::Label)
    }

    fn int_type(&mut self) -> Result<u32, ParseError> {
        let token = self.next("integer type")?;
        let TokenKind::Word(word) = &token.kind else {
            return Err(from_span(
                ParseErrorKind::MalformedControlFlow,
                token.span,
                "expected integer type",
            ));
        };
        let width = word
            .strip_prefix('i')
            .and_then(|digits| digits.parse::<u32>().ok())
            .filter(|width| *width > 0)
            .ok_or_else(|| {
                from_span(
                    ParseErrorKind::UnsupportedInstruction,
                    token.span,
                    "expected scalar integer type",
                )
            })?;
        Ok(width)
    }

    fn operand(&mut self) -> Result<Operand, ParseError> {
        let token = self.next("scalar operand")?;
        match &token.kind {
            TokenKind::LocalName(name) => Ok(Operand::Local(name.clone())),
            TokenKind::Word(word) if matches!(word.as_str(), "poison" | "undef") => Err(from_span(
                ParseErrorKind::UnsupportedSemantics,
                token.span,
                &format!("`{word}` is outside the checked scalar CFG slice"),
            )),
            TokenKind::Word(word) => Ok(Operand::Constant(word.clone())),
            _ => Err(from_span(
                ParseErrorKind::MalformedControlFlow,
                token.span,
                "expected scalar operand",
            )),
        }
    }

    fn constant(&mut self, what: &str) -> Result<String, ParseError> {
        let token = self.next(what)?;
        match &token.kind {
            TokenKind::Word(word) if matches!(word.as_str(), "poison" | "undef") => Err(from_span(
                ParseErrorKind::UnsupportedSemantics,
                token.span,
                &format!("`{word}` is outside the checked scalar CFG slice"),
            )),
            TokenKind::Word(word) => Ok(word.clone()),
            _ => Err(from_span(
                ParseErrorKind::MalformedControlFlow,
                token.span,
                &format!("expected {what}"),
            )),
        }
    }

    fn punct(&mut self, expected: char) -> Result<(), ParseError> {
        let token = self.next("punctuation")?;
        if token.kind == TokenKind::Punct(expected) {
            Ok(())
        } else {
            Err(from_span(
                ParseErrorKind::MalformedControlFlow,
                token.span,
                &format!("expected `{expected}`"),
            ))
        }
    }

    fn consume_punct(&mut self, expected: char) -> bool {
        if self
            .tokens
            .get(self.index)
            .is_some_and(|token| token.kind == TokenKind::Punct(expected))
        {
            self.index += 1;
            true
        } else {
            false
        }
    }

    fn end(&self, kind: ParseErrorKind, detail: &str) -> Result<(), ParseError> {
        if let Some(token) = self.tokens.get(self.index) {
            Err(from_span(kind, token.span, detail))
        } else {
            Ok(())
        }
    }

    fn next(&mut self, what: &str) -> Result<&'a Token, ParseError> {
        let token = self.tokens.get(self.index).ok_or_else(|| {
            from_span(
                ParseErrorKind::MalformedControlFlow,
                self.fallback,
                &format!("missing {what}"),
            )
        })?;
        self.index += 1;
        Ok(token)
    }

    fn error(&self, kind: ParseErrorKind, detail: &str) -> ParseError {
        from_span(
            kind,
            self.tokens
                .get(self.index)
                .map_or(self.fallback, |token| token.span),
            detail,
        )
    }

    fn current_span(&self) -> SourceSpan {
        self.tokens
            .get(self.index)
            .map_or(self.fallback, |token| token.span)
    }
}
