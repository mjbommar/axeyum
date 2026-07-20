//! Structured syntax boundary for textual LLVM functions.
//!
//! This module intentionally starts narrower than the LLVM language reference:
//! it identifies one `define`, its typed/named parameters, blocks, and source
//! instruction lines. Instruction semantics remain in the compatibility
//! reflector while later T5.1.2 slices replace raw lines with typed nodes.

use std::collections::BTreeSet;
use std::error::Error;
use std::fmt;

/// Half-open byte range plus one-based line and column of its first byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceSpan {
    /// Inclusive byte offset in the original input.
    pub start: usize,
    /// Exclusive byte offset in the original input.
    pub end: usize,
    /// One-based source line.
    pub line: usize,
    /// One-based UTF-8 byte column.
    pub column: usize,
}

/// One named, typed function parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    /// Leading LLVM type token (`i32`, `ptr`, and so on).
    pub ty: String,
    /// Logical local name without `%` or surrounding quotes.
    pub name: String,
    /// Source range covering this parameter declaration.
    pub span: SourceSpan,
}

/// One source instruction retained for incremental semantic migration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Instruction {
    /// Trimmed instruction text with an out-of-string comment removed.
    pub text: String,
    /// Exact range of `text` in the original input.
    pub span: SourceSpan,
}

/// One ordered basic block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Block {
    /// Logical label without quotes, or `None` for an unlabeled entry block.
    pub label: Option<String>,
    /// Ordered source instructions.
    pub instructions: Vec<Instruction>,
    /// Source range from the label/first instruction through the final line.
    pub span: SourceSpan,
}

/// Structured syntax for exactly one LLVM function definition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    /// Logical global function name without `@` or surrounding quotes.
    pub name: String,
    /// Exact range of the global name token.
    pub name_span: SourceSpan,
    /// Ordered function parameters.
    pub params: Vec<Parameter>,
    /// Ordered basic blocks.
    pub blocks: Vec<Block>,
    /// Range from `define` through the closing body brace.
    pub span: SourceSpan,
}

/// Stable parser failure classes for fail-closed unsupported accounting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseErrorKind {
    /// No function definition was present.
    MissingDefinition,
    /// More than one function definition was present.
    MultipleDefinitions,
    /// The definition header lacked a valid global name or body boundary.
    MalformedHeader,
    /// A parameter lacked a type or local name.
    MalformedParameter,
    /// A quoted token reached end of input without a closing quote.
    UnterminatedQuotedToken,
    /// Parentheses, brackets, or braces were not balanced.
    UnbalancedDelimiter,
    /// A function body did not have a closing brace.
    UnclosedBody,
    /// Two blocks declared the same source label.
    DuplicateBlockLabel,
}

/// Located syntax failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    kind: ParseErrorKind,
    span: SourceSpan,
    detail: String,
}

impl ParseError {
    /// Stable failure class.
    #[must_use]
    pub fn kind(&self) -> ParseErrorKind {
        self.kind
    }

    /// Source range responsible for the failure.
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

#[derive(Debug, Clone, PartialEq, Eq)]
enum TokenKind {
    Word(String),
    LocalName(String),
    GlobalName(String),
    String,
    Punct(char),
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Token {
    kind: TokenKind,
    span: SourceSpan,
}

/// Parse exactly one textual LLVM function definition.
///
/// Module-level comments, declarations, target lines, attributes, and metadata
/// outside the selected definition are ignored. Unsupported or malformed
/// structure returns a located error and never panics.
///
/// # Errors
///
/// Returns a located [`ParseError`] when the input does not contain exactly one
/// well-delimited function definition, when a parameter is malformed, or when
/// block labels are ambiguous.
pub fn parse_function(input: &str) -> Result<Function, ParseError> {
    let tokens = lex(input)?;
    let defines: Vec<usize> = tokens
        .iter()
        .enumerate()
        .filter_map(|(index, token)| match &token.kind {
            TokenKind::Word(word) if word == "define" => Some(index),
            _ => None,
        })
        .collect();

    let define_index = match defines.as_slice() {
        [] => {
            return Err(error_at(
                input,
                ParseErrorKind::MissingDefinition,
                0,
                "missing `define`",
            ));
        }
        [index] => *index,
        [_, second, ..] => {
            let span = tokens[*second].span;
            return Err(ParseError {
                kind: ParseErrorKind::MultipleDefinitions,
                span,
                detail: "multiple function definitions are not accepted".to_owned(),
            });
        }
    };

    let name_index = function_name_index(&tokens, define_index).ok_or_else(|| {
        from_span(
            ParseErrorKind::MalformedHeader,
            tokens[define_index].span,
            "function header has no global name",
        )
    })?;
    let name = match &tokens[name_index].kind {
        TokenKind::GlobalName(name) => name.clone(),
        _ => unreachable!("name_index selects a global name"),
    };

    let open_params = tokens
        .iter()
        .enumerate()
        .skip(name_index + 1)
        .find_map(|(index, token)| (token.kind == TokenKind::Punct('(')).then_some(index))
        .ok_or_else(|| {
            from_span(
                ParseErrorKind::MalformedHeader,
                tokens[name_index].span,
                "function header has no parameter list",
            )
        })?;
    let close_params = matching_token(
        &tokens,
        open_params,
        '(',
        ')',
        ParseErrorKind::UnbalancedDelimiter,
    )?;
    let params = parse_params(input, &tokens[open_params + 1..close_params])?;

    let open_body = tokens
        .iter()
        .enumerate()
        .skip(close_params + 1)
        .find_map(|(index, token)| (token.kind == TokenKind::Punct('{')).then_some(index))
        .ok_or_else(|| {
            from_span(
                ParseErrorKind::MalformedHeader,
                tokens[close_params].span,
                "function header has no body",
            )
        })?;
    let close_body = matching_token(&tokens, open_body, '{', '}', ParseErrorKind::UnclosedBody)?;
    let body_start = tokens[open_body].span.end;
    let body_end = tokens[close_body].span.start;
    let blocks = parse_blocks(input, body_start, body_end)?;

    Ok(Function {
        name,
        name_span: tokens[name_index].span,
        params,
        blocks,
        span: span(
            input,
            tokens[define_index].span.start,
            tokens[close_body].span.end,
        ),
    })
}

fn function_name_index(tokens: &[Token], define_index: usize) -> Option<usize> {
    let mut brace_depth = 0usize;
    (define_index + 1..tokens.len()).find(|&index| match tokens[index].kind {
        TokenKind::Punct('{') => {
            brace_depth += 1;
            false
        }
        TokenKind::Punct('}') => {
            brace_depth = brace_depth.saturating_sub(1);
            false
        }
        TokenKind::GlobalName(_) if brace_depth == 0 => tokens
            .get(index + 1)
            .is_some_and(|next| next.kind == TokenKind::Punct('(')),
        _ => false,
    })
}

fn parse_params(input: &str, tokens: &[Token]) -> Result<Vec<Parameter>, ParseError> {
    if tokens.is_empty()
        || matches!(tokens.first().map(|t| &t.kind), Some(TokenKind::Word(w)) if w == "void")
    {
        return Ok(Vec::new());
    }

    let mut ranges = Vec::new();
    let mut start = 0;
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate() {
        match token.kind {
            TokenKind::Punct('(' | '[' | '{' | '<') => depth += 1,
            TokenKind::Punct(')' | ']' | '}' | '>') => {
                if depth == 0 {
                    return Err(from_span(
                        ParseErrorKind::UnbalancedDelimiter,
                        token.span,
                        "unbalanced parameter delimiter",
                    ));
                }
                depth -= 1;
            }
            TokenKind::Punct(',') if depth == 0 => {
                ranges.push((start, index));
                start = index + 1;
            }
            _ => {}
        }
    }
    if depth != 0 {
        let token = tokens.last().expect("nonempty parameter tokens");
        return Err(from_span(
            ParseErrorKind::UnbalancedDelimiter,
            token.span,
            "unbalanced parameter delimiter",
        ));
    }
    ranges.push((start, tokens.len()));

    ranges
        .into_iter()
        .map(|(start, end)| parse_param(input, &tokens[start..end]))
        .collect()
}

fn parse_param(input: &str, tokens: &[Token]) -> Result<Parameter, ParseError> {
    let first = tokens.first().ok_or_else(|| {
        error_at(
            input,
            ParseErrorKind::MalformedParameter,
            0,
            "empty parameter declaration",
        )
    })?;
    let ty = match &first.kind {
        TokenKind::Word(word) => word.clone(),
        _ => {
            return Err(from_span(
                ParseErrorKind::MalformedParameter,
                first.span,
                "parameter has no leading type",
            ));
        }
    };
    let (name, name_span) = tokens
        .iter()
        .rev()
        .find_map(|token| match &token.kind {
            TokenKind::LocalName(name) => Some((name.clone(), token.span)),
            _ => None,
        })
        .ok_or_else(|| {
            from_span(
                ParseErrorKind::MalformedParameter,
                first.span,
                "parameter has no local name",
            )
        })?;
    Ok(Parameter {
        ty,
        name,
        span: span(input, first.span.start, name_span.end),
    })
}

fn parse_blocks(input: &str, start: usize, end: usize) -> Result<Vec<Block>, ParseError> {
    let mut blocks = Vec::<Block>::new();
    let mut labels = BTreeSet::new();
    let mut offset = start;

    for source_line in input[start..end].split_inclusive('\n') {
        let without_newline = source_line.strip_suffix('\n').unwrap_or(source_line);
        let code_end = comment_start(without_newline).unwrap_or(without_newline.len());
        let code = &without_newline[..code_end];
        let trim_start = code.len() - code.trim_start().len();
        let trimmed = code.trim();
        if trimmed.is_empty() {
            offset += source_line.len();
            continue;
        }
        let item_start = offset + trim_start;
        let item_end = item_start + trimmed.len();
        let item_span = span(input, item_start, item_end);

        if let Some(raw_label) = trimmed.strip_suffix(':') {
            let label = parse_label(input, raw_label.trim(), item_span)?;
            if !labels.insert(label.clone()) {
                return Err(from_span(
                    ParseErrorKind::DuplicateBlockLabel,
                    item_span,
                    &format!("duplicate block label `{label}`"),
                ));
            }
            blocks.push(Block {
                label: Some(label),
                instructions: Vec::new(),
                span: item_span,
            });
        } else {
            if blocks.is_empty() {
                blocks.push(Block {
                    label: None,
                    instructions: Vec::new(),
                    span: item_span,
                });
            }
            let block = blocks.last_mut().expect("entry block was inserted");
            block.instructions.push(Instruction {
                text: trimmed.to_owned(),
                span: item_span,
            });
            block.span.end = item_span.end;
        }
        offset += source_line.len();
    }
    Ok(blocks)
}

fn parse_label(input: &str, raw: &str, source: SourceSpan) -> Result<String, ParseError> {
    if let Some(quoted) = raw.strip_prefix('"') {
        let Some(inner) = quoted.strip_suffix('"') else {
            return Err(from_span(
                ParseErrorKind::UnterminatedQuotedToken,
                source,
                "unterminated quoted block label",
            ));
        };
        decode_quoted(input, inner, source.start + 1)
    } else if raw.is_empty() {
        Err(from_span(
            ParseErrorKind::MalformedHeader,
            source,
            "empty block label",
        ))
    } else {
        Ok(raw.to_owned())
    }
}

fn lex(input: &str) -> Result<Vec<Token>, ParseError> {
    let bytes = input.as_bytes();
    let mut tokens = Vec::new();
    let mut index = 0;
    while index < bytes.len() {
        let byte = bytes[index];
        if byte.is_ascii_whitespace() {
            index += 1;
            continue;
        }
        if byte == b';' {
            index = input[index..]
                .find('\n')
                .map_or(bytes.len(), |delta| index + delta + 1);
            continue;
        }
        if byte == b'@' || byte == b'%' {
            let prefix = byte;
            let start = index;
            index += 1;
            let name = if index < bytes.len() && bytes[index] == b'"' {
                let (decoded, next) = lex_quoted(input, index)?;
                index = next;
                decoded
            } else {
                let name_start = index;
                while index < bytes.len() && !is_boundary(bytes[index]) {
                    index += 1;
                }
                if index == name_start {
                    return Err(error_at(
                        input,
                        ParseErrorKind::MalformedHeader,
                        start,
                        "empty LLVM name",
                    ));
                }
                input[name_start..index].to_owned()
            };
            let kind = if prefix == b'@' {
                TokenKind::GlobalName(name)
            } else {
                TokenKind::LocalName(name)
            };
            tokens.push(Token {
                kind,
                span: span(input, start, index),
            });
            continue;
        }
        if byte == b'"' {
            let start = index;
            let (_, next) = lex_quoted(input, index)?;
            index = next;
            tokens.push(Token {
                kind: TokenKind::String,
                span: span(input, start, index),
            });
            continue;
        }
        let ch = byte as char;
        if is_punctuation(ch) {
            tokens.push(Token {
                kind: TokenKind::Punct(ch),
                span: span(input, index, index + 1),
            });
            index += 1;
            continue;
        }
        let start = index;
        while index < bytes.len()
            && !bytes[index].is_ascii_whitespace()
            && bytes[index] != b';'
            && bytes[index] != b'@'
            && bytes[index] != b'%'
            && bytes[index] != b'"'
            && !is_punctuation(bytes[index] as char)
        {
            index += 1;
        }
        tokens.push(Token {
            kind: TokenKind::Word(input[start..index].to_owned()),
            span: span(input, start, index),
        });
    }
    Ok(tokens)
}

fn lex_quoted(input: &str, quote: usize) -> Result<(String, usize), ParseError> {
    let bytes = input.as_bytes();
    let mut index = quote + 1;
    let mut decoded = String::new();
    while index < bytes.len() {
        match bytes[index] {
            b'"' => return Ok((decoded, index + 1)),
            b'\\' => {
                if index + 1 >= bytes.len() {
                    break;
                }
                decoded.push(bytes[index + 1] as char);
                index += 2;
            }
            byte => {
                decoded.push(byte as char);
                index += 1;
            }
        }
    }
    Err(error_at(
        input,
        ParseErrorKind::UnterminatedQuotedToken,
        quote,
        "unterminated quoted token",
    ))
}

fn decode_quoted(input: &str, inner: &str, start: usize) -> Result<String, ParseError> {
    let synthetic = format!("\"{inner}\"");
    lex_quoted(&synthetic, 0)
        .map(|(decoded, _)| decoded)
        .map_err(|_| {
            error_at(
                input,
                ParseErrorKind::UnterminatedQuotedToken,
                start.saturating_sub(1),
                "unterminated quoted token",
            )
        })
}

fn matching_token(
    tokens: &[Token],
    open_index: usize,
    open: char,
    close: char,
    missing_kind: ParseErrorKind,
) -> Result<usize, ParseError> {
    let mut depth = 0usize;
    for (index, token) in tokens.iter().enumerate().skip(open_index) {
        if token.kind == TokenKind::Punct(open) {
            depth += 1;
        } else if token.kind == TokenKind::Punct(close) {
            depth -= 1;
            if depth == 0 {
                return Ok(index);
            }
        }
    }
    Err(from_span(
        missing_kind,
        tokens[open_index].span,
        if missing_kind == ParseErrorKind::UnclosedBody {
            "function body is not closed"
        } else {
            "delimiter is not balanced"
        },
    ))
}

fn comment_start(line: &str) -> Option<usize> {
    let mut quoted = false;
    let mut escaped = false;
    for (index, byte) in line.bytes().enumerate() {
        if escaped {
            escaped = false;
        } else if byte == b'\\' && quoted {
            escaped = true;
        } else if byte == b'"' {
            quoted = !quoted;
        } else if byte == b';' && !quoted {
            return Some(index);
        }
    }
    None
}

fn is_boundary(byte: u8) -> bool {
    byte.is_ascii_whitespace()
        || byte == b';'
        || byte == b'@'
        || byte == b'%'
        || byte == b'"'
        || is_punctuation(byte as char)
}

fn is_punctuation(ch: char) -> bool {
    matches!(
        ch,
        '(' | ')' | '{' | '}' | '[' | ']' | '<' | '>' | ',' | ':' | '='
    )
}

fn span(input: &str, start: usize, end: usize) -> SourceSpan {
    let start = start.min(input.len().saturating_sub(1));
    let end = end.max(start + 1).min(input.len());
    let prefix = &input[..start];
    let line = prefix.bytes().filter(|byte| *byte == b'\n').count() + 1;
    let column = prefix
        .rfind('\n')
        .map_or(start + 1, |newline| start - newline);
    SourceSpan {
        start,
        end,
        line,
        column,
    }
}

fn error_at(input: &str, kind: ParseErrorKind, start: usize, detail: &str) -> ParseError {
    ParseError {
        kind,
        span: span(input, start, start + 1),
        detail: detail.to_owned(),
    }
}

fn from_span(kind: ParseErrorKind, span: SourceSpan, detail: &str) -> ParseError {
    ParseError {
        kind,
        span,
        detail: detail.to_owned(),
    }
}
