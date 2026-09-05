//! A native reader for the `Kernel::render_lean` fragment (Next Ten item 9,
//! first half).
//!
//! [`lean_pp`](crate::lean_pp) renders a kernel term to a small, fully
//! parenthesized textual fragment (binders, `fun`/`Pi`-as-arrow, flat
//! application spines, `Sort`, dotted constant names with optional
//! `.{levels}`, `let`, projections, and literals). This module reads that
//! fragment back into a kernel [`ExprId`] against the CURRENT environment, so
//! a `formal.statement` carrying `language: "lean4"` can be checked to be a
//! well-formed proposition of this kernel **on any host, without Lean** —
//! that is the whole point (see `docs/math-department/14-lean-lang.md`,
//! Next Ten item 9, and ADR-1680).
//!
//! # This is untrusted, like every other producer
//!
//! [`Kernel::read_lean`] builds an [`ExprId`] using only the kernel's own
//! public term constructors (`bvar`, `const_`, `app`, `lam`, `pi`, `let_`,
//! `lit`, `sort`) — the same API a prelude module uses. It never touches
//! [`crate::env::Environment::insert_unchecked`] or any other admission gate,
//! so it sits outside the trusted core
//! (`scripts/check-kernel-trusted-core.py`) exactly like a prelude builder:
//! whatever it produces is only as good as the trusted checker
//! (`Kernel::add_declaration`, `Kernel::def_eq`, `Kernel::infer`) that later
//! re-derives its type. A malformed reader can at worst hand the checker a
//! badly-shaped term, which the checker then rejects or accepts on its own
//! terms — it can never forge an admission.
//!
//! # What this does NOT read
//!
//! This reads the `render_lean` **fragment**, not general `.lean` source and
//! not the Mathlib-elaborator surface syntax (`language: "lean4-surface"`).
//! There is no `fun`/`let`/binder implicit-argument annotation (`{}`/`⦃⦄`/
//! `[]`) in this fragment — [`render_lean`](Kernel::render_lean) never emits
//! one — so every binder this reader creates is
//! [`BinderInfo::Default`](crate::BinderInfo::Default), which is exactly
//! what the writer assumed on the way out. The Mathlib surface subset is a
//! separate, larger grammar (typeclass search, coercions, notation) that
//! ADR-1662's census found gated on demand it does not yet have; it is
//! explicitly not built here.
//!
//! # Grammar (informal)
//!
//! ```text
//! expr      := atom+                              -- flat application spine
//! atom      := '(' pi_tail                        -- Pi, after backtracking
//!            | '(' expr ')' ('.' DIGITS)?          -- parenthesized / Proj
//!            | 'fun' '(' ident ':' expr ')' '=>' expr
//!            | 'let' ident ':' expr ':=' expr ';' expr
//!            | 'Prop'
//!            | 'Sort' '(' level ')'
//!            | '@'? name ('.{' level (',' level)* '}')?
//!            | DIGITS                              -- Nat literal
//!            | STRING                              -- Str literal
//! pi_tail   := '(' ident ':' expr ')' '->' expr ')'   -- outer '(' already consumed
//! name      := IDENT ('.' (IDENT | DIGITS))*          -- DIGITS segment only
//!                                                       when spelled `_N`
//! level     := DIGITS
//!            | (IDENT ('+' DIGITS)?)
//!            | '(' ('max'|'imax') level level ')' ('+' DIGITS)?
//! ```
//!
//! The Pi form is disambiguated from a plain parenthesized expression by
//! **backtracking**, not by a fixed-depth lookahead: an atom-wrapped Pi
//! nested inside another atom wrap (`(((x : T) -> B))`) is not structurally
//! different at the token level from a one-off parenthesized application, so
//! [`Reader::parse_atom`] tries the Pi production first only when the very
//! next token is another `(`, and unwinds to the generic parenthesized-expr
//! production on any mismatch.

use crate::{BinderInfo, ExprId, Kernel, LevelId, Lit, NameId, NameNode, NatLit};

// ---------------------------------------------------------------------------
// Tokens
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    LParen,
    RParen,
    LBrace,
    RBrace,
    Dot,
    Comma,
    Colon,
    ColonEq,
    Arrow,
    FatArrow,
    Semicolon,
    At,
    Plus,
    KwFun,
    KwLet,
    KwProp,
    KwSort,
    Ident(String),
    Number(String),
    Str(String),
}

impl Tok {
    fn describe(&self) -> String {
        match self {
            Tok::LParen => "'('".to_owned(),
            Tok::RParen => "')'".to_owned(),
            Tok::LBrace => "'{'".to_owned(),
            Tok::RBrace => "'}'".to_owned(),
            Tok::Dot => "'.'".to_owned(),
            Tok::Comma => "','".to_owned(),
            Tok::Colon => "':'".to_owned(),
            Tok::ColonEq => "':='".to_owned(),
            Tok::Arrow => "'->'".to_owned(),
            Tok::FatArrow => "'=>'".to_owned(),
            Tok::Semicolon => "';'".to_owned(),
            Tok::At => "'@'".to_owned(),
            Tok::Plus => "'+'".to_owned(),
            Tok::KwFun => "'fun'".to_owned(),
            Tok::KwLet => "'let'".to_owned(),
            Tok::KwProp => "'Prop'".to_owned(),
            Tok::KwSort => "'Sort'".to_owned(),
            Tok::Ident(s) => format!("identifier {s:?}"),
            Tok::Number(s) => format!("number {s:?}"),
            Tok::Str(s) => format!("string {s:?}"),
        }
    }
}

/// A typed reason [`Kernel::read_lean`] failed, with the byte position of the
/// offending token in the input where one is available.
///
/// Every variant is a distinct, machine-classifiable finding: a corpus sweep
/// over the fact ledger tabulates counts per variant rather than lumping
/// every non-reading statement into one bucket (see
/// `tests/lean_read_round_trip.rs`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReadError {
    /// A token was expected and something else (or nothing) was found.
    UnexpectedToken {
        /// Byte offset of the offending token.
        pos: usize,
        /// A description of the token actually found.
        found: String,
        /// A description of what the grammar expected at this position.
        expected: String,
    },
    /// The input ended while a production still needed more tokens.
    UnexpectedEof {
        /// A description of what the grammar still expected.
        expected: String,
    },
    /// A dotted (qualified) name does not resolve to any declaration this
    /// kernel currently admits.
    UnknownConstant {
        /// Byte offset where the name started.
        pos: usize,
        /// The dotted name text as read.
        name: String,
    },
    /// A bare (dot-free) name matched neither an enclosing binder nor a
    /// top-level declaration — most likely a variable used outside the
    /// scope that would bind it.
    UnboundVariable {
        /// Byte offset where the name started.
        pos: usize,
        /// The name text as read.
        name: String,
    },
    /// A universe-level expression was malformed (unknown keyword, missing
    /// operand, or a numeral read did not have a `+`).
    BadLevel {
        /// Byte offset of the offending token.
        pos: usize,
        /// A human-readable explanation.
        detail: String,
    },
    /// A literal (`Nat` or `Str`) did not decode.
    InvalidLiteral {
        /// Byte offset of the offending literal.
        pos: usize,
        /// A human-readable explanation.
        detail: String,
    },
    /// The expression production finished but input remained.
    TrailingInput {
        /// Byte offset of the first leftover token.
        pos: usize,
    },
}

impl std::fmt::Display for ReadError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReadError::UnexpectedToken {
                pos,
                found,
                expected,
            } => write!(f, "at byte {pos}: expected {expected}, found {found}"),
            ReadError::UnexpectedEof { expected } => {
                write!(f, "unexpected end of input: expected {expected}")
            }
            ReadError::UnknownConstant { pos, name } => {
                write!(f, "at byte {pos}: unknown constant {name:?}")
            }
            ReadError::UnboundVariable { pos, name } => {
                write!(f, "at byte {pos}: unbound variable {name:?}")
            }
            ReadError::BadLevel { pos, detail } => {
                write!(f, "at byte {pos}: bad universe level: {detail}")
            }
            ReadError::InvalidLiteral { pos, detail } => {
                write!(f, "at byte {pos}: invalid literal: {detail}")
            }
            ReadError::TrailingInput { pos } => {
                write!(
                    f,
                    "at byte {pos}: trailing input after a complete expression"
                )
            }
        }
    }
}

impl std::error::Error for ReadError {}

impl ReadError {
    /// A short, stable classification label, independent of the message
    /// text, for tabulating a population of failures by kind.
    #[must_use]
    pub fn class(&self) -> &'static str {
        match self {
            ReadError::UnexpectedToken { .. } => "unexpected-token",
            ReadError::UnexpectedEof { .. } => "unexpected-eof",
            ReadError::UnknownConstant { .. } => "unknown-constant",
            ReadError::UnboundVariable { .. } => "unbound-variable",
            ReadError::BadLevel { .. } => "bad-level",
            ReadError::InvalidLiteral { .. } => "invalid-literal",
            ReadError::TrailingInput { .. } => "trailing-input",
        }
    }
}

// ---------------------------------------------------------------------------
// Lexer
// ---------------------------------------------------------------------------

fn is_ident_start(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_ident_continue(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn tokenize(text: &str) -> Result<Vec<(Tok, usize)>, ReadError> {
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < bytes.len() {
        if (bytes[i] as char).is_whitespace() {
            i += 1;
            continue;
        }
        let start = i;
        let (tok, next) = lex_one(text, bytes, i)?;
        out.push((tok, start));
        i = next;
    }
    Ok(out)
}

/// One token starting at byte `i` (not whitespace). Returns the token and the
/// byte offset just past it.
fn lex_one(text: &str, bytes: &[u8], i: usize) -> Result<(Tok, usize), ReadError> {
    let c = bytes[i] as char;
    match c {
        '(' => Ok((Tok::LParen, i + 1)),
        ')' => Ok((Tok::RParen, i + 1)),
        '{' => Ok((Tok::LBrace, i + 1)),
        '}' => Ok((Tok::RBrace, i + 1)),
        ',' => Ok((Tok::Comma, i + 1)),
        ';' => Ok((Tok::Semicolon, i + 1)),
        '@' => Ok((Tok::At, i + 1)),
        '+' => Ok((Tok::Plus, i + 1)),
        '.' => Ok((Tok::Dot, i + 1)),
        ':' if bytes.get(i + 1) == Some(&b'=') => Ok((Tok::ColonEq, i + 2)),
        ':' => Ok((Tok::Colon, i + 1)),
        '-' if bytes.get(i + 1) == Some(&b'>') => Ok((Tok::Arrow, i + 2)),
        '=' if bytes.get(i + 1) == Some(&b'>') => Ok((Tok::FatArrow, i + 2)),
        '-' | '=' => Err(ReadError::UnexpectedToken {
            pos: i,
            found: format!("byte {c:?}"),
            expected: "'->' or '=>'".to_owned(),
        }),
        '"' => {
            let (s, next) = lex_string(text, i)?;
            Ok((Tok::Str(s), next))
        }
        c if c.is_ascii_digit() => {
            let mut j = i + 1;
            while j < bytes.len() && (bytes[j] as char).is_ascii_digit() {
                j += 1;
            }
            Ok((Tok::Number(text[i..j].to_owned()), j))
        }
        c if is_ident_start(c) => {
            let mut j = i + 1;
            while j < bytes.len() && is_ident_continue(bytes[j] as char) {
                j += 1;
            }
            let word = &text[i..j];
            let tok = match word {
                "fun" => Tok::KwFun,
                "let" => Tok::KwLet,
                "Prop" => Tok::KwProp,
                "Sort" => Tok::KwSort,
                _ => Tok::Ident(word.to_owned()),
            };
            Ok((tok, j))
        }
        other => Err(ReadError::UnexpectedToken {
            pos: i,
            found: format!("byte {other:?}"),
            expected: "a token of the render_lean fragment".to_owned(),
        }),
    }
}

/// Decode a Rust-`Debug`-style quoted string starting at `text[start]` (which
/// must be `"`). Returns the decoded value and the byte offset just past the
/// closing quote.
///
/// Supports the escapes [`Lit::Str`]'s rendering (`format!("{s:?}")`) can
/// produce for the ASCII range this fragment is exercised on: `\\`, `\"`,
/// `\n`, `\r`, `\t`, `\0`, and `\u{HEX...}`. No fact in the ledger currently
/// carries a `lean4` string literal (measured 2026-09), so this is exercised
/// by unit tests rather than the ledger population.
fn lex_string(text: &str, start: usize) -> Result<(String, usize), ReadError> {
    let bytes = text.as_bytes();
    let mut i = start + 1;
    let mut out = String::new();
    loop {
        let Some(&b) = bytes.get(i) else {
            return Err(ReadError::UnexpectedEof {
                expected: "closing '\"'".to_owned(),
            });
        };
        match b as char {
            '"' => return Ok((out, i + 1)),
            '\\' => {
                let Some(&esc) = bytes.get(i + 1) else {
                    return Err(ReadError::UnexpectedEof {
                        expected: "an escape after '\\'".to_owned(),
                    });
                };
                match esc as char {
                    '\\' => {
                        out.push('\\');
                        i += 2;
                    }
                    '"' => {
                        out.push('"');
                        i += 2;
                    }
                    'n' => {
                        out.push('\n');
                        i += 2;
                    }
                    'r' => {
                        out.push('\r');
                        i += 2;
                    }
                    't' => {
                        out.push('\t');
                        i += 2;
                    }
                    '0' => {
                        out.push('\0');
                        i += 2;
                    }
                    'u' => {
                        if bytes.get(i + 2) != Some(&b'{') {
                            return Err(ReadError::InvalidLiteral {
                                pos: i,
                                detail: "expected '{' after \\u".to_owned(),
                            });
                        }
                        let hex_start = i + 3;
                        let mut j = hex_start;
                        while bytes.get(j).is_some_and(u8::is_ascii_hexdigit) {
                            j += 1;
                        }
                        if bytes.get(j) != Some(&b'}') {
                            return Err(ReadError::InvalidLiteral {
                                pos: i,
                                detail: "expected '}' closing \\u{...}".to_owned(),
                            });
                        }
                        let hex = &text[hex_start..j];
                        let code = u32::from_str_radix(hex, 16).map_err(|e| {
                            ReadError::InvalidLiteral {
                                pos: i,
                                detail: format!("bad \\u{{...}} hex digits: {e}"),
                            }
                        })?;
                        let ch = char::from_u32(code).ok_or_else(|| ReadError::InvalidLiteral {
                            pos: i,
                            detail: format!("\\u{{{hex}}} is not a valid code point"),
                        })?;
                        out.push(ch);
                        i = j + 1;
                    }
                    other => {
                        return Err(ReadError::InvalidLiteral {
                            pos: i,
                            detail: format!("unsupported escape '\\{other}'"),
                        });
                    }
                }
            }
            other => {
                out.push(other);
                i += 1;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

/// A recursive-descent reader over one [`Kernel::read_lean`] call. Kept as a
/// type distinct from [`Kernel`] on purpose: none of its methods are named to
/// collide with a `Kernel` method a trusted file might call on an
/// unknown-type receiver (`scripts/check-kernel-trusted-core.py`'s guard D
/// resolves `.foo()` on an unresolved receiver to every same-named method
/// whose OWNER TYPE is merely mentioned in the same file — a generic name on
/// `impl Kernel` would risk being pulled into the trusted closure; a generic
/// name here cannot be, because `LeanTermReader` never appears in any
/// trusted file).
struct LeanTermReader<'k> {
    kernel: &'k mut Kernel,
    toks: Vec<(Tok, usize)>,
    pos: usize,
    end: usize,
    /// Binder name strings, outermost first — mirrors
    /// `Kernel::render_lean`'s own `binders: Vec<String>` bookkeeping exactly
    /// so de Bruijn indices invert correctly, including shadowing (a repeated
    /// name resolves to the INNERMOST occurrence, matching how the renderer
    /// picks `binders[len - 1 - i]` for a true index `i`).
    binder_names: Vec<String>,
}

impl<'k> LeanTermReader<'k> {
    fn new(kernel: &'k mut Kernel, toks: Vec<(Tok, usize)>, end: usize) -> Self {
        Self {
            kernel,
            toks,
            pos: 0,
            end,
            binder_names: Vec::new(),
        }
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|(t, _)| t)
    }

    fn peek_pos(&self) -> usize {
        self.toks.get(self.pos).map_or(self.end, |(_, p)| *p)
    }

    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).map(|(t, _)| t.clone());
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    fn expect(&mut self, want: &Tok) -> Result<(), ReadError> {
        match self.peek() {
            Some(t) if t == want => {
                self.pos += 1;
                Ok(())
            }
            Some(t) => Err(ReadError::UnexpectedToken {
                pos: self.peek_pos(),
                found: t.describe(),
                expected: want.describe(),
            }),
            None => Err(ReadError::UnexpectedEof {
                expected: want.describe(),
            }),
        }
    }

    fn expect_ident(&mut self, expected: &str) -> Result<String, ReadError> {
        match self.bump() {
            Some(Tok::Ident(s)) => Ok(s),
            Some(other) => Err(ReadError::UnexpectedToken {
                pos: self.toks[self.pos - 1].1,
                found: other.describe(),
                expected: expected.to_owned(),
            }),
            None => Err(ReadError::UnexpectedEof {
                expected: expected.to_owned(),
            }),
        }
    }

    fn expect_number(&mut self, expected: &str) -> Result<(String, usize), ReadError> {
        match self.bump() {
            Some(Tok::Number(s)) => Ok((s, self.toks[self.pos - 1].1)),
            Some(other) => Err(ReadError::UnexpectedToken {
                pos: self.toks[self.pos - 1].1,
                found: other.describe(),
                expected: expected.to_owned(),
            }),
            None => Err(ReadError::UnexpectedEof {
                expected: expected.to_owned(),
            }),
        }
    }

    // -- top level ----------------------------------------------------------

    /// The full expression, then confirms nothing else follows.
    fn read_to_end(mut self) -> Result<ExprId, ReadError> {
        let e = self.parse_expr()?;
        if self.pos != self.toks.len() {
            return Err(ReadError::TrailingInput {
                pos: self.peek_pos(),
            });
        }
        Ok(e)
    }

    /// A flat application spine: one or more atoms, left-associated.
    fn parse_expr(&mut self) -> Result<ExprId, ReadError> {
        let mut head = self.parse_atom()?;
        while self.starts_atom() {
            let arg = self.parse_atom()?;
            head = self.kernel.app(head, arg);
        }
        Ok(head)
    }

    fn starts_atom(&self) -> bool {
        matches!(
            self.peek(),
            Some(
                Tok::LParen
                    | Tok::KwFun
                    | Tok::KwLet
                    | Tok::KwProp
                    | Tok::KwSort
                    | Tok::At
                    | Tok::Ident(_)
                    | Tok::Number(_)
                    | Tok::Str(_)
            )
        )
    }

    fn parse_atom(&mut self) -> Result<ExprId, ReadError> {
        match self.peek().cloned() {
            Some(Tok::LParen) => self.parse_paren_atom(),
            Some(Tok::KwFun) => self.parse_lambda(),
            Some(Tok::KwLet) => self.parse_let(),
            Some(Tok::KwProp) => {
                self.bump();
                Ok(self.kernel.sort_zero())
            }
            Some(Tok::KwSort) => {
                self.bump();
                self.expect(&Tok::LParen)?;
                let level = self.parse_level()?;
                self.expect(&Tok::RParen)?;
                Ok(self.kernel.sort(level))
            }
            Some(Tok::At | Tok::Ident(_)) => self.parse_name_atom(),
            Some(Tok::Number(_)) => {
                let (digits, pos) = self.expect_number("a natural-number literal")?;
                let nat =
                    NatLit::from_decimal(&digits).ok_or_else(|| ReadError::InvalidLiteral {
                        pos,
                        detail: format!("{digits:?} is not a valid natural-number literal"),
                    })?;
                Ok(self.kernel.lit(Lit::Nat(nat)))
            }
            Some(Tok::Str(_)) => {
                let Some(Tok::Str(s)) = self.bump() else {
                    unreachable!("peeked Str above")
                };
                Ok(self.kernel.lit(Lit::Str(s)))
            }
            Some(other) => Err(ReadError::UnexpectedToken {
                pos: self.peek_pos(),
                found: other.describe(),
                expected: "the start of an expression".to_owned(),
            }),
            None => Err(ReadError::UnexpectedEof {
                expected: "the start of an expression".to_owned(),
            }),
        }
    }

    /// `'('` has not yet been consumed. Tries the `Pi` production (which
    /// itself opens a second `(` immediately); on any mismatch, backtracks
    /// and falls through to a plain parenthesized expression (optionally
    /// followed by `.DIGITS` for a projection).
    fn parse_paren_atom(&mut self) -> Result<ExprId, ReadError> {
        let save = self.pos;
        self.pos += 1; // consume the outer '('
        if matches!(self.peek(), Some(Tok::LParen)) {
            let inner_save = self.pos;
            match self.try_parse_pi_tail() {
                Ok(pi) => return Ok(pi),
                Err(_) => {
                    self.pos = inner_save;
                }
            }
        }
        self.pos = save;
        self.expect(&Tok::LParen)?;
        let inner = self.parse_expr()?;
        self.expect(&Tok::RParen)?;
        if matches!(self.peek(), Some(Tok::Dot)) {
            // Only a bare-digit projection index follows a closing paren in
            // this fragment; anything else means the '.' starts an unrelated
            // production the caller (application spine) should see instead,
            // so only commit to Proj when a Number genuinely follows.
            let after_dot = self.toks.get(self.pos + 1).map(|(t, _)| t);
            if matches!(after_dot, Some(Tok::Number(_))) {
                self.pos += 1; // consume '.'
                let (digits, pos) = self.expect_number("a projection field index")?;
                let one_based: u64 = digits.parse().map_err(|_| ReadError::InvalidLiteral {
                    pos,
                    detail: format!("{digits:?} is not a valid field index"),
                })?;
                let zero_based =
                    one_based
                        .checked_sub(1)
                        .ok_or_else(|| ReadError::InvalidLiteral {
                            pos,
                            detail: "a projection field index is 1-based and must be >= 1"
                                .to_owned(),
                        })?;
                let field_index =
                    u32::try_from(zero_based).map_err(|_| ReadError::InvalidLiteral {
                        pos,
                        detail: format!("{digits:?} does not fit a field index"),
                    })?;
                // The structure's declared type name is not recoverable from
                // the rendered text (render_lean prints only the field
                // number, never the type name); a synthetic placeholder is
                // sound because `Proj`'s type-name argument does not
                // participate in `def_eq`'s structural comparison of the
                // node itself, only in reduction, and this fragment carries
                // no reduction obligation.
                let anon = self.kernel.anon();
                let placeholder = self.kernel.name_str(anon, "_lean_read_proj_structure");
                return Ok(self.kernel.proj(placeholder, field_index, inner));
            }
        }
        Ok(inner)
    }

    /// Assumes the outer `(` of a Pi is already consumed and the next token
    /// is `(`. Parses `'(' ident ':' expr ')' '->' expr ')'`.
    fn try_parse_pi_tail(&mut self) -> Result<ExprId, ReadError> {
        self.expect(&Tok::LParen)?;
        let name = self.expect_ident("a binder name")?;
        self.expect(&Tok::Colon)?;
        let ty = self.parse_expr()?;
        self.expect(&Tok::RParen)?;
        self.expect(&Tok::Arrow)?;
        self.binder_names.push(name.clone());
        let body = self.parse_expr();
        self.binder_names.pop();
        let body = body?;
        self.expect(&Tok::RParen)?;
        let anon = self.kernel.anon();
        let name_id = self.kernel.name_str(anon, name);
        Ok(self.kernel.pi(name_id, ty, body, BinderInfo::Default))
    }

    fn parse_lambda(&mut self) -> Result<ExprId, ReadError> {
        self.expect(&Tok::KwFun)?;
        self.expect(&Tok::LParen)?;
        let name = self.expect_ident("a binder name")?;
        self.expect(&Tok::Colon)?;
        let ty = self.parse_expr()?;
        self.expect(&Tok::RParen)?;
        self.expect(&Tok::FatArrow)?;
        self.binder_names.push(name.clone());
        let body = self.parse_expr();
        self.binder_names.pop();
        let body = body?;
        let anon = self.kernel.anon();
        let name_id = self.kernel.name_str(anon, name);
        Ok(self.kernel.lam(name_id, ty, body, BinderInfo::Default))
    }

    fn parse_let(&mut self) -> Result<ExprId, ReadError> {
        self.expect(&Tok::KwLet)?;
        let name = self.expect_ident("a let-bound name")?;
        self.expect(&Tok::Colon)?;
        let ty = self.parse_expr()?;
        self.expect(&Tok::ColonEq)?;
        let value = self.parse_expr()?;
        self.expect(&Tok::Semicolon)?;
        self.binder_names.push(name.clone());
        let body = self.parse_expr();
        self.binder_names.pop();
        let body = body?;
        let anon = self.kernel.anon();
        let name_id = self.kernel.name_str(anon, name);
        Ok(self.kernel.let_(name_id, ty, value, body))
    }

    /// `'@'? IDENT ('.' (IDENT | DIGITS))* ('.{' level (',' level)* '}')?`.
    ///
    /// A dot-free identifier is checked against the enclosing binder scope
    /// FIRST (innermost occurrence wins, matching Lean's — and
    /// `render_lean`'s — shadowing), and only falls through to constant
    /// resolution when no binder matches. `@` is accepted and discarded: it
    /// is purely a rendering hint for Lean's elaborator
    /// (`render_lean_decl`'s `at_consts`) and carries no information the
    /// kernel's own `ExprNode::Const` records — `render_lean` (used for
    /// every `formal.statement` in the ledger) never emits it, so this path
    /// is exercised by unit tests, not the round-trip suite.
    fn parse_name_atom(&mut self) -> Result<ExprId, ReadError> {
        if matches!(self.peek(), Some(Tok::At)) {
            self.bump();
        }
        let first_pos = self.peek_pos();
        let first = self.expect_ident("a name")?;

        let binder_hit = self.binder_names.iter().rev().position(|n| n == &first);
        if let Some(depth_from_end) = binder_hit
            && !matches!(self.peek(), Some(Tok::Dot))
        {
            // A dot-free identifier matching an active binder is that bound
            // variable -- UNLESS a '.' follows, which means it is actually
            // the root of a qualified constant name that happens to share
            // text with a binder (never produced by our own renderer, since
            // binder names are always simple locals, but kept for
            // robustness against an adversarial/corrupted input).
            let idx = u32::try_from(depth_from_end).expect("binder depth fits u32");
            return Ok(self.kernel.bvar(idx));
        }

        // Root-segment remap: `Kernel::render_lean`'s `render_name` spells
        // the computational-`Nat` prelude's root as `AxNat` so the emitted
        // module never shadows Lean's built-in `Nat` (see `render_name`'s
        // doc comment); invert that single remap here.
        let anon = self.kernel.anon();
        let root_text = if first == "AxNat" {
            "Nat"
        } else {
            first.as_str()
        };
        let Some(mut current) = self.kernel_lookup_str(anon, root_text) else {
            // A following '.' means more segments were coming -- the writer
            // clearly meant a qualified constant, just not one this
            // environment declares. No '.' means a bare single word that is
            // neither an active binder nor a root declaration, which reads
            // more like a variable reference that escaped its binding scope.
            let dotted = matches!(self.peek(), Some(Tok::Dot));
            return Err(name_resolution_error(first_pos, &first, dotted));
        };
        let mut full = first.clone();

        loop {
            if !matches!(self.peek(), Some(Tok::Dot)) {
                break;
            }
            // Only commit to extending the name when a name-shaped segment
            // follows; a Proj's `.DIGITS` after a `)` is handled elsewhere
            // and never reaches this function (Const atoms are never
            // parenthesized).
            let after_dot = self.toks.get(self.pos + 1).map(|(t, _)| t.clone());
            match after_dot {
                Some(Tok::Ident(seg)) => {
                    self.pos += 2; // consume '.' and the identifier
                    full.push('.');
                    full.push_str(&seg);
                    current = if let Some(n) = parse_underscore_num(&seg) {
                        match self.kernel_lookup_num(current, n) {
                            Some(id) => id,
                            None => {
                                return Err(ReadError::UnknownConstant {
                                    pos: first_pos,
                                    name: full,
                                });
                            }
                        }
                    } else {
                        match self.kernel_lookup_str(current, &seg) {
                            Some(id) => id,
                            None => {
                                return Err(ReadError::UnknownConstant {
                                    pos: first_pos,
                                    name: full,
                                });
                            }
                        }
                    };
                }
                _ => break,
            }
        }

        let mut levels = Vec::new();
        if matches!(self.peek(), Some(Tok::Dot))
            && matches!(
                self.toks.get(self.pos + 1).map(|(t, _)| t),
                Some(Tok::LBrace)
            )
        {
            self.pos += 2; // consume '.' and '{'
            loop {
                levels.push(self.parse_level()?);
                match self.peek() {
                    Some(Tok::Comma) => {
                        self.pos += 1;
                    }
                    Some(Tok::RBrace) => {
                        self.pos += 1;
                        break;
                    }
                    Some(other) => {
                        return Err(ReadError::UnexpectedToken {
                            pos: self.peek_pos(),
                            found: other.describe(),
                            expected: "',' or '}' in a universe-argument list".to_owned(),
                        });
                    }
                    None => {
                        return Err(ReadError::UnexpectedEof {
                            expected: "',' or '}' in a universe-argument list".to_owned(),
                        });
                    }
                }
            }
        }

        Ok(self.kernel.const_(current, levels))
    }

    /// Wraps [`Kernel::lookup_name_str`] (`pub(crate)`) — a private-field/
    /// crate-visibility bridge, not a new public surface.
    fn kernel_lookup_str(&self, parent: NameId, s: &str) -> Option<NameId> {
        self.kernel.lookup_name_str_for_lean_read(parent, s)
    }

    fn kernel_lookup_num(&self, parent: NameId, n: u64) -> Option<NameId> {
        self.kernel.lookup_name_num_for_lean_read(parent, n)
    }

    // -- universe levels ------------------------------------------------

    fn parse_level(&mut self) -> Result<LevelId, ReadError> {
        match self.peek().cloned() {
            Some(Tok::Number(_)) => {
                let (digits, pos) = self.expect_number("a universe numeral")?;
                let n: u32 = digits.parse().map_err(|_| ReadError::BadLevel {
                    pos,
                    detail: format!("{digits:?} does not fit a universe offset"),
                })?;
                let mut level = self.kernel.level_zero();
                for _ in 0..n {
                    level = self.kernel.level_succ(level);
                }
                Ok(level)
            }
            Some(Tok::LParen) => {
                self.bump();
                let pos = self.peek_pos();
                let kw = self.expect_ident("'max' or 'imax'")?;
                let a = self.parse_level()?;
                let b = self.parse_level()?;
                self.expect(&Tok::RParen)?;
                let mut level = match kw.as_str() {
                    "max" => self.kernel.level_max(a, b),
                    "imax" => self.kernel.level_imax(a, b),
                    other => {
                        return Err(ReadError::BadLevel {
                            pos,
                            detail: format!("expected 'max' or 'imax', found {other:?}"),
                        });
                    }
                };
                if matches!(self.peek(), Some(Tok::Plus)) {
                    self.bump();
                    let (digits, npos) = self.expect_number("a universe offset")?;
                    let n: u32 = digits.parse().map_err(|_| ReadError::BadLevel {
                        pos: npos,
                        detail: format!("{digits:?} does not fit a universe offset"),
                    })?;
                    for _ in 0..n {
                        level = self.kernel.level_succ(level);
                    }
                }
                Ok(level)
            }
            Some(Tok::Ident(name)) => {
                self.bump();
                let anon = self.kernel.anon();
                let pname = self.kernel.name_str(anon, name);
                let mut level = self.kernel.level_param(pname);
                if matches!(self.peek(), Some(Tok::Plus)) {
                    self.bump();
                    let (digits, npos) = self.expect_number("a universe offset")?;
                    let n: u32 = digits.parse().map_err(|_| ReadError::BadLevel {
                        pos: npos,
                        detail: format!("{digits:?} does not fit a universe offset"),
                    })?;
                    for _ in 0..n {
                        level = self.kernel.level_succ(level);
                    }
                }
                Ok(level)
            }
            Some(other) => Err(ReadError::BadLevel {
                pos: self.peek_pos(),
                detail: format!("expected a universe level, found {}", other.describe()),
            }),
            None => Err(ReadError::UnexpectedEof {
                expected: "a universe level".to_owned(),
            }),
        }
    }
}

/// Classifies a name-lookup miss as [`ReadError::UnknownConstant`] (a
/// qualified/dotted name was clearly intended, `dotted` is `true`) or
/// [`ReadError::UnboundVariable`] (a bare word matched no binder and no
/// root declaration).
fn name_resolution_error(pos: usize, name: &str, dotted: bool) -> ReadError {
    if dotted {
        ReadError::UnknownConstant {
            pos,
            name: name.to_owned(),
        }
    } else {
        ReadError::UnboundVariable {
            pos,
            name: name.to_owned(),
        }
    }
}

/// `render_name`'s numeric-segment spelling is `_N` (parent non-empty) or a
/// root `_N` (parent anonymous) — see `Kernel::render_name`'s `NameNode::Num`
/// arm. Returns `Some(N)` exactly when `segment` is that spelling: a leading
/// `_` followed by one or more ASCII digits and nothing else.
fn parse_underscore_num(segment: &str) -> Option<u64> {
    let digits = segment.strip_prefix('_')?;
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    digits.parse().ok()
}

// ---------------------------------------------------------------------------
// The public entry point
// ---------------------------------------------------------------------------

impl Kernel {
    /// Reads `text` — a [`Kernel::render_lean`]-fragment expression — back
    /// into a kernel [`ExprId`] against `self`'s current environment.
    ///
    /// This is a bare-expression reader, matching exactly what
    /// [`Kernel::render_lean`] produces (it never emits a `theorem`/`def`/
    /// `axiom`/`inductive` keyword — that wrapping, when a `formal.statement`
    /// carries one, is `gen-kernel-facts.py`'s own `f"theorem {name} :
    /// {rendered_type}"`, not the kernel's). A caller reading a
    /// `formal.statement` of that shape strips the `KEYWORD NAME : ` prefix
    /// itself before calling this (see `tests/lean_read_round_trip.rs`).
    ///
    /// # Errors
    ///
    /// Returns a typed [`ReadError`]: an unexpected token or premature EOF (a
    /// syntax error in the fragment as this reader understands it), an
    /// unknown constant or unbound variable (the text is syntactically valid
    /// but names something `self`'s environment does not have — the common
    /// case for a statement whose prelude was not built into `self`, or
    /// whose vocabulary belongs to a different route entirely, e.g. an
    /// `imported-kernel-lean` fact spelled in Mathlib's own names), a bad
    /// universe level, an invalid literal, or trailing input.
    pub fn read_lean(&mut self, text: &str) -> Result<ExprId, ReadError> {
        let toks = tokenize(text)?;
        let end = text.len();
        LeanTermReader::new(self, toks, end).read_to_end()
    }

    /// Bridge to the `pub(crate)` [`Kernel::lookup_name_str`] for
    /// [`LeanTermReader`], which lives in this same file/module and could
    /// call the `pub(crate)` method directly -- this wrapper exists only so
    /// the method name attached to `impl Kernel` (this file's sole addition
    /// to `Kernel`'s public surface besides `read_lean` itself) is
    /// unambiguously specific to this reader, never a generic name a
    /// trusted file's loose `.method()` call could be conflated with by
    /// `scripts/check-kernel-trusted-core.py`'s guard D.
    fn lookup_name_str_for_lean_read(&self, parent: NameId, s: &str) -> Option<NameId> {
        self.lookup_name_str(parent, s)
    }

    /// As [`Kernel::lookup_name_str_for_lean_read`], for a numeric name
    /// segment (`NameNode::Num`). There is no existing `pub(crate)` lookup
    /// for this case (only [`Kernel::lookup_name_str`] exists), so this
    /// queries the `name_intern` field directly — a private field of
    /// `Kernel`, visible here because [`lean_read`](self) is a *descendant*
    /// module of the crate root where `Kernel` is defined (the same access
    /// `lean_pp.rs`'s own tests already rely on for this exact field).
    /// Sound because it never MINTS a name, only asks whether one already
    /// exists, exactly like [`Kernel::lookup_name_str`] does for the `Str`
    /// case.
    fn lookup_name_num_for_lean_read(&self, parent: NameId, n: u64) -> Option<NameId> {
        self.name_intern.get(&NameNode::Num(parent, n)).copied()
    }
}

#[cfg(test)]
mod tests {
    use crate::{BinderInfo, Kernel, build_nat_prelude};

    /// `render_lean(read_lean(s)) == s` for the simplest possible terms,
    /// independent of any prelude.
    #[test]
    fn round_trips_prop_and_identity_lambda() {
        let mut k = Kernel::new();
        let prop_id = k.read_lean("Prop").unwrap();
        assert_eq!(k.render_lean(prop_id), "Prop");

        let anon = k.anon();
        let p = k.name_str(anon, "p");
        let prop = k.sort_zero();
        let body = k.bvar(0);
        let lam = k.lam(p, prop, body, BinderInfo::Default);
        let rendered = k.render_lean(lam);
        assert_eq!(rendered, "fun (p : Prop) => p");
        let read = k.read_lean(&rendered).expect("must read back");
        assert_eq!(k.render_lean(read), rendered);
    }

    /// A `Pi` round-trips, including its self-wrapping parens.
    #[test]
    fn round_trips_pi() {
        let mut k = Kernel::new();
        let prop = k.sort_zero();
        let anon = k.anon();
        let a = k.name_str(anon, "a");
        let body = k.bvar(0);
        let pi = k.pi(a, prop, body, BinderInfo::Default);
        let rendered = k.render_lean(pi);
        assert_eq!(rendered, "((a : Prop) -> a)");
        let read = k.read_lean(&rendered).expect("must read back");
        assert_eq!(k.render_lean(read), rendered);
    }

    /// A doubly atom-wrapped `Pi` (an application argument whose type is
    /// itself a `Pi`) exercises the backtracking `Pi`-vs-generic-paren
    /// disambiguation at two nesting depths at once.
    #[test]
    fn round_trips_nested_pi_as_a_binder_type() {
        let mut k = Kernel::new();
        let prop = k.sort_zero();
        let anon = k.anon();
        let inner_x = k.name_str(anon, "x");
        let inner_body = k.bvar(0); // refers to the inner Pi's own `x`
        let inner_pi = k.pi(inner_x, prop, inner_body, BinderInfo::Default);
        // `(f : (x : Prop) -> x) -> Prop`
        let outer_f = k.name_str(anon, "f");
        let outer_body = k.sort_zero();
        let outer_pi = k.pi(outer_f, inner_pi, outer_body, BinderInfo::Default);
        let rendered = k.render_lean(outer_pi);
        assert_eq!(rendered, "((f : ((x : Prop) -> x)) -> Prop)");
        let read = k.read_lean(&rendered).expect("must read back");
        assert_eq!(k.render_lean(read), rendered);
    }

    /// Shadowing: a binder name reused at a deeper scope resolves to the
    /// INNERMOST occurrence, both when read and when re-rendered.
    #[test]
    fn round_trips_shadowed_binder_names() {
        let mut k = Kernel::new();
        let prop = k.sort_zero();
        let anon = k.anon();
        let n1 = k.name_str(anon, "n");
        let n2 = k.name_str(anon, "n");
        // (n : Prop) -> (n : Prop) -> n   -- the body's `n` is the INNER one.
        let inner_body = k.bvar(0);
        let inner_pi = k.pi(n2, prop, inner_body, BinderInfo::Default);
        let outer_pi = k.pi(n1, prop, inner_pi, BinderInfo::Default);
        let rendered = k.render_lean(outer_pi);
        assert_eq!(rendered, "((n : Prop) -> ((n : Prop) -> n))");
        let read = k.read_lean(&rendered).expect("must read back");
        assert_eq!(k.render_lean(read), rendered);
    }

    /// A real prelude theorem's rendered type reads back and is `def_eq` to
    /// the environment's own declared type.
    #[test]
    fn reads_a_real_nat_theorem_and_def_eqs_its_declared_type() {
        let mut k = Kernel::new();
        build_nat_prelude(&mut k).expect("the Nat prelude must build");
        let anon = k.anon();
        let nat = k.name_str(anon, "Nat");
        let name = k.name_str(nat, "le_of_succ_le_succ");
        let declared_ty = k
            .environment()
            .get(name)
            .expect("Nat.le_of_succ_le_succ must be declared")
            .ty();
        let rendered = k.render_lean(declared_ty);
        let read = k.read_lean(&rendered).expect("must read back");
        assert_eq!(k.render_lean(read), rendered, "byte-exact round trip");
        assert!(
            k.def_eq(read, declared_ty),
            "the read-back type must be def_eq to the declared one"
        );
    }

    /// Negative control: swapping a constant name (`succ` -> `pred`) must
    /// either fail to read (if `Nat.pred` is not declared) or, if it reads,
    /// must NOT be `def_eq` to the original -- proving the round-trip gate
    /// can actually fail.
    #[test]
    fn corrupted_statement_fails_to_read_or_fails_def_eq() {
        let mut k = Kernel::new();
        build_nat_prelude(&mut k).expect("the Nat prelude must build");
        let anon = k.anon();
        let nat = k.name_str(anon, "Nat");
        let name = k.name_str(nat, "le_of_succ_le_succ");
        let declared_ty = k
            .environment()
            .get(name)
            .expect("Nat.le_of_succ_le_succ must be declared")
            .ty();
        let rendered = k.render_lean(declared_ty);
        let corrupted = rendered.replace("AxNat.succ", "AxNat.pred");
        assert_ne!(
            corrupted, rendered,
            "the corruption must actually change the text"
        );
        match k.read_lean(&corrupted) {
            Err(_) => {} // AxNat.pred is not declared -- UnknownConstant, correctly rejected.
            Ok(read) => assert!(
                !k.def_eq(read, declared_ty),
                "a corrupted statement must not be def_eq to the original"
            ),
        }
    }

    /// Negative control: dropping a universe argument must fail to read.
    #[test]
    fn dropped_universe_argument_fails_to_read() {
        let mut k = Kernel::new();
        let u = k.anon();
        let uparam = k.name_str(u, "u");
        let level = k.level_param(uparam);
        let sort_u = k.sort(level);
        let rendered = k.render_lean(sort_u);
        assert_eq!(rendered, "Sort (u)");
        let corrupted = "Sort ()";
        assert!(k.read_lean(corrupted).is_err());
    }

    /// A `'` (or any byte outside the fragment) is a typed `unexpected
    /// token`, not a panic.
    #[test]
    fn garbage_input_is_a_typed_error_not_a_panic() {
        let mut k = Kernel::new();
        let err = k.read_lean("&&&").unwrap_err();
        assert_eq!(err.class(), "unexpected-token");
    }

    /// An unknown dotted constant is classified distinctly from a bare
    /// unbound variable.
    #[test]
    fn unknown_constant_vs_unbound_variable_are_distinct_classes() {
        let mut k = Kernel::new();
        let dotted = k.read_lean("Totally.Unknown.Thing").unwrap_err();
        assert_eq!(dotted.class(), "unknown-constant");
        let bare = k.read_lean("totally_unknown_thing").unwrap_err();
        assert_eq!(bare.class(), "unbound-variable");
    }

    /// Trailing input after a complete expression is rejected.
    #[test]
    fn trailing_input_is_rejected() {
        let mut k = Kernel::new();
        let err = k.read_lean("Prop Prop )").unwrap_err();
        assert_eq!(err.class(), "trailing-input");
    }

    /// A `Proj` round-trips through its 1-based surface syntax.
    #[test]
    fn round_trips_projection() {
        let mut k = Kernel::new();
        let anon = k.anon();
        let pair = k.name_str(anon, "Pair");
        let self_name = k.name_str(anon, "self");
        let prop = k.sort_zero();
        let self_value = k.bvar(0);
        let second = k.proj(pair, 1, self_value);
        let projection = k.lam(self_name, prop, second, BinderInfo::Default);
        let rendered = k.render_lean(projection);
        assert_eq!(rendered, "fun (self : Prop) => (self).2");
        let read = k.read_lean(&rendered).expect("must read back");
        assert_eq!(k.render_lean(read), rendered);
    }

    /// A string literal with escapes round-trips.
    #[test]
    fn round_trips_string_literal() {
        let mut k = Kernel::new();
        let lit = k.lit(crate::Lit::Str("a\\b\"c\nd".to_owned()));
        let rendered = k.render_lean(lit);
        let read = k.read_lean(&rendered).expect("must read back");
        assert_eq!(k.render_lean(read), rendered);
    }

    /// A `Nat` literal round-trips.
    #[test]
    fn round_trips_nat_literal() {
        let mut k = Kernel::new();
        let lit = k.lit(crate::Lit::nat(42_u32));
        let rendered = k.render_lean(lit);
        assert_eq!(rendered, "42");
        let read = k.read_lean(&rendered).expect("must read back");
        assert_eq!(k.render_lean(read), rendered);
    }

    /// A `max`/`imax` universe level, with and without a trailing offset,
    /// round-trips.
    #[test]
    fn round_trips_max_and_imax_levels_with_offset() {
        let mut k = Kernel::new();
        let anon = k.anon();
        let u = k.name_str(anon, "u");
        let v = k.name_str(anon, "v");
        let lu = k.level_param(u);
        let lv = k.level_param(v);
        let imax = k.level_imax(lu, lv);
        let imax_succ = k.level_succ(imax);
        let sort = k.sort(imax_succ);
        let rendered = k.render_lean(sort);
        assert_eq!(rendered, "Sort ((imax u v)+1)");
        let read = k.read_lean(&rendered).expect("must read back");
        assert_eq!(k.render_lean(read), rendered);
    }
}
