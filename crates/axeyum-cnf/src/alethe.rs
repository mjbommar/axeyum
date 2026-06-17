//! A self-contained Alethe proof checker — the resolution core plus a first
//! slice of EUF theory rules (Track 3, phase P3.2).
//!
//! Alethe is the proof format produced by veriT and cvc5. A proof is a list of
//! commands over clauses; the proof establishes UNSAT iff a verified step derives
//! the empty clause `(cl)`. This is a SOUNDNESS-CRITICAL checker: it accepts a
//! step only when it is genuinely valid, and rejects when in doubt.
//!
//! - **`resolution`/`th_resolution`** and the clause-manipulation rules
//!   **`contraction`/`reordering`/`weakening`** are checked by *entailment*: a step
//!   with premises `C1..Cn` and conclusion `D` is valid iff `{C1, …, Cn, ¬D}` is
//!   propositionally UNSAT (`¬D` = the unit clauses negating each literal of `D`).
//!   That UNSAT is decided by the **proof-producing** SAT core
//!   ([`crate::solve_with_drat_proof`]) and the resulting DRAT proof is **re-checked
//!   by [`crate::check_drat`]**, so the entailment underpinning every accepted
//!   such step is itself independently verified — not trusted to the search.
//! - The **EUF** rules `eq_reflexive`, `eq_symmetric`, `eq_transitive`, and
//!   `eq_congruent`, and the **Boolean CNF-introduction** rules `and_pos`,
//!   `and_neg`, `or_pos`, `or_neg` are checked *structurally* against each rule's
//!   exact tautology shape (strict and order-sensitive).
//!
//! Atoms are structured [`AletheTerm`]s (a symbol or an application), compared by
//! structural equality so theory rules can inspect their shape. Any other rule is
//! rejected with [`AletheError::UnsupportedRule`].

use std::collections::BTreeMap;

use crate::{CnfClause, CnfFormula, CnfLit, CnfVar, LratStep};

/// An Alethe term: an SMT-LIB-style symbol or application. Atoms in literals are
/// terms (so theory rules can inspect structure); they are compared structurally.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum AletheTerm {
    /// A symbol / nullary constant, e.g. `x`, `a`, `true`.
    Const(String),
    /// An application `(f a1 ... an)`, e.g. `(= a b)`, `(f x)`.
    App(String, Vec<AletheTerm>),
    /// An indexed-operator application `((_ op i0 i1 …) a0 a1 …)`, e.g.
    /// `((_ @bit_of 0) x)`. With no `args` it is the bare indexed identifier
    /// `(_ op i0 …)`. Indices are integer literals (SMT-LIB numerals).
    Indexed {
        /// The operator symbol, e.g. `@bit_of` or `extract`.
        op: String,
        /// The integer indices, e.g. `[0]` in `(_ @bit_of 0)`.
        indices: Vec<i128>,
        /// The operand terms; empty for a bare indexed identifier.
        args: Vec<AletheTerm>,
    },
}

impl AletheTerm {
    /// A canonical s-expression key (used to map a term to a `CnfVar` in the
    /// resolution entailment check, so structurally-equal terms share a
    /// variable).
    ///
    /// `Const(s)` maps to `s`; `App(f, args)` maps to `(f k1 k2 ...)`, where
    /// each `ki` is the key of the corresponding argument. An
    /// `Indexed { op, indices, args }` maps to `((_ op i0 i1 …) a0key a1key …)`
    /// with args, or the bare identifier `(_ op i0 i1 …)` without — so two
    /// structurally-equal indexed terms share a key.
    #[must_use]
    pub fn key(&self) -> String {
        match self {
            AletheTerm::Const(symbol) => symbol.clone(),
            AletheTerm::App(head, args) => {
                let mut out = String::from("(");
                out.push_str(head);
                for arg in args {
                    out.push(' ');
                    out.push_str(&arg.key());
                }
                out.push(')');
                out
            }
            AletheTerm::Indexed { op, indices, args } => {
                let head = indexed_head(op, indices);
                if args.is_empty() {
                    head
                } else {
                    let mut out = String::from("(");
                    out.push_str(&head);
                    for arg in args {
                        out.push(' ');
                        out.push_str(&arg.key());
                    }
                    out.push(')');
                    out
                }
            }
        }
    }
}

/// Renders the indexed identifier head `(_ op i0 i1 …)` for an indexed-operator
/// application. Shared by [`AletheTerm::key`] and the writer so the key and the
/// textual form stay consistent.
fn indexed_head(op: &str, indices: &[i128]) -> String {
    let mut out = String::from("(_ ");
    out.push_str(op);
    for index in indices {
        out.push(' ');
        out.push_str(&index.to_string());
    }
    out.push(')');
    out
}

/// A propositional literal: a [`AletheTerm`] atom, optionally negated.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AletheLit {
    /// The atom term. Atoms are equal iff they are structurally equal.
    pub atom: AletheTerm,
    /// Whether the literal is the negation of its atom.
    pub negated: bool,
}

/// A clause: a disjunction of literals. The empty clause is `false`.
pub type AletheClause = Vec<AletheLit>;

/// One command of an Alethe resolution-layer proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AletheCommand {
    /// Introduces a hypothesis clause under `id`.
    Assume {
        /// The command's identifier, referenced by later premises.
        id: String,
        /// The assumed term, interpreted as a clause.
        clause: AletheClause,
    },
    /// Derives `clause` from `premises` by `rule`, recorded under `id`.
    Step {
        /// The command's identifier, referenced by later premises.
        id: String,
        /// The derived clause (`(cl ...)`); empty means the empty clause.
        clause: AletheClause,
        /// The rule name (`resolution`/`th_resolution` by entailment; the EUF
        /// `eq_*` rules structurally; others unsupported).
        rule: String,
        /// Identifiers of the premise commands.
        premises: Vec<String>,
        /// The step's `:args` rule arguments — e.g. the `la_generic` Farkas
        /// coefficients (one per clause literal). Empty when the rule takes none;
        /// such steps render byte-identically to a step written without `:args`.
        args: Vec<AletheTerm>,
    },
}

/// Error from Alethe parsing or checking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AletheError {
    /// The proof text could not be parsed.
    Parse(String),
    /// A step cited a premise id that was never defined.
    UnknownPremise {
        /// The undefined premise identifier.
        id: String,
    },
    /// A step used a rule this checker does not yet support.
    UnsupportedRule {
        /// The unsupported rule name.
        rule: String,
    },
    /// A step's conclusion is not entailed by its premises.
    StepNotEntailed {
        /// The identifier of the rejected step.
        id: String,
    },
}

impl core::fmt::Display for AletheError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AletheError::Parse(what) => write!(f, "Alethe parse error: {what}"),
            AletheError::UnknownPremise { id } => write!(f, "unknown premise `{id}`"),
            AletheError::UnsupportedRule { rule } => {
                write!(f, "unsupported Alethe rule `{rule}`")
            }
            AletheError::StepNotEntailed { id } => {
                write!(f, "step `{id}` conclusion is not entailed by its premises")
            }
        }
    }
}

impl core::error::Error for AletheError {}

/// A token from the s-expression reader.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Token {
    Open,
    Close,
    Atom(String),
}

/// Tokenizes Alethe text into parens and atom tokens. Lines starting with `;`
/// are comments; a `;` anywhere starts a comment to end of line.
fn tokenize(text: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        match ch {
            ';' => {
                // Comment to end of line.
                flush_atom(&mut current, &mut tokens);
                for next in chars.by_ref() {
                    if next == '\n' {
                        break;
                    }
                }
            }
            '(' => {
                flush_atom(&mut current, &mut tokens);
                tokens.push(Token::Open);
            }
            ')' => {
                flush_atom(&mut current, &mut tokens);
                tokens.push(Token::Close);
            }
            c if c.is_whitespace() => {
                flush_atom(&mut current, &mut tokens);
            }
            c => current.push(c),
        }
    }
    flush_atom(&mut current, &mut tokens);
    tokens
}

fn flush_atom(current: &mut String, tokens: &mut Vec<Token>) {
    if !current.is_empty() {
        tokens.push(Token::Atom(std::mem::take(current)));
    }
}

/// A minimal s-expression tree.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl Sexp {
    fn as_atom(&self) -> Option<&str> {
        match self {
            Sexp::Atom(text) => Some(text.as_str()),
            Sexp::List(_) => None,
        }
    }
}

/// Reads a flat token stream into top-level s-expressions.
fn read_sexps(tokens: &[Token]) -> Result<Vec<Sexp>, AletheError> {
    let mut pos = 0;
    let mut top = Vec::new();
    while pos < tokens.len() {
        let (sexp, next) = read_one(tokens, pos)?;
        top.push(sexp);
        pos = next;
    }
    Ok(top)
}

fn read_one(tokens: &[Token], pos: usize) -> Result<(Sexp, usize), AletheError> {
    match tokens.get(pos) {
        None => Err(AletheError::Parse("unexpected end of input".to_owned())),
        Some(Token::Close) => Err(AletheError::Parse("unexpected `)`".to_owned())),
        Some(Token::Atom(text)) => Ok((Sexp::Atom(text.clone()), pos + 1)),
        Some(Token::Open) => {
            let mut items = Vec::new();
            let mut cursor = pos + 1;
            loop {
                match tokens.get(cursor) {
                    None => return Err(AletheError::Parse("unterminated `(`".to_owned())),
                    Some(Token::Close) => return Ok((Sexp::List(items), cursor + 1)),
                    Some(_) => {
                        let (item, next) = read_one(tokens, cursor)?;
                        items.push(item);
                        cursor = next;
                    }
                }
            }
        }
    }
}

/// Parses an Alethe resolution-layer proof.
///
/// Accepts `(assume <id> <term>)` and
/// `(step <id> (cl <lit>...) :rule <rule> :premises (<id>...))`. A `<term>` is
/// interpreted as a clause: `(or l1 l2 ...)` yields its literals, `(not a)`
/// yields one negated literal, and a bare atom yields one positive literal. A
/// literal is `(not atom)` or `atom`. `:premises` is optional (absent means no
/// premises). Lines/segments after `;` are comments.
///
/// # Errors
///
/// Returns [`AletheError::Parse`] for malformed s-expressions or commands.
pub fn parse_alethe(text: &str) -> Result<Vec<AletheCommand>, AletheError> {
    let tokens = tokenize(text);
    let sexps = read_sexps(&tokens)?;
    sexps.iter().map(parse_command).collect()
}

fn parse_command(sexp: &Sexp) -> Result<AletheCommand, AletheError> {
    let Sexp::List(items) = sexp else {
        return Err(AletheError::Parse(
            "top-level command must be a list".to_owned(),
        ));
    };
    let head = items
        .first()
        .and_then(Sexp::as_atom)
        .ok_or_else(|| AletheError::Parse("command missing head keyword".to_owned()))?;
    match head {
        "assume" => parse_assume(items),
        "step" => parse_step(items),
        other => Err(AletheError::Parse(format!("unknown command `{other}`"))),
    }
}

fn parse_assume(items: &[Sexp]) -> Result<AletheCommand, AletheError> {
    if items.len() != 3 {
        return Err(AletheError::Parse(
            "`assume` expects (assume <id> <term>)".to_owned(),
        ));
    }
    let id = items[1]
        .as_atom()
        .ok_or_else(|| AletheError::Parse("`assume` id must be an atom".to_owned()))?
        .to_owned();
    let clause = parse_term_as_clause(&items[2])?;
    Ok(AletheCommand::Assume { id, clause })
}

fn parse_step(items: &[Sexp]) -> Result<AletheCommand, AletheError> {
    // (step <id> (cl <lit>...) :rule R [:premises (id...)])
    if items.len() < 3 {
        return Err(AletheError::Parse(
            "`step` expects (step <id> (cl ...) :rule R ...)".to_owned(),
        ));
    }
    let id = items[1]
        .as_atom()
        .ok_or_else(|| AletheError::Parse("`step` id must be an atom".to_owned()))?
        .to_owned();
    let clause = parse_cl_clause(&items[2])?;

    let mut rule: Option<String> = None;
    let mut premises: Vec<String> = Vec::new();
    let mut args: Vec<AletheTerm> = Vec::new();
    let mut index = 3;
    while index < items.len() {
        let keyword = items[index]
            .as_atom()
            .ok_or_else(|| AletheError::Parse("expected `:`-keyword in step".to_owned()))?;
        match keyword {
            ":rule" => {
                let value = items.get(index + 1).ok_or_else(|| {
                    AletheError::Parse("`:rule` missing its rule name".to_owned())
                })?;
                rule = Some(
                    value
                        .as_atom()
                        .ok_or_else(|| {
                            AletheError::Parse("`:rule` value must be an atom".to_owned())
                        })?
                        .to_owned(),
                );
                index += 2;
            }
            ":premises" => {
                let value = items.get(index + 1).ok_or_else(|| {
                    AletheError::Parse("`:premises` missing its id list".to_owned())
                })?;
                let Sexp::List(ids) = value else {
                    return Err(AletheError::Parse(
                        "`:premises` value must be a list".to_owned(),
                    ));
                };
                premises = ids
                    .iter()
                    .map(|id_sexp| {
                        id_sexp.as_atom().map(str::to_owned).ok_or_else(|| {
                            AletheError::Parse("premise id must be an atom".to_owned())
                        })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                index += 2;
            }
            ":args" => {
                let value = items.get(index + 1).ok_or_else(|| {
                    AletheError::Parse("`:args` missing its term list".to_owned())
                })?;
                let Sexp::List(terms) = value else {
                    return Err(AletheError::Parse(
                        "`:args` value must be a list".to_owned(),
                    ));
                };
                args = terms
                    .iter()
                    .map(parse_term)
                    .collect::<Result<Vec<_>, _>>()?;
                index += 2;
            }
            // Tolerate (and ignore) other step annotations within the
            // resolution slice; the rule itself gates acceptance.
            other if other.starts_with(':') => {
                index += 2;
            }
            other => {
                return Err(AletheError::Parse(format!(
                    "unexpected token `{other}` in step"
                )));
            }
        }
    }

    let rule = rule.ok_or_else(|| AletheError::Parse("`step` missing `:rule`".to_owned()))?;
    Ok(AletheCommand::Step {
        id,
        clause,
        rule,
        premises,
        args,
    })
}

/// Parses a `(cl <lit>...)` step conclusion into a clause.
fn parse_cl_clause(sexp: &Sexp) -> Result<AletheClause, AletheError> {
    let Sexp::List(items) = sexp else {
        return Err(AletheError::Parse(
            "step conclusion must be a `(cl ...)` list".to_owned(),
        ));
    };
    match items.first().and_then(Sexp::as_atom) {
        Some("cl") => items[1..].iter().map(parse_literal).collect(),
        _ => Err(AletheError::Parse(
            "step conclusion must start with `cl`".to_owned(),
        )),
    }
}

/// Parses an assumed term as a clause: `(or ...)` is a disjunction; otherwise it
/// is a single literal (`(not a)` or bare atom `a`).
fn parse_term_as_clause(sexp: &Sexp) -> Result<AletheClause, AletheError> {
    if let Sexp::List(items) = sexp
        && items.first().and_then(Sexp::as_atom) == Some("or")
    {
        return items[1..].iter().map(parse_literal).collect();
    }
    Ok(vec![parse_literal(sexp)?])
}

/// Parses a single literal: `(not <term>)` (negated) or a bare `<term>`
/// (positive). The `not` connective is clause-level syntax (it negates the
/// literal); it is not an [`AletheTerm::App`] head.
fn parse_literal(sexp: &Sexp) -> Result<AletheLit, AletheError> {
    if let Sexp::List(items) = sexp
        && items.len() == 2
        && items[0].as_atom() == Some("not")
    {
        return Ok(AletheLit {
            atom: parse_term(&items[1])?,
            negated: true,
        });
    }
    Ok(AletheLit {
        atom: parse_term(sexp)?,
        negated: false,
    })
}

/// Parses an [`AletheTerm`]:
///
/// - a bare token is a [`AletheTerm::Const`];
/// - a list starting with the atom `_` — `(_ op i0 …)` — is a bare indexed
///   identifier [`AletheTerm::Indexed`] with no `args`;
/// - a list whose first element is itself an indexed identifier
///   `((_ op i0 …) a0 a1 …)` is an applied [`AletheTerm::Indexed`] whose `args`
///   are the remaining outer items;
/// - any other list whose head is a symbol is an [`AletheTerm::App`], with the
///   remaining elements parsed recursively as argument terms.
///
/// # Errors
///
/// Returns [`AletheError::Parse`] when an index does not parse as `i128`, when a
/// `(_ …)` lacks an op or indices, or when an application head is not a symbol.
fn parse_term(sexp: &Sexp) -> Result<AletheTerm, AletheError> {
    match sexp {
        Sexp::Atom(symbol) => Ok(AletheTerm::Const(symbol.clone())),
        Sexp::List(items) => {
            // Bare indexed identifier `(_ op i0 …)`.
            if items.first().and_then(Sexp::as_atom) == Some("_") {
                let (op, indices) = parse_indexed_identifier(items)?;
                return Ok(AletheTerm::Indexed {
                    op,
                    indices,
                    args: Vec::new(),
                });
            }
            // Applied indexed operator `((_ op i0 …) a0 a1 …)`: first element is
            // itself a `(_ …)` list.
            if let Some(Sexp::List(head_items)) = items.first()
                && head_items.first().and_then(Sexp::as_atom) == Some("_")
            {
                let (op, indices) = parse_indexed_identifier(head_items)?;
                let args = items[1..]
                    .iter()
                    .map(parse_term)
                    .collect::<Result<Vec<_>, _>>()?;
                return Ok(AletheTerm::Indexed { op, indices, args });
            }
            let head = items
                .first()
                .and_then(Sexp::as_atom)
                .ok_or_else(|| AletheError::Parse("application head must be a symbol".to_owned()))?
                .to_owned();
            let args = items[1..]
                .iter()
                .map(parse_term)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(AletheTerm::App(head, args))
        }
    }
}

/// Parses an indexed identifier `(_ op i0 i1 …)` into its operator symbol and
/// integer indices. `items` is the list including the leading `_` atom.
///
/// # Errors
///
/// Returns [`AletheError::Parse`] if `op` is missing, no indices are present, an
/// index is not an atom, or an index does not parse as `i128`.
fn parse_indexed_identifier(items: &[Sexp]) -> Result<(String, Vec<i128>), AletheError> {
    let op = items
        .get(1)
        .and_then(Sexp::as_atom)
        .ok_or_else(|| AletheError::Parse("`(_ …)` is missing its operator symbol".to_owned()))?
        .to_owned();
    if items.len() < 3 {
        return Err(AletheError::Parse(
            "`(_ op …)` is missing its index/indices".to_owned(),
        ));
    }
    let indices = items[2..]
        .iter()
        .map(|item| {
            item.as_atom()
                .ok_or_else(|| {
                    AletheError::Parse("indexed-operator index must be an atom".to_owned())
                })
                .and_then(|text| {
                    text.parse::<i128>().map_err(|_| {
                        AletheError::Parse(format!(
                            "indexed-operator index `{text}` is not an integer"
                        ))
                    })
                })
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((op, indices))
}

/// Serializes Alethe commands to the textual format. Round-trips through
/// [`parse_alethe`].
#[must_use]
pub fn write_alethe(commands: &[AletheCommand]) -> String {
    let mut out = String::new();
    for command in commands {
        match command {
            AletheCommand::Assume { id, clause } => {
                out.push_str("(assume ");
                out.push_str(id);
                out.push(' ');
                out.push_str(&write_term(clause));
                out.push_str(")\n");
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                args,
            } => {
                out.push_str("(step ");
                out.push_str(id);
                out.push(' ');
                out.push_str(&write_cl(clause));
                out.push_str(" :rule ");
                out.push_str(rule);
                if !premises.is_empty() {
                    out.push_str(" :premises (");
                    out.push_str(&premises.join(" "));
                    out.push(')');
                }
                if !args.is_empty() {
                    out.push_str(" :args (");
                    for (i, arg) in args.iter().enumerate() {
                        if i > 0 {
                            out.push(' ');
                        }
                        out.push_str(&write_atom(arg));
                    }
                    out.push(')');
                }
                out.push_str(")\n");
            }
        }
    }
    out
}

/// Renders an assumed term. A single literal renders bare; a multi-literal or
/// empty clause renders as `(or ...)`. (The empty `(or)` round-trips to the
/// empty clause through [`parse_term_as_clause`].)
fn write_term(clause: &AletheClause) -> String {
    if clause.len() == 1 {
        write_literal(&clause[0])
    } else {
        let mut out = String::from("(or");
        for lit in clause {
            out.push(' ');
            out.push_str(&write_literal(lit));
        }
        out.push(')');
        out
    }
}

fn write_cl(clause: &AletheClause) -> String {
    let mut out = String::from("(cl");
    for lit in clause {
        out.push(' ');
        out.push_str(&write_literal(lit));
    }
    out.push(')');
    out
}

fn write_literal(lit: &AletheLit) -> String {
    if lit.negated {
        format!("(not {})", write_atom(&lit.atom))
    } else {
        write_atom(&lit.atom)
    }
}

/// Renders an [`AletheTerm`]: `Const(s)` as `s`; `App(f, args)` as `(f a1 ...)`;
/// `Indexed { op, indices, args }` as `((_ op i0 …) a0 …)` with args, or the bare
/// `(_ op i0 …)` without. Round-trips through [`parse_term`].
fn write_atom(term: &AletheTerm) -> String {
    match term {
        AletheTerm::Const(symbol) => symbol.clone(),
        AletheTerm::App(head, args) => {
            let mut out = String::from("(");
            out.push_str(head);
            for arg in args {
                out.push(' ');
                out.push_str(&write_atom(arg));
            }
            out.push(')');
            out
        }
        AletheTerm::Indexed { op, indices, args } => {
            let head = indexed_head(op, indices);
            if args.is_empty() {
                head
            } else {
                let mut out = String::from("(");
                out.push_str(&head);
                for arg in args {
                    out.push(' ');
                    out.push_str(&write_atom(arg));
                }
                out.push(')');
                out
            }
        }
    }
}

/// Checks an Alethe resolution-layer proof.
///
/// Returns `Ok(true)` when every command checks and a verified step derives the
/// empty clause `(cl)` (UNSAT established), `Ok(false)` when every command
/// checks but the empty clause is never derived, and `Err` otherwise.
///
/// Each `assume` records its clause. Each `step` looks up its premises, then —
/// for `resolution`/`th_resolution` — verifies the conclusion is entailed by
/// the premises (the `{C1, …, Cn, ¬D}`-UNSAT test). A step is recorded only
/// after it verifies, so an invalid step is never available as a later premise.
///
/// # Errors
///
/// Returns [`AletheError::UnknownPremise`] for a missing premise id,
/// [`AletheError::UnsupportedRule`] for any rule outside the resolution slice,
/// and [`AletheError::StepNotEntailed`] for a step whose conclusion does not
/// follow from its premises.
pub fn check_alethe(commands: &[AletheCommand]) -> Result<bool, AletheError> {
    check_alethe_with(commands, &|_, _| None)
}

/// Like [`check_alethe`] but consults `extra` for any rule this checker does not
/// natively handle: `extra(rule, clause)` returns `Some(true)` to accept the step,
/// `Some(false)` to reject it ([`AletheError::StepNotEntailed`]), or `None` if it
/// too does not know the rule (then [`AletheError::UnsupportedRule`]). Used to plug
/// in theory-rule checkers (e.g. `la_generic` via an arithmetic solver) without
/// giving this crate an arithmetic dependency.
///
/// With `extra = &|_, _| None` this is byte-identical to [`check_alethe`].
///
/// # Errors
///
/// Returns [`AletheError::UnknownPremise`] for a missing premise id,
/// [`AletheError::UnsupportedRule`] for a rule neither this checker nor `extra`
/// handles, and [`AletheError::StepNotEntailed`] for a step whose conclusion does
/// not follow (natively, or as reported by `extra`).
pub fn check_alethe_with(
    commands: &[AletheCommand],
    extra: &dyn Fn(&str, &[AletheLit]) -> Option<bool>,
) -> Result<bool, AletheError> {
    // Deterministic id -> clause map (BTreeMap; no hashmap iteration).
    let mut clauses: BTreeMap<String, AletheClause> = BTreeMap::new();
    let mut derived_empty = false;

    for command in commands {
        match command {
            AletheCommand::Assume { id, clause } => {
                clauses.insert(id.clone(), clause.clone());
            }
            AletheCommand::Step {
                id,
                clause,
                rule,
                premises,
                ..
            } => {
                // Look up each premise; a missing id is a hard error.
                let mut premise_clauses: Vec<&AletheClause> = Vec::with_capacity(premises.len());
                for premise_id in premises {
                    let premise =
                        clauses
                            .get(premise_id)
                            .ok_or_else(|| AletheError::UnknownPremise {
                                id: premise_id.clone(),
                            })?;
                    premise_clauses.push(premise);
                }

                match rule.as_str() {
                    // Resolution and the clause-manipulation rules
                    // (`contraction` = drop duplicate literals, `reordering` =
                    // permute, `weakening` = add literals) all have a conclusion that
                    // is a logical consequence of the premise clauses, so the same
                    // proof-checked entailment test validates them. `or` unpacks an
                    // assumed disjunction `(or φ…)` into the clause `(cl φ…)` — also a
                    // pure entailment from the (clause-form) premise.
                    "resolution" | "th_resolution" | "contraction" | "reordering" | "weakening"
                    | "or" => {
                        if !premises_entail(&premise_clauses, clause)? {
                            return Err(AletheError::StepNotEntailed { id: id.clone() });
                        }
                    }
                    // The structurally-checked theory/CNF/equality rules.
                    other => match check_structural_rule(other, &premise_clauses, clause) {
                        Some(true) => {}
                        Some(false) => return Err(AletheError::StepNotEntailed { id: id.clone() }),
                        // Not a structural rule: defer to the caller's `extra` hook.
                        None => match extra(other, clause) {
                            Some(true) => {}
                            Some(false) => {
                                return Err(AletheError::StepNotEntailed { id: id.clone() });
                            }
                            None => {
                                return Err(AletheError::UnsupportedRule { rule: rule.clone() });
                            }
                        },
                    },
                }
                if clause.is_empty() {
                    derived_empty = true;
                }
                clauses.insert(id.clone(), clause.clone());
            }
        }
    }

    Ok(derived_empty)
}

/// Dispatches the structurally-checked Alethe rules (the EUF `eq_*` rules, the
/// Boolean CNF-introduction rules, and the general equality rules
/// `refl`/`symm`/`trans`/`cong`). Returns `Some(true)` if `rule` is one of these
/// and the step is valid, `Some(false)` if it is one of these but invalid, and
/// `None` if `rule` is not a structural rule this checker handles (so the caller
/// can defer to its `extra` hook). The premise-less rules additionally require an
/// empty premise list; the equality rules consume their unit-equality premises.
fn check_structural_rule(
    rule: &str,
    premise_clauses: &[&AletheClause],
    clause: &AletheClause,
) -> Option<bool> {
    let no_premises = premise_clauses.is_empty();
    match rule {
        "eq_reflexive" => Some(no_premises && is_eq_reflexive(clause)),
        "eq_transitive" => Some(no_premises && is_eq_transitive(clause)),
        "eq_symmetric" => Some(no_premises && is_eq_symmetric(clause)),
        "eq_congruent" => Some(no_premises && is_eq_congruent(clause)),
        "and_pos" => Some(no_premises && is_and_pos(clause)),
        "and_neg" => Some(no_premises && is_and_neg(clause)),
        "or_pos" => Some(no_premises && is_or_pos(clause)),
        "or_neg" => Some(no_premises && is_or_neg(clause)),
        "refl" => Some(no_premises && is_refl(clause)),
        "symm" => Some(is_symm(premise_clauses, clause)),
        "trans" => Some(is_trans(premise_clauses, clause)),
        "cong" => Some(is_cong(premise_clauses, clause)),
        _ => None,
    }
}

/// Returns the two arguments of a 2-arity `=` application, or `None` if the term
/// is not exactly an `(= a b)` application.
fn as_eq(term: &AletheTerm) -> Option<(&AletheTerm, &AletheTerm)> {
    match term {
        AletheTerm::App(head, args) if head == "=" && args.len() == 2 => Some((&args[0], &args[1])),
        _ => None,
    }
}

/// Returns the arguments of an application with the given `head`, or `None`.
fn as_app<'a>(term: &'a AletheTerm, head: &str) -> Option<&'a [AletheTerm]> {
    match term {
        AletheTerm::App(h, args) if h == head => Some(args),
        _ => None,
    }
}

/// Structural check for the Alethe `and_pos` rule:
/// `(cl (not (and t1 ... tn)) ti)` — a tautology `¬(t1∧…∧tn) ∨ ti` for any
/// conjunct `ti`. Valid iff two literals: a negated `and`-term, then a positive
/// literal whose atom is one of the conjuncts.
fn is_and_pos(clause: &AletheClause) -> bool {
    let [head, picked] = clause.as_slice() else {
        return false;
    };
    if !head.negated || picked.negated {
        return false;
    }
    let Some(conjuncts) = as_app(&head.atom, "and") else {
        return false;
    };
    conjuncts.contains(&picked.atom)
}

/// Structural check for the Alethe `or_neg` rule:
/// `(cl (or t1 ... tn) (not ti))` — a tautology `(t1∨…∨tn) ∨ ¬ti` for any
/// disjunct `ti`. Valid iff two literals: a positive `or`-term, then a negated
/// literal whose atom is one of the disjuncts.
fn is_or_neg(clause: &AletheClause) -> bool {
    let [head, picked] = clause.as_slice() else {
        return false;
    };
    if head.negated || !picked.negated {
        return false;
    }
    let Some(disjuncts) = as_app(&head.atom, "or") else {
        return false;
    };
    disjuncts.contains(&picked.atom)
}

/// Structural check for the Alethe `and_neg` rule:
/// `(cl (and t1 ... tn) (not t1) ... (not tn))` — the tautology
/// `(t1∧…∧tn) ∨ ¬t1 ∨ … ∨ ¬tn`. Valid iff a positive `and`-term followed by the
/// negation of each conjunct, in order.
fn is_and_neg(clause: &AletheClause) -> bool {
    polarity_spread(clause, "and", false)
}

/// Structural check for the Alethe `or_pos` rule:
/// `(cl (not (or t1 ... tn)) t1 ... tn)` — the tautology
/// `¬(t1∨…∨tn) ∨ t1 ∨ … ∨ tn`. Valid iff a negated `or`-term followed by each
/// disjunct, in order.
fn is_or_pos(clause: &AletheClause) -> bool {
    polarity_spread(clause, "or", true)
}

/// Shared shape for `and_neg` / `or_pos`: the first literal is the `head`-term
/// with `head_negated` polarity, followed by every argument as a literal of the
/// opposite polarity, in order.
fn polarity_spread(clause: &AletheClause, head: &str, head_negated: bool) -> bool {
    let Some((first, rest)) = clause.split_first() else {
        return false;
    };
    if first.negated != head_negated {
        return false;
    }
    let Some(args) = as_app(&first.atom, head) else {
        return false;
    };
    if args.len() != rest.len() {
        return false;
    }
    rest.iter()
        .zip(args)
        .all(|(lit, arg)| lit.negated != head_negated && &lit.atom == arg)
}

/// Structural check for the EUF `eq_reflexive` rule.
///
/// Valid iff the clause is exactly one positive literal `(= t t)` — i.e. a
/// single non-negated `App("=", [a, b])` with `a` structurally equal to `b`.
/// This clause `(= t t)` is an EUF tautology. Any other shape is rejected.
fn is_eq_reflexive(clause: &AletheClause) -> bool {
    let [lit] = clause.as_slice() else {
        return false;
    };
    if lit.negated {
        return false;
    }
    matches!(as_eq(&lit.atom), Some((a, b)) if a == b)
}

/// Structural check for the EUF `eq_transitive` rule.
///
/// Valid iff the clause has the exact ordered shape
/// `(cl (not (= t1 t2)) (not (= t2 t3)) ... (not (= t_{n-1} t_n)) (= t1 t_n))`
/// with `n >= 2` (so the clause has at least two literals):
///
/// - the first `k = len - 1` literals are each NEGATED equalities `¬(= aᵢ bᵢ)`
///   forming a chain — `bᵢ == a_{i+1}` structurally for consecutive literals;
/// - the last literal is a POSITIVE equality `(= s t)` with `s == a₁` (the first
///   chain lhs) and `t == b_k` (the last chain rhs).
///
/// Every expected-equality literal must be exactly a 2-arg `=` application; any
/// other head/arity rejects. The check is strict and order-sensitive: a
/// scrambled order is rejected (sound, just incomplete). The resulting clause is
/// the transitivity tautology `a₁=a₂ ∧ … ∧ a_{n-1}=aₙ → a₁=aₙ`.
fn is_eq_transitive(clause: &AletheClause) -> bool {
    // Need at least the chain (>= 1 hypothesis) plus the conclusion literal.
    if clause.len() < 2 {
        return false;
    }
    let (chain, last) = clause.split_at(clause.len() - 1);
    let conclusion = &last[0];

    // The conclusion is a positive equality `(= s t)`.
    if conclusion.negated {
        return false;
    }
    let Some((concl_lhs, concl_rhs)) = as_eq(&conclusion.atom) else {
        return false;
    };

    // The chain literals are negated equalities; collect their (lhs, rhs).
    let mut prev_rhs: Option<&AletheTerm> = None;
    let mut first_lhs: Option<&AletheTerm> = None;
    let mut last_rhs: Option<&AletheTerm> = None;
    for lit in chain {
        if !lit.negated {
            return false;
        }
        let Some((lhs, rhs)) = as_eq(&lit.atom) else {
            return false;
        };
        if let Some(expected) = prev_rhs {
            // Consecutive chain links must share the middle term.
            if expected != lhs {
                return false;
            }
        } else {
            first_lhs = Some(lhs);
        }
        prev_rhs = Some(rhs);
        last_rhs = Some(rhs);
    }

    // Conclusion endpoints must match the chain endpoints exactly.
    first_lhs == Some(concl_lhs) && last_rhs == Some(concl_rhs)
}

/// Structural check for the EUF `eq_symmetric` rule.
///
/// Valid iff the clause is exactly `(cl (not (= a b)) (= b a))` — a negated
/// equality followed by the positive equality with the sides swapped. This is the
/// symmetry tautology `a = b → b = a`. Any other shape is rejected.
fn is_eq_symmetric(clause: &AletheClause) -> bool {
    let [hyp, concl] = clause.as_slice() else {
        return false;
    };
    if !hyp.negated || concl.negated {
        return false;
    }
    let (Some((a, b)), Some((c, d))) = (as_eq(&hyp.atom), as_eq(&concl.atom)) else {
        return false;
    };
    // `(= a b)` hypothesis, `(= b a)` conclusion.
    a == d && b == c
}

/// Structural check for the EUF `eq_congruent` rule.
///
/// Valid iff the clause has the shape
/// `(cl (not (= a1 b1)) ... (not (= an bn)) (= (f a1 ... an) (f b1 ... bn)))`:
/// the last literal is a positive equality between two applications of the **same
/// head** `f` with the same arity `n`, and the first `n` literals are the negated
/// argument equalities `¬(= aᵢ bᵢ)` in order matching the conclusion's argument
/// pairs. This is the congruence tautology `⋀ᵢ aᵢ = bᵢ → f(a⃗) = f(b⃗)`. Strict and
/// order-sensitive; any deviation is rejected.
fn is_eq_congruent(clause: &AletheClause) -> bool {
    if clause.is_empty() {
        return false;
    }
    let (hyps, last) = clause.split_at(clause.len() - 1);
    let conclusion = &last[0];
    if conclusion.negated {
        return false;
    }
    // The conclusion equates `f(a1..an)` and `f(b1..bn)` (same head, same arity).
    let Some((lhs, rhs)) = as_eq(&conclusion.atom) else {
        return false;
    };
    let (AletheTerm::App(f_head, a_args), AletheTerm::App(g_head, b_args)) = (lhs, rhs) else {
        return false;
    };
    if f_head != g_head || a_args.len() != b_args.len() || a_args.len() != hyps.len() {
        return false;
    }
    // Each hypothesis is the negated equality of the matching argument pair, in
    // order. (A reflexive pair `aᵢ == bᵢ` still requires its `¬(= aᵢ bᵢ)` literal —
    // strict, sound; the omitted-reflexive form is left incomplete.)
    for (hyp, (a, b)) in hyps.iter().zip(a_args.iter().zip(b_args)) {
        if !hyp.negated {
            return false;
        }
        let Some((ha, hb)) = as_eq(&hyp.atom) else {
            return false;
        };
        if ha != a || hb != b {
            return false;
        }
    }
    true
}

/// Extracts the single positive equality `(= a b)` carried by a premise clause,
/// or `None` if the premise is not a unit clause holding one positive `=`
/// application of arity 2. The general equality rules (`symm`/`trans`/`cong`)
/// take their premises as such unit equality clauses; anything else rejects.
fn premise_eq(clause: &AletheClause) -> Option<(&AletheTerm, &AletheTerm)> {
    let [lit] = clause.as_slice() else {
        return None;
    };
    if lit.negated {
        return None;
    }
    as_eq(&lit.atom)
}

/// Structural check for the Alethe `refl` rule (structural subset).
///
/// No premises; the conclusion is the unit clause `(cl (= a b))`. Accepts iff `a`
/// and `b` are structurally equal. This is the sound core of Carcara's `refl`
/// (`reflexivity.rs`): Carcara's non-strict `refl` additionally permits
/// alpha-equivalence and context-substitution normalization, but for our purely
/// structural [`AletheTerm`]s plain structural equality is the valid subset —
/// any other shape (non-equality, two literals, or `a != b`) is rejected.
fn is_refl(clause: &AletheClause) -> bool {
    let [lit] = clause.as_slice() else {
        return false;
    };
    if lit.negated {
        return false;
    }
    matches!(as_eq(&lit.atom), Some((a, b)) if a == b)
}

/// Structural check for the Alethe `symm` rule.
///
/// One premise, the unit equality `(= a b)`; the conclusion is the unit clause
/// `(cl (= b a))`. Accepts iff the conclusion is exactly that equality with the
/// sides swapped relative to the premise. Mirrors Carcara's `symm` (`extras.rs`),
/// which takes one `=` premise and concludes the flipped `=`. Any other premise
/// count, a non-unit/non-positive/non-`=` premise or conclusion, or a conclusion
/// that is not the swap is rejected.
fn is_symm(premises: &[&AletheClause], clause: &AletheClause) -> bool {
    let [premise] = premises else {
        return false;
    };
    let Some((a, b)) = premise_eq(premise) else {
        return false;
    };
    let [lit] = clause.as_slice() else {
        return false;
    };
    if lit.negated {
        return false;
    }
    let Some((c, d)) = as_eq(&lit.atom) else {
        return false;
    };
    // Premise `(= a b)`, conclusion `(= b a)`.
    c == b && d == a
}

/// Structural check for the Alethe `trans` rule.
///
/// Premises are a chain of unit equalities `(= x0 x1)`, `(= x1 x2)`, …,
/// `(= x_{n-1} xn)`; the conclusion is the unit clause `(cl (= x0 xn))`. Accepts
/// iff the premises form a connected chain whose adjacent links share their
/// linking term (premise[i] right-hand side equals premise[i+1] left-hand side)
/// and whose endpoints are exactly the conclusion's two sides. This mirrors
/// Carcara's `trans` (`transitivity.rs::find_chain`) *adjacency* requirement:
/// each step extends the chain from the running endpoint. (Carcara also allows
/// each premise to be used flipped while resolving the chain; here we require the
/// premises to already be in chain order and orientation — a sound subset, just
/// incomplete on reordered/flipped premises.) At least one premise is required;
/// a broken (non-adjacent) chain or wrong endpoints are rejected.
fn is_trans(premises: &[&AletheClause], clause: &AletheClause) -> bool {
    let [lit] = clause.as_slice() else {
        return false;
    };
    if lit.negated {
        return false;
    }
    let Some((concl_lhs, concl_rhs)) = as_eq(&lit.atom) else {
        return false;
    };
    if premises.is_empty() {
        return false;
    }
    let mut endpoint: Option<&AletheTerm> = None;
    let mut first_lhs: Option<&AletheTerm> = None;
    for premise in premises {
        let Some((lhs, rhs)) = premise_eq(premise) else {
            return false;
        };
        match endpoint {
            None => first_lhs = Some(lhs),
            Some(expected) => {
                if expected != lhs {
                    return false;
                }
            }
        }
        endpoint = Some(rhs);
    }
    first_lhs == Some(concl_lhs) && endpoint == Some(concl_rhs)
}

/// Structural check for the Alethe `cong` rule.
///
/// Premises are argument equalities `(= a_i b_i)` (unit equality clauses); the
/// conclusion is the unit clause `(cl (= (f a1 … an) (f b1 … bn)))`, where the
/// two sides are applications of the same head with the same arity. Accepts iff:
/// both sides share a head — same [`AletheTerm::App`] symbol, or same
/// [`AletheTerm::Indexed`] `op`+`indices` — with equal arity, and the argument
/// pairs are justified following Carcara's `cong` premise-consumption convention
/// (`congruence.rs::check_cong`): iterate the zipped argument pairs and, for each
/// pair, *prefer to consume* the next premise if it equates the pair (in either
/// orientation); otherwise the pair must be directly structurally equal (no
/// premise consumed); otherwise reject. At the end **every** premise must have
/// been consumed (an unconsumed premise rejects). A head mismatch, arity
/// mismatch, a pair neither equal nor premise-justified, or a leftover premise is
/// rejected.
fn is_cong(premises: &[&AletheClause], clause: &AletheClause) -> bool {
    let [lit] = clause.as_slice() else {
        return false;
    };
    if lit.negated {
        return false;
    }
    let Some((lhs, rhs)) = as_eq(&lit.atom) else {
        return false;
    };
    // Same head + arity: either matching `App` symbols or matching `Indexed`
    // op+indices.
    let (f_args, g_args): (&[AletheTerm], &[AletheTerm]) = match (lhs, rhs) {
        (AletheTerm::App(f, fa), AletheTerm::App(g, ga)) if f == g => (fa, ga),
        (
            AletheTerm::Indexed {
                op: f_op,
                indices: f_ix,
                args: fa,
            },
            AletheTerm::Indexed {
                op: g_op,
                indices: g_ix,
                args: ga,
            },
        ) if f_op == g_op && f_ix == g_ix => (fa, ga),
        _ => return false,
    };
    if f_args.len() != g_args.len() {
        return false;
    }
    // Extract each premise's equality up front; any non-unit-equality rejects.
    let mut prem_eqs: Vec<(&AletheTerm, &AletheTerm)> = Vec::with_capacity(premises.len());
    for premise in premises {
        let Some(pair) = premise_eq(premise) else {
            return false;
        };
        prem_eqs.push(pair);
    }
    // Walk argument pairs, consuming premises per Carcara's `check_cong`: prefer
    // consuming the next premise when it justifies the pair, else require direct
    // structural equality.
    let mut next = 0;
    for (f_arg, g_arg) in f_args.iter().zip(g_args) {
        match prem_eqs.get(next) {
            Some(&(t, u)) if (f_arg == t && g_arg == u) || (f_arg == u && g_arg == t) => {
                next += 1;
            }
            _ if f_arg == g_arg => {}
            _ => return false,
        }
    }
    // All premises must have been consumed.
    next == prem_eqs.len()
}

/// Returns `true` iff `premises ⊨ conclusion`, decided as
/// `{premises..., ¬conclusion}`-UNSAT via the **proof-producing** SAT core with
/// the DRAT proof re-checked by [`crate::check_drat`].
///
/// Sound by construction: it returns `true` only when negating every conclusion
/// literal makes the premise set unsatisfiable *and* the refutation derives the
/// empty clause under an independent re-check — i.e. the conclusion truly follows.
/// A `Sat` (or resource-out) result yields `false`, so the checker rejects rather
/// than blessing an unverified step.
fn premises_entail(
    premises: &[&AletheClause],
    conclusion: &AletheClause,
) -> Result<bool, AletheError> {
    // Map each distinct atom (over premises and conclusion) to a fresh CnfVar,
    // deterministically by sorted atom text.
    let mut var_of: BTreeMap<String, CnfVar> = BTreeMap::new();
    for clause in premises {
        for lit in *clause {
            register_atom(&mut var_of, &lit.atom)?;
        }
    }
    for lit in conclusion {
        register_atom(&mut var_of, &lit.atom)?;
    }

    let mut formula = CnfFormula::new(var_of.len());
    // One clause per premise Ci.
    for clause in premises {
        let lits = clause
            .iter()
            .map(|lit| cnf_lit(&var_of, lit))
            .collect::<Vec<_>>();
        formula
            .add_clause(CnfClause::new(lits))
            .map_err(|error| AletheError::Parse(error.to_string()))?;
    }
    // One unit clause [¬l] for each literal l of the conclusion D (encoding ¬D).
    for lit in conclusion {
        let negated = cnf_lit(&var_of, lit).negated();
        formula
            .add_clause(CnfClause::new(vec![negated]))
            .map_err(|error| AletheError::Parse(error.to_string()))?;
    }

    // Decide `{premises, ¬D}` with the **proof-producing** core and re-check its
    // DRAT proof, so the entailment underpinning each accepted step is itself
    // independently verified (not merely trusted to the SAT search). Entailment
    // holds iff the formula is UNSAT *and* the proof derives the empty clause.
    match crate::solve_with_drat_proof(&formula) {
        crate::ProofSolveOutcome::Unsat(proof) => crate::check_drat(&formula, &proof)
            .map_err(|error| AletheError::Parse(error.to_string())),
        // Sat => a model satisfies the premises but falsifies D => not entailed.
        // ResourceOut => cannot establish entailment => reject (sound default).
        crate::ProofSolveOutcome::Sat(_) | crate::ProofSolveOutcome::ResourceOut => Ok(false),
    }
}

/// Bridges a clausal **LRAT** proof into an Alethe resolution proof over the same
/// formula, so a `QF_BV` (or any CNF) refutation produced through the
/// `solve_with_drat_proof` → `elaborate_drat_to_lrat` pipeline can be re-checked by
/// [`check_alethe`] as well as by [`crate::check_lrat`].
///
/// Each input clause becomes an `assume` with id `"1".."n"` (matching the LRAT
/// numbering); each LRAT `Add { id, clause, hints }` becomes a `resolution` step
/// whose premises are the antecedent hint ids — and since the learned clause is RUP
/// from exactly those antecedents, `{premises, ¬clause}` is UNSAT, so the
/// entailment check in [`check_alethe`] accepts it. LRAT deletions are dropped
/// (Alethe checking does not need them). CNF variable `k` maps to the atom `vk`.
#[must_use]
pub fn lrat_to_alethe(formula: &CnfFormula, proof: &[LratStep]) -> Vec<AletheCommand> {
    // Alethe command ids are SMT-LIB symbols, which may not be bare numerals;
    // LRAT clause ids (input clauses `1..=N`, then learned clauses) are numeric,
    // so every id is prefixed (`t` for a clause-producing step / unit assume, `a`
    // for a disjunction assume) to stay valid Alethe.
    //
    // A subtlety the lenient `check_alethe` hides but an external checker enforces:
    // an `assume (or φ…)` introduces the *formula* as a unit clause, not the clause
    // `(cl φ…)`. So each multi-literal input clause is `assume`d and then unpacked
    // with an explicit `:rule or` step into the clause form that resolution consumes.
    // `clause_form[k]` maps LRAT clause id `k` to the id of its `(cl …)` form.
    let mut commands = Vec::new();
    let mut or_steps = Vec::new();
    let mut clause_form: BTreeMap<u64, String> = BTreeMap::new();
    // All `assume`s first (Alethe convention; some checkers warn otherwise), with
    // the `or`-unpacking steps for multi-literal clauses deferred until after them.
    for (i, clause) in formula.clauses().iter().enumerate() {
        let lrat_id = i as u64 + 1;
        let lits = clause.lits();
        if lits.len() >= 2 {
            // Multi-literal: assume the disjunction, then `or`-unpack to a clause.
            let assume_id = format!("a{lrat_id}");
            let clause_id = format!("t{lrat_id}");
            commands.push(AletheCommand::Assume {
                id: assume_id.clone(),
                clause: alethe_clause(lits),
            });
            or_steps.push(AletheCommand::Step {
                id: clause_id.clone(),
                clause: alethe_clause(lits),
                rule: "or".to_owned(),
                premises: vec![assume_id],
                args: Vec::new(),
            });
            clause_form.insert(lrat_id, clause_id);
        } else {
            // Unit (or empty) input clause: the assume is already in clause form.
            let id = format!("t{lrat_id}");
            commands.push(AletheCommand::Assume {
                id: id.clone(),
                clause: alethe_clause(lits),
            });
            clause_form.insert(lrat_id, id);
        }
    }
    commands.append(&mut or_steps);
    for step in proof {
        if let LratStep::Add { id, clause, hints } = step {
            let step_id = format!("t{id}");
            commands.push(AletheCommand::Step {
                id: step_id.clone(),
                clause: alethe_clause(clause),
                rule: "resolution".to_owned(),
                premises: hints
                    .iter()
                    .map(|&h| {
                        clause_form
                            .get(&h)
                            .cloned()
                            .unwrap_or_else(|| format!("t{h}"))
                    })
                    .collect(),
                args: Vec::new(),
            });
            clause_form.insert(*id, step_id);
        }
    }
    commands
}

/// Lowers a CNF clause to an Alethe clause, mapping variable `k` to atom `vk`.
fn alethe_clause(lits: &[CnfLit]) -> AletheClause {
    lits.iter()
        .map(|lit| AletheLit {
            atom: AletheTerm::Const(format!("v{}", lit.var().index())),
            negated: lit.is_negated(),
        })
        .collect()
}

fn register_atom(
    var_of: &mut BTreeMap<String, CnfVar>,
    atom: &AletheTerm,
) -> Result<(), AletheError> {
    let key = atom.key();
    if !var_of.contains_key(&key) {
        let index = var_of.len();
        let var = CnfVar::new(index).map_err(|error| AletheError::Parse(error.to_string()))?;
        var_of.insert(key, var);
    }
    Ok(())
}

/// Maps an [`AletheLit`] to a [`CnfLit`] over the atom-variable map, keyed by the
/// atom's canonical [`AletheTerm::key`]. The atom is guaranteed present (every
/// atom is registered before this is called).
fn cnf_lit(var_of: &BTreeMap<String, CnfVar>, lit: &AletheLit) -> CnfLit {
    let var = *var_of
        .get(&lit.atom.key())
        .expect("atom registered before literal lowering");
    let cnf = CnfLit::positive(var);
    if lit.negated { cnf.negated() } else { cnf }
}

#[cfg(test)]
mod tests {
    use super::{
        AletheClause, AletheCommand, AletheError, AletheLit, AletheTerm, check_alethe,
        check_alethe_with, lrat_to_alethe, parse_alethe, write_alethe,
    };
    use crate::{
        CnfClause, CnfFormula, CnfLit, CnfVar, ProofSolveOutcome, elaborate_drat_to_lrat,
        solve_with_drat_proof,
    };

    fn lit(atom: &str) -> AletheLit {
        AletheLit {
            atom: AletheTerm::Const(atom.to_owned()),
            negated: false,
        }
    }

    fn neg(atom: &str) -> AletheLit {
        AletheLit {
            atom: AletheTerm::Const(atom.to_owned()),
            negated: true,
        }
    }

    /// A positive literal `(= a b)`.
    fn eq_lit(a: &str, b: &str) -> AletheLit {
        AletheLit {
            atom: AletheTerm::App(
                "=".to_owned(),
                vec![
                    AletheTerm::Const(a.to_owned()),
                    AletheTerm::Const(b.to_owned()),
                ],
            ),
            negated: false,
        }
    }

    /// A negated literal `(not (= a b))`.
    fn neq_lit(a: &str, b: &str) -> AletheLit {
        AletheLit {
            negated: true,
            ..eq_lit(a, b)
        }
    }

    fn assume(id: &str, clause: AletheClause) -> AletheCommand {
        AletheCommand::Assume {
            id: id.to_owned(),
            clause,
        }
    }

    fn step(id: &str, clause: AletheClause, rule: &str, premises: &[&str]) -> AletheCommand {
        AletheCommand::Step {
            id: id.to_owned(),
            clause,
            rule: rule.to_owned(),
            premises: premises.iter().map(|p| (*p).to_owned()).collect(),
            args: Vec::new(),
        }
    }

    #[test]
    fn lrat_proof_bridges_to_a_checkable_alethe_proof() {
        // End-to-end: a CNF UNSAT formula → proof-producing CDCL → DRAT → LRAT →
        // Alethe resolution → check_alethe accepts. (a∨b)∧(a∨¬b)∧(¬a∨b)∧(¬a∨¬b).
        let v = |i: usize| CnfVar::new(i).unwrap();
        let pos = |i: usize| CnfLit::positive(v(i));
        let neg_l = |i: usize| CnfLit::positive(v(i)).negated();
        let mut formula = CnfFormula::new(2);
        for clause in [
            vec![pos(0), pos(1)],
            vec![pos(0), neg_l(1)],
            vec![neg_l(0), pos(1)],
            vec![neg_l(0), neg_l(1)],
        ] {
            formula.add_clause(CnfClause::new(clause)).unwrap();
        }

        let ProofSolveOutcome::Unsat(drat) = solve_with_drat_proof(&formula) else {
            panic!("the formula is unsatisfiable");
        };
        let lrat = elaborate_drat_to_lrat(&formula, &drat).expect("RUP proof elaborates to LRAT");
        let alethe = lrat_to_alethe(&formula, &lrat);
        assert_eq!(
            check_alethe(&alethe),
            Ok(true),
            "the bridged Alethe resolution proof must check and derive the empty clause"
        );
        // The bridged proof also survives a text round-trip and still checks.
        let reparsed = parse_alethe(&write_alethe(&alethe)).expect("bridged Alethe round-trips");
        assert_eq!(check_alethe(&reparsed), Ok(true));
    }

    #[test]
    fn extra_callback_gates_unknown_rules() {
        // A made-up rule `foo` is dispatched to the `extra` callback: accepted iff
        // it returns Some(true), rejected on Some(false), unsupported on None.
        let proof = vec![step("s1", vec![lit("a")], "foo", &[])];

        // Some(true): the step is recorded; no empty clause, so Ok(false).
        assert_eq!(
            check_alethe_with(&proof, &|rule, _| (rule == "foo").then_some(true)),
            Ok(false)
        );

        // Some(false): rejected as not entailed.
        assert_eq!(
            check_alethe_with(&proof, &|rule, _| (rule == "foo").then_some(false)),
            Err(AletheError::StepNotEntailed {
                id: "s1".to_owned()
            })
        );

        // None: the callback does not know the rule either => unsupported.
        assert_eq!(
            check_alethe_with(&proof, &|_, _| None),
            Err(AletheError::UnsupportedRule {
                rule: "foo".to_owned()
            })
        );

        // Some(true) on the empty clause derives UNSAT (Ok(true)).
        let empty = vec![step("s1", vec![], "foo", &[])];
        assert_eq!(
            check_alethe_with(&empty, &|_, _| Some(true)),
            Ok(true),
            "an accepted empty-clause step establishes UNSAT"
        );
    }

    #[test]
    fn parse_write_roundtrip() {
        let commands = vec![
            assume("h1", vec![lit("a"), lit("b")]),
            assume("h2", vec![neg("a")]),
            assume("h3", vec![lit("a"), neg("b"), lit("c")]),
            step("t1", vec![lit("b")], "resolution", &["h1", "h2"]),
            step("t2", vec![], "th_resolution", &["t1", "h2", "h3"]),
        ];
        let text = write_alethe(&commands);
        let parsed = parse_alethe(&text).unwrap();
        assert_eq!(parsed, commands);
    }

    #[test]
    fn checks_a_resolution_refutation() {
        // Classic 2x2 UNSAT over atoms a, b:
        //   (a ∨ b), (a ∨ ¬b), (¬a ∨ b), (¬a ∨ ¬b).
        // Resolve to (a), then (¬a), then the empty clause.
        let commands = vec![
            assume("h1", vec![lit("a"), lit("b")]),
            assume("h2", vec![lit("a"), neg("b")]),
            assume("h3", vec![neg("a"), lit("b")]),
            assume("h4", vec![neg("a"), neg("b")]),
            // (a∨b) ⊗ (a∨¬b) ⊨ (a).
            step("s1", vec![lit("a")], "resolution", &["h1", "h2"]),
            // (¬a∨b) ⊗ (¬a∨¬b) ⊨ (¬a).
            step("s2", vec![neg("a")], "resolution", &["h3", "h4"]),
            // (a) ⊗ (¬a) ⊨ ().
            step("s3", vec![], "resolution", &["s1", "s2"]),
        ];
        assert_eq!(check_alethe(&commands), Ok(true));
    }

    #[test]
    fn rejects_a_non_entailed_step() {
        // From (a ∨ b) alone, (cl a) does NOT follow: b could hold with a false.
        let commands = vec![
            assume("h1", vec![lit("a"), lit("b")]),
            step("s1", vec![lit("a")], "resolution", &["h1"]),
        ];
        assert_eq!(
            check_alethe(&commands),
            Err(AletheError::StepNotEntailed {
                id: "s1".to_owned()
            })
        );
    }

    #[test]
    fn rejects_unknown_premise() {
        let commands = vec![
            assume("h1", vec![lit("a"), lit("b")]),
            // `ghost` was never defined.
            step("s1", vec![lit("a")], "resolution", &["h1", "ghost"]),
        ];
        assert_eq!(
            check_alethe(&commands),
            Err(AletheError::UnknownPremise {
                id: "ghost".to_owned()
            })
        );
    }

    #[test]
    fn rejects_unsupported_rule() {
        let commands = vec![
            assume("h1", vec![lit("a")]),
            assume("h2", vec![lit("b")]),
            step("s1", vec![lit("a"), lit("b")], "and", &["h1", "h2"]),
        ];
        assert_eq!(
            check_alethe(&commands),
            Err(AletheError::UnsupportedRule {
                rule: "and".to_owned()
            })
        );
    }

    #[test]
    fn empty_clause_required_for_unsat() {
        // Valid resolution that never reaches the empty clause => Ok(false).
        let commands = vec![
            assume("h1", vec![lit("a"), lit("b")]),
            assume("h2", vec![neg("b")]),
            // (a∨b) ⊗ (¬b) ⊨ (a). Valid, but not the empty clause.
            step("s1", vec![lit("a")], "resolution", &["h1", "h2"]),
        ];
        assert_eq!(check_alethe(&commands), Ok(false));
    }

    #[test]
    fn parse_real_alethe_snippet() {
        let text = "\
; a small resolution refutation over atoms x and y
(assume h1 (or x y))
(assume h2 (or x (not y)))
(assume h3 (or (not x) y))
(assume h4 (or (not x) (not y)))
(step s1 (cl x) :rule resolution :premises (h1 h2))
(step s2 (cl (not x)) :rule resolution :premises (h3 h4))
(step s3 (cl) :rule resolution :premises (s1 s2))
";
        let commands = parse_alethe(text).unwrap();
        assert_eq!(commands.len(), 7);
        assert_eq!(check_alethe(&commands), Ok(true));
    }

    #[test]
    fn eq_reflexive_checks() {
        // A lone valid `eq_reflexive` step `(cl (= a a))` verifies but does not
        // derive the empty clause => Ok(false).
        let valid = vec![step("r1", vec![eq_lit("a", "a")], "eq_reflexive", &[])];
        assert_eq!(check_alethe(&valid), Ok(false));

        // A broken reflexivity `(cl (= a b))` with a != b is rejected.
        let broken = vec![step("r1", vec![eq_lit("a", "b")], "eq_reflexive", &[])];
        assert_eq!(
            check_alethe(&broken),
            Err(AletheError::StepNotEntailed {
                id: "r1".to_owned()
            })
        );
    }

    #[test]
    fn eq_transitive_checks() {
        // Valid: (not (= a b)) (not (= b c)) (= a c).
        let valid = vec![step(
            "t1",
            vec![neq_lit("a", "b"), neq_lit("b", "c"), eq_lit("a", "c")],
            "eq_transitive",
            &[],
        )];
        assert_eq!(check_alethe(&valid), Ok(false));

        // Broken: wrong final rhs `d` instead of `c`.
        let bad_rhs = vec![step(
            "t1",
            vec![neq_lit("a", "b"), neq_lit("b", "c"), eq_lit("a", "d")],
            "eq_transitive",
            &[],
        )];
        assert_eq!(
            check_alethe(&bad_rhs),
            Err(AletheError::StepNotEntailed {
                id: "t1".to_owned()
            })
        );

        // Broken: a non-equality middle literal `(not (p b))`.
        let non_eq_middle = vec![step(
            "t1",
            vec![
                neq_lit("a", "b"),
                AletheLit {
                    atom: AletheTerm::App("p".to_owned(), vec![AletheTerm::Const("b".to_owned())]),
                    negated: true,
                },
                eq_lit("a", "c"),
            ],
            "eq_transitive",
            &[],
        )];
        assert_eq!(
            check_alethe(&non_eq_middle),
            Err(AletheError::StepNotEntailed {
                id: "t1".to_owned()
            })
        );

        // Broken: scrambled chain order is rejected (sound, just incomplete).
        let scrambled = vec![step(
            "t1",
            vec![neq_lit("b", "c"), neq_lit("a", "b"), eq_lit("a", "c")],
            "eq_transitive",
            &[],
        )];
        assert_eq!(
            check_alethe(&scrambled),
            Err(AletheError::StepNotEntailed {
                id: "t1".to_owned()
            })
        );
    }

    #[test]
    fn eq_symmetric_checks() {
        // Valid: (cl (not (= a b)) (= b a)).
        let valid = vec![step(
            "s1",
            vec![neq_lit("a", "b"), eq_lit("b", "a")],
            "eq_symmetric",
            &[],
        )];
        assert_eq!(check_alethe(&valid), Ok(false));

        // Broken: conclusion not swapped — (cl (not (= a b)) (= a b)).
        let not_swapped = vec![step(
            "s1",
            vec![neq_lit("a", "b"), eq_lit("a", "b")],
            "eq_symmetric",
            &[],
        )];
        assert_eq!(
            check_alethe(&not_swapped),
            Err(AletheError::StepNotEntailed {
                id: "s1".to_owned()
            })
        );
    }

    #[test]
    fn eq_congruent_checks() {
        // Valid: (cl (not (= a c)) (not (= b d)) (= (f a b) (f c d))).
        let fab = AletheTerm::App(
            "f".to_owned(),
            vec![
                AletheTerm::Const("a".to_owned()),
                AletheTerm::Const("b".to_owned()),
            ],
        );
        let fcd = AletheTerm::App(
            "f".to_owned(),
            vec![
                AletheTerm::Const("c".to_owned()),
                AletheTerm::Const("d".to_owned()),
            ],
        );
        let concl = AletheLit {
            atom: AletheTerm::App("=".to_owned(), vec![fab, fcd]),
            negated: false,
        };
        let valid = vec![step(
            "c1",
            vec![neq_lit("a", "c"), neq_lit("b", "d"), concl.clone()],
            "eq_congruent",
            &[],
        )];
        assert_eq!(check_alethe(&valid), Ok(false));

        // Broken: a hypothesis pair does not match the conclusion's argument pair
        // — uses (not (= a d)) where the first f-argument pair is (a, c).
        let mismatched = vec![step(
            "c1",
            vec![neq_lit("a", "d"), neq_lit("b", "d"), concl.clone()],
            "eq_congruent",
            &[],
        )];
        assert_eq!(
            check_alethe(&mismatched),
            Err(AletheError::StepNotEntailed {
                id: "c1".to_owned()
            })
        );

        // Broken: mismatched function heads f vs g in the conclusion.
        let gcd = AletheTerm::App(
            "g".to_owned(),
            vec![
                AletheTerm::Const("c".to_owned()),
                AletheTerm::Const("d".to_owned()),
            ],
        );
        let fab2 = AletheTerm::App(
            "f".to_owned(),
            vec![
                AletheTerm::Const("a".to_owned()),
                AletheTerm::Const("b".to_owned()),
            ],
        );
        let head_mismatch = vec![step(
            "c1",
            vec![
                neq_lit("a", "c"),
                neq_lit("b", "d"),
                AletheLit {
                    atom: AletheTerm::App("=".to_owned(), vec![fab2, gcd]),
                    negated: false,
                },
            ],
            "eq_congruent",
            &[],
        )];
        assert_eq!(
            check_alethe(&head_mismatch),
            Err(AletheError::StepNotEntailed {
                id: "c1".to_owned()
            })
        );
    }

    /// An `(= a b)` literal whose sides are arbitrary terms.
    fn eq_term_lit(a: AletheTerm, b: AletheTerm) -> AletheLit {
        AletheLit {
            atom: AletheTerm::App("=".to_owned(), vec![a, b]),
            negated: false,
        }
    }

    /// `App(head, args)` over `Const` arguments.
    fn app(head: &str, args: &[&str]) -> AletheTerm {
        AletheTerm::App(
            head.to_owned(),
            args.iter()
                .map(|a| AletheTerm::Const((*a).to_owned()))
                .collect(),
        )
    }

    #[test]
    fn refl_checks() {
        // Accepts `(= x x)`.
        let valid = vec![step("r", vec![eq_lit("x", "x")], "refl", &[])];
        assert_eq!(check_alethe(&valid), Ok(false));

        // Accepts a compound reflexive `(= (f a) (f a))`.
        let compound = vec![step(
            "r",
            vec![eq_term_lit(app("f", &["a"]), app("f", &["a"]))],
            "refl",
            &[],
        )];
        assert_eq!(check_alethe(&compound), Ok(false));

        // Rejects `(= x y)` with x != y.
        let bad = vec![step("r", vec![eq_lit("x", "y")], "refl", &[])];
        assert_eq!(
            check_alethe(&bad),
            Err(AletheError::StepNotEntailed { id: "r".to_owned() })
        );

        // Rejects a stray premise (refl takes none).
        let with_premise = vec![
            assume("h", vec![eq_lit("a", "b")]),
            step("r", vec![eq_lit("x", "x")], "refl", &["h"]),
        ];
        assert_eq!(
            check_alethe(&with_premise),
            Err(AletheError::StepNotEntailed { id: "r".to_owned() })
        );
    }

    #[test]
    fn symm_checks() {
        // Accepts the swap: premise `(= a b)`, conclusion `(= b a)`.
        let valid = vec![
            assume("h", vec![eq_lit("a", "b")]),
            step("s", vec![eq_lit("b", "a")], "symm", &["h"]),
        ];
        assert_eq!(check_alethe(&valid), Ok(false));

        // Rejects a non-swap: conclusion `(= a b)` (same orientation).
        let not_swapped = vec![
            assume("h", vec![eq_lit("a", "b")]),
            step("s", vec![eq_lit("a", "b")], "symm", &["h"]),
        ];
        assert_eq!(
            check_alethe(&not_swapped),
            Err(AletheError::StepNotEntailed { id: "s".to_owned() })
        );

        // Rejects wrong terms: conclusion `(= c a)`.
        let wrong = vec![
            assume("h", vec![eq_lit("a", "b")]),
            step("s", vec![eq_lit("c", "a")], "symm", &["h"]),
        ];
        assert_eq!(
            check_alethe(&wrong),
            Err(AletheError::StepNotEntailed { id: "s".to_owned() })
        );

        // Rejects a missing premise (symm needs exactly one).
        let no_premise = vec![step("s", vec![eq_lit("b", "a")], "symm", &[])];
        assert_eq!(
            check_alethe(&no_premise),
            Err(AletheError::StepNotEntailed { id: "s".to_owned() })
        );
    }

    #[test]
    fn trans_checks() {
        // 2-link chain: (= a b), (= b c) ⊢ (= a c).
        let two = vec![
            assume("h1", vec![eq_lit("a", "b")]),
            assume("h2", vec![eq_lit("b", "c")]),
            step("t", vec![eq_lit("a", "c")], "trans", &["h1", "h2"]),
        ];
        assert_eq!(check_alethe(&two), Ok(false));

        // 3-link chain: (= a b), (= b c), (= c d) ⊢ (= a d).
        let three = vec![
            assume("h1", vec![eq_lit("a", "b")]),
            assume("h2", vec![eq_lit("b", "c")]),
            assume("h3", vec![eq_lit("c", "d")]),
            step("t", vec![eq_lit("a", "d")], "trans", &["h1", "h2", "h3"]),
        ];
        assert_eq!(check_alethe(&three), Ok(false));

        // Broken chain: links are not adjacent — (= a b), (= c d) does not connect.
        let broken = vec![
            assume("h1", vec![eq_lit("a", "b")]),
            assume("h2", vec![eq_lit("c", "d")]),
            step("t", vec![eq_lit("a", "d")], "trans", &["h1", "h2"]),
        ];
        assert_eq!(
            check_alethe(&broken),
            Err(AletheError::StepNotEntailed { id: "t".to_owned() })
        );

        // Wrong endpoints: chain (= a b), (= b c) but conclusion (= a d).
        let wrong_end = vec![
            assume("h1", vec![eq_lit("a", "b")]),
            assume("h2", vec![eq_lit("b", "c")]),
            step("t", vec![eq_lit("a", "d")], "trans", &["h1", "h2"]),
        ];
        assert_eq!(
            check_alethe(&wrong_end),
            Err(AletheError::StepNotEntailed { id: "t".to_owned() })
        );
    }

    #[test]
    fn cong_checks() {
        // f(a) = f(b) from a = b.
        let unary = vec![
            assume("h", vec![eq_lit("a", "b")]),
            step(
                "c",
                vec![eq_term_lit(app("f", &["a"]), app("f", &["b"]))],
                "cong",
                &["h"],
            ),
        ];
        assert_eq!(check_alethe(&unary), Ok(false));

        // g(a, c) = g(b, c) from a = b: the unchanged 2nd argument needs no premise.
        let binary = vec![
            assume("h", vec![eq_lit("a", "b")]),
            step(
                "c",
                vec![eq_term_lit(app("g", &["a", "c"]), app("g", &["b", "c"]))],
                "cong",
                &["h"],
            ),
        ];
        assert_eq!(check_alethe(&binary), Ok(false));

        // Indexed-head congruence: ((_ @bit_of 0) a) = ((_ @bit_of 0) b) from a = b.
        let indexed = vec![
            assume("h", vec![eq_lit("a", "b")]),
            step(
                "c",
                vec![eq_term_lit(bit_of(0, "a"), bit_of(0, "b"))],
                "cong",
                &["h"],
            ),
        ];
        assert_eq!(check_alethe(&indexed), Ok(false));

        // Head mismatch: f(a) vs g(b).
        let head_mismatch = vec![
            assume("h", vec![eq_lit("a", "b")]),
            step(
                "c",
                vec![eq_term_lit(app("f", &["a"]), app("g", &["b"]))],
                "cong",
                &["h"],
            ),
        ];
        assert_eq!(
            check_alethe(&head_mismatch),
            Err(AletheError::StepNotEntailed { id: "c".to_owned() })
        );

        // Arity mismatch: f(a) vs f(b, c).
        let arity_mismatch = vec![
            assume("h", vec![eq_lit("a", "b")]),
            step(
                "c",
                vec![eq_term_lit(app("f", &["a"]), app("f", &["b", "c"]))],
                "cong",
                &["h"],
            ),
        ];
        assert_eq!(
            check_alethe(&arity_mismatch),
            Err(AletheError::StepNotEntailed { id: "c".to_owned() })
        );

        // A position neither equal nor justified: f(a, c) vs f(b, d) with only a = b.
        let unjustified = vec![
            assume("h", vec![eq_lit("a", "b")]),
            step(
                "c",
                vec![eq_term_lit(app("f", &["a", "c"]), app("f", &["b", "d"]))],
                "cong",
                &["h"],
            ),
        ];
        assert_eq!(
            check_alethe(&unjustified),
            Err(AletheError::StepNotEntailed { id: "c".to_owned() })
        );
    }

    #[test]
    fn cong_and_trans_drive_an_unsat_refutation() {
        // End-to-end mirroring the QF_BV bridge: use cong + trans to derive an
        // equality, then resolve it against its negation to the empty clause.
        // h1: a = b ; cong ⊢ f(a) = f(b) ; (assumed) f(b) = c ; trans ⊢ f(a) = c ;
        // assumed ¬(f(a) = c) ; resolve to (cl).
        let fa = app("f", &["a"]);
        let fb = app("f", &["b"]);
        let c = AletheTerm::Const("c".to_owned());
        let commands = vec![
            assume("h1", vec![eq_lit("a", "b")]),
            assume("h2", vec![eq_term_lit(fb.clone(), c.clone())]),
            assume(
                "h3",
                vec![AletheLit {
                    negated: true,
                    ..eq_term_lit(fa.clone(), c.clone())
                }],
            ),
            step(
                "s1",
                vec![eq_term_lit(fa.clone(), fb.clone())],
                "cong",
                &["h1"],
            ),
            step(
                "s2",
                vec![eq_term_lit(fa.clone(), c.clone())],
                "trans",
                &["s1", "h2"],
            ),
            step("s3", vec![], "resolution", &["s2", "h3"]),
        ];
        assert_eq!(check_alethe(&commands), Ok(true));
    }

    #[test]
    fn clause_manipulation_rules_check() {
        // contraction: drop a duplicate literal.
        let contraction = vec![
            assume("h", vec![lit("a"), lit("a"), lit("b")]),
            step("c", vec![lit("a"), lit("b")], "contraction", &["h"]),
        ];
        assert_eq!(check_alethe(&contraction), Ok(false));

        // reordering: permute the literals.
        let reordering = vec![
            assume("h", vec![lit("a"), lit("b")]),
            step("r", vec![lit("b"), lit("a")], "reordering", &["h"]),
        ];
        assert_eq!(check_alethe(&reordering), Ok(false));

        // weakening: add a literal (the conclusion is weaker).
        let weakening = vec![
            assume("h", vec![lit("a")]),
            step("w", vec![lit("a"), lit("b")], "weakening", &["h"]),
        ];
        assert_eq!(check_alethe(&weakening), Ok(false));

        // Broken "weakening" that DROPS a literal is not entailed ⇒ rejected.
        let bad = vec![
            assume("h", vec![lit("a"), lit("b")]),
            step("w", vec![lit("a")], "weakening", &["h"]),
        ];
        assert_eq!(
            check_alethe(&bad),
            Err(AletheError::StepNotEntailed { id: "w".to_owned() })
        );
    }

    #[test]
    fn boolean_cnf_intro_rules_check() {
        let cst = |s: &str| AletheTerm::Const(s.to_owned());
        let and_ab = AletheTerm::App("and".to_owned(), vec![cst("a"), cst("b")]);
        let or_ab = AletheTerm::App("or".to_owned(), vec![cst("a"), cst("b")]);
        let lit_t = |t: AletheTerm| AletheLit {
            atom: t,
            negated: false,
        };
        let lit_f = |t: AletheTerm| AletheLit {
            atom: t,
            negated: true,
        };

        // and_pos: (cl (not (and a b)) a) — valid.
        let and_pos = vec![step(
            "p",
            vec![lit_f(and_ab.clone()), lit_t(cst("a"))],
            "and_pos",
            &[],
        )];
        assert_eq!(check_alethe(&and_pos), Ok(false));

        // and_pos broken: picked conjunct `c` is not in (and a b).
        let and_pos_bad = vec![step(
            "p",
            vec![lit_f(and_ab.clone()), lit_t(cst("c"))],
            "and_pos",
            &[],
        )];
        assert_eq!(
            check_alethe(&and_pos_bad),
            Err(AletheError::StepNotEntailed { id: "p".to_owned() })
        );

        // or_neg: (cl (or a b) (not b)) — valid.
        let or_neg = vec![step(
            "p",
            vec![lit_t(or_ab.clone()), lit_f(cst("b"))],
            "or_neg",
            &[],
        )];
        assert_eq!(check_alethe(&or_neg), Ok(false));

        // and_neg: (cl (and a b) (not a) (not b)) — valid.
        let and_neg = vec![step(
            "p",
            vec![lit_t(and_ab.clone()), lit_f(cst("a")), lit_f(cst("b"))],
            "and_neg",
            &[],
        )];
        assert_eq!(check_alethe(&and_neg), Ok(false));

        // and_neg broken: wrong order of negated conjuncts.
        let and_neg_bad = vec![step(
            "p",
            vec![lit_t(and_ab.clone()), lit_f(cst("b")), lit_f(cst("a"))],
            "and_neg",
            &[],
        )];
        assert_eq!(
            check_alethe(&and_neg_bad),
            Err(AletheError::StepNotEntailed { id: "p".to_owned() })
        );

        // or_pos: (cl (not (or a b)) a b) — valid.
        let or_pos = vec![step(
            "p",
            vec![lit_f(or_ab.clone()), lit_t(cst("a")), lit_t(cst("b"))],
            "or_pos",
            &[],
        )];
        assert_eq!(check_alethe(&or_pos), Ok(false));
    }

    #[test]
    fn typed_term_resolution_still_works() {
        // The same structured atom `(= a b)` used across two clauses must unify
        // to one entailment variable: (¬(= a b)) and ((= a b)) resolve to ().
        let commands = vec![
            assume("h1", vec![eq_lit("a", "b")]),
            assume("h2", vec![neq_lit("a", "b")]),
            step("s1", vec![], "resolution", &["h1", "h2"]),
        ];
        assert_eq!(check_alethe(&commands), Ok(true));

        // And the structured atoms survive a text round-trip.
        let reparsed = parse_alethe(&write_alethe(&commands)).unwrap();
        assert_eq!(reparsed, commands);
    }

    #[test]
    fn step_with_args_parse_write_roundtrip() {
        // A `la_generic` step carrying Farkas-coefficient `:args` round-trips,
        // and its rendering places `:args` after the clause (no `:premises` here).
        let commands = vec![step("la", vec![neg("a"), neg("b")], "la_generic", &[])];
        // Inject `:args` into the step (the constructor helper leaves them empty).
        let with_args = {
            let mut cmd = commands;
            if let AletheCommand::Step { args, .. } = &mut cmd[0] {
                *args = vec![
                    AletheTerm::Const("1".to_owned()),
                    AletheTerm::App(
                        "/".to_owned(),
                        vec![
                            AletheTerm::Const("1.0".to_owned()),
                            AletheTerm::Const("3.0".to_owned()),
                        ],
                    ),
                ];
            }
            cmd
        };
        let text = write_alethe(&with_args);
        assert!(
            text.contains(":args (1 (/ 1.0 3.0))"),
            "args render after the clause/premises:\n{text}"
        );
        let parsed = parse_alethe(&text).unwrap();
        assert_eq!(parsed, with_args);
    }

    #[test]
    fn typed_term_parse_write_roundtrip() {
        let commands = vec![
            assume("h1", vec![eq_lit("a", "b"), lit("p")]),
            assume("h2", vec![neq_lit("a", "b")]),
            step(
                "t1",
                vec![neq_lit("a", "b"), neq_lit("b", "c"), eq_lit("a", "c")],
                "eq_transitive",
                &[],
            ),
        ];
        let parsed = parse_alethe(&write_alethe(&commands)).unwrap();
        assert_eq!(parsed, commands);
    }

    /// An applied indexed bit-extraction `((_ @bit_of i) x)`.
    fn bit_of(i: i128, x: &str) -> AletheTerm {
        AletheTerm::Indexed {
            op: "@bit_of".to_owned(),
            indices: vec![i],
            args: vec![AletheTerm::Const(x.to_owned())],
        }
    }

    #[test]
    fn indexed_bitblast_step_round_trips() {
        // A `bitblast_var`-shaped step: `(= x (@bbterm ((_ @bit_of 0) x) ((_ @bit_of 1) x)))`.
        let bbterm = AletheTerm::App("@bbterm".to_owned(), vec![bit_of(0, "x"), bit_of(1, "x")]);
        let conclusion = AletheLit {
            atom: AletheTerm::App(
                "=".to_owned(),
                vec![AletheTerm::Const("x".to_owned()), bbterm],
            ),
            negated: false,
        };
        let commands = vec![step("s", vec![conclusion], "bitblast_var", &[])];
        let reparsed = parse_alethe(&write_alethe(&commands)).expect("indexed step round-trips");
        assert_eq!(reparsed, commands);
    }

    #[test]
    fn indexed_write_exact_strings() {
        // Applied form renders `((_ @bit_of 0) x)`.
        let applied = AletheCommand::Assume {
            id: "h".to_owned(),
            clause: vec![AletheLit {
                atom: bit_of(0, "x"),
                negated: false,
            }],
        };
        assert_eq!(write_alethe(&[applied]), "(assume h ((_ @bit_of 0) x))\n");

        // Bare indexed identifier renders `(_ @bit_of 1)`.
        let bare = AletheCommand::Assume {
            id: "h".to_owned(),
            clause: vec![AletheLit {
                atom: AletheTerm::Indexed {
                    op: "@bit_of".to_owned(),
                    indices: vec![1],
                    args: vec![],
                },
                negated: false,
            }],
        };
        assert_eq!(write_alethe(&[bare]), "(assume h (_ @bit_of 1))\n");
    }

    #[test]
    fn indexed_key_distinctness() {
        // Different index ⇒ different key.
        assert_ne!(bit_of(0, "x").key(), bit_of(1, "x").key());
        // Structurally-equal indexed terms share a key.
        assert_eq!(bit_of(0, "x").key(), bit_of(0, "x").key());
        // The applied form key is exactly the canonical s-expression.
        assert_eq!(bit_of(0, "x").key(), "((_ @bit_of 0) x)");
    }

    #[test]
    fn indexed_parse_from_text() {
        // A bare indexed identifier `(_ @bit_of 1)`.
        let bare = parse_alethe("(assume h (_ @bit_of 1))").expect("bare indexed parses");
        let AletheCommand::Assume { clause, .. } = &bare[0] else {
            panic!("expected assume");
        };
        assert_eq!(
            clause[0].atom,
            AletheTerm::Indexed {
                op: "@bit_of".to_owned(),
                indices: vec![1],
                args: vec![],
            }
        );

        // An applied indexed operator `((_ @bit_of 0) x)`.
        let applied = parse_alethe("(assume h ((_ @bit_of 0) x))").expect("applied indexed parses");
        let AletheCommand::Assume { clause, .. } = &applied[0] else {
            panic!("expected assume");
        };
        assert_eq!(clause[0].atom, bit_of(0, "x"));

        // A `(_ …)` with no indices is a parse error.
        assert!(matches!(
            parse_alethe("(assume h (_ @bit_of))"),
            Err(AletheError::Parse(_))
        ));
        // A non-integer index is a parse error.
        assert!(matches!(
            parse_alethe("(assume h (_ @bit_of foo))"),
            Err(AletheError::Parse(_))
        ));
    }
}
