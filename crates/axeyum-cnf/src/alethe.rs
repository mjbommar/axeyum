//! A self-contained Alethe proof checker for the propositional resolution
//! layer (Track 3, phase P3.2).
//!
//! Alethe is the proof format produced by veriT and cvc5. This module checks
//! the **propositional resolution core**: a proof is a list of commands over
//! clauses, where each `resolution`/`th_resolution` step's conclusion must be a
//! logical consequence of its premises. The proof establishes UNSAT iff a
//! verified step derives the empty clause `(cl)`.
//!
//! This is a SOUNDNESS-CRITICAL checker: it accepts a step only when its
//! conclusion genuinely follows from its premises. The entailment test reuses
//! the pure-Rust SAT adapter [`crate::solve_with_rustsat_batsat`]: a step with
//! premises `C1..Cn` and conclusion `D` is valid iff `{C1, …, Cn, ¬D}` is
//! propositionally UNSAT (where `¬D` is the unit clauses negating each literal
//! of `D`). Because that test accepts `D` only when `D` truly follows, a checker
//! built on it can never bless an invalid step. When in doubt, it rejects.
//!
//! Atoms are uninterpreted: two atoms are equal iff their token text is
//! identical. Only `resolution` and `th_resolution` rules are supported in this
//! slice; any other rule is rejected with [`AletheError::UnsupportedRule`].

use std::collections::BTreeMap;

use crate::{CnfClause, CnfFormula, CnfLit, CnfVar};

/// A propositional literal: an atom token, optionally negated.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AletheLit {
    /// The atom's opaque identifier text. Atoms are equal iff this text is
    /// identical.
    pub atom: String,
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
        /// The rule name (only `resolution`/`th_resolution` are supported).
        rule: String,
        /// Identifiers of the premise commands.
        premises: Vec<String>,
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
    /// A step used a rule outside this resolution-only slice.
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
                write!(
                    f,
                    "unsupported Alethe rule `{rule}` (resolution layer only)"
                )
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
            // Tolerate (and ignore) other step annotations within the
            // resolution slice (e.g. `:args`); the rule itself gates acceptance.
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

/// Parses a single literal: `(not atom)` (negated) or a bare `atom` (positive).
fn parse_literal(sexp: &Sexp) -> Result<AletheLit, AletheError> {
    match sexp {
        Sexp::Atom(atom) => Ok(AletheLit {
            atom: atom.clone(),
            negated: false,
        }),
        Sexp::List(items) => {
            if items.len() == 2 && items[0].as_atom() == Some("not") {
                let atom = items[1].as_atom().ok_or_else(|| {
                    AletheError::Parse("`(not ...)` argument must be an atom".to_owned())
                })?;
                Ok(AletheLit {
                    atom: atom.to_owned(),
                    negated: true,
                })
            } else {
                Err(AletheError::Parse(
                    "literal must be an atom or `(not atom)`".to_owned(),
                ))
            }
        }
    }
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
        format!("(not {})", lit.atom)
    } else {
        lit.atom.clone()
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

                if rule == "resolution" || rule == "th_resolution" {
                    if !premises_entail(&premise_clauses, clause)? {
                        return Err(AletheError::StepNotEntailed { id: id.clone() });
                    }
                    if clause.is_empty() {
                        derived_empty = true;
                    }
                    clauses.insert(id.clone(), clause.clone());
                } else {
                    return Err(AletheError::UnsupportedRule { rule: rule.clone() });
                }
            }
        }
    }

    Ok(derived_empty)
}

/// Returns `true` iff `premises ⊨ conclusion`, decided as
/// `{premises..., ¬conclusion}`-UNSAT via the pure-Rust SAT adapter.
///
/// Sound by construction: it returns `true` only when adding the unit clauses
/// that negate every conclusion literal makes the premise set unsatisfiable —
/// i.e. the conclusion truly follows. A `Sat` (or `Unknown`) result yields
/// `false`, so the checker rejects rather than blessing an unverified step.
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

fn register_atom(var_of: &mut BTreeMap<String, CnfVar>, atom: &str) -> Result<(), AletheError> {
    if !var_of.contains_key(atom) {
        let index = var_of.len();
        let var = CnfVar::new(index).map_err(|error| AletheError::Parse(error.to_string()))?;
        var_of.insert(atom.to_owned(), var);
    }
    Ok(())
}

/// Maps an [`AletheLit`] to a [`CnfLit`] over the atom-variable map. The atom is
/// guaranteed present (every atom is registered before this is called).
fn cnf_lit(var_of: &BTreeMap<String, CnfVar>, lit: &AletheLit) -> CnfLit {
    let var = *var_of
        .get(&lit.atom)
        .expect("atom registered before literal lowering");
    let cnf = CnfLit::positive(var);
    if lit.negated { cnf.negated() } else { cnf }
}

#[cfg(test)]
mod tests {
    use super::{
        AletheClause, AletheCommand, AletheError, AletheLit, check_alethe, parse_alethe,
        write_alethe,
    };

    fn lit(atom: &str) -> AletheLit {
        AletheLit {
            atom: atom.to_owned(),
            negated: false,
        }
    }

    fn neg(atom: &str) -> AletheLit {
        AletheLit {
            atom: atom.to_owned(),
            negated: true,
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
        }
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
}
