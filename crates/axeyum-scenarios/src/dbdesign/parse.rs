//! The committed instance format: a schema, its decompositions, its queries,
//! and — deliberately — **the answers it expects**.
//!
//! The expectations live in the instance file rather than on a command line
//! for one reason: a checker that reports whatever it found pins nothing. A
//! run of `db_design_certify` over a file with no `expect` line is refused,
//! not passed, because a tool that exits `0` on completion alone is
//! indistinguishable from one that never ran the check. That failure mode is
//! not hypothetical in this repository, which is why it is designed out here.
//!
//! ```text
//! # comments run to end of line
//! attributes street city zip
//! fd  addr    : street city -> zip
//! fd  zipcity : zip -> city
//! decomposition bcnf : (zip city) (zip street)
//!
//! expect implies       : street city -> city
//! expect notimplies    : zip -> street
//! expect keys          : (street city) (street zip)
//! expect bcnf          : no
//! expect 3nf           : yes
//! expect lossless      : bcnf
//! expect notpreserving : bcnf
//! ```
//!
//! Conjunctive queries use the same file, in Prolog-ish surface syntax. A
//! lowercase-initial argument is a variable; anything else is a constant, so
//! `R(x, Bob)` has one of each.
//!
//! ```text
//! query Q1(x)  :- R(x, y), R(y, z)
//! query Q2(x)  :- R(x, w)
//! expect subset    : Q1 Q2
//! expect notsubset : Q2 Q1
//! ```

use super::cq::{Atom, Cq, CqProgram, Term};
use super::{AttrSet, DbDesignError, Fd, Schema};

/// A named decomposition of the schema into fragments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decomposition {
    /// The label, referenced by `expect lossless` and friends.
    pub name: String,
    /// The fragments, in declaration order — which fixes the chase tableau's
    /// row order and so makes a trace reproducible.
    pub fragments: Vec<AttrSet>,
}

/// One pinned answer the instance asserts about itself.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expectation {
    /// `F ⊨ lhs → rhs`, to be backed by an Armstrong derivation.
    Implies {
        /// Determinant.
        lhs: AttrSet,
        /// Dependent.
        rhs: AttrSet,
    },
    /// `F ⊭ lhs → rhs`, to be backed by a two-row counterexample relation.
    NotImplies {
        /// Determinant.
        lhs: AttrSet,
        /// Dependent.
        rhs: AttrSet,
    },
    /// The candidate keys are exactly these, to be backed by the exhaustive
    /// subset sweep.
    Keys(Vec<AttrSet>),
    /// Whether the schema is in BCNF.
    Bcnf(bool),
    /// Whether the schema is in 3NF.
    ThirdNf(bool),
    /// The named decomposition has a lossless join.
    Lossless(String),
    /// The named decomposition loses information.
    Lossy(String),
    /// The named decomposition preserves every dependency.
    Preserving(String),
    /// The named decomposition loses a dependency.
    NotPreserving(String),
    /// `left ⊆ right` as conjunctive queries.
    Subset {
        /// The contained query.
        left: String,
        /// The containing query.
        right: String,
    },
    /// `left ⊄ right`.
    NotSubset {
        /// The query that is not contained.
        left: String,
        /// The query that does not contain it.
        right: String,
    },
}

impl Expectation {
    /// A short label for reporting, e.g. `implies` or `notpreserving`.
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Implies { .. } => "implies",
            Self::NotImplies { .. } => "notimplies",
            Self::Keys(_) => "keys",
            Self::Bcnf(_) => "bcnf",
            Self::ThirdNf(_) => "3nf",
            Self::Lossless(_) => "lossless",
            Self::Lossy(_) => "lossy",
            Self::Preserving(_) => "preserving",
            Self::NotPreserving(_) => "notpreserving",
            Self::Subset { .. } => "subset",
            Self::NotSubset { .. } => "notsubset",
        }
    }
}

/// A parsed instance file.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Instance {
    /// The relation schema and its dependency set.
    pub schema: Schema,
    /// Named decompositions.
    pub decompositions: Vec<Decomposition>,
    /// The conjunctive queries, if any.
    pub program: CqProgram,
    /// The pinned answers.
    pub expectations: Vec<Expectation>,
}

impl Instance {
    /// Find a decomposition by label.
    pub fn decomposition(&self, name: &str) -> Option<&Decomposition> {
        self.decompositions
            .iter()
            .find(|candidate| candidate.name == name)
    }

    /// Parse an instance file.
    ///
    /// # Errors
    ///
    /// On any unknown directive, undeclared attribute, malformed dependency,
    /// duplicate label, or an `expect` naming something the file does not
    /// declare. Nothing is skipped silently: a line this parser does not
    /// understand is an error, because an ignored expectation is an
    /// expectation that never ran.
    #[allow(clippy::too_many_lines)]
    pub fn parse(text: &str) -> Result<Self, DbDesignError> {
        let mut instance = Self::default();
        let mut attributes_seen = false;

        for (number, raw) in text.lines().enumerate() {
            let line = raw.split('#').next().unwrap_or("").trim();
            if line.is_empty() {
                continue;
            }
            let at =
                |message: String| DbDesignError::new(format!("line {}: {message}", number + 1));
            let (directive, rest) = split_word(line);

            match directive {
                "attributes" => {
                    if attributes_seen {
                        return Err(at("`attributes` is declared twice".to_owned()));
                    }
                    attributes_seen = true;
                    let names: Vec<String> = rest
                        .split([' ', '\t', ','])
                        .filter(|token| !token.is_empty())
                        .map(str::to_owned)
                        .collect();
                    if names.is_empty() {
                        return Err(at("`attributes` needs at least one name".to_owned()));
                    }
                    instance.schema = Schema::new(names).map_err(|error| at(error.0))?;
                }
                "fd" => {
                    let (name, body) = split_label(rest)
                        .ok_or_else(|| at("expected `fd <label> : <lhs> -> <rhs>`".to_owned()))?;
                    let (lhs, rhs) = split_arrow(&instance.schema, body).map_err(|e| at(e.0))?;
                    instance
                        .schema
                        .push_fd(Fd {
                            name: name.to_owned(),
                            lhs,
                            rhs,
                        })
                        .map_err(|error| at(error.0))?;
                }
                "decomposition" => {
                    let (name, body) = split_label(rest).ok_or_else(|| {
                        at("expected `decomposition <label> : (…) (…)`".to_owned())
                    })?;
                    if instance.decomposition(name).is_some() {
                        return Err(at(format!("decomposition `{name}` is declared twice")));
                    }
                    let fragments = parse_groups(&instance.schema, body).map_err(|e| at(e.0))?;
                    instance.decompositions.push(Decomposition {
                        name: name.to_owned(),
                        fragments,
                    });
                }
                "query" => {
                    let query = parse_query(&mut instance.program, rest).map_err(|e| at(e.0))?;
                    if instance.program.query(&query.name).is_some() {
                        return Err(at(format!("query `{}` is declared twice", query.name)));
                    }
                    instance.program.queries.push(query);
                }
                "expect" => {
                    let (kind, body) = split_label(rest)
                        .ok_or_else(|| at("expected `expect <kind> : <argument>`".to_owned()))?;
                    let expectation =
                        parse_expectation(&instance, kind, body).map_err(|e| at(e.0))?;
                    instance.expectations.push(expectation);
                }
                other => {
                    return Err(at(format!(
                        "unknown directive `{other}`; a line this parser does not understand is \
                         an error, not a comment"
                    )));
                }
            }
        }

        if !attributes_seen && instance.program.queries.is_empty() {
            return Err(DbDesignError::new(
                "the instance declares neither attributes nor queries".to_owned(),
            ));
        }
        if instance.expectations.is_empty() {
            return Err(DbDesignError::new(
                "the instance pins no expectations, so a run of it would check nothing and still \
                 exit 0"
                    .to_owned(),
            ));
        }
        Ok(instance)
    }
}

fn split_word(line: &str) -> (&str, &str) {
    match line.find(char::is_whitespace) {
        Some(index) => (&line[..index], line[index..].trim_start()),
        None => (line, ""),
    }
}

/// `label : body` — the colon must come before any `(`, so a query head's
/// parentheses are never mistaken for a label separator.
fn split_label(text: &str) -> Option<(&str, &str)> {
    let index = text.find(':')?;
    let label = text[..index].trim();
    if label.is_empty() {
        return None;
    }
    Some((label, text[index + 1..].trim()))
}

fn split_arrow(schema: &Schema, body: &str) -> Result<(AttrSet, AttrSet), DbDesignError> {
    let index = body
        .find("->")
        .ok_or_else(|| DbDesignError::new("expected `<lhs> -> <rhs>`".to_owned()))?;
    let lhs = schema.parse_attrs(body[..index].trim())?;
    let rhs = schema.parse_attrs(body[index + 2..].trim())?;
    if rhs.is_empty() {
        return Err(DbDesignError::new(
            "the dependent side is empty, which says nothing".to_owned(),
        ));
    }
    Ok((lhs, rhs))
}

/// `(A B) (B C D)` into attribute sets.
fn parse_groups(schema: &Schema, body: &str) -> Result<Vec<AttrSet>, DbDesignError> {
    let mut groups = Vec::new();
    let mut rest = body.trim();
    while !rest.is_empty() {
        if !rest.starts_with('(') {
            return Err(DbDesignError::new(format!(
                "expected a parenthesised group, found `{rest}`"
            )));
        }
        let end = rest
            .find(')')
            .ok_or_else(|| DbDesignError::new("unclosed `(`".to_owned()))?;
        groups.push(schema.parse_attrs(&rest[1..end])?);
        rest = rest[end + 1..].trim();
    }
    if groups.is_empty() {
        return Err(DbDesignError::new(
            "expected at least one parenthesised group".to_owned(),
        ));
    }
    Ok(groups)
}

fn intern(table: &mut Vec<String>, name: &str) -> usize {
    if let Some(index) = table.iter().position(|known| known == name) {
        return index;
    }
    table.push(name.to_owned());
    table.len() - 1
}

/// `Name(t, …) :- P(a, b), Q(c)`.
fn parse_query(program: &mut CqProgram, text: &str) -> Result<Cq, DbDesignError> {
    let split = text
        .find(":-")
        .ok_or_else(|| DbDesignError::new("expected `<head> :- <body>`".to_owned()))?;
    let head_text = text[..split].trim();
    let body_text = text[split + 2..].trim();

    let open = head_text
        .find('(')
        .ok_or_else(|| DbDesignError::new("the head needs an argument list".to_owned()))?;
    let name = head_text[..open].trim().to_owned();
    if name.is_empty() {
        return Err(DbDesignError::new("the query has no name".to_owned()));
    }
    let close = head_text
        .rfind(')')
        .ok_or_else(|| DbDesignError::new("unclosed `(` in the head".to_owned()))?;
    let head_args: Vec<&str> = head_text[open + 1..close]
        .split(',')
        .map(str::trim)
        .filter(|token| !token.is_empty())
        .collect();

    // Body atoms first, so variables are numbered in body order and a head
    // variable that never occurs in the body is caught.
    let mut variables: Vec<String> = Vec::new();
    let mut body = Vec::new();
    let mut rest = body_text;
    while !rest.is_empty() {
        let open = rest
            .find('(')
            .ok_or_else(|| DbDesignError::new(format!("expected an atom, found `{rest}`")))?;
        let close = rest[open..]
            .find(')')
            .map(|offset| open + offset)
            .ok_or_else(|| DbDesignError::new("unclosed `(` in the body".to_owned()))?;
        let predicate_name = rest[..open].trim();
        if predicate_name.is_empty() {
            return Err(DbDesignError::new("an atom has no predicate".to_owned()));
        }
        let args: Vec<Term> = rest[open + 1..close]
            .split(',')
            .map(str::trim)
            .filter(|token| !token.is_empty())
            .map(|token| classify(program, &mut variables, token))
            .collect();
        let predicate = intern(&mut program.predicates, predicate_name);
        if program.arities.len() <= predicate {
            program.arities.resize(predicate + 1, args.len());
        } else if program.arities[predicate] != args.len() {
            return Err(DbDesignError::new(format!(
                "`{predicate_name}` is used at arity {} and at arity {}",
                program.arities[predicate],
                args.len()
            )));
        }
        body.push(Atom { predicate, args });
        rest = rest[close + 1..]
            .trim_start()
            .trim_start_matches(',')
            .trim();
    }
    if body.is_empty() {
        return Err(DbDesignError::new(
            "a conjunctive query needs at least one body atom".to_owned(),
        ));
    }

    let mut head = Vec::with_capacity(head_args.len());
    for token in head_args {
        let term = classify_head(program, &variables, token)?;
        head.push(term);
    }
    Ok(Cq {
        name,
        variables,
        head,
        body,
    })
}

fn is_variable(token: &str) -> bool {
    token
        .chars()
        .next()
        .is_some_and(|first| first.is_ascii_lowercase() || first == '_')
}

fn classify(program: &mut CqProgram, variables: &mut Vec<String>, token: &str) -> Term {
    if is_variable(token) {
        Term::Var(intern(variables, token))
    } else {
        Term::Const(intern(&mut program.constants, token))
    }
}

fn classify_head(
    program: &CqProgram,
    variables: &[String],
    token: &str,
) -> Result<Term, DbDesignError> {
    if is_variable(token) {
        variables
            .iter()
            .position(|known| known == token)
            .map(Term::Var)
            .ok_or_else(|| {
                DbDesignError::new(format!(
                    "head variable `{token}` does not occur in the body, so the query is unsafe"
                ))
            })
    } else {
        program
            .constants
            .iter()
            .position(|known| known == token)
            .map(Term::Const)
            .ok_or_else(|| {
                DbDesignError::new(format!(
                    "head constant `{token}` does not occur in the body"
                ))
            })
    }
}

fn parse_expectation(
    instance: &Instance,
    kind: &str,
    body: &str,
) -> Result<Expectation, DbDesignError> {
    let two_queries = |body: &str| -> Result<(String, String), DbDesignError> {
        let names: Vec<&str> = body.split_whitespace().collect();
        let [left, right] = names.as_slice() else {
            return Err(DbDesignError::new("expected two query names".to_owned()));
        };
        for name in [left, right] {
            if instance.program.query(name).is_none() {
                return Err(DbDesignError::new(format!("no query named `{name}`")));
            }
        }
        Ok(((*left).to_owned(), (*right).to_owned()))
    };
    let decomposition = |body: &str| -> Result<String, DbDesignError> {
        let name = body.trim();
        if instance.decomposition(name).is_none() {
            return Err(DbDesignError::new(format!(
                "no decomposition named `{name}`"
            )));
        }
        Ok(name.to_owned())
    };
    let yes_no = |body: &str| -> Result<bool, DbDesignError> {
        match body.trim() {
            "yes" => Ok(true),
            "no" => Ok(false),
            other => Err(DbDesignError::new(format!(
                "expected `yes` or `no`, found `{other}`"
            ))),
        }
    };

    Ok(match kind {
        "implies" => {
            let (lhs, rhs) = split_arrow(&instance.schema, body)?;
            Expectation::Implies { lhs, rhs }
        }
        "notimplies" => {
            let (lhs, rhs) = split_arrow(&instance.schema, body)?;
            Expectation::NotImplies { lhs, rhs }
        }
        "keys" => Expectation::Keys(parse_groups(&instance.schema, body)?),
        "bcnf" => Expectation::Bcnf(yes_no(body)?),
        "3nf" => Expectation::ThirdNf(yes_no(body)?),
        "lossless" => Expectation::Lossless(decomposition(body)?),
        "lossy" => Expectation::Lossy(decomposition(body)?),
        "preserving" => Expectation::Preserving(decomposition(body)?),
        "notpreserving" => Expectation::NotPreserving(decomposition(body)?),
        "subset" => {
            let (left, right) = two_queries(body)?;
            Expectation::Subset { left, right }
        }
        "notsubset" => {
            let (left, right) = two_queries(body)?;
            Expectation::NotSubset { left, right }
        }
        other => {
            return Err(DbDesignError::new(format!(
                "unknown expectation kind `{other}`"
            )));
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const ZIP: &str = "\
# the textbook street/city/zip schema
attributes street city zip
fd  addr    : street city -> zip
fd  zipcity : zip -> city
decomposition bcnf : (zip city) (zip street)
expect implies       : street city -> city
expect notimplies    : zip -> street
expect keys          : (street city) (street zip)
expect bcnf          : no
expect 3nf           : yes
expect lossless      : bcnf
expect notpreserving : bcnf
";

    #[test]
    fn the_zip_instance_parses() {
        let instance = Instance::parse(ZIP).unwrap();
        assert_eq!(instance.schema.arity(), 3);
        assert_eq!(instance.schema.fds().len(), 2);
        assert_eq!(instance.decompositions.len(), 1);
        assert_eq!(instance.expectations.len(), 7);
        assert_eq!(instance.expectations[0].kind(), "implies");
        assert_eq!(instance.decomposition("bcnf").unwrap().fragments.len(), 2);
    }

    #[test]
    fn queries_parse_with_variables_and_constants() {
        let text = "\
query Q1(x) :- R(x, y), R(y, z)
query Q2(x) :- R(x, w)
query Q3(x) :- R(x, Bob)
expect subset    : Q1 Q2
expect notsubset : Q2 Q1
";
        let instance = Instance::parse(text).unwrap();
        assert_eq!(instance.program.queries.len(), 3);
        assert_eq!(instance.program.arities, vec![2]);
        assert_eq!(instance.program.constants, vec!["Bob".to_owned()]);
        let q3 = instance.program.query("Q3").unwrap();
        assert_eq!(q3.body[0].args, vec![Term::Var(0), Term::Const(0)]);
    }

    #[test]
    fn an_instance_that_pins_nothing_is_refused() {
        let text = "attributes A B\nfd f : A -> B\n";
        let error = Instance::parse(text).unwrap_err();
        assert!(error.message().contains("pins no expectations"));
    }

    #[test]
    fn unknown_directives_and_kinds_are_errors() {
        assert!(Instance::parse("attributes A\nwibble x\nexpect bcnf : yes\n").is_err());
        assert!(Instance::parse("attributes A\nexpect wibble : yes\n").is_err());
        assert!(Instance::parse("attributes A\nexpect lossless : nope\n").is_err());
        assert!(Instance::parse("attributes A B\nfd f : A -> Z\nexpect bcnf : yes\n").is_err());
        assert!(Instance::parse("attributes A B\nexpect bcnf : maybe\n").is_err());
    }

    #[test]
    fn unsafe_queries_are_refused() {
        let text = "query Q(nowhere) :- R(x, y)\nexpect subset : Q Q\n";
        assert!(Instance::parse(text).is_err());
        let arity_clash = "query Q(x) :- R(x, y), R(x)\nexpect subset : Q Q\n";
        assert!(Instance::parse(arity_clash).is_err());
    }
}
