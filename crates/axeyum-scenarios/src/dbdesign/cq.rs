//! Conjunctive query containment by the Chandra–Merlin homomorphism theorem.
//!
//! `Q₁ ⊆ Q₂` — every database gives `Q₁` a subset of the answers it gives
//! `Q₂` — is the question behind view reuse, query rewriting, redundant-join
//! elimination and answering queries using views. It is NP-complete, and
//! Chandra and Merlin (1977) reduced it to something a first-year student can
//! check:
//!
//! > `Q₁ ⊆ Q₂` if and only if there is a **homomorphism** from `Q₂` to the
//! > *frozen* body of `Q₁` mapping `Q₂`'s head to `Q₁`'s frozen head.
//!
//! Freezing turns each variable of `Q₁` into a fresh constant, so its body
//! becomes a finite database `D` and its head becomes one tuple of `D`'s
//! constants. The theorem is the sharpest example in this repository of the
//! project's own identity sentence: **finding** the map is the NP-complete
//! half, and **checking** it is a nested loop over `Q₂`'s atoms
//! ([`check_homomorphism`]).
//!
//! Non-containment gets a certificate too, and a more useful one: the frozen
//! database `D` *is itself* the counterexample. `Q₁` returns the frozen head
//! on `D` by construction — the identity map is a match — and
//! [`evaluate`] shows by exhaustive enumeration that `Q₂` does not. A designer
//! told "no, that view does not subsume your query" gets back a two-row
//! database on which the two queries disagree.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use super::DbDesignError;

/// A term in a query: a variable of the query, or a constant of the program.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    /// Index into the owning [`Cq`]'s variable list.
    Var(usize),
    /// Index into the owning [`CqProgram`]'s constant list.
    Const(usize),
}

/// A body atom `P(t₁, …, t_k)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Atom {
    /// Index into the owning [`CqProgram`]'s predicate list.
    pub predicate: usize,
    /// The arguments, in order.
    pub args: Vec<Term>,
}

/// One conjunctive query `Q(head) :- body`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Cq {
    /// The query's name, used by expectations and diagnostics.
    pub name: String,
    /// The variable names, in first-occurrence order.
    pub variables: Vec<String>,
    /// The distinguished (head) terms.
    pub head: Vec<Term>,
    /// The body atoms.
    pub body: Vec<Atom>,
}

/// A set of conjunctive queries sharing a vocabulary.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CqProgram {
    /// Predicate names, in first-occurrence order.
    pub predicates: Vec<String>,
    /// Declared arity per predicate.
    pub arities: Vec<usize>,
    /// Constant names, in first-occurrence order.
    pub constants: Vec<String>,
    /// The queries.
    pub queries: Vec<Cq>,
}

impl CqProgram {
    /// Look a query up by name.
    pub fn query(&self, name: &str) -> Option<&Cq> {
        self.queries.iter().find(|query| query.name == name)
    }
}

/// The **frozen** form of a query: its body read as a finite database.
///
/// Elements `0 .. constants.len()` are the program's constants and keep their
/// identity, so a constant in one query matches the same constant in another.
/// Elements above that are the frozen variables of this query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrozenQuery {
    /// The facts, as `(predicate, arguments)`, deduplicated and ordered.
    pub facts: BTreeSet<(usize, Vec<usize>)>,
    /// The frozen head tuple.
    pub head: Vec<usize>,
    /// How many elements the active domain has.
    pub domain: usize,
    /// A printable name per element, for diagnostics.
    pub element_names: Vec<String>,
}

/// Freeze a query: replace each variable by a fresh constant.
///
/// # Errors
///
/// If an atom's arity disagrees with its predicate's declared arity.
pub fn freeze(program: &CqProgram, query: &Cq) -> Result<FrozenQuery, DbDesignError> {
    let base = program.constants.len();
    let element = |term: Term| -> usize {
        match term {
            Term::Const(index) => index,
            Term::Var(index) => base + index,
        }
    };
    let mut facts = BTreeSet::new();
    for atom in &query.body {
        let declared = program.arities.get(atom.predicate).copied().unwrap_or(0);
        if atom.args.len() != declared {
            return Err(DbDesignError::new(format!(
                "`{}` uses `{}` at arity {} but it is declared at arity {declared}",
                query.name,
                program
                    .predicates
                    .get(atom.predicate)
                    .map_or("?", String::as_str),
                atom.args.len()
            )));
        }
        facts.insert((
            atom.predicate,
            atom.args.iter().copied().map(element).collect::<Vec<_>>(),
        ));
    }
    let mut element_names: Vec<String> = program.constants.clone();
    for name in &query.variables {
        element_names.push(format!("{}#{name}", query.name));
    }
    Ok(FrozenQuery {
        facts,
        head: query.head.iter().copied().map(element).collect(),
        domain: base + query.variables.len(),
        element_names,
    })
}

/// A homomorphism from a query's variables into a frozen database's domain.
///
/// Position `i` is the element assigned to variable `i`. Constants are not
/// mapped: a homomorphism of conjunctive queries fixes constants, which is
/// what makes `Q(x) :- R(x, Bob)` and `Q(x) :- R(x, Alice)` incomparable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Homomorphism {
    /// Element assigned to each variable of the source query.
    pub image: Vec<usize>,
}

fn apply(term: Term, image: &[usize]) -> Option<usize> {
    match term {
        Term::Const(index) => Some(index),
        Term::Var(index) => image.get(index).copied(),
    }
}

/// **The checker.** Confirm a map really is a containment-witnessing
/// homomorphism from `source` into `target`.
///
/// Two obligations, both decided by lookup:
///
/// 1. every body atom of `source`, with the map applied, is a fact of
///    `target`;
/// 2. the head of `source`, with the map applied, is the head tuple of
///    `target`.
///
/// That is the entire trusted surface of the containment direction. It does
/// not search, does not backtrack, and does not know the Chandra–Merlin
/// theorem — it just applies a function and looks things up.
///
/// # Errors
///
/// If the map is the wrong size, sends an element outside the domain, misses
/// an atom, or gets the head wrong.
pub fn check_homomorphism(
    source: &Cq,
    target: &FrozenQuery,
    hom: &Homomorphism,
) -> Result<(), DbDesignError> {
    if hom.image.len() != source.variables.len() {
        return Err(DbDesignError::new(format!(
            "the map assigns {} elements but `{}` has {} variables",
            hom.image.len(),
            source.name,
            source.variables.len()
        )));
    }
    if let Some(bad) = hom.image.iter().find(|&&element| element >= target.domain) {
        return Err(DbDesignError::new(format!(
            "the map sends a variable to element {bad}, which is outside the target domain of {}",
            target.domain
        )));
    }
    for atom in &source.body {
        let image: Option<Vec<usize>> = atom
            .args
            .iter()
            .copied()
            .map(|term| apply(term, &hom.image))
            .collect();
        let image = image.ok_or_else(|| {
            DbDesignError::new(format!("`{}` has an unmapped variable", source.name))
        })?;
        if !target.facts.contains(&(atom.predicate, image)) {
            return Err(DbDesignError::new(format!(
                "the image of an atom of `{}` is not a fact of the target database",
                source.name
            )));
        }
    }
    let head: Option<Vec<usize>> = source
        .head
        .iter()
        .copied()
        .map(|term| apply(term, &hom.image))
        .collect();
    let head =
        head.ok_or_else(|| DbDesignError::new("the head has an unmapped variable".to_owned()))?;
    if head != target.head {
        return Err(DbDesignError::new(format!(
            "the image of `{}`'s head is not the target's frozen head tuple",
            source.name
        )));
    }
    Ok(())
}

/// The largest search space [`find_homomorphism`] and [`evaluate`] will
/// enumerate, as `domain^variables`.
///
/// Exceeding it is an **error**, never a silent `no`: an unsearched space and
/// an exhausted one are the same output otherwise, and the whole value of the
/// negative certificate is that the space really was exhausted.
pub const MAX_SEARCH_SPACE: u64 = 50_000_000;

fn search_space(domain: usize, variables: usize) -> Option<u64> {
    let domain = u64::try_from(domain).ok()?;
    let mut total: u64 = 1;
    for _ in 0..variables {
        total = total.checked_mul(domain)?;
        if total > MAX_SEARCH_SPACE {
            return None;
        }
    }
    Some(total)
}

/// **The finder.** Search for a homomorphism from `source` into `target`.
///
/// A plain backtracking search over the variables in declaration order. It is
/// the untrusted half: whatever it returns is handed to
/// [`check_homomorphism`] before anyone sees it, and when it returns `None` the
/// negative claim rests on [`evaluate`] rather than on this function's word.
///
/// # Errors
///
/// If the search space exceeds [`MAX_SEARCH_SPACE`], or a produced map fails
/// its own checker.
pub fn find_homomorphism(
    source: &Cq,
    target: &FrozenQuery,
) -> Result<Option<Homomorphism>, DbDesignError> {
    if search_space(target.domain, source.variables.len()).is_none() {
        return Err(DbDesignError::new(format!(
            "the map space {}^{} exceeds the {MAX_SEARCH_SPACE} cap",
            target.domain,
            source.variables.len()
        )));
    }
    let mut image = vec![usize::MAX; source.variables.len()];
    if backtrack(source, target, &mut image, 0) {
        let hom = Homomorphism { image };
        check_homomorphism(source, target, &hom)?;
        return Ok(Some(hom));
    }
    Ok(None)
}

fn partial_ok(source: &Cq, target: &FrozenQuery, image: &[usize], assigned: usize) -> bool {
    // An atom all of whose variables are assigned must already be a fact.
    source.body.iter().all(|atom| {
        let ready = atom
            .args
            .iter()
            .all(|term| !matches!(term, Term::Var(index) if *index >= assigned));
        if !ready {
            return true;
        }
        let mapped: Vec<usize> = atom
            .args
            .iter()
            .map(|term| match term {
                Term::Const(index) => *index,
                Term::Var(index) => image[*index],
            })
            .collect();
        target.facts.contains(&(atom.predicate, mapped))
    })
}

fn backtrack(source: &Cq, target: &FrozenQuery, image: &mut [usize], next: usize) -> bool {
    if next == source.variables.len() {
        let head: Vec<usize> = source
            .head
            .iter()
            .map(|term| match term {
                Term::Const(index) => *index,
                Term::Var(index) => image[*index],
            })
            .collect();
        return head == target.head;
    }
    for element in 0..target.domain {
        image[next] = element;
        if partial_ok(source, target, image, next + 1) && backtrack(source, target, image, next + 1)
        {
            return true;
        }
    }
    image[next] = usize::MAX;
    false
}

/// **The complete evaluator.** All answer tuples of `query` over the database
/// `target`, by brute-force enumeration of every variable assignment.
///
/// This is the independent decision procedure for the *negative* direction.
/// It shares no code with [`find_homomorphism`]: no pruning, no ordering, no
/// early exit — every one of the `domain^variables` maps is tried. That is
/// what makes "the answer set does not contain the frozen head" a result
/// rather than a report about a search that gave up.
///
/// # Errors
///
/// If the enumeration would exceed [`MAX_SEARCH_SPACE`].
pub fn evaluate(query: &Cq, target: &FrozenQuery) -> Result<BTreeSet<Vec<usize>>, DbDesignError> {
    let variables = query.variables.len();
    let total = search_space(target.domain, variables).ok_or_else(|| {
        DbDesignError::new(format!(
            "evaluating `{}` would enumerate more than {MAX_SEARCH_SPACE} assignments",
            query.name
        ))
    })?;
    let domain = u64::try_from(target.domain).unwrap_or(0);
    let mut answers = BTreeSet::new();
    let mut image = vec![0usize; variables];
    for index in 0..total {
        let mut rest = index;
        for slot in &mut image {
            if domain == 0 {
                break;
            }
            *slot = usize::try_from(rest % domain).unwrap_or(0);
            rest /= domain;
        }
        let satisfied = query.body.iter().all(|atom| {
            let mapped: Vec<usize> = atom
                .args
                .iter()
                .map(|term| match term {
                    Term::Const(constant) => *constant,
                    Term::Var(variable) => image[*variable],
                })
                .collect();
            target.facts.contains(&(atom.predicate, mapped))
        });
        if satisfied {
            answers.insert(
                query
                    .head
                    .iter()
                    .map(|term| match term {
                        Term::Const(constant) => *constant,
                        Term::Var(variable) => image[*variable],
                    })
                    .collect(),
            );
        }
    }
    Ok(answers)
}

/// A decided containment question with its certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ContainmentVerdict {
    /// `Q₁ ⊆ Q₂`, witnessed by a homomorphism `Q₂ → freeze(Q₁)`.
    Contained {
        /// The frozen canonical database of `Q₁`.
        frozen: Box<FrozenQuery>,
        /// The map, already replayed by [`check_homomorphism`].
        homomorphism: Homomorphism,
    },
    /// `Q₁ ⊄ Q₂`, witnessed by `freeze(Q₁)` as a counterexample database.
    NotContained {
        /// The counterexample database: `Q₁` returns `frozen.head` on it and
        /// `Q₂` does not.
        frozen: Box<FrozenQuery>,
        /// How many assignments the complete evaluator tried before
        /// concluding. Recorded so an unsearched space cannot masquerade as an
        /// exhausted one.
        assignments_enumerated: u64,
    },
}

/// **Decide `left ⊆ right`, and certify the answer.**
///
/// Both branches are verified before returning: the positive one by replaying
/// the homomorphism, the negative one by exhaustively evaluating both queries
/// over the frozen database and confirming that `left` returns the frozen head
/// and `right` does not.
///
/// # Errors
///
/// If freezing fails, a search space is over the cap, or a certificate fails
/// its checker — including the sanity check that `left` really does return its
/// own frozen head, which must hold by construction and is verified anyway.
pub fn decide_containment(
    program: &CqProgram,
    left: &Cq,
    right: &Cq,
) -> Result<ContainmentVerdict, DbDesignError> {
    if left.head.len() != right.head.len() {
        return Err(DbDesignError::new(format!(
            "`{}` has arity {} and `{}` has arity {}; containment is not a question about them",
            left.name,
            left.head.len(),
            right.name,
            right.head.len()
        )));
    }
    let frozen = freeze(program, left)?;

    if let Some(homomorphism) = find_homomorphism(right, &frozen)? {
        check_homomorphism(right, &frozen, &homomorphism)?;
        return Ok(ContainmentVerdict::Contained {
            frozen: Box::new(frozen),
            homomorphism,
        });
    }

    // No homomorphism. The frozen database is then a counterexample, and that
    // is established by evaluating both queries over it rather than by
    // citing the theorem.
    let left_answers = evaluate(left, &frozen)?;
    if !left_answers.contains(&frozen.head) {
        return Err(DbDesignError::new(format!(
            "`{}` does not return its own frozen head; the freeze is wrong",
            left.name
        )));
    }
    let right_answers = evaluate(right, &frozen)?;
    if right_answers.contains(&frozen.head) {
        return Err(DbDesignError::new(format!(
            "no homomorphism was found, yet `{}` returns the frozen head on the canonical \
             database: the search and the evaluator disagree",
            right.name
        )));
    }
    let assignments_enumerated =
        search_space(frozen.domain, right.variables.len()).unwrap_or(u64::MAX);
    Ok(ContainmentVerdict::NotContained {
        frozen: Box::new(frozen),
        assignments_enumerated,
    })
}

/// Render a frozen database as a stable, human-readable listing — the form a
/// certificate is printed in.
pub fn render_frozen(program: &CqProgram, frozen: &FrozenQuery) -> String {
    let name = |element: usize| -> &str {
        frozen
            .element_names
            .get(element)
            .map_or("?", String::as_str)
    };
    let mut out = String::new();
    for (predicate, args) in &frozen.facts {
        let rendered: Vec<&str> = args.iter().copied().map(name).collect();
        let _ = writeln!(
            out,
            "  {}({})",
            program
                .predicates
                .get(*predicate)
                .map_or("?", String::as_str),
            rendered.join(", ")
        );
    }
    let head: Vec<&str> = frozen.head.iter().copied().map(name).collect();
    let _ = writeln!(out, "  head ({})", head.join(", "));
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `R` binary; `Q1(x) :- R(x,y), R(y,z)` and `Q2(x) :- R(x,w)`.
    fn program() -> CqProgram {
        CqProgram {
            predicates: vec!["R".to_owned()],
            arities: vec![2],
            constants: vec!["Bob".to_owned()],
            queries: vec![
                Cq {
                    name: "Q1".to_owned(),
                    variables: vec!["x".to_owned(), "y".to_owned(), "z".to_owned()],
                    head: vec![Term::Var(0)],
                    body: vec![
                        Atom {
                            predicate: 0,
                            args: vec![Term::Var(0), Term::Var(1)],
                        },
                        Atom {
                            predicate: 0,
                            args: vec![Term::Var(1), Term::Var(2)],
                        },
                    ],
                },
                Cq {
                    name: "Q2".to_owned(),
                    variables: vec!["x".to_owned(), "w".to_owned()],
                    head: vec![Term::Var(0)],
                    body: vec![Atom {
                        predicate: 0,
                        args: vec![Term::Var(0), Term::Var(1)],
                    }],
                },
            ],
        }
    }

    #[test]
    fn the_longer_path_is_contained_in_the_shorter() {
        let program = program();
        let q1 = program.query("Q1").unwrap();
        let q2 = program.query("Q2").unwrap();
        let verdict = decide_containment(&program, q1, q2).unwrap();
        let ContainmentVerdict::Contained {
            frozen,
            homomorphism,
        } = verdict
        else {
            panic!("Q1 subseteq Q2");
        };
        check_homomorphism(q2, &frozen, &homomorphism).unwrap();
        assert_eq!(homomorphism.image.len(), 2);
    }

    #[test]
    fn the_shorter_path_is_not_contained_in_the_longer() {
        let program = program();
        let q1 = program.query("Q1").unwrap();
        let q2 = program.query("Q2").unwrap();
        let verdict = decide_containment(&program, q2, q1).unwrap();
        let ContainmentVerdict::NotContained {
            frozen,
            assignments_enumerated,
        } = verdict
        else {
            panic!("Q2 is not contained in Q1: one edge does not make a path of two");
        };
        assert!(assignments_enumerated > 0);
        // The counterexample database really does separate them.
        assert!(evaluate(q2, &frozen).unwrap().contains(&frozen.head));
        assert!(!evaluate(q1, &frozen).unwrap().contains(&frozen.head));
        assert!(!render_frozen(&program, &frozen).is_empty());
    }

    #[test]
    fn a_tampered_homomorphism_is_rejected() {
        let program = program();
        let q1 = program.query("Q1").unwrap();
        let q2 = program.query("Q2").unwrap();
        let frozen = freeze(&program, q1).unwrap();
        let good = find_homomorphism(q2, &frozen).unwrap().unwrap();

        // Wrong length.
        let short = Homomorphism { image: vec![0] };
        assert!(check_homomorphism(q2, &frozen, &short).is_err());

        // Out of domain.
        let out = Homomorphism {
            image: vec![999, 0],
        };
        assert!(check_homomorphism(q2, &frozen, &out).is_err());

        // In domain but not a homomorphism: send the head variable to the
        // wrong element.
        let mut wrong = good.clone();
        wrong.image[0] = 0; // the constant `Bob`, which is not the frozen head
        assert!(check_homomorphism(q2, &frozen, &wrong).is_err());
    }

    #[test]
    fn constants_are_not_mapped() {
        // Q3(x) :- R(x, Bob) is not contained in Q4(x) :- R(x, Bob), R(Bob, x).
        let mut program = program();
        program.queries.push(Cq {
            name: "Q3".to_owned(),
            variables: vec!["x".to_owned()],
            head: vec![Term::Var(0)],
            body: vec![Atom {
                predicate: 0,
                args: vec![Term::Var(0), Term::Const(0)],
            }],
        });
        program.queries.push(Cq {
            name: "Q4".to_owned(),
            variables: vec!["x".to_owned()],
            head: vec![Term::Var(0)],
            body: vec![
                Atom {
                    predicate: 0,
                    args: vec![Term::Var(0), Term::Const(0)],
                },
                Atom {
                    predicate: 0,
                    args: vec![Term::Const(0), Term::Var(0)],
                },
            ],
        });
        let q3 = program.query("Q3").unwrap();
        let q4 = program.query("Q4").unwrap();
        assert!(matches!(
            decide_containment(&program, q4, q3).unwrap(),
            ContainmentVerdict::Contained { .. }
        ));
        assert!(matches!(
            decide_containment(&program, q3, q4).unwrap(),
            ContainmentVerdict::NotContained { .. }
        ));
    }

    #[test]
    fn arity_mismatch_is_not_a_containment_question() {
        let mut program = program();
        program.queries.push(Cq {
            name: "Qpair".to_owned(),
            variables: vec!["x".to_owned(), "y".to_owned()],
            head: vec![Term::Var(0), Term::Var(1)],
            body: vec![Atom {
                predicate: 0,
                args: vec![Term::Var(0), Term::Var(1)],
            }],
        });
        let q1 = program.query("Q1").unwrap();
        let pair = program.query("Qpair").unwrap();
        assert!(decide_containment(&program, q1, pair).is_err());
    }
}
