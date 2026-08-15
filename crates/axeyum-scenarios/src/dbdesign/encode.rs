//! The same questions, handed to the **solver** instead of to a combinatorial
//! routine.
//!
//! Everything else in [`super`] decides database-design questions with
//! special-purpose algorithms: attribute closure, the tableau chase,
//! backtracking search for a homomorphism. This module encodes two of those
//! questions as Boolean [`axeyum_ir`] terms so the solver decides them by a
//! completely different route — parse, rewrite, bit-blast, CNF, SAT — and the
//! two answers can be compared.
//!
//! That is worth more than a second opinion, because of *what the solver
//! returns when it says `sat`*:
//!
//! * **Functional-dependency implication.** `F ⊨ X → Y` fails exactly when the
//!   Horn theory `{⋀L → ⋀R : L → R ∈ F} ∪ X ∪ {¬y}` is satisfiable. Any model
//!   of it — not just the least one — is an **agreement set**: the two-row
//!   relation that agrees exactly on the true attributes satisfies `F` and
//!   violates `X → Y`. So the solver's model *is* the counterexample
//!   database, and [`super::armstrong::witness_from_agreement`] hands it
//!   straight to the same checker every other witness goes through.
//! * **Conjunctive-query containment.** A homomorphism is a total function
//!   from the source query's variables into the target's active domain, which
//!   is a one-hot Boolean encoding with one clause per body atom. A `sat`
//!   model decodes to a map that [`super::cq::check_homomorphism`] replays.
//!
//! In both cases the solver is *untrusted*: it proposes, and a checker that
//! shares no code with it disposes. An `unsat` from the solver is not taken as
//! the last word either — it is cross-checked against the closure algorithm
//! (which then produces an Armstrong derivation) or against the complete
//! evaluator (which then produces a counterexample database).

use axeyum_ir::{IrError, SymbolId, TermArena, TermId};

use super::cq::{Cq, FrozenQuery, Homomorphism, Term};
use super::{AttrSet, Schema};

/// A Boolean encoding of "`F` does **not** imply `X → Y`".
#[derive(Debug, Clone)]
pub struct FdImplicationQuery {
    /// The assertions to hand the solver. `sat` means the implication fails.
    pub assertions: Vec<TermId>,
    /// One Boolean symbol per attribute, in attribute-index order, so a model
    /// can be read back as an [`AttrSet`].
    pub attribute_symbols: Vec<SymbolId>,
}

/// Encode "`F` does not imply `X → Y`" over a fresh set of Boolean symbols.
///
/// The symbols are named `<prefix><attribute>` so several encodings can share
/// one arena without colliding.
///
/// # Errors
///
/// Propagates [`IrError`] from term construction — in practice only a repeated
/// symbol name, which a distinct `prefix` avoids.
pub fn fd_implication_query(
    arena: &mut TermArena,
    schema: &Schema,
    x: AttrSet,
    y: AttrSet,
    prefix: &str,
) -> Result<FdImplicationQuery, IrError> {
    let mut attribute_symbols = Vec::with_capacity(schema.arity());
    let mut vars = Vec::with_capacity(schema.arity());
    for name in schema.attributes() {
        let symbol = arena.declare(&format!("{prefix}{name}"), axeyum_ir::Sort::Bool)?;
        attribute_symbols.push(symbol);
        vars.push(arena.var(symbol));
    }

    let mut assertions = Vec::new();
    // The Horn body of the theory: one implication per dependency.
    for fd in schema.fds() {
        let antecedent = conjoin(arena, fd.lhs.iter().map(|index| vars[index]))?;
        let consequent = conjoin(arena, fd.rhs.iter().map(|index| vars[index]))?;
        assertions.push(arena.implies(antecedent, consequent)?);
    }
    // The determinant holds.
    for index in x.iter() {
        assertions.push(vars[index]);
    }
    // Some attribute of the dependent does not.
    let mut missing = arena.bool_const(false);
    for index in y.iter() {
        let negated = arena.not(vars[index])?;
        missing = arena.or(missing, negated)?;
    }
    assertions.push(missing);

    Ok(FdImplicationQuery {
        assertions,
        attribute_symbols,
    })
}

/// Read a solver model of [`fd_implication_query`] back as the agreement set
/// of a two-row relation.
///
/// `lookup` is whatever the caller's model type offers — this crate does not
/// depend on the solver, and does not need to: it only needs to be told, per
/// symbol, whether the model made it true. An attribute the model leaves
/// unassigned is read as `false`, which only shrinks the agreement set and is
/// checked downstream regardless.
pub fn agreement_from_model(
    query: &FdImplicationQuery,
    lookup: impl Fn(SymbolId) -> Option<bool>,
) -> AttrSet {
    AttrSet::from_indices(
        query
            .attribute_symbols
            .iter()
            .enumerate()
            .filter(|&(_, &symbol)| lookup(symbol) == Some(true))
            .map(|(index, _)| index),
    )
}

/// A Boolean encoding of "there is a homomorphism from `source` into
/// `target`".
#[derive(Debug, Clone)]
pub struct HomomorphismQuery {
    /// The assertions. `sat` means a homomorphism exists, which by
    /// Chandra–Merlin means the containment holds.
    pub assertions: Vec<TermId>,
    /// `cells[v][e]` is the symbol for "variable `v` maps to element `e`".
    pub cells: Vec<Vec<SymbolId>>,
}

/// Encode homomorphism existence as a one-hot Boolean query.
///
/// Three groups of assertions:
///
/// 1. **totality** — every variable maps somewhere;
/// 2. **functionality** — no variable maps to two elements, so a model decodes
///    to an actual function rather than a relation;
/// 3. **atoms and head** — for each body atom, a disjunction over the target's
///    facts of that predicate, each disjunct pinning every argument; and for
///    the head, the pinning is asserted outright.
///
/// A source atom whose predicate has no matching fact yields the empty
/// disjunction, i.e. `false`, which is the correct — and immediately
/// `unsat` — encoding.
///
/// # Errors
///
/// Propagates [`IrError`] from term construction.
pub fn homomorphism_query(
    arena: &mut TermArena,
    source: &Cq,
    target: &FrozenQuery,
    prefix: &str,
) -> Result<HomomorphismQuery, IrError> {
    let mut cells: Vec<Vec<SymbolId>> = Vec::with_capacity(source.variables.len());
    let mut vars: Vec<Vec<TermId>> = Vec::with_capacity(source.variables.len());
    for variable in 0..source.variables.len() {
        let mut row_symbols = Vec::with_capacity(target.domain);
        let mut row_vars = Vec::with_capacity(target.domain);
        for element in 0..target.domain {
            let symbol = arena.declare(
                &format!("{prefix}h_{variable}_{element}"),
                axeyum_ir::Sort::Bool,
            )?;
            row_symbols.push(symbol);
            row_vars.push(arena.var(symbol));
        }
        cells.push(row_symbols);
        vars.push(row_vars);
    }

    let mut assertions = Vec::new();
    for row in &vars {
        let mut somewhere = arena.bool_const(false);
        for &cell in row {
            somewhere = arena.or(somewhere, cell)?;
        }
        assertions.push(somewhere);
        for (i, &left) in row.iter().enumerate() {
            for &right in row.iter().skip(i + 1) {
                let both = arena.and(left, right)?;
                assertions.push(arena.not(both)?);
            }
        }
    }

    // `pin` says "this source term takes this target element".
    let pin = |arena: &mut TermArena, term: Term, element: usize| -> Result<TermId, IrError> {
        Ok(match term {
            Term::Const(constant) => arena.bool_const(constant == element),
            Term::Var(variable) => vars[variable][element],
        })
    };

    for atom in &source.body {
        let mut matched = arena.bool_const(false);
        for (predicate, args) in &target.facts {
            if *predicate != atom.predicate || args.len() != atom.args.len() {
                continue;
            }
            let mut conjunct = arena.bool_const(true);
            for (term, &element) in atom.args.iter().copied().zip(args.iter()) {
                let pinned = pin(arena, term, element)?;
                conjunct = arena.and(conjunct, pinned)?;
            }
            matched = arena.or(matched, conjunct)?;
        }
        assertions.push(matched);
    }

    for (term, &element) in source.head.iter().copied().zip(target.head.iter()) {
        let pinned = pin(arena, term, element)?;
        assertions.push(pinned);
    }

    Ok(HomomorphismQuery { assertions, cells })
}

/// Decode a solver model of [`homomorphism_query`] into a [`Homomorphism`].
///
/// Returns `None` when the model leaves some variable unmapped, which the
/// totality clauses forbid but which is checked rather than assumed.
pub fn homomorphism_from_model(
    query: &HomomorphismQuery,
    lookup: impl Fn(SymbolId) -> Option<bool>,
) -> Option<Homomorphism> {
    let mut image = Vec::with_capacity(query.cells.len());
    for row in &query.cells {
        let chosen = row
            .iter()
            .position(|&symbol| lookup(symbol) == Some(true))?;
        image.push(chosen);
    }
    Some(Homomorphism { image })
}

fn conjoin(arena: &mut TermArena, terms: impl Iterator<Item = TermId>) -> Result<TermId, IrError> {
    let mut result = arena.bool_const(true);
    for term in terms {
        result = arena.and(result, term)?;
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::super::Fd;
    use super::*;
    use axeyum_ir::{Assignment, Value, eval};

    fn schema() -> Schema {
        let mut schema = Schema::new(
            ["A", "B", "C", "D"]
                .into_iter()
                .map(str::to_owned)
                .collect(),
        )
        .unwrap();
        for (name, lhs, rhs) in [
            ("f1", vec![0, 1], vec![2]),
            ("f2", vec![2], vec![3]),
            ("f3", vec![3], vec![0]),
        ] {
            schema
                .push_fd(Fd {
                    name: name.to_owned(),
                    lhs: AttrSet::from_indices(lhs),
                    rhs: AttrSet::from_indices(rhs),
                })
                .unwrap();
        }
        schema
    }

    /// Evaluate the encoding under an explicit assignment, with no solver in
    /// the picture: the encoding's meaning is checked by the IR evaluator.
    fn holds_under(schema: &Schema, x: AttrSet, y: AttrSet, truthy: AttrSet) -> bool {
        let mut arena = TermArena::new();
        let query = fd_implication_query(&mut arena, schema, x, y, "t_").unwrap();
        let mut assignment = Assignment::new();
        for (index, &symbol) in query.attribute_symbols.iter().enumerate() {
            assignment.set(symbol, Value::Bool(truthy.contains(index)));
        }
        query
            .assertions
            .iter()
            .all(|&term| matches!(eval(&arena, term, &assignment), Ok(Value::Bool(true))))
    }

    #[test]
    fn the_closure_is_a_model_when_the_dependency_fails() {
        let schema = schema();
        let x = AttrSet::from_indices([2]); // C
        let y = AttrSet::from_indices([1]); // B
        // C+ = {A, C, D} is a model; the full set is not (B would be true).
        assert!(holds_under(&schema, x, y, schema.closure(x)));
        assert!(!holds_under(&schema, x, y, AttrSet::full(4)));
    }

    #[test]
    fn nothing_models_an_implied_dependency() {
        let schema = schema();
        let x = AttrSet::from_indices([0, 1]); // A B
        let y = AttrSet::from_indices([3]); // D, which A B does determine
        for bits in 0u64..16 {
            let truthy = AttrSet::from_indices((0..4).filter(|i| (bits >> i) & 1 == 1));
            assert!(
                !holds_under(&schema, x, y, truthy),
                "assignment {bits:04b} should not satisfy an unsatisfiable encoding"
            );
        }
    }

    #[test]
    fn agreement_is_read_back_from_a_model() {
        let schema = schema();
        let mut arena = TermArena::new();
        let query = fd_implication_query(
            &mut arena,
            &schema,
            AttrSet::from_indices([2]),
            AttrSet::from_indices([1]),
            "r_",
        )
        .unwrap();
        let true_symbols: Vec<SymbolId> = query
            .attribute_symbols
            .iter()
            .enumerate()
            .filter(|(index, _)| *index != 1)
            .map(|(_, &symbol)| symbol)
            .collect();
        assert_eq!(
            agreement_from_model(&query, |symbol| Some(true_symbols.contains(&symbol))),
            AttrSet::from_indices([0, 2, 3])
        );
    }

    #[test]
    fn homomorphism_encoding_matches_the_direct_search() {
        use super::super::cq::{Atom, CqProgram, find_homomorphism, freeze};
        let program = CqProgram {
            predicates: vec!["R".to_owned()],
            arities: vec![2],
            constants: Vec::new(),
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
        };
        let q1 = program.query("Q1").unwrap();
        let q2 = program.query("Q2").unwrap();
        let frozen = freeze(&program, q1).unwrap();
        let found = find_homomorphism(q2, &frozen).unwrap().unwrap();

        // The map the direct search found satisfies every assertion of the
        // encoding, under the IR evaluator.
        let mut arena = TermArena::new();
        let query = homomorphism_query(&mut arena, q2, &frozen, "hq_").unwrap();
        let mut assignment = Assignment::new();
        for (variable, row) in query.cells.iter().enumerate() {
            for (element, &symbol) in row.iter().enumerate() {
                assignment.set(symbol, Value::Bool(found.image[variable] == element));
            }
        }
        assert!(
            query
                .assertions
                .iter()
                .all(|&term| matches!(eval(&arena, term, &assignment), Ok(Value::Bool(true))))
        );

        // And the decoder inverts the encoder.
        let true_cells: Vec<SymbolId> = query
            .cells
            .iter()
            .enumerate()
            .map(|(variable, row)| row[found.image[variable]])
            .collect();
        assert_eq!(
            homomorphism_from_model(&query, |symbol| Some(true_cells.contains(&symbol))),
            Some(found)
        );
    }
}
