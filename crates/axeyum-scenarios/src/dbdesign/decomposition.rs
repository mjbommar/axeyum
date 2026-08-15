//! Lossless join and dependency preservation, by the tableau **chase**.
//!
//! Splitting a relation is the whole activity of schema design, and it can go
//! wrong in two independent ways. The decomposition can *lose information* —
//! rejoining the pieces yields tuples that were never there — or it can lose
//! *enforceability*: every original dependency still holds, but no single
//! fragment can be given a constraint that enforces it.
//!
//! Both questions have certificates far smaller than their decision
//! procedures, and this module refuses to report either verdict without one.
//!
//! # Lossless join
//!
//! The chase (Aho, Beeri and Ullman, 1979) starts from a tableau with one row
//! per fragment — distinguished symbol `a` in the columns the fragment keeps,
//! a private subscripted symbol elsewhere — and repeatedly identifies symbols
//! forced equal by a dependency. The join is lossless exactly when some row
//! becomes all-`a`.
//!
//! * **Lossless** carries a [`ChaseTrace`]: the numbered list of
//!   identifications. [`check_chase_trace`] rebuilds the initial tableau,
//!   checks each identification is licensed by a dependency in `F` whose
//!   determinant the two rows already agree on, applies it, and finally looks
//!   for an all-`a` row. It never chases anything itself, so it cannot be
//!   fooled by a bug in the chase.
//! * **Lossy** carries a [`SpuriousTupleWitness`]: the *final tableau, read as
//!   an ordinary relation*. It satisfies every dependency in `F`; each
//!   fragment still has a row that is all-`a` on that fragment, so the all-`a`
//!   tuple is in the join of the projections; and the all-`a` tuple is not one
//!   of its rows. That is a concrete database exhibiting a spurious tuple, and
//!   [`check_spurious_tuple`] verifies all three points with array
//!   comparisons. No chase, no closure — a designer can paste it into a test
//!   fixture.
//!
//! # Dependency preservation
//!
//! `G = ⋃ᵢ π_{Rᵢ}(F)` is computed by taking, for every subset `Z` of a
//! fragment, the dependency `Z → (Z⁺ ∩ Rᵢ)`; that set covers the projection.
//! Preservation is then `F ⊆ G⁺`, and the certificate is symmetric: an
//! Armstrong derivation of every `f ∈ F` from `G`, plus one of every `g ∈ G`
//! from `F` (so the reader knows `G` was not smuggled in). Non-preservation
//! carries the offending `f` and a two-row relation satisfying `G` that
//! violates it.

use super::armstrong::{
    Derivation, TwoTupleWitness, check_derivation, check_two_tuple_witness, derive,
    two_tuple_witness,
};
use super::{AttrSet, DbDesignError, Fd, Schema};

/// The widest fragment for which the projected dependency set is computed.
///
/// The projection sweep is `2^|Rᵢ|` closures per fragment. Refusing above this
/// is deliberate: a projected set from a truncated sweep would be *smaller*
/// than the truth, which turns a preservation question into a wrong `no`.
pub const MAX_PROJECTION_ARITY: usize = 16;

/// A tableau cell.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Symbol {
    /// The distinguished symbol `a_j` for this column.
    Distinguished,
    /// A subscripted symbol `b_{i,j}`, identified by its origin cell so the
    /// initial tableau is reconstructible from the schema alone.
    Subscripted {
        /// The row it was born in.
        row: usize,
        /// The column it was born in.
        column: usize,
    },
}

impl Symbol {
    /// The value this symbol contributes when the tableau is read as an
    /// ordinary relation: `0` for the distinguished symbol, and a distinct
    /// positive code for each subscripted one. Only compared within a column,
    /// which is where relational equality is defined anyway.
    pub fn code(self, arity: usize) -> u64 {
        match self {
            Self::Distinguished => 0,
            Self::Subscripted { row, column } => 1 + (row * arity + column) as u64,
        }
    }
}

/// One identification made by the chase.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ChaseStep {
    /// Index into [`Schema::fds`] of the dependency that licenses it.
    pub fd_index: usize,
    /// The first of the two rows that agree on the determinant.
    pub row_a: usize,
    /// The second.
    pub row_b: usize,
    /// The column being equated; must lie in the dependency's dependent.
    pub column: usize,
    /// The symbol being eliminated, everywhere in the tableau.
    pub from: Symbol,
    /// The symbol it becomes. Must be the distinguished symbol whenever
    /// either side is distinguished — otherwise a chase could "lose" an `a`.
    pub to: Symbol,
}

/// A replayable chase.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChaseTrace {
    /// The fragments, in the order that fixes the tableau's rows.
    pub fragments: Vec<AttrSet>,
    /// The identifications, in order.
    pub steps: Vec<ChaseStep>,
}

/// A relation over `R` that satisfies `F` yet whose projections rejoin to
/// something bigger.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpuriousTupleWitness {
    /// The fragments the decomposition uses.
    pub fragments: Vec<AttrSet>,
    /// The relation: one row per column-indexed value vector.
    pub rows: Vec<Vec<u64>>,
    /// The tuple that the join produces and the relation does not. It is
    /// all-zero by construction — the codes of the distinguished symbols.
    pub spurious: Vec<u64>,
}

fn initial_tableau(schema: &Schema, fragments: &[AttrSet]) -> Vec<Vec<Symbol>> {
    let arity = schema.arity();
    fragments
        .iter()
        .enumerate()
        .map(|(row, fragment)| {
            (0..arity)
                .map(|column| {
                    if fragment.contains(column) {
                        Symbol::Distinguished
                    } else {
                        Symbol::Subscripted { row, column }
                    }
                })
                .collect()
        })
        .collect()
}

fn rows_agree(tableau: &[Vec<Symbol>], a: usize, b: usize, on: AttrSet) -> bool {
    on.iter()
        .all(|column| tableau[a][column] == tableau[b][column])
}

fn replace_everywhere(tableau: &mut [Vec<Symbol>], from: Symbol, to: Symbol) {
    for row in tableau.iter_mut() {
        for cell in row.iter_mut() {
            if *cell == from {
                *cell = to;
            }
        }
    }
}

/// Reject a fragment list that is not a decomposition of `R`.
///
/// # Errors
///
/// If the fragments do not cover every attribute, or if fewer than two are
/// given (a "decomposition" into one piece is the identity and says nothing).
pub fn check_fragments(schema: &Schema, fragments: &[AttrSet]) -> Result<(), DbDesignError> {
    if fragments.len() < 2 {
        return Err(DbDesignError::new(
            "a decomposition needs at least two fragments".to_owned(),
        ));
    }
    let covered = fragments
        .iter()
        .fold(AttrSet::EMPTY, |acc, fragment| acc.union(*fragment));
    if covered != schema.all() {
        return Err(DbDesignError::new(format!(
            "the fragments cover {} but the schema is {}",
            schema.render(covered),
            schema.render(schema.all())
        )));
    }
    Ok(())
}

/// The verdict of a chase, with its certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JoinVerdict {
    /// The join is lossless; replay this to see why.
    Lossless(Box<ChaseTrace>),
    /// The join loses information; here is a database that proves it.
    Lossy(Box<SpuriousTupleWitness>),
}

/// **The finder.** Run the chase and return the matching certificate.
///
/// # Errors
///
/// If the fragments are not a decomposition, or the produced certificate fails
/// its own checker.
pub fn chase(schema: &Schema, fragments: &[AttrSet]) -> Result<JoinVerdict, DbDesignError> {
    check_fragments(schema, fragments)?;
    let arity = schema.arity();
    let mut tableau = initial_tableau(schema, fragments);
    let mut steps = Vec::new();

    loop {
        let mut changed = false;
        for (fd_index, fd) in schema.fds().iter().enumerate() {
            for a in 0..tableau.len() {
                for b in (a + 1)..tableau.len() {
                    if !rows_agree(&tableau, a, b, fd.lhs) {
                        continue;
                    }
                    for column in fd.rhs.iter() {
                        let (left, right) = (tableau[a][column], tableau[b][column]);
                        if left == right {
                            continue;
                        }
                        // Distinguished symbols win; otherwise the smaller
                        // origin cell wins, which makes the trace canonical.
                        let (from, to) = match (left, right) {
                            (Symbol::Distinguished, other) | (other, Symbol::Distinguished) => {
                                (other, Symbol::Distinguished)
                            }
                            (l, r) if l < r => (r, l),
                            (l, r) => (l, r),
                        };
                        steps.push(ChaseStep {
                            fd_index,
                            row_a: a,
                            row_b: b,
                            column,
                            from,
                            to,
                        });
                        replace_everywhere(&mut tableau, from, to);
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    let lossless = tableau
        .iter()
        .any(|row| row.iter().all(|cell| *cell == Symbol::Distinguished));
    if lossless {
        let trace = ChaseTrace {
            fragments: fragments.to_vec(),
            steps,
        };
        check_chase_trace(schema, &trace)?;
        return Ok(JoinVerdict::Lossless(Box::new(trace)));
    }

    let witness = SpuriousTupleWitness {
        fragments: fragments.to_vec(),
        rows: tableau
            .iter()
            .map(|row| row.iter().map(|cell| cell.code(arity)).collect())
            .collect(),
        spurious: vec![0; arity],
    };
    check_spurious_tuple(schema, &witness)?;
    Ok(JoinVerdict::Lossy(Box::new(witness)))
}

/// **The checker.** Replay a chase trace and confirm it reaches an all-`a`
/// row.
///
/// Each step must cite a real dependency, name two rows that *already* agree
/// on its determinant, touch a column inside its dependent, and identify two
/// symbols that are actually there — preferring the distinguished one. Extra
/// steps beyond the first all-`a` row are harmless and are not forbidden; a
/// certificate is allowed to be longer than necessary, only not wrong.
///
/// # Errors
///
/// If any step is unlicensed, or no row ends up all-distinguished.
pub fn check_chase_trace(schema: &Schema, trace: &ChaseTrace) -> Result<(), DbDesignError> {
    check_fragments(schema, &trace.fragments)?;
    let arity = schema.arity();
    let mut tableau = initial_tableau(schema, &trace.fragments);

    for (position, step) in trace.steps.iter().enumerate() {
        let fd = schema.fds().get(step.fd_index).ok_or_else(|| {
            DbDesignError::new(format!(
                "chase step {position}: cites dependency #{}, which is not in F",
                step.fd_index
            ))
        })?;
        if step.row_a >= tableau.len() || step.row_b >= tableau.len() {
            return Err(DbDesignError::new(format!(
                "chase step {position}: names a row outside the tableau"
            )));
        }
        if step.column >= arity || !fd.rhs.contains(step.column) {
            return Err(DbDesignError::new(format!(
                "chase step {position}: column is not in the dependent of `{}`",
                fd.name
            )));
        }
        if !rows_agree(&tableau, step.row_a, step.row_b, fd.lhs) {
            return Err(DbDesignError::new(format!(
                "chase step {position}: rows {} and {} do not agree on the determinant of `{}`, \
                 so the identification is unlicensed",
                step.row_a, step.row_b, fd.name
            )));
        }
        let left = tableau[step.row_a][step.column];
        let right = tableau[step.row_b][step.column];
        if step.from == step.to {
            return Err(DbDesignError::new(format!(
                "chase step {position}: identifies a symbol with itself"
            )));
        }
        let present =
            (left == step.from && right == step.to) || (left == step.to && right == step.from);
        if !present {
            return Err(DbDesignError::new(format!(
                "chase step {position}: the two cells do not hold the symbols the step claims"
            )));
        }
        if step.from == Symbol::Distinguished {
            return Err(DbDesignError::new(format!(
                "chase step {position}: eliminates the distinguished symbol, which the chase \
                 never does"
            )));
        }
        replace_everywhere(&mut tableau, step.from, step.to);
    }

    if tableau
        .iter()
        .any(|row| row.iter().all(|cell| *cell == Symbol::Distinguished))
    {
        Ok(())
    } else {
        Err(DbDesignError::new(
            "the trace never produces an all-distinguished row, so it does not establish a \
             lossless join"
                .to_owned(),
        ))
    }
}

/// **The checker.** Confirm a relation really exhibits a spurious tuple.
///
/// Three obligations:
///
/// 1. the relation satisfies every dependency in `F`;
/// 2. every fragment has a row agreeing with the claimed spurious tuple on
///    that fragment — so the tuple is in the join of the projections;
/// 3. the tuple is not a row of the relation.
///
/// # Errors
///
/// If any obligation fails, naming which.
pub fn check_spurious_tuple(
    schema: &Schema,
    witness: &SpuriousTupleWitness,
) -> Result<(), DbDesignError> {
    check_fragments(schema, &witness.fragments)?;
    let arity = schema.arity();
    if witness.spurious.len() != arity || witness.rows.iter().any(|row| row.len() != arity) {
        return Err(DbDesignError::new(
            "the witness relation is not over this schema's attributes".to_owned(),
        ));
    }

    for fd in schema.fds() {
        for (i, row_i) in witness.rows.iter().enumerate() {
            for row_j in witness.rows.iter().skip(i + 1) {
                let agree_lhs = fd.lhs.iter().all(|column| row_i[column] == row_j[column]);
                if agree_lhs && !fd.rhs.iter().all(|column| row_i[column] == row_j[column]) {
                    return Err(DbDesignError::new(format!(
                        "the witness relation violates `{}`, so it is not a legal instance",
                        fd.name
                    )));
                }
            }
        }
    }

    for fragment in &witness.fragments {
        let joined = witness.rows.iter().any(|row| {
            fragment
                .iter()
                .all(|column| row[column] == witness.spurious[column])
        });
        if !joined {
            return Err(DbDesignError::new(format!(
                "no row projects onto the claimed spurious tuple over {}, so the join does not \
                 produce it",
                schema.render(*fragment)
            )));
        }
    }

    if witness.rows.contains(&witness.spurious) {
        return Err(DbDesignError::new(
            "the claimed spurious tuple is already a row of the relation".to_owned(),
        ));
    }
    Ok(())
}

/// The projected dependency set `G = ⋃ᵢ π_{Rᵢ}(F)`, as a schema over the same
/// attributes.
///
/// Trivial and duplicate dependencies are dropped, so `G` is small enough to
/// print.
///
/// # Errors
///
/// If any fragment is wider than [`MAX_PROJECTION_ARITY`].
pub fn project_dependencies(
    schema: &Schema,
    fragments: &[AttrSet],
) -> Result<Schema, DbDesignError> {
    let mut projected = Schema::new(schema.attributes().to_vec())?;
    let mut seen: Vec<(AttrSet, AttrSet)> = Vec::new();
    for (index, fragment) in fragments.iter().enumerate() {
        let columns: Vec<usize> = fragment.iter().collect();
        if columns.len() > MAX_PROJECTION_ARITY {
            return Err(DbDesignError::new(format!(
                "fragment {index} has {} attributes; the projection sweep limit is \
                 {MAX_PROJECTION_ARITY}, and a truncated sweep would understate G",
                columns.len()
            )));
        }
        for bits in 0u64..(1u64 << columns.len()) {
            let z = AttrSet::from_indices(
                columns
                    .iter()
                    .enumerate()
                    .filter(|(slot, _)| (bits >> slot) & 1 == 1)
                    .map(|(_, &column)| column),
            );
            let dependent = schema.closure(z).intersect(*fragment).difference(z);
            if dependent.is_empty() || seen.contains(&(z, dependent)) {
                continue;
            }
            seen.push((z, dependent));
            projected.push_fd(Fd {
                name: format!("g{}_{}", index, seen.len()),
                lhs: z,
                rhs: dependent,
            })?;
        }
    }
    Ok(projected)
}

/// The verdict on dependency preservation, with its certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PreservationVerdict {
    /// Every dependency of `F` is recoverable from the fragments.
    Preserved {
        /// The projected set that recovers them.
        projected: Box<Schema>,
        /// A derivation of each `f ∈ F` from `G`.
        f_from_g: Vec<Derivation>,
        /// A derivation of each `g ∈ G` from `F`, so `G` is not smuggled in.
        g_from_f: Vec<Derivation>,
    },
    /// Some dependency is unenforceable on the fragments.
    NotPreserved {
        /// The projected set.
        projected: Box<Schema>,
        /// The label of the dependency that is lost.
        lost_fd: String,
        /// A two-row relation satisfying `G` that violates it.
        witness: Box<TwoTupleWitness>,
    },
}

/// **The finder.** Decide dependency preservation and certify the verdict.
///
/// # Errors
///
/// If the fragments are not a decomposition, a fragment is too wide, or a
/// produced certificate fails its checker.
pub fn preservation(
    schema: &Schema,
    fragments: &[AttrSet],
) -> Result<PreservationVerdict, DbDesignError> {
    check_fragments(schema, fragments)?;
    let projected = project_dependencies(schema, fragments)?;

    for fd in schema.fds() {
        if projected.implies(fd.lhs, fd.rhs) {
            continue;
        }
        let witness = two_tuple_witness(&projected, fd.lhs, fd.rhs)?;
        check_two_tuple_witness(&projected, &witness)?;
        return Ok(PreservationVerdict::NotPreserved {
            projected: Box::new(projected),
            lost_fd: fd.name.clone(),
            witness: Box::new(witness),
        });
    }

    let mut f_from_g = Vec::with_capacity(schema.fds().len());
    for fd in schema.fds() {
        let derivation = derive(&projected, fd.lhs, fd.rhs)?;
        check_derivation(projected.fds(), &derivation)?;
        f_from_g.push(derivation);
    }
    let mut g_from_f = Vec::with_capacity(projected.fds().len());
    for fd in projected.fds() {
        let derivation = derive(schema, fd.lhs, fd.rhs)?;
        check_derivation(schema.fds(), &derivation)?;
        g_from_f.push(derivation);
    }
    Ok(PreservationVerdict::Preserved {
        projected: Box::new(projected),
        f_from_g,
        g_from_f,
    })
}

#[cfg(test)]
mod tests {
    use super::super::Fd;
    use super::*;

    fn build(attrs: &[&str], fds: &[(&str, &[usize], &[usize])]) -> Schema {
        let mut schema =
            Schema::new(attrs.iter().map(|name| (*name).to_owned()).collect()).unwrap();
        for (name, lhs, rhs) in fds {
            schema
                .push_fd(Fd {
                    name: (*name).to_owned(),
                    lhs: AttrSet::from_indices(lhs.iter().copied()),
                    rhs: AttrSet::from_indices(rhs.iter().copied()),
                })
                .unwrap();
        }
        schema
    }

    #[test]
    fn a_key_preserving_split_is_lossless() {
        // A -> B, A -> C. Split on A: {A,B} and {A,C}.
        let schema = build(&["A", "B", "C"], &[("f1", &[0], &[1]), ("f2", &[0], &[2])]);
        let fragments = vec![AttrSet::from_indices([0, 1]), AttrSet::from_indices([0, 2])];
        let verdict = chase(&schema, &fragments).unwrap();
        let JoinVerdict::Lossless(trace) = verdict else {
            panic!("splitting on a key is lossless");
        };
        check_chase_trace(&schema, &trace).unwrap();
    }

    #[test]
    fn splitting_off_a_non_key_loses_information() {
        // A -> B only. Split {A,B} / {B,C}: B is not a key of either side.
        let schema = build(&["A", "B", "C"], &[("f1", &[0], &[1])]);
        let fragments = vec![AttrSet::from_indices([0, 1]), AttrSet::from_indices([1, 2])];
        let verdict = chase(&schema, &fragments).unwrap();
        let JoinVerdict::Lossy(witness) = verdict else {
            panic!("B determines nothing, so the split is lossy");
        };
        check_spurious_tuple(&schema, &witness).unwrap();
        assert_eq!(witness.spurious, vec![0, 0, 0]);
    }

    #[test]
    fn a_tampered_chase_trace_is_rejected() {
        let schema = build(&["A", "B", "C"], &[("f1", &[0], &[1]), ("f2", &[0], &[2])]);
        let fragments = vec![AttrSet::from_indices([0, 1]), AttrSet::from_indices([0, 2])];
        let JoinVerdict::Lossless(good) = chase(&schema, &fragments).unwrap() else {
            unreachable!()
        };

        // An empty trace on this decomposition proves nothing.
        let empty = ChaseTrace {
            fragments: fragments.clone(),
            steps: Vec::new(),
        };
        assert!(check_chase_trace(&schema, &empty).is_err());

        // A step citing a dependency that is not in F.
        let mut bad_fd = (*good).clone();
        bad_fd.steps[0].fd_index = 42;
        assert!(check_chase_trace(&schema, &bad_fd).is_err());

        // A step on a column outside the dependent.
        let mut bad_column = (*good).clone();
        bad_column.steps[0].column = 0;
        assert!(check_chase_trace(&schema, &bad_column).is_err());

        // A fabricated step between rows that do not agree on the determinant,
        // over a decomposition where nothing lines up.
        let lossy_schema = build(&["A", "B", "C"], &[("f1", &[0], &[1])]);
        let lossy_fragments = vec![AttrSet::from_indices([0, 1]), AttrSet::from_indices([1, 2])];
        let fabricated = ChaseTrace {
            fragments: lossy_fragments,
            steps: vec![ChaseStep {
                fd_index: 0,
                row_a: 0,
                row_b: 1,
                column: 1,
                from: Symbol::Subscripted { row: 1, column: 0 },
                to: Symbol::Distinguished,
            }],
        };
        assert!(check_chase_trace(&lossy_schema, &fabricated).is_err());
    }

    #[test]
    fn a_tampered_spurious_witness_is_rejected() {
        let schema = build(&["A", "B", "C"], &[("f1", &[0], &[1])]);
        let fragments = vec![AttrSet::from_indices([0, 1]), AttrSet::from_indices([1, 2])];
        let JoinVerdict::Lossy(good) = chase(&schema, &fragments).unwrap() else {
            unreachable!()
        };

        // Put the spurious tuple into the relation: the claim collapses.
        let mut contains_it = (*good).clone();
        contains_it.rows.push(vec![0, 0, 0]);
        assert!(check_spurious_tuple(&schema, &contains_it).is_err());

        // Break the projection cover.
        let mut no_cover = (*good).clone();
        no_cover.rows[0][1] = 77;
        assert!(check_spurious_tuple(&schema, &no_cover).is_err());

        // A relation that violates F is not a legal instance.
        let illegal = SpuriousTupleWitness {
            fragments: fragments.clone(),
            rows: vec![vec![0, 0, 5], vec![0, 9, 0]],
            spurious: vec![0, 0, 0],
        };
        assert!(check_spurious_tuple(&schema, &illegal).is_err());
    }

    #[test]
    fn preservation_holds_for_the_key_split() {
        let schema = build(&["A", "B", "C"], &[("f1", &[0], &[1]), ("f2", &[0], &[2])]);
        let fragments = vec![AttrSet::from_indices([0, 1]), AttrSet::from_indices([0, 2])];
        let verdict = preservation(&schema, &fragments).unwrap();
        let PreservationVerdict::Preserved {
            f_from_g, g_from_f, ..
        } = verdict
        else {
            panic!("both dependencies live inside a fragment");
        };
        assert_eq!(f_from_g.len(), 2);
        assert!(!g_from_f.is_empty());
    }

    #[test]
    fn the_classical_bcnf_price_is_a_lost_dependency() {
        // The textbook `city street zip` example: {street, city} -> zip and
        // zip -> city. The BCNF decomposition {zip, city} / {zip, street} is
        // lossless but cannot enforce {street, city} -> zip.
        let schema = build(
            &["street", "city", "zip"],
            &[("addr", &[0, 1], &[2]), ("zipcity", &[2], &[1])],
        );
        let fragments = vec![AttrSet::from_indices([2, 1]), AttrSet::from_indices([2, 0])];
        let JoinVerdict::Lossless(_) = chase(&schema, &fragments).unwrap() else {
            panic!("zip is a key of the first fragment, so the join is lossless");
        };
        let verdict = preservation(&schema, &fragments).unwrap();
        let PreservationVerdict::NotPreserved {
            lost_fd,
            witness,
            projected,
        } = verdict
        else {
            panic!("`addr` spans both fragments and is lost");
        };
        assert_eq!(lost_fd, "addr");
        check_two_tuple_witness(&projected, &witness).unwrap();
    }
}
