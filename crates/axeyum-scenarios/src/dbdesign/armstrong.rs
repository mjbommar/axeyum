//! Certificates for functional-dependency implication, in both directions.
//!
//! `F ⊨ X → Y` is decided in linear time by attribute closure, so the
//! interesting engineering is not the decision — it is producing something a
//! stranger can replay without running, reading or trusting the closure
//! algorithm. Both directions have one:
//!
//! * **Implied.** A [`Derivation`]: a numbered sequence of dependencies, each
//!   one either a member of `F` cited by name or the result of applying
//!   *reflexivity*, *augmentation* or *transitivity* to earlier lines. That is
//!   Armstrong's axiom system and nothing else; [`check_derivation`]
//!   implements those three rules in about forty lines and knows nothing about
//!   closure.
//! * **Not implied.** A [`TwoTupleWitness`]: a relation with exactly two rows
//!   that satisfies every dependency in `F` and violates `X → Y`. This is the
//!   construction behind the *completeness* half of Armstrong's theorem — the
//!   two rows agree exactly on `X⁺` — and [`check_two_tuple_witness`] verifies
//!   it by comparing two arrays of bits.
//!
//! The asymmetry is the point. A designer who is told "yes, that dependency is
//! forced" gets a proof; a designer told "no" gets a *counterexample database*
//! they can paste into a test.

use super::{AttrSet, DbDesignError, Fd, Schema};

/// One line of an Armstrong derivation.
///
/// Every variant names only earlier lines, so a derivation is a DAG in list
/// form and the checker needs no cycle detection beyond an index comparison.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Step {
    /// **Reflexivity.** `X → Y` whenever `Y ⊆ X`. An axiom: no premises.
    Reflexivity {
        /// The determinant `X`.
        lhs: AttrSet,
        /// The dependent `Y`, which must be a subset of `lhs`.
        rhs: AttrSet,
    },
    /// A dependency taken verbatim from `F`, cited by its position.
    Given {
        /// Index into [`Schema::fds`].
        index: usize,
    },
    /// **Augmentation.** From `X → Y` conclude `X ∪ Z → Y ∪ Z`.
    Augmentation {
        /// The line proving `X → Y`.
        premise: usize,
        /// The attributes `Z` added to both sides.
        extra: AttrSet,
    },
    /// **Transitivity.** From `X → Y` and `Y → Z` conclude `X → Z`.
    Transitivity {
        /// The line proving `X → Y`.
        left: usize,
        /// The line proving `Y → Z`; its determinant must equal the left
        /// line's dependent *exactly*, because that is what the axiom says.
        right: usize,
    },
}

/// A derivation of `goal_lhs → goal_rhs` from `F` under Armstrong's axioms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Derivation {
    /// The determinant of the derived dependency.
    pub goal_lhs: AttrSet,
    /// The dependent of the derived dependency.
    pub goal_rhs: AttrSet,
    /// The lines, in order. The last line must be the goal.
    pub steps: Vec<Step>,
}

impl Derivation {
    /// How many lines the derivation has, which is what a reader has to check.
    pub fn len(&self) -> usize {
        self.steps.len()
    }

    /// Is the derivation empty? (Only a malformed one is.)
    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

/// **The checker.** Replay a derivation against `F` and confirm it establishes
/// its stated goal.
///
/// This function is the whole trusted surface of the "implied" direction. It
/// implements the three Armstrong axioms and the citation of a given
/// dependency, in that order, and deliberately implements nothing else — no
/// union rule, no decomposition rule, no pseudo-transitivity, and above all no
/// attribute closure. A derivation that needs a derived rule must spell that
/// rule out in terms of the three axioms, which is exactly what makes the
/// certificate checkable by someone who does not have our code.
///
/// Returns the per-line conclusions on success, so a caller can print the
/// derivation with its inferred dependencies rather than re-deriving them.
///
/// # Errors
///
/// If any line is malformed, cites a later or out-of-range line, misapplies
/// its rule, or if the final line is not the stated goal.
pub fn check_derivation(
    fds: &[Fd],
    derivation: &Derivation,
) -> Result<Vec<(AttrSet, AttrSet)>, DbDesignError> {
    let mut lines: Vec<(AttrSet, AttrSet)> = Vec::with_capacity(derivation.steps.len());
    for (position, step) in derivation.steps.iter().enumerate() {
        let conclusion = match step {
            Step::Reflexivity { lhs, rhs } => {
                if !rhs.is_subset_of(*lhs) {
                    return Err(DbDesignError::new(format!(
                        "line {position}: reflexivity needs the dependent to be a subset of the \
                         determinant"
                    )));
                }
                (*lhs, *rhs)
            }
            Step::Given { index } => {
                let fd = fds.get(*index).ok_or_else(|| {
                    DbDesignError::new(format!(
                        "line {position}: cites dependency #{index}, which is not in F"
                    ))
                })?;
                (fd.lhs, fd.rhs)
            }
            Step::Augmentation { premise, extra } => {
                let (lhs, rhs) = *earlier(&lines, *premise, position)?;
                (lhs.union(*extra), rhs.union(*extra))
            }
            Step::Transitivity { left, right } => {
                let (x, y) = *earlier(&lines, *left, position)?;
                let (y2, z) = *earlier(&lines, *right, position)?;
                if y != y2 {
                    return Err(DbDesignError::new(format!(
                        "line {position}: transitivity needs the left line's dependent to equal \
                         the right line's determinant"
                    )));
                }
                (x, z)
            }
        };
        lines.push(conclusion);
    }

    let last = lines.last().ok_or_else(|| {
        DbDesignError::new("the derivation has no lines, so it establishes nothing".to_owned())
    })?;
    if *last != (derivation.goal_lhs, derivation.goal_rhs) {
        return Err(DbDesignError::new(
            "the last line is not the stated goal".to_owned(),
        ));
    }
    Ok(lines)
}

fn earlier(
    lines: &[(AttrSet, AttrSet)],
    cited: usize,
    position: usize,
) -> Result<&(AttrSet, AttrSet), DbDesignError> {
    if cited >= position {
        return Err(DbDesignError::new(format!(
            "line {position}: cites line {cited}, which is not strictly earlier"
        )));
    }
    lines.get(cited).ok_or_else(|| {
        DbDesignError::new(format!("line {position}: cites nonexistent line {cited}"))
    })
}

/// **The finder.** Build an Armstrong derivation of `X → Y`, or report that
/// `F` does not imply it.
///
/// The construction mirrors the closure fixpoint, three lines per round:
/// having `X → C` for the closure-so-far `C`, an applicable dependency
/// `L → R` with `L ⊆ C` is cited, *augmented* by `C` to give `C → R ∪ C`
/// (using `L ∪ C = C`), and composed by *transitivity* to give `X → R ∪ C`.
/// A final reflexivity step `X⁺ → Y` and one more transitivity land the goal.
/// So the certificate is at most `3·|F| + 3` lines regardless of how long the
/// search took.
///
/// # Errors
///
/// If `F` does not imply `X → Y` — in which case
/// [`two_tuple_witness`] is the certificate to reach for instead.
pub fn derive(schema: &Schema, x: AttrSet, y: AttrSet) -> Result<Derivation, DbDesignError> {
    let closure = schema.closure(x);
    if !y.is_subset_of(closure) {
        return Err(DbDesignError::new(format!(
            "F does not imply {} -> {}",
            schema.render(x),
            schema.render(y)
        )));
    }

    let mut steps = Vec::new();
    // Line 0: `X -> X` by reflexivity. The running invariant is that
    // `current_line` proves `X -> current`.
    steps.push(Step::Reflexivity { lhs: x, rhs: x });
    let mut current_line = 0usize;
    let mut current = x;

    loop {
        let mut grew = false;
        for (index, fd) in schema.fds().iter().enumerate() {
            if fd.lhs.is_subset_of(current) && !fd.rhs.is_subset_of(current) {
                // `L -> R` from F.
                steps.push(Step::Given { index });
                let given = steps.len() - 1;
                // Augment by `current`: `L ∪ current -> R ∪ current`, and
                // `L ⊆ current` so the determinant is exactly `current`.
                steps.push(Step::Augmentation {
                    premise: given,
                    extra: current,
                });
                let augmented = steps.len() - 1;
                // Compose: `X -> current` then `current -> R ∪ current`.
                steps.push(Step::Transitivity {
                    left: current_line,
                    right: augmented,
                });
                current_line = steps.len() - 1;
                current = current.union(fd.rhs);
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }

    // `X⁺ -> Y` by reflexivity, then transitivity with `X -> X⁺`.
    if y == current {
        // Already exactly the goal; a reflexivity/transitivity pair would be
        // sound but noise.
    } else {
        steps.push(Step::Reflexivity {
            lhs: current,
            rhs: y,
        });
        let reflexive = steps.len() - 1;
        steps.push(Step::Transitivity {
            left: current_line,
            right: reflexive,
        });
    }

    Ok(Derivation {
        goal_lhs: x,
        goal_rhs: y,
        steps,
    })
}

/// A two-row relation that satisfies `F` and violates a dependency.
///
/// The rows are attribute-indexed bit patterns: `row_a` is all zeros and
/// `row_b` is zero exactly on `agreement` and one elsewhere, so the two rows
/// agree precisely on `agreement`. Two values per column is enough — the
/// classical completeness proof for Armstrong's axioms uses exactly this
/// relation — and it keeps the certificate down to one bitmask.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TwoTupleWitness {
    /// The attributes on which the two rows agree.
    pub agreement: AttrSet,
    /// The dependency the witness refutes: its determinant.
    pub violated_lhs: AttrSet,
    /// The dependency the witness refutes: its dependent.
    pub violated_rhs: AttrSet,
}

impl TwoTupleWitness {
    /// The first row: `0` in every column.
    pub fn row_a(&self, arity: usize) -> Vec<u8> {
        vec![0; arity]
    }

    /// The second row: `0` on the agreement set, `1` elsewhere.
    pub fn row_b(&self, arity: usize) -> Vec<u8> {
        (0..arity)
            .map(|index| u8::from(!self.agreement.contains(index)))
            .collect()
    }
}

/// **The checker.** Confirm a two-row relation really is a counterexample.
///
/// Three obligations, all decided by comparing bits:
///
/// 1. every dependency in `F` holds on the two rows — if the rows agree on the
///    determinant they agree on the dependent;
/// 2. the rows agree on the violated determinant;
/// 3. the rows differ somewhere in the violated dependent.
///
/// Nothing here computes a closure, so this is an independent refutation of
/// `F ⊨ X → Y` and not a restatement of the algorithm that proposed it.
///
/// # Errors
///
/// If any of the three fails, naming which.
pub fn check_two_tuple_witness(
    schema: &Schema,
    witness: &TwoTupleWitness,
) -> Result<(), DbDesignError> {
    let arity = schema.arity();
    let row_a = witness.row_a(arity);
    let row_b = witness.row_b(arity);
    let agree_on = |set: AttrSet| -> bool { set.iter().all(|index| row_a[index] == row_b[index]) };

    for fd in schema.fds() {
        if agree_on(fd.lhs) && !agree_on(fd.rhs) {
            return Err(DbDesignError::new(format!(
                "the two rows violate `{}`, so they are not a relation over this schema",
                fd.name
            )));
        }
    }
    if !agree_on(witness.violated_lhs) {
        return Err(DbDesignError::new(format!(
            "the two rows do not agree on {}, so they say nothing about it",
            schema.render(witness.violated_lhs)
        )));
    }
    if agree_on(witness.violated_rhs) {
        return Err(DbDesignError::new(format!(
            "the two rows agree on {}, so the dependency is not violated",
            schema.render(witness.violated_rhs)
        )));
    }
    Ok(())
}

/// **The finder.** Build the two-row counterexample to `X → Y`, or report that
/// `F` does imply it.
///
/// # Errors
///
/// If `F ⊨ X → Y`, in which case [`derive()`] is the certificate to reach for.
pub fn two_tuple_witness(
    schema: &Schema,
    x: AttrSet,
    y: AttrSet,
) -> Result<TwoTupleWitness, DbDesignError> {
    let closure = schema.closure(x);
    if y.is_subset_of(closure) {
        return Err(DbDesignError::new(format!(
            "F implies {} -> {}, so no counterexample relation exists",
            schema.render(x),
            schema.render(y)
        )));
    }
    Ok(TwoTupleWitness {
        agreement: closure,
        violated_lhs: x,
        violated_rhs: y,
    })
}

/// Build a two-row witness from an **agreement set produced elsewhere** — in
/// practice a solver model for the Horn encoding in
/// [`super::encode`] — and check it.
///
/// This is how a `sat` answer from the solver becomes a certificate: the set
/// of attributes the model makes true is an agreement set, and *any* model of
/// the Horn encoding yields a valid counterexample, not just the closure. The
/// check is the same [`check_two_tuple_witness`] every other witness goes
/// through, so trusting the solver is not on the table.
///
/// # Errors
///
/// If the resulting relation is not a counterexample.
pub fn witness_from_agreement(
    schema: &Schema,
    agreement: AttrSet,
    x: AttrSet,
    y: AttrSet,
) -> Result<TwoTupleWitness, DbDesignError> {
    let witness = TwoTupleWitness {
        agreement,
        violated_lhs: x,
        violated_rhs: y,
    };
    check_two_tuple_witness(schema, &witness)?;
    Ok(witness)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn schema() -> Schema {
        // A B -> C, C -> D, D -> A : the textbook cyclic example.
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

    #[test]
    fn derivation_is_found_and_checks() {
        let schema = schema();
        let x = AttrSet::from_indices([0, 1]);
        let y = AttrSet::from_indices([3]);
        let derivation = derive(&schema, x, y).unwrap();
        let lines = check_derivation(schema.fds(), &derivation).unwrap();
        assert_eq!(lines.last().copied().unwrap(), (x, y));
        assert!(derivation.len() <= 3 * schema.fds().len() + 3);
        assert!(!derivation.is_empty());
    }

    #[test]
    fn derivation_of_the_whole_closure_checks() {
        let schema = schema();
        let x = AttrSet::from_indices([1, 2]);
        let closure = schema.closure(x);
        let derivation = derive(&schema, x, closure).unwrap();
        check_derivation(schema.fds(), &derivation).unwrap();
    }

    #[test]
    fn a_tampered_derivation_is_rejected() {
        let schema = schema();
        let x = AttrSet::from_indices([0, 1]);
        let y = AttrSet::from_indices([3]);
        let good = derive(&schema, x, y).unwrap();

        // Swap the goal for something the lines do not establish.
        let mut wrong_goal = good.clone();
        wrong_goal.goal_rhs = AttrSet::from_indices([0, 1, 2, 3]);
        assert!(check_derivation(schema.fds(), &wrong_goal).is_err());

        // A reflexivity step whose dependent is not a subset.
        let bogus = Derivation {
            goal_lhs: x,
            goal_rhs: y,
            steps: vec![Step::Reflexivity { lhs: x, rhs: y }],
        };
        assert!(check_derivation(schema.fds(), &bogus).is_err());

        // A forward reference.
        let forward = Derivation {
            goal_lhs: x,
            goal_rhs: y,
            steps: vec![
                Step::Augmentation {
                    premise: 1,
                    extra: AttrSet::EMPTY,
                },
                Step::Given { index: 0 },
            ],
        };
        assert!(check_derivation(schema.fds(), &forward).is_err());

        // Transitivity with a mismatched middle.
        let mismatch = Derivation {
            goal_lhs: AttrSet::from_indices([2]),
            goal_rhs: AttrSet::from_indices([0]),
            steps: vec![
                Step::Given { index: 1 }, // C -> D
                Step::Given { index: 0 }, // A B -> C   (middle is D, not A B)
                Step::Transitivity { left: 0, right: 1 },
            ],
        };
        assert!(check_derivation(schema.fds(), &mismatch).is_err());

        // A citation outside F.
        let out_of_range = Derivation {
            goal_lhs: x,
            goal_rhs: y,
            steps: vec![Step::Given { index: 99 }],
        };
        assert!(check_derivation(schema.fds(), &out_of_range).is_err());

        // No lines at all.
        let empty = Derivation {
            goal_lhs: x,
            goal_rhs: y,
            steps: Vec::new(),
        };
        assert!(check_derivation(schema.fds(), &empty).is_err());
    }

    #[test]
    fn non_implication_gets_a_two_row_relation() {
        let schema = schema();
        let x = AttrSet::from_indices([2]); // C
        let y = AttrSet::from_indices([1]); // B
        assert!(derive(&schema, x, y).is_err());
        let witness = two_tuple_witness(&schema, x, y).unwrap();
        check_two_tuple_witness(&schema, &witness).unwrap();
        assert_eq!(witness.row_a(4), vec![0, 0, 0, 0]);
        // C+ = {A, C, D}; B is the only column the rows differ on.
        assert_eq!(witness.row_b(4), vec![0, 1, 0, 0]);
    }

    #[test]
    fn a_bogus_two_row_relation_is_rejected() {
        let schema = schema();
        // Claim C -> B is violated, but let the rows agree on B as well.
        let agrees_everywhere = TwoTupleWitness {
            agreement: AttrSet::full(4),
            violated_lhs: AttrSet::from_indices([2]),
            violated_rhs: AttrSet::from_indices([1]),
        };
        assert!(check_two_tuple_witness(&schema, &agrees_everywhere).is_err());

        // Rows that agree only on C: they break `f2` (C -> D), so they are not
        // a legal relation over this schema at all.
        let breaks_f2 = TwoTupleWitness {
            agreement: AttrSet::from_indices([2]),
            violated_lhs: AttrSet::from_indices([2]),
            violated_rhs: AttrSet::from_indices([1]),
        };
        assert!(check_two_tuple_witness(&schema, &breaks_f2).is_err());

        // Rows that do not agree on the claimed determinant.
        let no_agreement = TwoTupleWitness {
            agreement: AttrSet::EMPTY,
            violated_lhs: AttrSet::from_indices([2]),
            violated_rhs: AttrSet::from_indices([1]),
        };
        assert!(check_two_tuple_witness(&schema, &no_agreement).is_err());

        // And two_tuple_witness refuses to invent one for an implied FD.
        assert!(
            two_tuple_witness(
                &schema,
                AttrSet::from_indices([0, 1]),
                AttrSet::from_indices([3])
            )
            .is_err()
        );
    }

    #[test]
    fn a_non_closure_agreement_set_is_still_a_witness() {
        let schema = schema();
        // {A, C, D} is C+; {A, B, C, D} minus B is the same. Take a *larger*
        // legal agreement set for a different question: A -> B is not implied,
        // and A+ = {A}. The full set minus B is a model of the Horn encoding
        // that is not a closure of anything -- and it still certifies.
        let x = AttrSet::from_indices([0]);
        let y = AttrSet::from_indices([1]);
        let agreement = AttrSet::from_indices([0, 2, 3]);
        let witness = witness_from_agreement(&schema, agreement, x, y).unwrap();
        assert_eq!(witness.agreement, agreement);
        // An agreement set that is not closed under F is refused.
        assert!(witness_from_agreement(&schema, AttrSet::from_indices([0, 2]), x, y).is_err());
    }
}
