//! Disjunction under `∃` as a **first-class object**: `∃x. ⋁ᵢ ⋀ⱼ pᵢⱼ(x) ▷ᵢⱼ 0`,
//! with certificates on both verdicts.
//!
//! The first slice of [`crate::qe`] decided a disjunctive existential by
//! running [`crate::qe::decide_exists`] on each disjunct in the caller's loop.
//! That works, but it produces no object: a `true` answer has no way to say
//! *which* disjunct it came from, and a `false` answer is a pile of `n`
//! unrelated refutations over `n` different cell decompositions, so nothing
//! checks that they are refutations of the *same* line.
//!
//! Here the decomposition is computed **once**, from the roots of every
//! polynomial in every disjunct, and both certificates speak about it:
//!
//! - [`DnfSampleCertificate`] names the disjunct it satisfies, and its `verify`
//!   re-derives the signs of exactly that disjunct's conjuncts at the sample;
//! - [`DnfRefutationCertificate`] carries, for **every cell**, one failing
//!   conjunct **per disjunct**. The count guard
//!   ([`crate::qe::Fault::DisjunctFailureCountMismatch`]) is what stops a
//!   refutation from quietly skipping a branch — a cell that refutes three of
//!   four disjuncts is refused, and refused with a fault distinct from every
//!   other refusal.
//!
//! Both share [`crate::qe`]'s decomposition guards, so "the cells really are
//! sign-invariant" is checked by exactly one piece of code for the conjunctive
//! and disjunctive cases alike.
//!
//! # The dual
//!
//! `∀x. ⋀ᵢ ⋁ⱼ …` is the De Morgan dual and is *not* provided: negating a DNF
//! gives a CNF, whose conversion back to DNF is exponential. The one-quantifier
//! universal that **is** decided is [`crate::qe::decide_forall`], over a single
//! disjunction of atoms.

use num_rational::BigRational;

use super::{
    Atom, CellFailure, Fault, SamplePoint, cell_sample_of, check_atoms_hold, check_cell_failure,
    check_decomposition, check_sample_is_isolated, decompose, first_failure, sign_at_sample,
};

/// `∃x. ⋁ᵢ ⋀ⱼ disjuncts[i][j]` — a disjunction of conjunctions of atoms.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Dnf {
    /// The disjuncts. An **empty** disjunction is `false`; an empty *conjunct
    /// list* inside one is `true`.
    pub disjuncts: Vec<Vec<Atom>>,
}

impl Dnf {
    /// Build `∃x. ⋁ ⋀ disjuncts`.
    #[must_use]
    pub fn new(disjuncts: Vec<Vec<Atom>>) -> Dnf {
        Dnf { disjuncts }
    }

    /// Every atom of every disjunct, in order — the population whose roots cut
    /// the line.
    #[must_use]
    pub(crate) fn all_atoms(&self) -> Vec<Atom> {
        self.disjuncts.iter().flatten().cloned().collect()
    }
}

/// Witness that `∃x. ⋁ᵢ ⋀ⱼ pᵢⱼ ▷ᵢⱼ 0` is **true**: a point, the disjunct it
/// satisfies, and the sign of that disjunct's conjuncts there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DnfSampleCertificate {
    /// The formula this certificate is about.
    pub disjuncts: Vec<Vec<Atom>>,
    /// Which disjunct the sample satisfies.
    pub disjunct: usize,
    /// The satisfying point.
    pub sample: SamplePoint,
    /// `signs[j]` is the claimed sign of `disjuncts[disjunct][j].poly` at
    /// `sample`.
    pub signs: Vec<i8>,
}

impl DnfSampleCertificate {
    /// Re-derive the claim from the formula and the sample alone.
    ///
    /// Guards, in order: the named disjunct exists; it has one recorded sign
    /// per conjunct; an algebraic sample's bracket really isolates one root;
    /// every recorded sign equals the recomputed one; every relation of that
    /// disjunct holds at the recomputed sign.
    ///
    /// A sample that satisfies **no** disjunct is refused as
    /// [`Fault::RelationFails`] on the disjunct it claimed — a different fault
    /// from every refutation guard, so the two forgery classes are
    /// distinguishable.
    ///
    /// # Errors
    ///
    /// The [`Fault`] naming the guard that rejected, or [`Fault::Declined`] if
    /// a step budget ran out.
    pub fn verify(&self) -> Result<(), Fault> {
        let Some(atoms) = self.disjuncts.get(self.disjunct) else {
            return Err(Fault::DisjunctIndexOutOfRange {
                recorded: self.disjunct,
                disjuncts: self.disjuncts.len(),
            });
        };
        if self.signs.len() != atoms.len() {
            return Err(Fault::SignCountMismatch {
                recorded: self.signs.len(),
                atoms: atoms.len(),
            });
        }
        check_sample_is_isolated(&self.sample)?;
        check_atoms_hold(atoms, &self.sample, Some(&self.signs))
    }
}

/// Witness that `∃x. ⋁ᵢ ⋀ⱼ pᵢⱼ ▷ᵢⱼ 0` is **false**: the sign-invariant cell
/// decomposition of ℝ induced by *every* polynomial in *every* disjunct, and,
/// in every cell, a failing conjunct for **every** disjunct.
///
/// Cells interleave exactly as in [`crate::qe::RefutationCertificate`]:
/// `open_samples[0]`, `roots[0]`, `open_samples[1]`, …
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DnfRefutationCertificate {
    /// The formula this certificate is about.
    pub disjuncts: Vec<Vec<Atom>>,
    /// The distinct real roots of every polynomial of every disjunct, strictly
    /// ascending.
    pub roots: Vec<SamplePoint>,
    /// One rational sample per open cell; `roots.len() + 1` of them.
    pub open_samples: Vec<BigRational>,
    /// `failures[cell][disjunct]` is a conjunct of that disjunct that fails in
    /// that cell. Every cell carries one entry **per disjunct**.
    pub failures: Vec<Vec<CellFailure>>,
}

impl DnfRefutationCertificate {
    /// Re-derive the refutation from the formula alone.
    ///
    /// Guards, in order: the cell and open-sample counts match the root list;
    /// every algebraic root's bracket isolates one root; the cells cover ℝ in
    /// order; the root list is complete against **every** polynomial of every
    /// disjunct (an independent `BigRational` Sturm recount); every cell
    /// records exactly one failing conjunct per disjunct; and every one of
    /// those conjuncts has the recorded sign there and genuinely fails.
    ///
    /// # Errors
    ///
    /// The [`Fault`] naming the guard that rejected, or [`Fault::Declined`] if
    /// a step budget ran out.
    pub fn verify(&self) -> Result<(), Fault> {
        let expected_cells = 2 * self.roots.len() + 1;
        if self.failures.len() != expected_cells {
            return Err(Fault::CellCountMismatch {
                recorded: self.failures.len(),
                expected: expected_cells,
            });
        }
        let all_atoms: Vec<Atom> = self.disjuncts.iter().flatten().cloned().collect();
        check_decomposition(&self.roots, &self.open_samples, &all_atoms)?;
        for (cell, per_disjunct) in self.failures.iter().enumerate() {
            if per_disjunct.len() != self.disjuncts.len() {
                return Err(Fault::DisjunctFailureCountMismatch {
                    cell,
                    recorded: per_disjunct.len(),
                    disjuncts: self.disjuncts.len(),
                });
            }
            let sample = cell_sample_of(&self.roots, &self.open_samples, cell)
                .ok_or(Fault::Declined("cell index has no sample"))?;
            for (disjunct, failure) in per_disjunct.iter().enumerate() {
                check_cell_failure(&self.disjuncts[disjunct], cell, &sample, failure)?;
            }
        }
        Ok(())
    }
}

/// The verdict on a [`Dnf`], with its certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DnfDecision {
    /// Satisfiable, witnessed by a sample and the disjunct it satisfies.
    True(Box<DnfSampleCertificate>),
    /// Unsatisfiable, witnessed by the cell decomposition and a failing
    /// conjunct per disjunct per cell.
    False(Box<DnfRefutationCertificate>),
    /// Exact arithmetic declined. Never a verdict.
    Unknown(String),
}

impl DnfDecision {
    /// Check this decision's own certificate, returning the verdict it
    /// establishes. `Ok(None)` is a decline — there is no claim to check.
    ///
    /// # Errors
    ///
    /// The [`Fault`] naming the guard that refused the certificate.
    pub fn verify(&self) -> Result<Option<bool>, Fault> {
        match self {
            DnfDecision::True(cert) => cert.verify().map(|()| Some(true)),
            DnfDecision::False(cert) => cert.verify().map(|()| Some(false)),
            DnfDecision::Unknown(_) => Ok(None),
        }
    }
}

/// Decide `∃x. ⋁ᵢ ⋀ⱼ pᵢⱼ(x) ▷ᵢⱼ 0`.
///
/// One decomposition of ℝ, from the roots of every polynomial in every
/// disjunct; then, cell by cell, the first disjunct all of whose conjuncts hold
/// is the witness. If no cell satisfies any disjunct, the accumulated per-cell,
/// per-disjunct failures are the refutation.
///
/// ```
/// use axeyum_cas::qe::{Atom, Relation, integer_poly};
/// use axeyum_cas::qe::dnf::{Dnf, decide_exists_dnf};
///
/// // ∃x. (x² + 1 < 0) ∨ (x − 3 = 0) — true, and only through the second
/// // disjunct.
/// let formula = Dnf::new(vec![
///     vec![Atom::new(integer_poly(&[1, 0, 1]), Relation::Lt)],
///     vec![Atom::new(integer_poly(&[-3, 1]), Relation::Eq)],
/// ]);
/// let decision = decide_exists_dnf(&formula);
/// assert_eq!(decision.verify(), Ok(Some(true)));
/// ```
#[must_use]
pub fn decide_exists_dnf(formula: &Dnf) -> DnfDecision {
    let all_atoms = formula.all_atoms();
    let decomposition = match decompose(&all_atoms) {
        Ok(parts) => parts,
        Err(reason) => return DnfDecision::Unknown(reason),
    };
    let open_samples = decomposition.open_samples;
    let root_samples: Vec<SamplePoint> = decomposition
        .roots
        .iter()
        .map(|root| SamplePoint::from_isolated(&decomposition.cut, root))
        .collect();

    let cells = 2 * root_samples.len() + 1;
    let mut failures: Vec<Vec<CellFailure>> = Vec::with_capacity(cells);
    for cell in 0..cells {
        let Some(sample) = cell_sample_of(&root_samples, &open_samples, cell) else {
            return DnfDecision::Unknown(format!("cell {cell} has no sample"));
        };
        let mut cell_failures: Vec<CellFailure> = Vec::with_capacity(formula.disjuncts.len());
        for (disjunct, atoms) in formula.disjuncts.iter().enumerate() {
            let mut signs: Vec<i8> = Vec::with_capacity(atoms.len());
            for atom in atoms {
                match sign_at_sample(&atom.poly, &sample) {
                    Some(sign) => signs.push(sign),
                    None => {
                        return DnfDecision::Unknown(format!(
                            "exact sign evaluation declined in cell {cell}, disjunct {disjunct}"
                        ));
                    }
                }
            }
            match first_failure(atoms, &signs) {
                None => {
                    return DnfDecision::True(Box::new(DnfSampleCertificate {
                        disjuncts: formula.disjuncts.clone(),
                        disjunct,
                        sample,
                        signs,
                    }));
                }
                Some(failure) => cell_failures.push(failure),
            }
        }
        failures.push(cell_failures);
    }
    DnfDecision::False(Box::new(DnfRefutationCertificate {
        disjuncts: formula.disjuncts.clone(),
        roots: root_samples,
        open_samples,
        failures,
    }))
}

/// The thin, **self-checking** front door for a disjunctive existential: decide
/// and verify the certificate before answering. A decline, or a certificate the
/// checker refuses, both yield `None`.
#[must_use]
pub fn eliminate_dnf(formula: &Dnf) -> Option<bool> {
    decide_exists_dnf(formula).verify().unwrap_or(None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::qe::{Relation, integer_poly};
    use num_bigint::BigInt;

    /// `n` as a `BigRational`.
    fn int(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    fn atom(coeffs: &[i64], relation: Relation) -> Atom {
        Atom::new(integer_poly(coeffs), relation)
    }

    fn as_true(decision: DnfDecision) -> DnfSampleCertificate {
        match decision {
            DnfDecision::True(cert) => *cert,
            other => panic!("expected True, got {other:?}"),
        }
    }

    fn as_false(decision: DnfDecision) -> DnfRefutationCertificate {
        match decision {
            DnfDecision::False(cert) => *cert,
            other => panic!("expected False, got {other:?}"),
        }
    }

    // ------------------------------------------------------------- verdicts

    #[test]
    fn a_disjunction_true_only_through_its_second_disjunct_names_that_disjunct() {
        // (x² + 1 < 0) ∨ (x² − 2 = 0 ∧ x > 0): the first disjunct is
        // unsatisfiable, the second holds at +√2.
        let formula = Dnf::new(vec![
            vec![atom(&[1, 0, 1], Relation::Lt)],
            vec![atom(&[-2, 0, 1], Relation::Eq), atom(&[0, 1], Relation::Gt)],
        ]);
        let cert = as_true(decide_exists_dnf(&formula));
        assert_eq!(cert.disjunct, 1, "only the second disjunct is satisfiable");
        assert!(matches!(cert.sample, SamplePoint::Algebraic { .. }));
        assert_eq!(cert.signs, vec![0, 1]);
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate_dnf(&formula), Some(true));
    }

    #[test]
    fn a_false_two_disjunct_formula_refutes_both_disjuncts_in_every_cell() {
        // (x² + 1 < 0) ∨ (x² < 0 ∧ x > 0): neither disjunct is satisfiable
        // anywhere. `x²` contributes the single root 0, so there are 3 cells.
        let formula = Dnf::new(vec![
            vec![atom(&[1, 0, 1], Relation::Lt)],
            vec![atom(&[0, 0, 1], Relation::Lt), atom(&[0, 1], Relation::Gt)],
        ]);
        let cert = as_false(decide_exists_dnf(&formula));
        assert_eq!(cert.roots, vec![SamplePoint::Rational(int(0))]);
        assert_eq!(cert.failures.len(), 3, "2·1 + 1 cells");
        for (cell, per_disjunct) in cert.failures.iter().enumerate() {
            assert_eq!(
                per_disjunct.len(),
                2,
                "cell {cell} must refute both disjuncts"
            );
        }
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate_dnf(&formula), Some(false));
    }

    #[test]
    fn an_empty_disjunction_is_false_and_an_empty_conjunct_list_is_true() {
        assert_eq!(eliminate_dnf(&Dnf::new(Vec::new())), Some(false));
        assert_eq!(eliminate_dnf(&Dnf::new(vec![Vec::new()])), Some(true));
    }

    #[test]
    fn the_disjunction_of_two_half_lines_covers_a_point_cell_only_through_one_branch() {
        // (x < 0) ∨ (x > 0) is true; the cell decomposition has 3 cells and the
        // producer stops at the first satisfying one.
        let formula = Dnf::new(vec![
            vec![atom(&[0, 1], Relation::Lt)],
            vec![atom(&[0, 1], Relation::Gt)],
        ]);
        let cert = as_true(decide_exists_dnf(&formula));
        assert_eq!(cert.disjunct, 0);
        assert_eq!(cert.verify(), Ok(()));
    }

    // ------------------------------------------------------------ forgeries

    #[test]
    fn a_sample_that_satisfies_no_disjunct_is_refused_as_a_failing_relation() {
        // 0 satisfies neither `x < 0` nor `x > 0`, but the certificate claims
        // the second disjunct.
        let cert = DnfSampleCertificate {
            disjuncts: vec![
                vec![atom(&[0, 1], Relation::Lt)],
                vec![atom(&[0, 1], Relation::Gt)],
            ],
            disjunct: 1,
            sample: SamplePoint::Rational(int(0)),
            signs: vec![0],
        };
        assert_eq!(
            cert.verify(),
            Err(Fault::RelationFails { index: 0, sign: 0 })
        );
    }

    #[test]
    fn a_sample_naming_a_disjunct_the_formula_does_not_have_is_refused() {
        let cert = DnfSampleCertificate {
            disjuncts: vec![vec![atom(&[0, 1], Relation::Gt)]],
            disjunct: 7,
            sample: SamplePoint::Rational(int(1)),
            signs: vec![1],
        };
        assert_eq!(
            cert.verify(),
            Err(Fault::DisjunctIndexOutOfRange {
                recorded: 7,
                disjuncts: 1
            })
        );
    }

    /// A valid refutation of `(x² + 1 < 0) ∨ (x² < 0 ∧ x > 0)`, the fixture the
    /// refutation forgeries mutate.
    fn two_disjunct_refutation() -> DnfRefutationCertificate {
        let formula = Dnf::new(vec![
            vec![atom(&[1, 0, 1], Relation::Lt)],
            vec![atom(&[0, 0, 1], Relation::Lt), atom(&[0, 1], Relation::Gt)],
        ]);
        let cert = as_false(decide_exists_dnf(&formula));
        assert_eq!(cert.verify(), Ok(()));
        cert
    }

    #[test]
    fn a_refutation_cell_missing_one_disjuncts_failing_conjunct_is_refused() {
        let mut cert = two_disjunct_refutation();
        // Drop the second disjunct's failure in the middle cell. Every
        // remaining entry is still a genuine failure, and every other count is
        // still right: only the per-cell disjunct count can catch this.
        cert.failures[1].pop();
        assert_eq!(
            cert.verify(),
            Err(Fault::DisjunctFailureCountMismatch {
                cell: 1,
                recorded: 1,
                disjuncts: 2
            })
        );
    }

    #[test]
    fn a_refutation_naming_a_conjunct_that_actually_holds_is_refused() {
        let mut cert = two_disjunct_refutation();
        // In cell 2 (x > 0) the second disjunct's conjunct `x > 0` holds, so
        // nominating it — with its true sign — is a forgery.
        let sample = SamplePoint::Rational(cert.open_samples[1].clone());
        let sign = sign_at_sample(&cert.disjuncts[1][1].poly, &sample).expect("exact sign");
        cert.failures[2][1] = CellFailure { conjunct: 1, sign };
        assert_eq!(
            cert.verify(),
            Err(Fault::ConjunctDoesNotFail {
                cell: 2,
                index: 1,
                sign
            })
        );
    }

    #[test]
    fn a_refutation_that_drops_a_root_is_refused_as_an_incomplete_root_list() {
        let mut cert = two_disjunct_refutation();
        // Collapse the three cells to one by deleting the only root, keeping
        // every count self-consistent.
        cert.roots.clear();
        cert.open_samples = vec![int(-1)];
        cert.failures = vec![cert.failures[0].clone()];
        assert!(
            matches!(cert.verify(), Err(Fault::IncompleteRootList { .. })),
            "the Sturm recount must notice the missing cut point"
        );
    }

    #[test]
    fn a_refutation_with_the_wrong_number_of_cells_is_refused() {
        let mut cert = two_disjunct_refutation();
        cert.failures.pop();
        assert_eq!(
            cert.verify(),
            Err(Fault::CellCountMismatch {
                recorded: 2,
                expected: 3
            })
        );
    }

    #[test]
    fn the_decision_front_door_refuses_a_forged_certificate_rather_than_answering() {
        let mut cert = two_disjunct_refutation();
        cert.failures[0].pop();
        assert!(matches!(
            DnfDecision::False(Box::new(cert)).verify(),
            Err(Fault::DisjunctFailureCountMismatch { .. })
        ));
        assert_eq!(
            DnfDecision::Unknown("declined".to_string()).verify(),
            Ok(None)
        );
    }
}
