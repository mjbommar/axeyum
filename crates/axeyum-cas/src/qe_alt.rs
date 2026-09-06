//! The first **quantifier alternation**: `∀x ∃y. φ(x, y)` and `∃x ∀y. φ(x, y)`
//! over bivariate polynomial atoms, both certificate-carrying.
//!
//! # How an alternation is decided here
//!
//! [`crate::qe::bivariate`] eliminates the inner quantifier and returns a
//! *quantifier-free* description of the `x`-line: `2r + 1` sign-invariant cells
//! with a verdict each, merged into a union of maximal intervals with algebraic
//! endpoints. Once the inner quantifier is gone, the outer one is a question
//! about that truth set `T(x)`, and both answers are read off the same object:
//!
//! - **`∀x ∃y. ⋀ᵢ pᵢ ▷ᵢ 0`** holds iff `T(x)` is all of ℝ. The certificate is
//!   the elimination plus the claim, and the checker demands that the merged
//!   interval union be the **single** interval `(−∞, ∞)` — one interval, no
//!   finite endpoint. That is exactly "no gap and no missing point": a gap
//!   would split the union in two, and a missing point would put a finite
//!   endpoint on one of the pieces. A `false` claim carries the witness cell,
//!   its sample and its interval, and the checker re-reads that cell's verdict.
//! - **`∃x ∀y. ⋀ᵢ pᵢ ▷ᵢ 0`** is the complement of an inner existential:
//!   `∀y. ⋀ᵢ pᵢ ▷ᵢ 0` is `¬∃y. ⋁ᵢ ¬pᵢ ▷ᵢ 0`, and the negation of a conjunction
//!   is a **disjunction** — so the inner problem is a bivariate DNF, which is
//!   what [`eliminate_y_dnf`] here decides, reusing
//!   [`crate::qe::dnf::decide_exists_dnf`] fibre by fibre. `∃x ∀y` then holds
//!   iff **some** cell of that elimination is `false`, and the witness is that
//!   cell.
//!
//! Only the relations are negated, never the polynomials
//! ([`crate::qe::Relation::negate`]), so the negated formula induces literally
//! the same cell decomposition of the `x`-line as the original — the projection
//! set is a function of the polynomials alone.
//!
//! # The bivariate DNF, and why the two fibre routes differ
//!
//! [`eliminate_y_dnf`] projects `y` out of `⋁ᵢ ⋀ⱼ pᵢⱼ(x, y) ▷ᵢⱼ 0` with the
//! **same** Collins projection set as the conjunctive case, taken over every
//! polynomial of every disjunct — delineability is a statement about
//! polynomials, not about the boolean structure over them. The fibre over each
//! `x`-cell is then decided in one of two ways:
//!
//! - at a **rational** sample, by [`crate::qe::dnf::decide_exists_dnf`], which
//!   builds one decomposition of the `y`-line for the whole disjunction and
//!   whose refutation names a failing conjunct of *every* disjunct in *every*
//!   cell;
//! - at an **algebraic** sample `α`, by running [`crate::qe::fibre::decide_fibre`]
//!   **once per disjunct** over `ℚ(α)` and taking the disjunction of the
//!   verdicts. This is sound because `∃y` distributes over `∨`; it is a weaker
//!   certificate than the shared-decomposition one (there are `d` unrelated
//!   `y`-decompositions rather than one), which is precisely the quality
//!   difference [`crate::qe::dnf`] exists to record. `qe::fibre` has no
//!   disjunctive front door, so this is the honest reuse rather than a new
//!   `ℚ(α)` engine.
//!
//! # What is decided, and what is not
//!
//! **Decided.** `∀x ∃y` over a conjunction and `∃x ∀y` over a conjunction, at
//! [`crate::qe::bivariate::MAX_TOTAL_DEGREE`], including irrational cell
//! boundaries; and `∃y` over a bivariate DNF, which is the general inner step
//! both of them are built on.
//!
//! **Not decided.** Three variables under an alternation — [`crate::qe::lift`]
//! lifts a cell of the line into the plane, but its cylinder is not yet an
//! input this module can quantify over. More than one alternation. `∀x ∀y` and
//! `∃x ∃y` are not provided: they are not alternations, and the second is
//! already `some cell true` on a plain elimination.
//!
//! # Cost — ADVISORY
//!
//! An alternation costs exactly one inner elimination plus a constant: every
//! guard here reads the cell list the inner certificate already carries. The
//! rows in [`crate::qe::bivariate`] are therefore the cost of an alternation
//! too, and the `60×` penalty for an irrational boundary carries over
//! unchanged. Measured 2026-09-05, `--release`; advisory only.

use num_rational::BigRational;

use super::bivariate::{
    self, BiAtom, ExistsYFormula, FormulaCertificate, ProjectionCertificate, XInterval,
    eliminate_y_to_formula,
};
use super::dnf::{Dnf, DnfDecision, decide_exists_dnf};
use super::{Atom, SamplePoint, big, fibre};

// ============================================================================
// Faults.
// ============================================================================

/// Why an alternation, a bivariate DNF elimination, or one of their
/// certificates was refused. Every variant is a **distinct guard**;
/// [`Fault::Declined`] is the one that is not an accusation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fault {
    /// The inner elimination refused; the bivariate module's fault says why.
    Bivariate(Box<bivariate::Fault>),
    /// The recomputed projection set is not the recorded one.
    ProjectionMismatch {
        /// Polynomials recorded.
        recorded: usize,
        /// Polynomials re-derived.
        recomputed: usize,
    },
    /// The recomputed cut polynomial is not the recorded one.
    CutMismatch {
        /// The degree recorded.
        recorded: usize,
        /// The degree re-derived.
        recomputed: usize,
    },
    /// The recorded cut points are not the real roots of the projection set.
    RootsMismatch {
        /// Roots recorded.
        recorded: usize,
        /// Roots re-derived.
        recomputed: usize,
    },
    /// A recorded cut point is not the re-derived one at that position.
    RootValueMismatch {
        /// Which cut point.
        index: usize,
    },
    /// The certificate records the wrong number of cells (`2r + 1`).
    CellCountMismatch {
        /// Cells recorded.
        recorded: usize,
        /// Cells required.
        expected: usize,
    },
    /// A cell's recorded `x`-sample does not lie in that cell.
    CellSampleOutOfOrder {
        /// The offending cell.
        cell: usize,
    },
    /// A cell's fibre certificate is of the wrong kind for its sample.
    FibreKindMismatch {
        /// The offending cell.
        cell: usize,
    },
    /// A cell's fibre certificate is not about the substituted formula.
    SubstitutionMismatch {
        /// The offending cell.
        cell: usize,
        /// Which disjunct's fibre is wrong, for the `ℚ(α)` route.
        disjunct: usize,
    },
    /// An algebraic cell's fibre names a different bracket than its cut point.
    FibreBracketMismatch {
        /// The offending cell.
        cell: usize,
        /// The offending disjunct.
        disjunct: usize,
    },
    /// An algebraic cell's fibre modulus does not divide the cut polynomial.
    ModulusNotADivisor {
        /// The offending cell.
        cell: usize,
        /// The offending disjunct.
        disjunct: usize,
    },
    /// An algebraic cell does not carry exactly one fibre certificate per
    /// disjunct, so some branch of the disjunction is unaccounted for.
    DisjunctCertificateCountMismatch {
        /// The offending cell.
        cell: usize,
        /// Certificates recorded.
        recorded: usize,
        /// Disjuncts the formula has.
        disjuncts: usize,
    },
    /// A cell's recorded verdict is not the one its fibre establishes.
    CellVerdictMismatch {
        /// The offending cell.
        cell: usize,
        /// The verdict recorded.
        recorded: bool,
        /// The verdict the certificate establishes.
        recomputed: bool,
    },
    /// A cell's univariate (rational-`x`) certificate was refused.
    Univariate {
        /// The offending cell.
        cell: usize,
        /// The univariate guard that rejected.
        fault: super::Fault,
    },
    /// A cell's `ℚ(α)` fibre certificate was refused.
    Fibre {
        /// The offending cell.
        cell: usize,
        /// The offending disjunct.
        disjunct: usize,
        /// The fibre guard that rejected.
        fault: fibre::Fault,
    },
    /// The inner certificate is not about this formula, so it eliminates some
    /// other inner quantifier.
    FormulaMismatch,
    /// The inner DNF is not the negation of this `∀y` conjunction, so the
    /// complement being taken is of the wrong set.
    NegationMismatch,
    /// A `∀x` claim whose truth set is not all of ℝ: this cell is false, so the
    /// interval union has a gap or a missing point.
    CoverageIncomplete {
        /// A cell the truth set misses.
        cell: usize,
    },
    /// An `∃x ∀y` claim of **false** that this cell refutes.
    MissedWitness {
        /// The cell that witnesses the outer existential after all.
        cell: usize,
    },
    /// The claim needs a witness cell and carries none.
    MissingWitness,
    /// The witness names a cell the decomposition does not have.
    WitnessOutOfRange {
        /// The index it named.
        cell: usize,
        /// How many cells there are.
        cells: usize,
    },
    /// The witness cell's verdict is not the one the claim needs.
    WitnessNotFalse {
        /// The offending cell.
        cell: usize,
    },
    /// The witness's sample is not the sample of the cell it names.
    WitnessSampleMismatch {
        /// The offending cell.
        cell: usize,
    },
    /// The witness's interval is not the interval of the cell it names.
    WitnessIntervalMismatch {
        /// The offending cell.
        cell: usize,
    },
    /// A claim of **true** carries a counterexample witness, which no true
    /// claim has.
    WitnessOnTrueClaim,
    /// Exact arithmetic ran out of a named step budget. Not a refusal of any
    /// claim.
    Declined(String),
}

/// A bivariate fault as an alternation fault, keeping a decline a decline.
fn lift_fault(fault: bivariate::Fault) -> Fault {
    match fault {
        bivariate::Fault::Declined(reason) => Fault::Declined(reason),
        other => Fault::Bivariate(Box::new(other)),
    }
}

// ============================================================================
// `∃y` over a bivariate DNF.
// ============================================================================

/// `∃y. ⋁ᵢ ⋀ⱼ disjuncts[i][j]`, with `x` left free.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BiDnf {
    /// The disjuncts. An **empty** disjunction is `false` everywhere; an empty
    /// conjunct list inside one is `true` everywhere.
    pub disjuncts: Vec<Vec<BiAtom>>,
}

impl BiDnf {
    /// Build `∃y. ⋁ ⋀ disjuncts`.
    #[must_use]
    pub fn new(disjuncts: Vec<Vec<BiAtom>>) -> BiDnf {
        BiDnf { disjuncts }
    }

    /// Every atom of every disjunct — the population whose projection cuts the
    /// `x`-line.
    #[must_use]
    fn all_atoms(&self) -> Vec<BiAtom> {
        self.disjuncts.iter().flatten().cloned().collect()
    }
}

/// How one cell's disjunctive fibre was decided.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DnfCellFibre {
    /// The `x`-sample is rational: one decomposition of the `y`-line for the
    /// whole disjunction.
    Rational(DnfDecision),
    /// The `x`-sample is algebraic: one `ℚ(α)` fibre **per disjunct**, whose
    /// verdicts are combined with `∨`.
    Algebraic(Vec<fibre::FibreCertificate>),
}

/// The decision for one `x`-cell of a disjunctive elimination.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DnfCellCertificate {
    /// The `x` at which the fibre was decided.
    pub sample: SamplePoint,
    /// Whether `∃y. ⋁ᵢ ⋀ⱼ pᵢⱼ(sample, y) ▷ᵢⱼ 0` holds.
    pub verdict: bool,
    /// The fibre decision, certificate and all.
    pub fibre: DnfCellFibre,
}

/// The result of eliminating `y` from a bivariate DNF.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DnfProjectionCertificate {
    /// The formula this certificate is about.
    pub disjuncts: Vec<Vec<BiAtom>>,
    /// The projection set, monic and deduplicated, in a deterministic order.
    pub projection: Vec<Vec<axeyum_ir::Rational>>,
    /// The cut polynomial: the square-free part of the projection's product.
    pub cut: Vec<BigRational>,
    /// The cut points, ascending.
    pub roots: Vec<SamplePoint>,
    /// One entry per cell, interleaved `(−∞, α₀)`, `{α₀}`, `(α₀, α₁)`, ….
    pub cells: Vec<DnfCellCertificate>,
}

impl DnfProjectionCertificate {
    /// Re-derive the whole elimination from the disjuncts alone.
    ///
    /// Guards, in order: every atom is within the degree bound; the projection
    /// set, the cut polynomial and the cut points recomputed from the atoms are
    /// exactly the recorded ones; the cell count matches; every cell's sample
    /// lies in that cell in order; and every cell's fibre certificate is of the
    /// right kind, is about the substituted disjunction, and establishes the
    /// recorded verdict.
    ///
    /// # Errors
    ///
    /// The [`Fault`] naming the guard that rejected.
    pub fn verify(&self) -> Result<(), Fault> {
        let atoms = self.all_atoms();
        bivariate::check_degree_bound(&atoms).map_err(lift_fault)?;
        let projection = bivariate::projection_set(&atoms).map_err(lift_fault)?;
        if projection != self.projection {
            return Err(Fault::ProjectionMismatch {
                recorded: self.projection.len(),
                recomputed: projection.len(),
            });
        }
        let cut = bivariate::projection_cut(&projection);
        if cut != self.cut {
            return Err(Fault::CutMismatch {
                recorded: big::degree(&self.cut).unwrap_or(0),
                recomputed: big::degree(&cut).unwrap_or(0),
            });
        }
        let roots = bivariate::cut_points(&cut).map_err(lift_fault)?;
        self.check_roots(&roots)?;
        for (cell, entry) in self.cells.iter().enumerate() {
            bivariate::check_sample_in_cell(&roots, cell, &entry.sample)
                .map_err(|_| Fault::CellSampleOutOfOrder { cell })?;
            let verdict = self.check_fibre(cell, entry)?;
            if verdict != entry.verdict {
                return Err(Fault::CellVerdictMismatch {
                    cell,
                    recorded: entry.verdict,
                    recomputed: verdict,
                });
            }
        }
        Ok(())
    }

    /// Every atom of every disjunct.
    fn all_atoms(&self) -> Vec<BiAtom> {
        self.disjuncts.iter().flatten().cloned().collect()
    }

    /// The recorded cut points and the cell count.
    fn check_roots(&self, roots: &[SamplePoint]) -> Result<(), Fault> {
        if roots.len() != self.roots.len() {
            return Err(Fault::RootsMismatch {
                recorded: self.roots.len(),
                recomputed: roots.len(),
            });
        }
        for (index, root) in roots.iter().enumerate() {
            if *root != self.roots[index] {
                return Err(Fault::RootValueMismatch { index });
            }
        }
        let expected = 2 * roots.len() + 1;
        if self.cells.len() != expected {
            return Err(Fault::CellCountMismatch {
                recorded: self.cells.len(),
                expected,
            });
        }
        Ok(())
    }

    /// One cell's fibre: right kind, right formula, own verdict.
    fn check_fibre(&self, cell: usize, entry: &DnfCellCertificate) -> Result<bool, Fault> {
        match (&entry.sample, &entry.fibre) {
            (SamplePoint::Rational(x), DnfCellFibre::Rational(decision)) => {
                let substituted = self.substitute(x);
                if certificate_disjuncts(decision) != Some(substituted) {
                    return Err(Fault::SubstitutionMismatch { cell, disjunct: 0 });
                }
                decision
                    .verify()
                    .map_err(|fault| Fault::Univariate { cell, fault })?
                    .ok_or_else(|| Fault::Declined(format!("cell {cell} carries no claim")))
            }
            (
                SamplePoint::Algebraic {
                    lower,
                    upper,
                    defining_poly,
                },
                DnfCellFibre::Algebraic(certificates),
            ) => self.check_algebraic_fibre(cell, defining_poly, lower, upper, certificates),
            _ => Err(Fault::FibreKindMismatch { cell }),
        }
    }

    /// The `ℚ(α)` route: one certificate per disjunct, each about *this* `α`
    /// and *its own* disjunct, combined with `∨`.
    fn check_algebraic_fibre(
        &self,
        cell: usize,
        defining_poly: &[BigRational],
        lower: &BigRational,
        upper: &BigRational,
        certificates: &[fibre::FibreCertificate],
    ) -> Result<bool, Fault> {
        if certificates.len() != self.disjuncts.len() {
            return Err(Fault::DisjunctCertificateCountMismatch {
                cell,
                recorded: certificates.len(),
                disjuncts: self.disjuncts.len(),
            });
        }
        let mut verdict = false;
        for (disjunct, certificate) in certificates.iter().enumerate() {
            if certificate.lower != *lower || certificate.upper != *upper {
                return Err(Fault::FibreBracketMismatch { cell, disjunct });
            }
            if !bivariate::divides(&certificate.modulus, defining_poly) {
                return Err(Fault::ModulusNotADivisor { cell, disjunct });
            }
            let field = fibre::RealField::new(&certificate.modulus, lower, upper).map_err(
                |fault| Fault::Fibre {
                    cell,
                    disjunct,
                    fault,
                },
            )?;
            let substituted =
                fibre::substitute(&field, &bivariate::substitution_atoms(&self.disjuncts[disjunct]));
            if certificate.atoms != substituted {
                return Err(Fault::SubstitutionMismatch { cell, disjunct });
            }
            verdict |= certificate.verify().map_err(|fault| Fault::Fibre {
                cell,
                disjunct,
                fault,
            })?;
        }
        Ok(verdict)
    }

    /// The disjunction with `x = x₀`.
    fn substitute(&self, x: &BigRational) -> Vec<Vec<Atom>> {
        self.disjuncts
            .iter()
            .map(|atoms| bivariate::substitute_atoms(atoms, x))
            .collect()
    }

    /// The first cell whose verdict is `false`, if any.
    fn first_false_cell(&self) -> Option<usize> {
        self.cells.iter().position(|cell| !cell.verdict)
    }

    /// The first cell whose verdict is `true`, if any.
    fn first_true_cell(&self) -> Option<usize> {
        self.cells.iter().position(|cell| cell.verdict)
    }
}

/// The disjuncts a DNF decision's certificate is about, or `None` for a
/// decline.
fn certificate_disjuncts(decision: &DnfDecision) -> Option<Vec<Vec<Atom>>> {
    match decision {
        DnfDecision::True(cert) => Some(cert.disjuncts.clone()),
        DnfDecision::False(cert) => Some(cert.disjuncts.clone()),
        DnfDecision::Unknown(_) => None,
    }
}

/// Eliminate `y` from `∃y. ⋁ᵢ ⋀ⱼ pᵢⱼ(x, y) ▷ᵢⱼ 0`.
///
/// # Errors
///
/// The [`Fault`] naming the bound, the degeneracy, or the decline that stopped
/// it. A successful return is a certificate, not a bare answer: call
/// [`DnfProjectionCertificate::verify`] on it.
pub fn eliminate_y_dnf(formula: &BiDnf) -> Result<DnfProjectionCertificate, Fault> {
    let atoms = formula.all_atoms();
    bivariate::check_degree_bound(&atoms).map_err(lift_fault)?;
    let projection = bivariate::projection_set(&atoms).map_err(lift_fault)?;
    let cut = bivariate::projection_cut(&projection);
    let isolated = bivariate::isolate_cut(&cut).map_err(lift_fault)?;
    let roots: Vec<SamplePoint> = isolated
        .iter()
        .map(|root| SamplePoint::from_isolated(&cut, root))
        .collect();
    let open_samples = super::open_cell_samples(&cut, &isolated).map_err(Fault::Declined)?;

    let count = 2 * roots.len() + 1;
    let mut cells: Vec<DnfCellCertificate> = Vec::with_capacity(count);
    for cell in 0..count {
        let sample = if cell.is_multiple_of(2) {
            SamplePoint::Rational(open_samples[cell / 2].clone())
        } else {
            roots[cell / 2].clone()
        };
        cells.push(decide_dnf_cell(&formula.disjuncts, cell, sample)?);
    }
    Ok(DnfProjectionCertificate {
        disjuncts: formula.disjuncts.clone(),
        projection,
        cut,
        roots,
        cells,
    })
}

/// One cell of a disjunctive elimination.
fn decide_dnf_cell(
    disjuncts: &[Vec<BiAtom>],
    cell: usize,
    sample: SamplePoint,
) -> Result<DnfCellCertificate, Fault> {
    match &sample {
        SamplePoint::Rational(x) => {
            let substituted: Vec<Vec<Atom>> = disjuncts
                .iter()
                .map(|atoms| bivariate::substitute_atoms(atoms, x))
                .collect();
            let decision = decide_exists_dnf(&Dnf::new(substituted));
            let verdict = decision
                .verify()
                .map_err(|fault| Fault::Univariate { cell, fault })?
                .ok_or_else(|| {
                    Fault::Declined(format!("the fibre over cell {cell} could not be decided"))
                })?;
            Ok(DnfCellCertificate {
                sample,
                verdict,
                fibre: DnfCellFibre::Rational(decision),
            })
        }
        SamplePoint::Algebraic {
            defining_poly,
            lower,
            upper,
        } => {
            let mut certificates = Vec::with_capacity(disjuncts.len());
            let mut verdict = false;
            for (disjunct, atoms) in disjuncts.iter().enumerate() {
                let certificate = fibre::decide_fibre(
                    defining_poly,
                    lower,
                    upper,
                    &bivariate::substitution_atoms(atoms),
                )
                .map_err(|fault| Fault::Fibre {
                    cell,
                    disjunct,
                    fault,
                })?;
                verdict |= certificate.verdict();
                certificates.push(certificate);
            }
            Ok(DnfCellCertificate {
                sample,
                verdict,
                fibre: DnfCellFibre::Algebraic(certificates),
            })
        }
    }
}

// ============================================================================
// The alternation witnesses.
// ============================================================================

/// The cell that decides an alternation: which cell, its sample, and the
/// `x`-interval it denotes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AlternationWitness {
    /// The index of the cell in the inner elimination's cell list.
    pub cell: usize,
    /// That cell's `x`-sample.
    pub sample: SamplePoint,
    /// That cell as an interval; a point cell is a closed interval whose
    /// endpoints coincide.
    pub interval: XInterval,
}

/// `∀x ∃y. ⋀ᵢ atoms[i]`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ForallExistsFormula {
    /// The inner conjuncts.
    pub atoms: Vec<BiAtom>,
}

impl ForallExistsFormula {
    /// Build `∀x ∃y. ⋀ atoms`.
    #[must_use]
    pub fn new(atoms: Vec<BiAtom>) -> ForallExistsFormula {
        ForallExistsFormula { atoms }
    }
}

/// The decision on a `∀x ∃y` sentence, with the inner elimination it rests on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ForallExistsCertificate {
    /// The inner conjuncts this certificate is about.
    pub atoms: Vec<BiAtom>,
    /// The claim.
    pub holds: bool,
    /// The inner elimination of `∃y`, cells, intervals and all.
    pub inner: FormulaCertificate,
    /// The cell that refutes the universal; `Some` exactly when `holds` is
    /// false.
    pub witness: Option<AlternationWitness>,
}

impl ForallExistsCertificate {
    /// Re-derive the whole answer from `atoms` alone.
    ///
    /// The inner certificate is re-verified in full — projection, cut points,
    /// every cell's fibre, and the four interval guards — and then the outer
    /// quantifier is checked against it: a `true` claim demands that the merged
    /// interval union be the single interval `(−∞, ∞)`, and a `false` claim
    /// demands a witness cell whose recorded verdict really is `false` and
    /// whose sample and interval are that cell's own.
    ///
    /// # Errors
    ///
    /// The [`Fault`] naming the guard that rejected.
    pub fn verify(&self) -> Result<(), Fault> {
        self.inner.verify().map_err(lift_fault)?;
        if self.inner.projection.atoms != self.atoms {
            return Err(Fault::FormulaMismatch);
        }
        if self.holds {
            if self.witness.is_some() {
                return Err(Fault::WitnessOnTrueClaim);
            }
            if !covers_the_line(&self.inner.intervals) {
                return Err(Fault::CoverageIncomplete {
                    cell: first_false_cell(&self.inner.projection),
                });
            }
            return Ok(());
        }
        let witness = self.witness.as_ref().ok_or(Fault::MissingWitness)?;
        check_witness(&self.inner.projection, witness, false)
    }

    /// The truth set of the inner `∃y`, as the bivariate step prints it.
    #[must_use]
    pub fn describe(&self) -> String {
        self.inner.describe()
    }
}

/// `∃x ∀y. ⋀ᵢ atoms[i]`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ExistsForallFormula {
    /// The inner conjuncts, under `∀y`.
    pub atoms: Vec<BiAtom>,
}

impl ExistsForallFormula {
    /// Build `∃x ∀y. ⋀ atoms`.
    #[must_use]
    pub fn new(atoms: Vec<BiAtom>) -> ExistsForallFormula {
        ExistsForallFormula { atoms }
    }

    /// The inner negation `∃y. ⋁ᵢ ¬atoms[i]`, whose **false** cells are exactly
    /// the `x` at which `∀y. ⋀ᵢ atoms[i]` holds.
    ///
    /// Only relations are negated, so the projection set — and therefore the
    /// cell decomposition — is unchanged.
    #[must_use]
    pub fn negate(&self) -> BiDnf {
        BiDnf::new(
            self.atoms
                .iter()
                .map(|atom| vec![BiAtom::new(atom.poly.clone(), atom.relation.negate())])
                .collect(),
        )
    }
}

/// The decision on an `∃x ∀y` sentence, with the inner elimination of its
/// negation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExistsForallCertificate {
    /// The inner conjuncts, under `∀y`.
    pub atoms: Vec<BiAtom>,
    /// The claim.
    pub holds: bool,
    /// The elimination of `∃y. ⋁ᵢ ¬atoms[i]`.
    pub inner: DnfProjectionCertificate,
    /// The cell at which `∀y` holds; `Some` exactly when `holds` is true.
    pub witness: Option<AlternationWitness>,
}

impl ExistsForallCertificate {
    /// Re-derive the whole answer from `atoms` alone.
    ///
    /// Guards: the inner DNF elimination re-verifies; the formula it eliminated
    /// is **the negation of this one** ([`Fault::NegationMismatch`] — the guard
    /// that stops a complement being taken of the wrong set); and then a `true`
    /// claim demands a witness cell whose inner verdict is `false` (no `y`
    /// falsifies the conjunction there), while a `false` claim demands that
    /// **every** inner cell be true.
    ///
    /// # Errors
    ///
    /// The [`Fault`] naming the guard that rejected.
    pub fn verify(&self) -> Result<(), Fault> {
        self.inner.verify()?;
        let expected = ExistsForallFormula::new(self.atoms.clone()).negate();
        if self.inner.disjuncts != expected.disjuncts {
            return Err(Fault::NegationMismatch);
        }
        if self.holds {
            let witness = self.witness.as_ref().ok_or(Fault::MissingWitness)?;
            return check_dnf_witness(&self.inner, witness);
        }
        if self.witness.is_some() {
            return Err(Fault::WitnessOnTrueClaim);
        }
        match self.inner.first_false_cell() {
            Some(cell) => Err(Fault::MissedWitness { cell }),
            None => Ok(()),
        }
    }
}

/// The interval union is the whole line: one interval, both endpoints
/// infinite. A gap would split it in two; a missing point would give one of
/// the pieces a finite endpoint.
fn covers_the_line(intervals: &[XInterval]) -> bool {
    intervals.len() == 1 && intervals[0].lower.is_none() && intervals[0].upper.is_none()
}

/// The first false cell of a conjunctive elimination, or `0` when there is
/// none — the index a coverage fault reports.
fn first_false_cell(projection: &ProjectionCertificate) -> usize {
    projection
        .cells
        .iter()
        .position(|cell| !cell.verdict)
        .unwrap_or(0)
}

/// The witness names a real cell, with the required verdict, its own sample and
/// its own interval.
fn check_witness(
    projection: &ProjectionCertificate,
    witness: &AlternationWitness,
    required: bool,
) -> Result<(), Fault> {
    let Some(cell) = projection.cells.get(witness.cell) else {
        return Err(Fault::WitnessOutOfRange {
            cell: witness.cell,
            cells: projection.cells.len(),
        });
    };
    if cell.verdict != required {
        return Err(Fault::WitnessNotFalse { cell: witness.cell });
    }
    if cell.sample != witness.sample {
        return Err(Fault::WitnessSampleMismatch { cell: witness.cell });
    }
    if projection.interval_of_run(witness.cell, witness.cell) != witness.interval {
        return Err(Fault::WitnessIntervalMismatch { cell: witness.cell });
    }
    Ok(())
}

/// The same, against a disjunctive elimination: the witness cell must be
/// **false**, which is where the negated inner formula fails and therefore
/// where `∀y` holds.
fn check_dnf_witness(
    inner: &DnfProjectionCertificate,
    witness: &AlternationWitness,
) -> Result<(), Fault> {
    let Some(cell) = inner.cells.get(witness.cell) else {
        return Err(Fault::WitnessOutOfRange {
            cell: witness.cell,
            cells: inner.cells.len(),
        });
    };
    if cell.verdict {
        return Err(Fault::WitnessNotFalse { cell: witness.cell });
    }
    if cell.sample != witness.sample {
        return Err(Fault::WitnessSampleMismatch { cell: witness.cell });
    }
    if interval_of_cell(&inner.roots, witness.cell) != witness.interval {
        return Err(Fault::WitnessIntervalMismatch { cell: witness.cell });
    }
    Ok(())
}

/// One cell of a cut-point list as an interval: an open cell between its
/// neighbours, a point cell as a closed interval whose endpoints coincide.
fn interval_of_cell(roots: &[SamplePoint], cell: usize) -> XInterval {
    if cell.is_multiple_of(2) {
        let k = cell / 2;
        XInterval {
            lower: if k == 0 {
                None
            } else {
                Some(roots[k - 1].clone())
            },
            lower_closed: false,
            upper: if k == roots.len() {
                None
            } else {
                Some(roots[k].clone())
            },
            upper_closed: false,
        }
    } else {
        let point = roots[cell / 2].clone();
        XInterval {
            lower: Some(point.clone()),
            lower_closed: true,
            upper: Some(point),
            upper_closed: true,
        }
    }
}

// ============================================================================
// The producers.
// ============================================================================

/// Decide `∀x ∃y. ⋀ᵢ pᵢ(x, y) ▷ᵢ 0`.
///
/// ```
/// use axeyum_cas::qe::Relation;
/// use axeyum_cas::qe::bivariate::BiAtom;
/// use axeyum_cas::qe::alt::{ForallExistsFormula, decide_forall_exists};
/// use axeyum_ir::Rational;
///
/// // ∀x ∃y. y² − x² = 0 — true, at y = ±x.
/// let zero = Rational::zero();
/// let one = Rational::integer(1);
/// let minus_one = Rational::integer(-1);
/// let atom = BiAtom::new(
///     vec![vec![zero, zero, minus_one], vec![zero], vec![one]],
///     Relation::Eq,
/// );
/// let certificate =
///     decide_forall_exists(&ForallExistsFormula::new(vec![atom])).unwrap();
/// certificate.verify().unwrap();
/// assert!(certificate.holds);
/// ```
///
/// # Errors
///
/// The [`Fault`] that stopped the inner elimination. A successful return is a
/// certificate, not a bare answer: call [`ForallExistsCertificate::verify`].
pub fn decide_forall_exists(
    formula: &ForallExistsFormula,
) -> Result<ForallExistsCertificate, Fault> {
    let inner = eliminate_y_to_formula(&ExistsYFormula::new(formula.atoms.clone()))
        .map_err(lift_fault)?;
    let false_cell = inner.projection.cells.iter().position(|cell| !cell.verdict);
    let (holds, witness) = match false_cell {
        None => (true, None),
        Some(cell) => (
            false,
            Some(AlternationWitness {
                cell,
                sample: inner.projection.cells[cell].sample.clone(),
                interval: inner.projection.interval_of_run(cell, cell),
            }),
        ),
    };
    Ok(ForallExistsCertificate {
        atoms: formula.atoms.clone(),
        holds,
        inner,
        witness,
    })
}

/// Decide `∃x ∀y. ⋀ᵢ pᵢ(x, y) ▷ᵢ 0`, by eliminating `y` from the negated
/// disjunction and looking for a cell where **it** fails.
///
/// # Errors
///
/// The [`Fault`] that stopped the inner elimination. A successful return is a
/// certificate, not a bare answer: call [`ExistsForallCertificate::verify`].
pub fn decide_exists_forall(
    formula: &ExistsForallFormula,
) -> Result<ExistsForallCertificate, Fault> {
    let inner = eliminate_y_dnf(&formula.negate())?;
    let (holds, witness) = match inner.first_false_cell() {
        None => (false, None),
        Some(cell) => (
            true,
            Some(AlternationWitness {
                cell,
                sample: inner.cells[cell].sample.clone(),
                interval: interval_of_cell(&inner.roots, cell),
            }),
        ),
    };
    Ok(ExistsForallCertificate {
        atoms: formula.atoms.clone(),
        holds,
        inner,
        witness,
    })
}

/// The self-checking front door for `∀x ∃y`: decide, verify the certificate,
/// and answer only if the checker accepted it.
///
/// # Errors
///
/// The [`Fault`] that stopped the producer, or the guard that refused its own
/// certificate.
pub fn eliminate_forall_exists(formula: &ForallExistsFormula) -> Result<bool, Fault> {
    let certificate = decide_forall_exists(formula)?;
    certificate.verify()?;
    Ok(certificate.holds)
}

/// The self-checking front door for `∃x ∀y`.
///
/// # Errors
///
/// The [`Fault`] that stopped the producer, or the guard that refused its own
/// certificate.
pub fn eliminate_exists_forall(formula: &ExistsForallFormula) -> Result<bool, Fault> {
    let certificate = decide_exists_forall(formula)?;
    certificate.verify()?;
    Ok(certificate.holds)
}

/// The first cell of a disjunctive elimination whose verdict is `true` — the
/// helper a caller uses to report where an inner existential succeeded.
#[must_use]
pub fn first_satisfied_cell(certificate: &DnfProjectionCertificate) -> Option<usize> {
    certificate.first_true_cell()
}
#[cfg(test)]
mod tests {
    use super::*;
    use crate::qe::Relation;
    use crate::qe::dnf::DnfDecision;
    use axeyum_ir::Rational;
    use num_traits::Zero;

    // ------------------------------------------------------------------
    // Shapes.
    // ------------------------------------------------------------------

    /// A bivariate atom from monomials `(coefficient, x-power, y-power)`.
    fn bi_terms(terms: &[(i64, usize, usize)], relation: Relation) -> BiAtom {
        let mut poly: Vec<Vec<Rational>> = Vec::new();
        for &(coefficient, x_power, y_power) in terms {
            if poly.len() <= y_power {
                poly.resize(y_power + 1, Vec::new());
            }
            let row = &mut poly[y_power];
            if row.len() <= x_power {
                row.resize(x_power + 1, Rational::zero());
            }
            row[x_power] = row[x_power]
                .checked_add(Rational::integer(i128::from(coefficient)))
                .expect("small integer coefficients");
        }
        BiAtom::new(poly, relation)
    }

    /// `y² = x²`.
    fn squares() -> BiAtom {
        bi_terms(&[(1, 0, 2), (-1, 2, 0)], Relation::Eq)
    }

    /// `y² = x`.
    fn square_root() -> BiAtom {
        bi_terms(&[(1, 0, 2), (-1, 1, 0)], Relation::Eq)
    }

    /// `y² ≥ x`.
    fn dominates() -> BiAtom {
        bi_terms(&[(1, 0, 2), (-1, 1, 0)], Relation::Ge)
    }

    /// `y² < x`.
    fn below() -> BiAtom {
        bi_terms(&[(1, 0, 2), (-1, 1, 0)], Relation::Lt)
    }

    /// `x·y = 1`.
    fn hyperbola() -> BiAtom {
        bi_terms(&[(1, 1, 1), (-1, 0, 0)], Relation::Eq)
    }

    /// `x² + y² = 2`, whose cut points `±√2` are irrational.
    fn circle() -> BiAtom {
        bi_terms(&[(1, 0, 2), (1, 2, 0), (-2, 0, 0)], Relation::Eq)
    }

    fn forall_exists(atom: BiAtom) -> ForallExistsCertificate {
        let certificate = decide_forall_exists(&ForallExistsFormula::new(vec![atom]))
            .expect("the inner elimination decides this shape");
        certificate.verify().expect("its own checker accepts it");
        certificate
    }

    fn exists_forall(atom: BiAtom) -> ExistsForallCertificate {
        let certificate = decide_exists_forall(&ExistsForallFormula::new(vec![atom]))
            .expect("the inner elimination decides this shape");
        certificate.verify().expect("its own checker accepts it");
        certificate
    }

    /// The `∃y` elimination of `y² = x`, three cells verdicted `F, T, T`.
    fn root_dnf() -> DnfProjectionCertificate {
        eliminate_y_dnf(&BiDnf::new(vec![vec![square_root()]])).expect("decides")
    }

    /// The `∃y` elimination of `x² + y² = 2`, whose point cells are algebraic.
    /// Not pre-verified: the forgery tests that use it pay for one `verify`,
    /// not two.
    fn circle_dnf() -> DnfProjectionCertificate {
        eliminate_y_dnf(&BiDnf::new(vec![vec![circle()]])).expect("decides")
    }

    fn verdicts(certificate: &DnfProjectionCertificate) -> Vec<bool> {
        certificate.cells.iter().map(|cell| cell.verdict).collect()
    }

    fn rational(value: i64) -> num_rational::BigRational {
        num_rational::BigRational::from_integer(num_bigint::BigInt::from(value))
    }

    // ------------------------------------------------------------------
    // `∀x ∃y`.
    // ------------------------------------------------------------------

    #[test]
    fn forall_x_exists_y_with_matching_squares_holds() {
        let certificate = forall_exists(squares());
        assert!(certificate.holds);
        assert!(certificate.witness.is_none());
        // The truth set is the whole line, in one interval.
        assert_eq!(certificate.describe(), "x ∈ (-∞, ∞)");
        assert_eq!(certificate.inner.intervals.len(), 1);
        assert!(covers_the_line(&certificate.inner.intervals));
        assert_eq!(eliminate_forall_exists(&ForallExistsFormula::new(vec![squares()])), Ok(true));
    }

    #[test]
    fn forall_x_exists_y_square_root_fails_below_zero() {
        let certificate = forall_exists(square_root());
        assert!(!certificate.holds);
        // The inner truth set is [0, ∞); the witness is the cell x < 0.
        assert_eq!(certificate.describe(), "x ∈ [0, ∞)");
        let witness = certificate.witness.as_ref().expect("a false claim has one");
        assert_eq!(witness.cell, 0);
        assert_eq!(
            witness.interval,
            XInterval {
                lower: None,
                lower_closed: false,
                upper: Some(SamplePoint::Rational(rational(0))),
                upper_closed: false,
            }
        );
        assert_eq!(
            eliminate_forall_exists(&ForallExistsFormula::new(vec![square_root()])),
            Ok(false)
        );
    }

    #[test]
    fn forall_x_exists_y_reciprocal_fails_at_a_point_cell() {
        let certificate = forall_exists(hyperbola());
        assert!(!certificate.holds);
        // The gap is the single point x = 0 — a point cell, not an interval.
        assert_eq!(certificate.describe(), "x ∈ (-∞, 0) ∪ (0, ∞)");
        let witness = certificate.witness.as_ref().expect("a false claim has one");
        assert_eq!(witness.cell, 1);
        assert_eq!(witness.sample, SamplePoint::Rational(rational(0)));
        assert_eq!(
            witness.interval,
            XInterval {
                lower: Some(SamplePoint::Rational(rational(0))),
                lower_closed: true,
                upper: Some(SamplePoint::Rational(rational(0))),
                upper_closed: true,
            }
        );
    }

    // ------------------------------------------------------------------
    // `∃x ∀y`.
    // ------------------------------------------------------------------

    #[test]
    fn exists_x_forall_y_square_dominates_holds_below_zero() {
        let certificate = exists_forall(dominates());
        assert!(certificate.holds);
        // The negated inner formula ∃y. y² < x is false exactly on x ≤ 0, and
        // those are the cells where ∀y. y² ≥ x holds.
        assert_eq!(verdicts(&certificate.inner), vec![false, false, true]);
        let witness = certificate.witness.as_ref().expect("a true claim has one");
        assert_eq!(witness.cell, 0);
        assert_eq!(
            witness.interval,
            XInterval {
                lower: None,
                lower_closed: false,
                upper: Some(SamplePoint::Rational(rational(0))),
                upper_closed: false,
            }
        );
        assert_eq!(
            eliminate_exists_forall(&ExistsForallFormula::new(vec![dominates()])),
            Ok(true)
        );
    }

    #[test]
    fn exists_x_forall_y_square_below_never_holds() {
        let certificate = exists_forall(below());
        assert!(!certificate.holds);
        assert!(certificate.witness.is_none());
        // Every cell of the negated elimination is satisfied, so no x survives.
        assert_eq!(verdicts(&certificate.inner), vec![true, true, true]);
    }

    #[test]
    fn only_relations_are_negated() {
        let formula = ExistsForallFormula::new(vec![dominates()]);
        let negated = formula.negate();
        assert_eq!(negated.disjuncts.len(), 1);
        assert_eq!(negated.disjuncts[0][0].poly, dominates().poly);
        assert_eq!(negated.disjuncts[0][0].relation, Relation::Lt);
    }

    // ------------------------------------------------------------------
    // The bivariate DNF elimination itself.
    // ------------------------------------------------------------------

    #[test]
    fn a_disjunction_over_an_irrational_boundary_is_decided_per_disjunct() {
        let certificate = circle_dnf();
        certificate.verify().expect("its own checker accepts it");
        assert_eq!(certificate.roots.len(), 2);
        assert!(
            certificate
                .roots
                .iter()
                .all(|root| matches!(root, SamplePoint::Algebraic { .. }))
        );
        assert_eq!(verdicts(&certificate), vec![false, true, true, true, false]);
        assert!(matches!(
            certificate.cells[1].fibre,
            DnfCellFibre::Algebraic(_)
        ));
        assert_eq!(first_satisfied_cell(&certificate), Some(1));
    }

    #[test]
    fn a_two_branch_disjunction_is_the_union_of_its_branches() {
        // (y² = x) ∨ (y·x = 1): true for x ≥ 0 from the first disjunct and for
        // x ≠ 0 from the second, so the union is the whole line. The cut is
        // x·(1 − x³) — the second factor is the resultant of the two atoms —
        // so the line is cut at 0 and 1 even though no verdict changes there.
        let formula = BiDnf::new(vec![vec![square_root()], vec![hyperbola()]]);
        let certificate = eliminate_y_dnf(&formula).expect("decides");
        certificate.verify().expect("accepted");
        assert_eq!(certificate.roots.len(), 2);
        assert_eq!(verdicts(&certificate), vec![true; 5]);
    }

    // ------------------------------------------------------------------
    // Forged certificates: one test per guard.
    // ------------------------------------------------------------------

    #[test]
    fn a_degree_bound_violation_is_reported_as_the_bivariate_fault() {
        let atom = bi_terms(&[(1, 3, 2), (1, 0, 0)], Relation::Eq);
        assert!(matches!(
            decide_forall_exists(&ForallExistsFormula::new(vec![atom])),
            Err(Fault::Bivariate(_))
        ));
    }

    #[test]
    fn a_forged_projection_set_is_refused() {
        let mut certificate = root_dnf();
        certificate.projection.clear();
        assert!(matches!(
            certificate.verify(),
            Err(Fault::ProjectionMismatch { .. })
        ));
    }

    #[test]
    fn a_forged_cut_polynomial_is_refused() {
        let mut certificate = root_dnf();
        certificate.cut.push(rational(1));
        assert!(matches!(
            certificate.verify(),
            Err(Fault::CutMismatch { .. })
        ));
    }

    #[test]
    fn a_dropped_cut_point_is_refused() {
        let mut certificate = root_dnf();
        certificate.roots.clear();
        assert!(matches!(
            certificate.verify(),
            Err(Fault::RootsMismatch { .. })
        ));
    }

    #[test]
    fn a_moved_cut_point_is_refused() {
        let mut certificate = root_dnf();
        certificate.roots[0] = SamplePoint::Rational(rational(4));
        assert_eq!(
            certificate.verify(),
            Err(Fault::RootValueMismatch { index: 0 })
        );
    }

    #[test]
    fn a_missing_cell_is_refused() {
        let mut certificate = root_dnf();
        certificate.cells.pop();
        assert!(matches!(
            certificate.verify(),
            Err(Fault::CellCountMismatch { .. })
        ));
    }

    #[test]
    fn a_sample_outside_its_cell_is_refused() {
        let mut certificate = root_dnf();
        certificate.cells[0].sample = SamplePoint::Rational(rational(3));
        assert_eq!(
            certificate.verify(),
            Err(Fault::CellSampleOutOfOrder { cell: 0 })
        );
    }

    #[test]
    fn a_fibre_for_another_sample_is_refused() {
        let mut certificate = root_dnf();
        let borrowed = certificate.cells[0].fibre.clone();
        certificate.cells[2].fibre = borrowed;
        assert_eq!(
            certificate.verify(),
            Err(Fault::SubstitutionMismatch {
                cell: 2,
                disjunct: 0
            })
        );
    }

    #[test]
    fn a_flipped_verdict_is_refused() {
        let mut certificate = root_dnf();
        certificate.cells[0].verdict = true;
        assert!(matches!(
            certificate.verify(),
            Err(Fault::CellVerdictMismatch { cell: 0, .. })
        ));
    }

    #[test]
    fn a_forged_sign_inside_a_rational_fibre_is_refused() {
        let mut certificate = root_dnf();
        if let DnfCellFibre::Rational(DnfDecision::False(refutation)) =
            &mut certificate.cells[0].fibre
        {
            refutation.failures[0][0].sign = -refutation.failures[0][0].sign;
        } else {
            panic!("cell 0 of y² = x is refuted");
        }
        assert!(matches!(
            certificate.verify(),
            Err(Fault::Univariate { cell: 0, .. })
        ));
    }

    #[test]
    fn a_rational_fibre_on_an_algebraic_sample_is_refused() {
        let mut certificate = circle_dnf();
        let borrowed = certificate.cells[0].fibre.clone();
        certificate.cells[1].fibre = borrowed;
        assert_eq!(
            certificate.verify(),
            Err(Fault::FibreKindMismatch { cell: 1 })
        );
    }

    #[test]
    fn a_missing_per_disjunct_fibre_is_refused() {
        let mut certificate = circle_dnf();
        if let DnfCellFibre::Algebraic(fibres) = &mut certificate.cells[1].fibre {
            fibres.clear();
        }
        assert_eq!(
            certificate.verify(),
            Err(Fault::DisjunctCertificateCountMismatch {
                cell: 1,
                recorded: 0,
                disjuncts: 1,
            })
        );
    }

    #[test]
    fn an_algebraic_fibre_about_another_bracket_is_refused() {
        let mut certificate = circle_dnf();
        if let DnfCellFibre::Algebraic(fibres) = &mut certificate.cells[1].fibre {
            fibres[0].lower -= rational(1);
        }
        assert_eq!(
            certificate.verify(),
            Err(Fault::FibreBracketMismatch {
                cell: 1,
                disjunct: 0
            })
        );
    }

    #[test]
    fn an_algebraic_fibre_whose_modulus_is_not_a_divisor_is_refused() {
        let mut certificate = circle_dnf();
        if let DnfCellFibre::Algebraic(fibres) = &mut certificate.cells[1].fibre {
            fibres[0].modulus = vec![rational(1), rational(0), rational(1)];
        }
        assert_eq!(
            certificate.verify(),
            Err(Fault::ModulusNotADivisor {
                cell: 1,
                disjunct: 0
            })
        );
    }

    #[test]
    fn a_forged_sign_inside_an_algebraic_fibre_is_refused() {
        let mut certificate = circle_dnf();
        if let DnfCellFibre::Algebraic(fibres) = &mut certificate.cells[1].fibre {
            if let fibre::FibreDecision::True(witness) = &mut fibres[0].decision {
                witness.signs[0] = 1;
            } else {
                panic!("x = −√2 has the solution y = 0");
            }
        }
        assert!(matches!(
            certificate.verify(),
            Err(Fault::Fibre {
                cell: 1,
                disjunct: 0,
                ..
            })
        ));
    }

    // ------------------------------------------------------------------
    // Forged alternations.
    // ------------------------------------------------------------------

    #[test]
    fn forged_coverage_is_refused() {
        // `∀x ∃y. y² = x` is false; claiming otherwise leaves a truth set that
        // is not the whole line.
        let mut certificate = forall_exists(square_root());
        certificate.holds = true;
        certificate.witness = None;
        assert_eq!(
            certificate.verify(),
            Err(Fault::CoverageIncomplete { cell: 0 })
        );
    }

    #[test]
    fn a_witness_on_a_true_claim_is_refused() {
        let mut certificate = forall_exists(squares());
        certificate.witness = Some(AlternationWitness {
            cell: 0,
            sample: certificate.inner.projection.cells[0].sample.clone(),
            interval: certificate.inner.projection.interval_of_run(0, 0),
        });
        assert_eq!(certificate.verify(), Err(Fault::WitnessOnTrueClaim));
    }

    #[test]
    fn a_missing_witness_is_refused() {
        let mut certificate = forall_exists(square_root());
        certificate.witness = None;
        assert_eq!(certificate.verify(), Err(Fault::MissingWitness));
    }

    #[test]
    fn a_witness_out_of_range_is_refused() {
        let mut certificate = forall_exists(square_root());
        if let Some(witness) = certificate.witness.as_mut() {
            witness.cell = 9;
        }
        assert_eq!(
            certificate.verify(),
            Err(Fault::WitnessOutOfRange { cell: 9, cells: 3 })
        );
    }

    #[test]
    fn a_witness_on_a_satisfied_cell_is_refused() {
        let mut certificate = forall_exists(square_root());
        if let Some(witness) = certificate.witness.as_mut() {
            witness.cell = 2; // x > 0, where ∃y really does hold
        }
        assert_eq!(certificate.verify(), Err(Fault::WitnessNotFalse { cell: 2 }));
    }

    #[test]
    fn a_witness_with_another_sample_is_refused() {
        let mut certificate = forall_exists(square_root());
        if let Some(witness) = certificate.witness.as_mut() {
            witness.sample = SamplePoint::Rational(rational(-5));
        }
        assert_eq!(
            certificate.verify(),
            Err(Fault::WitnessSampleMismatch { cell: 0 })
        );
    }

    #[test]
    fn a_witness_with_another_interval_is_refused() {
        let mut certificate = forall_exists(square_root());
        if let Some(witness) = certificate.witness.as_mut() {
            witness.interval.upper = None;
        }
        assert_eq!(
            certificate.verify(),
            Err(Fault::WitnessIntervalMismatch { cell: 0 })
        );
    }

    #[test]
    fn an_inner_elimination_of_another_formula_is_refused() {
        let mut certificate = forall_exists(square_root());
        certificate.atoms = vec![squares()];
        assert_eq!(certificate.verify(), Err(Fault::FormulaMismatch));
    }

    #[test]
    fn a_complement_of_the_wrong_set_is_refused() {
        let mut certificate = exists_forall(dominates());
        // The inner DNF is the negation of `y² ≥ x`; claim it is the negation
        // of `y² < x` instead.
        certificate.atoms = vec![below()];
        assert_eq!(certificate.verify(), Err(Fault::NegationMismatch));
    }

    #[test]
    fn a_false_exists_forall_claim_with_a_surviving_cell_is_refused() {
        let mut certificate = exists_forall(dominates());
        certificate.holds = false;
        certificate.witness = None;
        assert_eq!(certificate.verify(), Err(Fault::MissedWitness { cell: 0 }));
    }

    #[test]
    fn an_exists_forall_witness_on_a_satisfied_cell_is_refused() {
        let mut certificate = exists_forall(dominates());
        if let Some(witness) = certificate.witness.as_mut() {
            witness.cell = 2; // where ∃y. y² < x holds, so ∀y does not
        }
        assert_eq!(certificate.verify(), Err(Fault::WitnessNotFalse { cell: 2 }));
    }

    #[test]
    fn an_exists_forall_witness_with_another_sample_is_refused() {
        let mut certificate = exists_forall(dominates());
        if let Some(witness) = certificate.witness.as_mut() {
            witness.sample = SamplePoint::Rational(rational(-7));
        }
        assert_eq!(
            certificate.verify(),
            Err(Fault::WitnessSampleMismatch { cell: 0 })
        );
    }

    #[test]
    fn an_exists_forall_witness_with_another_interval_is_refused() {
        let mut certificate = exists_forall(dominates());
        if let Some(witness) = certificate.witness.as_mut() {
            witness.interval.lower_closed = true;
        }
        assert_eq!(
            certificate.verify(),
            Err(Fault::WitnessIntervalMismatch { cell: 0 })
        );
    }

    #[test]
    fn an_exists_forall_witness_out_of_range_is_refused() {
        let mut certificate = exists_forall(dominates());
        if let Some(witness) = certificate.witness.as_mut() {
            witness.cell = 11;
        }
        assert_eq!(
            certificate.verify(),
            Err(Fault::WitnessOutOfRange {
                cell: 11,
                cells: 3
            })
        );
    }

    #[test]
    fn an_exists_forall_witness_on_a_true_claim_of_false_is_refused() {
        let mut certificate = exists_forall(below());
        certificate.witness = Some(AlternationWitness {
            cell: 0,
            sample: certificate.inner.cells[0].sample.clone(),
            interval: interval_of_cell(&certificate.inner.roots, 0),
        });
        assert_eq!(certificate.verify(), Err(Fault::WitnessOnTrueClaim));
    }

    #[test]
    fn an_exists_forall_claim_of_true_needs_a_witness() {
        let mut certificate = exists_forall(dominates());
        certificate.witness = None;
        assert_eq!(certificate.verify(), Err(Fault::MissingWitness));
    }
}
