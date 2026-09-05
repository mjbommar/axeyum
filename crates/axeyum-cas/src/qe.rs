//! Real quantifier elimination for the **univariate** fragment, with
//! sample-point certificates.
//!
//! # What is decided
//!
//! One quantifier, one variable, polynomial atoms with rational coefficients:
//!
//! - [`ExistsFormula`] — `∃x. ⋀ᵢ pᵢ(x) ▷ᵢ 0` with `▷ ∈ {=, ≠, <, ≤, >, ≥}`,
//!   decided by [`decide_exists`];
//! - [`ForallFormula`] — `∀x. ⋁ᵢ pᵢ(x) ▷ᵢ 0`, decided by [`decide_forall`]
//!   through the De Morgan dual (the negation table is on
//!   [`Relation::negate`]);
//! - [`eliminate`] is the thin, self-checking front door: it decides and then
//!   *verifies its own certificate* before returning a `bool`.
//!
//! The method is the sign-invariant cell decomposition of ℝ. The real roots of
//! every `pᵢ` cut the line into finitely many cells — the roots themselves
//! (point cells) and the open intervals between and beyond them. Inside one
//! cell no `pᵢ` changes sign, so the whole conjunction has a constant truth
//! value there, and testing one sample per cell decides the sentence. A `true`
//! answer is witnessed by the satisfying sample ([`SampleCertificate`]); a
//! `false` answer is witnessed by the whole decomposition together with, for
//! every cell, a conjunct that fails in it ([`RefutationCertificate`]).
//!
//! # What is **not** decided
//!
//! - **Multivariate** formulas — nothing here builds a projection operator.
//! - **CAD.** Low-dimensional cylindrical algebraic decomposition is the next
//!   slice of this item and is deliberately absent; a univariate cell
//!   decomposition is CAD in dimension one and nothing more.
//! - **Quantifier alternation.** `∃x∀y` has no representation here; the
//!   formula types carry a single implicit variable.
//! - **Transcendental atoms** (`sin`, `exp`, …). Atoms are polynomials.
//! - **Disjunction under `∃`** (and the dual, conjunction under `∀`). A
//!   disjunctive existential is decided by running [`decide_exists`] on each
//!   disjunct, but that loop is the caller's, because a single certificate for
//!   the disjunction would have to name which disjunct it certifies and this
//!   slice does not define that object.
//!
//! # Certificates
//!
//! Both certificates are **data, not a trace**: each carries the formula it
//! speaks about, and its `verify` re-derives every claim from the polynomials
//! alone — it re-isolates roots, recomputes every sign, and re-checks every
//! relation. Nothing produced by the search is trusted. A `verify` failure is
//! reported as a [`Fault`] naming the specific guard that rejected, so a forged
//! certificate is refused with a reason rather than a bare `false`.
//!
//! # Exactness
//!
//! No floating point. Signs at rational samples are computed by Horner
//! evaluation over `BigRational`, so a high-degree polynomial at a
//! fine-denominator sample cannot overflow. Signs at algebraic samples go
//! through [`axeyum_ir::RealAlgebraic::sign_at_big`], which is bignum
//! throughout. The only `i128` arithmetic left is inside the **reused** root
//! isolation ([`crate::sturm`], [`crate::algebraic`]), which reports overflow
//! as `None`; that becomes [`Decision::Unknown`], never a verdict.
//!
//! # What this module reuses
//!
//! - [`crate::algebraic::real_roots`] — irreducible factorization over ℚ plus
//!   Sturm isolation, giving every real root of every atom as an
//!   [`AlgebraicReal`] (minimal polynomial + isolating bracket).
//! - [`crate::sturm::count_real_roots_in`] — the checker's independent
//!   re-derivation of "this bracket isolates exactly one root" and of "the
//!   recorded root list is complete".
//! - [`crate::algebraic::AlgebraicReal::refine`] — bracket separation, to find
//!   a rational strictly between two consecutive roots.
//! - [`crate::real_algebraic::from_algebraic_real`] and
//!   [`crate::real_algebraic::algebraic_cmp`] — the exact ordering of two
//!   algebraic numbers, used only as the fallback when the cheap bracket tests
//!   do not settle it.
//! - [`axeyum_ir::RealAlgebraic::sign_at_big`] and
//!   [`axeyum_ir::RealAlgebraic::compare_rational`] — the exact sign of a
//!   polynomial at an algebraic number, and the exact position of an algebraic
//!   number relative to a rational.
//!
//! Root isolation and sign evaluation at an algebraic point are **not**
//! re-implemented here.
//!
//! # Cost profile
//!
//! Not measured. The shape is: one irreducible factorization plus one Sturm
//! isolation per atom, then `2r + 1` cells for `r` distinct roots, each cell
//! costing one sign evaluation per atom. The sign at an *algebraic* sample
//! dominates — it is a polynomial-division test plus bracket refinement in
//! bignum — so the practical limit is the degree at which
//! [`crate::factor_univariate_over_q`] and the `i128` Sturm chain decline, not
//! anything in this module.

use core::cmp::Ordering;

use axeyum_ir::{Rational, RealAlgebraic, Sign};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::algebraic::{self, AlgebraicReal};
use crate::real_algebraic;
use crate::sturm;

/// How many alternating bisections we will spend separating two consecutive
/// roots before declining. Each step halves the target width, and the brackets
/// are `i128` rationals, so the denominators cannot survive many more than this
/// anyway — [`AlgebraicReal::refine`] declines first.
const MAX_SEPARATION_STEPS: usize = 60;

// ============================================================================
// The fragment: atoms and formulas.
// ============================================================================

/// The comparison in an atom `p(x) ▷ 0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Relation {
    /// `p(x) = 0`
    Eq,
    /// `p(x) ≠ 0`
    Ne,
    /// `p(x) < 0`
    Lt,
    /// `p(x) ≤ 0`
    Le,
    /// `p(x) > 0`
    Gt,
    /// `p(x) ≥ 0`
    Ge,
}

impl Relation {
    /// The logical negation of this relation — the **sign-flip table** that
    /// turns `∀x. ⋁ᵢ pᵢ ▷ᵢ 0` into `¬∃x. ⋀ᵢ pᵢ ▷̄ᵢ 0`:
    ///
    /// | relation | negated |
    /// |---|---|
    /// | `=` | `≠` |
    /// | `≠` | `=` |
    /// | `<` | `≥` |
    /// | `≤` | `>` |
    /// | `>` | `≤` |
    /// | `≥` | `<` |
    ///
    /// Note that the polynomial is untouched: negating the *relation* is
    /// enough, so no atom is ever rewritten and the cell decomposition of the
    /// dual formula is literally the same decomposition.
    #[must_use]
    pub fn negate(self) -> Relation {
        match self {
            Relation::Eq => Relation::Ne,
            Relation::Ne => Relation::Eq,
            Relation::Lt => Relation::Ge,
            Relation::Le => Relation::Gt,
            Relation::Gt => Relation::Le,
            Relation::Ge => Relation::Lt,
        }
    }

    /// Whether `p(x) ▷ 0` holds when `p(x)` has sign `sign` (`-1`, `0`, or
    /// `1`). This is the *only* place a relation is interpreted; both the
    /// producer and both checkers call it, which is what makes "the relation
    /// holds at the recomputed sign" a single auditable guard.
    #[must_use]
    pub fn holds(self, sign: i8) -> bool {
        match self {
            Relation::Eq => sign == 0,
            Relation::Ne => sign != 0,
            Relation::Lt => sign < 0,
            Relation::Le => sign <= 0,
            Relation::Gt => sign > 0,
            Relation::Ge => sign >= 0,
        }
    }
}

/// One atom `poly(x) ▷ 0`, with `poly` LSB-first over ℚ.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Atom {
    /// The polynomial, LSB-first (`poly[k]` is the coefficient of `xᵏ`).
    pub poly: Vec<Rational>,
    /// The comparison against `0`.
    pub relation: Relation,
}

impl Atom {
    /// Build an atom from an LSB-first coefficient vector and a relation.
    #[must_use]
    pub fn new(poly: Vec<Rational>, relation: Relation) -> Atom {
        Atom { poly, relation }
    }

    /// The same polynomial with the relation logically negated
    /// ([`Relation::negate`]).
    #[must_use]
    pub fn negate(&self) -> Atom {
        Atom {
            poly: self.poly.clone(),
            relation: self.relation.negate(),
        }
    }
}

/// `∃x. ⋀ᵢ atoms[i]` — the fragment this module decides.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ExistsFormula {
    /// The conjuncts. An **empty** conjunction is `true` (witnessed at `x = 0`).
    pub atoms: Vec<Atom>,
}

impl ExistsFormula {
    /// Build `∃x. ⋀ atoms`.
    #[must_use]
    pub fn new(atoms: Vec<Atom>) -> ExistsFormula {
        ExistsFormula { atoms }
    }
}

/// `∀x. ⋁ᵢ atoms[i]` — the De Morgan dual of [`ExistsFormula`].
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ForallFormula {
    /// The disjuncts. An **empty** disjunction is `false`.
    pub atoms: Vec<Atom>,
}

impl ForallFormula {
    /// Build `∀x. ⋁ atoms`.
    #[must_use]
    pub fn new(atoms: Vec<Atom>) -> ForallFormula {
        ForallFormula { atoms }
    }

    /// The negated existential `∃x. ⋀ᵢ ¬atoms[i]`, whose refutation is exactly
    /// a proof of this universal. See [`Relation::negate`] for the table.
    #[must_use]
    pub fn negate(&self) -> ExistsFormula {
        ExistsFormula {
            atoms: self.atoms.iter().map(Atom::negate).collect(),
        }
    }
}

// ============================================================================
// Sample points.
// ============================================================================

/// A point of ℝ named exactly: either a rational, or a real algebraic number
/// given by a defining polynomial and a Sturm-isolating bracket
/// `(lower, upper]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SamplePoint {
    /// An exact rational.
    Rational(Rational),
    /// The unique real root of `defining_poly` in `(lower, upper]`.
    Algebraic {
        /// The defining polynomial, LSB-first over ℚ.
        defining_poly: Vec<Rational>,
        /// The bracket's lower endpoint (exclusive).
        lower: Rational,
        /// The bracket's upper endpoint (inclusive).
        upper: Rational,
    },
}

impl SamplePoint {
    /// The sample for an [`AlgebraicReal`]: a degree-1 root is emitted as an
    /// exact [`SamplePoint::Rational`], anything else keeps its minimal
    /// polynomial and bracket.
    fn from_algebraic(root: &AlgebraicReal) -> SamplePoint {
        if let Some(value) = root.rational_value() {
            return SamplePoint::Rational(value);
        }
        let (lower, upper) = root.isolating_interval();
        SamplePoint::Algebraic {
            defining_poly: root.minimal_polynomial().to_vec(),
            lower,
            upper,
        }
    }
}

// ============================================================================
// Certificates and their faults.
// ============================================================================

/// Why a certificate was refused. Every variant is a **distinct guard**;
/// [`Fault::Declined`] is the one variant that is not an accusation — it means
/// the exact arithmetic gave up (a cap or an `i128` overflow in the reused
/// isolation), so the certificate was neither accepted nor disproved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Fault {
    /// The certificate records a different number of signs than the formula
    /// has conjuncts, so some `pᵢ` is unaccounted for.
    SignCountMismatch {
        /// Signs recorded in the certificate.
        recorded: usize,
        /// Conjuncts in the formula.
        atoms: usize,
    },
    /// A recorded bracket does not contain exactly one root of the recorded
    /// defining polynomial, so the "algebraic sample" names nothing.
    NotIsolating {
        /// How many distinct real roots the bracket actually contains.
        roots_in_bracket: usize,
    },
    /// A recomputed sign disagrees with the recorded one.
    SignMismatch {
        /// Index of the conjunct.
        index: usize,
        /// The sign the certificate claims.
        recorded: i8,
        /// The sign re-derived from the polynomial and the sample.
        recomputed: i8,
    },
    /// A conjunct's relation does not hold at the recomputed sign, so the
    /// sample does not satisfy the formula.
    RelationFails {
        /// Index of the conjunct.
        index: usize,
        /// The recomputed sign at which the relation fails.
        sign: i8,
    },
    /// The refutation records the wrong number of cells for its root list
    /// (`2r + 1` cells are required for `r` roots).
    CellCountMismatch {
        /// Cells recorded.
        recorded: usize,
        /// Cells required by the root list.
        expected: usize,
    },
    /// The refutation records the wrong number of open-cell samples
    /// (`r + 1` are required for `r` roots).
    OpenSampleCountMismatch {
        /// Open samples recorded.
        recorded: usize,
        /// Open samples required by the root list.
        expected: usize,
    },
    /// The cells do not cover ℝ in order: an open sample is not strictly below
    /// the next root, or not strictly above the previous one.
    CellOrderViolation {
        /// Index of the open sample that is out of place.
        index: usize,
    },
    /// The recorded root list misses a real root of some `pᵢ`, so the recorded
    /// cells are not sign-invariant and the refutation proves nothing.
    IncompleteRootList {
        /// Index of the conjunct whose roots were miscounted.
        atom: usize,
        /// Distinct real roots of that conjunct, by an independent Sturm count.
        sturm_count: usize,
        /// Recorded roots at which that conjunct vanishes.
        recorded: usize,
    },
    /// A cell names a conjunct index that the formula does not have.
    ConjunctIndexOutOfRange {
        /// The offending cell.
        cell: usize,
        /// The out-of-range index it named.
        index: usize,
    },
    /// A cell's nominated conjunct **holds** at that cell's sample, so the cell
    /// is not refuted at all.
    ConjunctDoesNotFail {
        /// The offending cell.
        cell: usize,
        /// The conjunct the cell nominated.
        index: usize,
        /// The recomputed sign, at which the relation holds.
        sign: i8,
    },
    /// Exact arithmetic declined. Not a refusal of the claim.
    Declined(&'static str),
}

/// Witness that `∃x. ⋀ᵢ pᵢ ▷ᵢ 0` is **true**: one point at which every
/// conjunct holds, plus the sign of every conjunct there.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SampleCertificate {
    /// The formula this certificate is about.
    pub atoms: Vec<Atom>,
    /// The satisfying point.
    pub sample: SamplePoint,
    /// `signs[i]` is the claimed sign of `atoms[i].poly` at `sample`.
    pub signs: Vec<i8>,
}

impl SampleCertificate {
    /// Re-derive the claim from `atoms` and `sample` alone.
    ///
    /// Guards, in order: every `pᵢ` has a recorded sign; the bracket of an
    /// algebraic sample really isolates one root of its defining polynomial
    /// (independent Sturm count); every recorded sign equals the recomputed
    /// one; every relation holds at the recomputed sign. Nothing the producer
    /// computed is reused — the signs are recomputed from the polynomials, by
    /// `BigRational` Horner at a rational sample and by
    /// [`axeyum_ir::RealAlgebraic::sign_at_big`] at an algebraic one.
    ///
    /// # Errors
    ///
    /// Returns the [`Fault`] naming the guard that rejected, or
    /// [`Fault::Declined`] if the exact arithmetic gave up.
    pub fn verify(&self) -> Result<(), Fault> {
        if self.signs.len() != self.atoms.len() {
            return Err(Fault::SignCountMismatch {
                recorded: self.signs.len(),
                atoms: self.atoms.len(),
            });
        }
        check_sample_is_isolated(&self.sample)?;
        for (index, atom) in self.atoms.iter().enumerate() {
            let recomputed = sign_at_sample(&atom.poly, &self.sample)
                .ok_or(Fault::Declined("sign at the sample point declined"))?;
            let recorded = self.signs[index];
            if recorded != recomputed {
                return Err(Fault::SignMismatch {
                    index,
                    recorded,
                    recomputed,
                });
            }
            if !atom.relation.holds(recomputed) {
                return Err(Fault::RelationFails {
                    index,
                    sign: recomputed,
                });
            }
        }
        Ok(())
    }
}

/// The conjunct that fails in one cell, and its sign there.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CellFailure {
    /// Index into the formula's conjuncts.
    pub conjunct: usize,
    /// The sign that conjunct's polynomial takes in this cell.
    pub sign: i8,
}

/// Witness that `∃x. ⋀ᵢ pᵢ ▷ᵢ 0` is **false**: the full sign-invariant cell
/// decomposition of ℝ, and a failing conjunct for every cell.
///
/// Cells are ordered along the line and interleaved:
///
/// ```text
/// cell 0    (−∞, α₀)      sample open_samples[0]
/// cell 1    {α₀}          sample roots[0]
/// cell 2    (α₀, α₁)      sample open_samples[1]
/// ...
/// cell 2r−1 {α_{r−1}}     sample roots[r−1]
/// cell 2r   (α_{r−1}, ∞)  sample open_samples[r]
/// ```
///
/// With no roots at all there is one cell, all of ℝ, sampled at
/// `open_samples[0]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RefutationCertificate {
    /// The formula this certificate is about.
    pub atoms: Vec<Atom>,
    /// The distinct real roots of all the `pᵢ`, strictly ascending.
    pub roots: Vec<SamplePoint>,
    /// One rational sample per open cell; `roots.len() + 1` of them.
    pub open_samples: Vec<Rational>,
    /// One failing conjunct per cell; `2·roots.len() + 1` of them.
    pub failures: Vec<CellFailure>,
}

impl RefutationCertificate {
    /// The sample point of cell `index`, in the interleaved order documented on
    /// the struct.
    fn cell_sample(&self, index: usize) -> Option<SamplePoint> {
        if index % 2 == 0 {
            self.open_samples
                .get(index / 2)
                .copied()
                .map(SamplePoint::Rational)
        } else {
            self.roots.get(index / 2).cloned()
        }
    }

    /// Re-derive the refutation from `atoms` alone.
    ///
    /// Guards, in order: the cell and open-sample counts match the root list;
    /// every recorded algebraic root's bracket really isolates one root; the
    /// samples and roots strictly interleave, so the cells cover ℝ in order;
    /// the root list is **complete** — for every conjunct, an independent Sturm
    /// count of its distinct real roots over a Cauchy bound equals the number
    /// of recorded roots at which it vanishes; and every cell's nominated
    /// conjunct has the recorded sign there and genuinely fails.
    ///
    /// Completeness is the guard that makes the decomposition sign-invariant:
    /// if no `pᵢ` has a root strictly inside an open cell, `pᵢ`'s sign is
    /// constant on that cell, so the one sample decides it.
    ///
    /// # Errors
    ///
    /// Returns the [`Fault`] naming the guard that rejected, or
    /// [`Fault::Declined`] if the exact arithmetic gave up.
    pub fn verify(&self) -> Result<(), Fault> {
        let expected_cells = 2 * self.roots.len() + 1;
        if self.failures.len() != expected_cells {
            return Err(Fault::CellCountMismatch {
                recorded: self.failures.len(),
                expected: expected_cells,
            });
        }
        let expected_open = self.roots.len() + 1;
        if self.open_samples.len() != expected_open {
            return Err(Fault::OpenSampleCountMismatch {
                recorded: self.open_samples.len(),
                expected: expected_open,
            });
        }
        for root in &self.roots {
            check_sample_is_isolated(root)?;
        }
        self.check_cell_order()?;
        self.check_root_list_complete()?;
        self.check_every_cell_fails()
    }

    /// The cells cover ℝ in order: `open_samples[k] < αₖ < open_samples[k+1]`.
    /// This forces the open samples to be strictly increasing *and* the roots
    /// to be strictly separated by them, so no two recorded roots collide and
    /// no cell is empty.
    fn check_cell_order(&self) -> Result<(), Fault> {
        for (index, root) in self.roots.iter().enumerate() {
            let below = self.open_samples[index];
            let above = self.open_samples[index + 1];
            if compare_sample_to_rational(root, below)
                .ok_or(Fault::Declined("root/sample comparison declined"))?
                != Ordering::Greater
            {
                return Err(Fault::CellOrderViolation { index });
            }
            if compare_sample_to_rational(root, above)
                .ok_or(Fault::Declined("root/sample comparison declined"))?
                != Ordering::Less
            {
                return Err(Fault::CellOrderViolation { index: index + 1 });
            }
        }
        Ok(())
    }

    /// Every real root of every `pᵢ` appears in `roots`, re-checked by Sturm
    /// counts over a Cauchy bound rather than by trusting the producer's search.
    fn check_root_list_complete(&self) -> Result<(), Fault> {
        for (atom_index, atom) in self.atoms.iter().enumerate() {
            let Some(bound) = cauchy_root_bound(&atom.poly) else {
                continue; // the zero polynomial or a constant: no roots to miss
            };
            let sturm_count = sturm::count_real_roots_in(
                &atom.poly,
                bound
                    .checked_neg()
                    .ok_or(Fault::Declined("Cauchy bound negation overflowed"))?,
                bound,
            )
            .ok_or(Fault::Declined("Sturm root count declined"))?;
            let mut recorded = 0usize;
            for root in &self.roots {
                let sign = sign_at_sample(&atom.poly, root)
                    .ok_or(Fault::Declined("sign at a recorded root declined"))?;
                if sign == 0 {
                    recorded += 1;
                }
            }
            if sturm_count != recorded {
                return Err(Fault::IncompleteRootList {
                    atom: atom_index,
                    sturm_count,
                    recorded,
                });
            }
        }
        Ok(())
    }

    /// Every cell names a conjunct that really fails there, at the sign the
    /// certificate records.
    fn check_every_cell_fails(&self) -> Result<(), Fault> {
        for (cell, failure) in self.failures.iter().enumerate() {
            let Some(atom) = self.atoms.get(failure.conjunct) else {
                return Err(Fault::ConjunctIndexOutOfRange {
                    cell,
                    index: failure.conjunct,
                });
            };
            let sample = self
                .cell_sample(cell)
                .ok_or(Fault::Declined("cell index has no sample"))?;
            let recomputed = sign_at_sample(&atom.poly, &sample)
                .ok_or(Fault::Declined("sign at a cell sample declined"))?;
            if recomputed != failure.sign {
                return Err(Fault::SignMismatch {
                    index: failure.conjunct,
                    recorded: failure.sign,
                    recomputed,
                });
            }
            if atom.relation.holds(recomputed) {
                return Err(Fault::ConjunctDoesNotFail {
                    cell,
                    index: failure.conjunct,
                    sign: recomputed,
                });
            }
        }
        Ok(())
    }
}

// ============================================================================
// Decisions.
// ============================================================================

/// The verdict on an [`ExistsFormula`], with its certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decision {
    /// Satisfiable, witnessed by a sample point.
    True(Box<SampleCertificate>),
    /// Unsatisfiable, witnessed by the cell decomposition.
    False(Box<RefutationCertificate>),
    /// Exact arithmetic declined. Never a verdict.
    Unknown(String),
}

/// The verdict on a [`ForallFormula`]. Note the certificates swap sides: a
/// universal is *proved* by a refutation of its negation, and *refuted* by a
/// counterexample sample.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ForallDecision {
    /// Valid; the certificate refutes the negated existential.
    True(Box<RefutationCertificate>),
    /// Invalid; the certificate is a counterexample to the disjunction.
    False(Box<SampleCertificate>),
    /// Exact arithmetic declined. Never a verdict.
    Unknown(String),
}

/// Decide `∃x. ⋀ᵢ pᵢ(x) ▷ᵢ 0`.
///
/// Isolates the real roots of every `pᵢ` (reusing
/// [`crate::algebraic::real_roots`]), merges them into one strictly ascending
/// list, forms the `2r + 1` sign-invariant cells, and tests the conjunction at
/// one sample per cell — the root itself for a point cell, a rational strictly
/// between consecutive brackets for an open cell.
///
/// Returns [`Decision::Unknown`] with a human-readable reason whenever the
/// reused exact machinery declines (an `i128` overflow in the Sturm chain, a
/// factorization cap, or a bracket that will not separate within the
/// refinement budget). It never guesses.
#[must_use]
pub fn decide_exists(formula: &ExistsFormula) -> Decision {
    let roots = match merged_roots(formula) {
        Ok(roots) => roots,
        Err(reason) => return Decision::Unknown(reason),
    };
    let open_samples = match open_cell_samples(&roots) {
        Ok(samples) => samples,
        Err(reason) => return Decision::Unknown(reason),
    };
    let root_samples: Vec<SamplePoint> = roots.iter().map(SamplePoint::from_algebraic).collect();

    let cells = 2 * root_samples.len() + 1;
    let mut failures: Vec<CellFailure> = Vec::with_capacity(cells);
    for cell in 0..cells {
        let sample = if cell % 2 == 0 {
            SamplePoint::Rational(open_samples[cell / 2])
        } else {
            root_samples[cell / 2].clone()
        };
        let mut signs: Vec<i8> = Vec::with_capacity(formula.atoms.len());
        for atom in &formula.atoms {
            match sign_at_sample(&atom.poly, &sample) {
                Some(sign) => signs.push(sign),
                None => {
                    return Decision::Unknown(format!(
                        "exact sign evaluation declined in cell {cell}"
                    ));
                }
            }
        }
        match first_failure(&formula.atoms, &signs) {
            None => {
                return Decision::True(Box::new(SampleCertificate {
                    atoms: formula.atoms.clone(),
                    sample,
                    signs,
                }));
            }
            Some(failure) => failures.push(failure),
        }
    }
    Decision::False(Box::new(RefutationCertificate {
        atoms: formula.atoms.clone(),
        roots: root_samples,
        open_samples,
        failures,
    }))
}

/// Decide `∀x. ⋁ᵢ pᵢ(x) ▷ᵢ 0`, by deciding the negated existential
/// ([`ForallFormula::negate`], whose table is on [`Relation::negate`]) and
/// swapping the verdict.
#[must_use]
pub fn decide_forall(formula: &ForallFormula) -> ForallDecision {
    match decide_exists(&formula.negate()) {
        Decision::False(refutation) => ForallDecision::True(refutation),
        Decision::True(sample) => ForallDecision::False(sample),
        Decision::Unknown(reason) => ForallDecision::Unknown(reason),
    }
}

/// The thin, **self-checking** front door: decide `∃x. ⋀ᵢ pᵢ ▷ᵢ 0` and verify
/// the certificate before answering.
///
/// `Some(true)` / `Some(false)` are returned only when the corresponding
/// certificate passed its own `verify`; a decline, or a certificate this
/// module's own checker refuses, both yield `None`. Callers that want the
/// certificate itself call [`decide_exists`] and verify it themselves — this
/// function exists so that "the producer and the checker agree" is the default
/// path rather than an opt-in.
#[must_use]
pub fn eliminate(formula: &ExistsFormula) -> Option<bool> {
    match decide_exists(formula) {
        Decision::True(cert) => cert.verify().ok().map(|()| true),
        Decision::False(cert) => cert.verify().ok().map(|()| false),
        Decision::Unknown(_) => None,
    }
}

/// The universal front door, dual to [`eliminate`]; likewise self-checking.
#[must_use]
pub fn eliminate_forall(formula: &ForallFormula) -> Option<bool> {
    eliminate(&formula.negate()).map(|satisfiable| !satisfiable)
}

/// The first conjunct whose relation fails at the given signs, if any.
fn first_failure(atoms: &[Atom], signs: &[i8]) -> Option<CellFailure> {
    for (index, atom) in atoms.iter().enumerate() {
        let sign = signs[index];
        if !atom.relation.holds(sign) {
            return Some(CellFailure {
                conjunct: index,
                sign,
            });
        }
    }
    None
}

// ============================================================================
// Root collection and cell samples (producer side).
// ============================================================================

/// Every distinct real root of every conjunct, strictly ascending.
fn merged_roots(formula: &ExistsFormula) -> Result<Vec<AlgebraicReal>, String> {
    let mut roots: Vec<AlgebraicReal> = Vec::new();
    for (index, atom) in formula.atoms.iter().enumerate() {
        if axeyum_ir::poly::rat_degree(&atom.poly).unwrap_or(0) == 0 {
            continue; // the zero polynomial or a nonzero constant: no roots
        }
        let Some(found) = algebraic::real_roots(&atom.poly) else {
            return Err(format!(
                "real-root isolation declined for conjunct {index} (overflow or a degree cap)"
            ));
        };
        for root in found {
            let mut duplicate = false;
            for existing in &roots {
                match compare_roots(existing, &root) {
                    Some(Ordering::Equal) => {
                        duplicate = true;
                        break;
                    }
                    Some(_) => {}
                    None => {
                        return Err(format!(
                            "exact comparison of two algebraic roots declined (conjunct {index})"
                        ));
                    }
                }
            }
            if !duplicate {
                roots.push(root);
            }
        }
    }
    // Insertion sort, so a declining comparison is an error rather than a panic
    // or a silently wrong order (`sort_by` cannot propagate `None`).
    let mut sorted: Vec<AlgebraicReal> = Vec::with_capacity(roots.len());
    for root in roots {
        let mut position = sorted.len();
        for (index, existing) in sorted.iter().enumerate() {
            match compare_roots(&root, existing) {
                Some(Ordering::Less) => {
                    position = index;
                    break;
                }
                Some(_) => {}
                None => return Err("exact comparison of two algebraic roots declined".to_string()),
            }
        }
        sorted.insert(position, root);
    }
    Ok(sorted)
}

/// Exact comparison of two isolated real roots.
///
/// Three cheap sound tests first — both rational; brackets already disjoint;
/// identical minimal polynomial *and* identical bracket — and only then the
/// reused [`crate::real_algebraic::algebraic_cmp`], which costs a resultant.
fn compare_roots(a: &AlgebraicReal, b: &AlgebraicReal) -> Option<Ordering> {
    if let (Some(x), Some(y)) = (a.rational_value(), b.rational_value()) {
        return x.checked_cmp(&y);
    }
    let (a_lo, a_hi) = a.isolating_interval();
    let (b_lo, b_hi) = b.isolating_interval();
    // Bracket is `(lo, hi]`, so `a_hi <= b_lo` forces `a <= a_hi <= b_lo < b`.
    if a_hi.checked_cmp(&b_lo)? != Ordering::Greater {
        return Some(Ordering::Less);
    }
    if b_hi.checked_cmp(&a_lo)? != Ordering::Greater {
        return Some(Ordering::Greater);
    }
    if a.minimal_polynomial() == b.minimal_polynomial() && a_lo == b_lo && a_hi == b_hi {
        return Some(Ordering::Equal);
    }
    let left = real_algebraic::from_algebraic_real(a)?;
    let right = real_algebraic::from_algebraic_real(b)?;
    real_algebraic::algebraic_cmp(&left, &right)
}

/// One rational sample strictly inside every open cell: below the first root,
/// between each consecutive pair, and above the last.
fn open_cell_samples(roots: &[AlgebraicReal]) -> Result<Vec<Rational>, String> {
    if roots.is_empty() {
        // No root anywhere: ℝ is one cell and every point decides it.
        return Ok(vec![Rational::zero()]);
    }
    let mut samples: Vec<Rational> = Vec::with_capacity(roots.len() + 1);
    // Every root lies inside its own Sturm bracket, so the smallest recorded
    // lower endpoint minus one is below all of them, and the largest upper
    // endpoint plus one is above all of them — a tighter and overflow-free
    // stand-in for a Cauchy bound over the product of the polynomials.
    let mut lowest = roots[0].isolating_interval().0;
    let mut highest = roots[0].isolating_interval().1;
    for root in roots {
        let (lo, hi) = root.isolating_interval();
        if lo
            .checked_cmp(&lowest)
            .ok_or("bracket comparison overflowed")?
            == Ordering::Less
        {
            lowest = lo;
        }
        if hi
            .checked_cmp(&highest)
            .ok_or("bracket comparison overflowed")?
            == Ordering::Greater
        {
            highest = hi;
        }
    }
    samples.push(
        lowest
            .checked_sub(Rational::integer(1))
            .ok_or("left-hand sample overflowed")?,
    );
    for window in roots.windows(2) {
        samples.push(rational_between(&window[0], &window[1])?);
    }
    samples.push(
        highest
            .checked_add(Rational::integer(1))
            .ok_or("right-hand sample overflowed")?,
    );
    Ok(samples)
}

/// A rational strictly between two consecutive roots `a < b`, found by refining
/// both brackets until they are disjoint and taking the midpoint of the gap.
fn rational_between(a: &AlgebraicReal, b: &AlgebraicReal) -> Result<Rational, String> {
    let mut left = a.clone();
    let mut right = b.clone();
    let mut width = Rational::integer(1);
    for _ in 0..MAX_SEPARATION_STEPS {
        let left_hi = left.isolating_interval().1;
        let right_lo = right.isolating_interval().0;
        if left_hi
            .checked_cmp(&right_lo)
            .ok_or("bracket comparison overflowed")?
            == Ordering::Less
        {
            let sum = left_hi
                .checked_add(right_lo)
                .ok_or("gap midpoint overflowed")?;
            return sum
                .checked_div(Rational::integer(2))
                .ok_or_else(|| "gap midpoint overflowed".to_string());
        }
        width = width
            .checked_div(Rational::integer(2))
            .ok_or("refinement width overflowed")?;
        left = left
            .refine(width)
            .ok_or("bracket refinement declined (i128 overflow)")?;
        right = right
            .refine(width)
            .ok_or("bracket refinement declined (i128 overflow)")?;
    }
    Err("two roots did not separate within the refinement budget".to_string())
}

// ============================================================================
// Exact sign evaluation (checker side; also used by the producer).
// ============================================================================

/// The polynomial's coefficients as `BigRational`s.
fn big_coefficients(poly: &[Rational]) -> Vec<BigRational> {
    poly.iter()
        .map(|c| BigRational::new(BigInt::from(c.numerator()), BigInt::from(c.denominator())))
        .collect()
}

/// The polynomial scaled by the positive lcm of its denominators, so the
/// coefficients are integers and every sign is unchanged.
fn integer_coefficients(poly: &[Rational]) -> Vec<BigInt> {
    let mut lcm = BigInt::one();
    for coeff in poly {
        let den = BigInt::from(coeff.denominator());
        let gcd = big_gcd(&lcm, &den);
        lcm = &lcm / &gcd * den;
    }
    poly.iter()
        .map(|c| BigInt::from(c.numerator()) * &lcm / BigInt::from(c.denominator()))
        .collect()
}

/// Euclid's algorithm on [`BigInt`]s, returning `1` for `gcd(0, 0)` so the lcm
/// fold above never divides by zero.
fn big_gcd(a: &BigInt, b: &BigInt) -> BigInt {
    let mut x = a.abs();
    let mut y = b.abs();
    while !y.is_zero() {
        let r = &x % &y;
        x = y;
        y = r;
    }
    if x.is_zero() { BigInt::one() } else { x }
}

/// The exact sign of `poly` at the rational `x`, by Horner over `BigRational`.
/// Cannot overflow and cannot decline.
fn sign_at_rational(poly: &[Rational], x: Rational) -> i8 {
    let point = BigRational::new(BigInt::from(x.numerator()), BigInt::from(x.denominator()));
    let mut acc = BigRational::zero();
    for coeff in big_coefficients(poly).iter().rev() {
        acc = acc * &point + coeff;
    }
    if acc.is_zero() {
        0
    } else if acc.is_negative() {
        -1
    } else {
        1
    }
}

/// The [`axeyum_ir::RealAlgebraic`] a sample point denotes, or `None` if the
/// bracket does not straddle a root of the (denominator-cleared) defining
/// polynomial.
fn as_real_algebraic(sample: &SamplePoint) -> Option<RealAlgebraic> {
    match sample {
        SamplePoint::Rational(value) => RealAlgebraic::from_rational(*value),
        SamplePoint::Algebraic {
            defining_poly,
            lower,
            upper,
        } => {
            let coeffs = integer_coefficients(defining_poly);
            let lo = BigRational::new(
                BigInt::from(lower.numerator()),
                BigInt::from(lower.denominator()),
            );
            let hi = BigRational::new(
                BigInt::from(upper.numerator()),
                BigInt::from(upper.denominator()),
            );
            RealAlgebraic::new_big(coeffs, lo, hi)
        }
    }
}

/// The exact sign of `poly` at a sample point: `BigRational` Horner for a
/// rational, and the reused [`axeyum_ir::RealAlgebraic::sign_at_big`] for an
/// algebraic one (an exact polynomial-divisibility test for the zero case, then
/// bracket refinement until the sign is constant — no Sturm count, no float).
fn sign_at_sample(poly: &[Rational], sample: &SamplePoint) -> Option<i8> {
    match sample {
        SamplePoint::Rational(value) => Some(sign_at_rational(poly, *value)),
        SamplePoint::Algebraic { .. } => {
            let alpha = as_real_algebraic(sample)?;
            let sign = alpha.sign_at_big(&integer_coefficients(poly))?;
            Some(match sign {
                Sign::Neg => -1,
                Sign::Zero => 0,
                Sign::Pos => 1,
            })
        }
    }
}

/// Where a sample point sits relative to a rational.
fn compare_sample_to_rational(sample: &SamplePoint, x: Rational) -> Option<Ordering> {
    match sample {
        SamplePoint::Rational(value) => value.checked_cmp(&x),
        SamplePoint::Algebraic { .. } => as_real_algebraic(sample)?.compare_rational(&x),
    }
}

/// The guard behind both certificates' "this bracket names one real number":
/// an independent Sturm count over the recorded bracket must be exactly one.
/// A rational sample has nothing to isolate.
fn check_sample_is_isolated(sample: &SamplePoint) -> Result<(), Fault> {
    let SamplePoint::Algebraic {
        defining_poly,
        lower,
        upper,
    } = sample
    else {
        return Ok(());
    };
    let count = sturm::count_real_roots_in(defining_poly, *lower, *upper)
        .ok_or(Fault::Declined("Sturm count over the bracket declined"))?;
    if count == 1 {
        Ok(())
    } else {
        Err(Fault::NotIsolating {
            roots_in_bracket: count,
        })
    }
}

/// A Cauchy bound `B = 1 + maxᵢ |aᵢ / aₙ|`: every real root of `poly` lies in
/// `(−B, B)`. Computed in `BigRational` and rounded up to an integer, so it
/// cannot overflow on the way; `None` for the zero polynomial, for a constant,
/// or if the rounded bound does not fit `i128` (the reused Sturm count needs an
/// `i128` rational endpoint).
fn cauchy_root_bound(poly: &[Rational]) -> Option<Rational> {
    let degree = axeyum_ir::poly::rat_degree(poly)?;
    if degree == 0 {
        return None;
    }
    let coeffs = big_coefficients(poly);
    let leading = coeffs[degree].clone();
    let mut max_ratio = BigRational::zero();
    for coeff in &coeffs[..degree] {
        let ratio = (coeff / &leading).abs();
        if ratio > max_ratio {
            max_ratio = ratio;
        }
    }
    let bound = (max_ratio + BigRational::one()).ceil().to_integer();
    i128::try_from(bound).ok().map(Rational::integer)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// An integer-coefficient polynomial, LSB-first.
    fn ipoly(coeffs: &[i128]) -> Vec<Rational> {
        coeffs.iter().copied().map(Rational::integer).collect()
    }

    /// `x`, LSB-first.
    fn x_poly() -> Vec<Rational> {
        ipoly(&[0, 1])
    }

    fn exists(atoms: Vec<Atom>) -> ExistsFormula {
        ExistsFormula::new(atoms)
    }

    fn as_true(decision: Decision) -> SampleCertificate {
        match decision {
            Decision::True(cert) => *cert,
            other => panic!("expected True, got {other:?}"),
        }
    }

    fn as_false(decision: Decision) -> RefutationCertificate {
        match decision {
            Decision::False(cert) => *cert,
            other => panic!("expected False, got {other:?}"),
        }
    }

    // ---------------------------------------------------------------- table

    #[test]
    fn relation_negation_is_an_involution_and_flips_every_sign_verdict() {
        for relation in [
            Relation::Eq,
            Relation::Ne,
            Relation::Lt,
            Relation::Le,
            Relation::Gt,
            Relation::Ge,
        ] {
            assert_eq!(relation.negate().negate(), relation);
            for sign in [-1i8, 0, 1] {
                assert_ne!(
                    relation.holds(sign),
                    relation.negate().holds(sign),
                    "{relation:?} at sign {sign}"
                );
            }
        }
    }

    // ------------------------------------------------------------- verdicts

    #[test]
    fn exists_x_squared_minus_two_equals_zero_is_true_at_an_algebraic_sample() {
        let formula = exists(vec![Atom::new(ipoly(&[-2, 0, 1]), Relation::Eq)]);
        let cert = as_true(decide_exists(&formula));
        assert!(
            matches!(cert.sample, SamplePoint::Algebraic { .. }),
            "sqrt(2) is irrational, so the sample must be algebraic: {:?}",
            cert.sample
        );
        assert_eq!(cert.signs, vec![0]);
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate(&formula), Some(true));
    }

    #[test]
    fn exists_x_squared_plus_one_negative_is_false_with_a_single_whole_line_cell() {
        let formula = exists(vec![Atom::new(ipoly(&[1, 0, 1]), Relation::Lt)]);
        let cert = as_false(decide_exists(&formula));
        // `x² + 1` has no real root, so the sign-invariant decomposition of ℝ
        // is one cell, not two: there is nothing to cut the line at.
        assert!(cert.roots.is_empty());
        assert_eq!(cert.open_samples.len(), 1);
        assert_eq!(cert.failures.len(), 1);
        assert_eq!(cert.failures[0].conjunct, 0);
        assert_eq!(cert.failures[0].sign, 1);
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate(&formula), Some(false));
    }

    #[test]
    fn exists_x_squared_lt_two_and_x_gt_one_is_true_at_a_rational_sample() {
        let formula = exists(vec![
            Atom::new(ipoly(&[-2, 0, 1]), Relation::Lt),
            Atom::new(ipoly(&[-1, 1]), Relation::Gt),
        ]);
        let cert = as_true(decide_exists(&formula));
        let SamplePoint::Rational(sample) = cert.sample else {
            panic!("the satisfying cell is open, so the sample is rational");
        };
        // Strictly between 1 and sqrt(2).
        assert_eq!(sign_at_rational(&ipoly(&[-1, 1]), sample), 1);
        assert_eq!(sign_at_rational(&ipoly(&[-2, 0, 1]), sample), -1);
        assert_eq!(cert.signs, vec![-1, 1]);
        assert_eq!(cert.verify(), Ok(()));
    }

    #[test]
    fn exists_cubic_root_strictly_inside_the_unit_interval_is_false_at_the_point_cell_on_one() {
        // ∃x. x³ − x = 0 ∧ x > 0 ∧ x < 1.  The only positive root is 1, which
        // the strict upper bound excludes.
        let formula = exists(vec![
            Atom::new(ipoly(&[0, -1, 0, 1]), Relation::Eq),
            Atom::new(x_poly(), Relation::Gt),
            Atom::new(ipoly(&[-1, 1]), Relation::Lt),
        ]);
        let cert = as_false(decide_exists(&formula));
        assert_eq!(
            cert.roots,
            vec![
                SamplePoint::Rational(Rational::integer(-1)),
                SamplePoint::Rational(Rational::zero()),
                SamplePoint::Rational(Rational::integer(1)),
            ]
        );
        assert_eq!(cert.failures.len(), 7);
        // Cell 5 is the point cell {1}: `x − 1` has sign 0 there, so `x < 1`
        // is the conjunct that fails.
        assert_eq!(
            cert.failures[5],
            CellFailure {
                conjunct: 2,
                sign: 0
            }
        );
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate(&formula), Some(false));
    }

    #[test]
    fn forall_x_squared_nonnegative_is_true() {
        let formula = ForallFormula::new(vec![Atom::new(ipoly(&[0, 0, 1]), Relation::Ge)]);
        let ForallDecision::True(cert) = decide_forall(&formula) else {
            panic!("x² ≥ 0 is valid");
        };
        assert_eq!(cert.roots, vec![SamplePoint::Rational(Rational::zero())]);
        assert_eq!(cert.failures.len(), 3);
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate_forall(&formula), Some(true));
    }

    #[test]
    fn forall_x_squared_minus_x_nonnegative_is_false_with_a_counterexample_below_one() {
        let formula = ForallFormula::new(vec![Atom::new(ipoly(&[0, -1, 1]), Relation::Ge)]);
        let ForallDecision::False(cert) = decide_forall(&formula) else {
            panic!("x² − x < 0 on (0, 1), so the universal is false");
        };
        let SamplePoint::Rational(sample) = cert.sample else {
            panic!("the counterexample cell (0, 1) is open");
        };
        assert_eq!(sign_at_rational(&x_poly(), sample), 1, "sample > 0");
        assert_eq!(sign_at_rational(&ipoly(&[-1, 1]), sample), -1, "sample < 1");
        assert_eq!(cert.verify(), Ok(()));
        assert_eq!(eliminate_forall(&formula), Some(false));
    }

    #[test]
    fn exists_double_root_case_is_true_at_the_double_root_as_a_point_cell() {
        // (x−1)²·(x−2) = x³ − 4x² + 5x − 2 ≥ 0 ∧ x < 3/2.  The only point where
        // the cubic is non-negative below 3/2 is the double root x = 1.
        let cubic = ipoly(&[-2, 5, -4, 1]);
        let bound = vec![Rational::new(-3, 2), Rational::integer(1)];
        let formula = exists(vec![
            Atom::new(cubic, Relation::Ge),
            Atom::new(bound, Relation::Lt),
        ]);
        let cert = as_true(decide_exists(&formula));
        assert_eq!(cert.sample, SamplePoint::Rational(Rational::integer(1)));
        assert_eq!(cert.signs, vec![0, -1]);
        assert_eq!(cert.verify(), Ok(()));
    }

    // ------------------------------------------------------- forged samples

    #[test]
    fn forged_sample_certificate_with_a_missing_conjunct_sign_is_refused() {
        let atoms = vec![Atom::new(x_poly(), Relation::Gt)];
        let cert = SampleCertificate {
            atoms,
            sample: SamplePoint::Rational(Rational::integer(1)),
            signs: Vec::new(),
        };
        assert_eq!(
            cert.verify(),
            Err(Fault::SignCountMismatch {
                recorded: 0,
                atoms: 1
            })
        );
    }

    #[test]
    fn forged_sample_certificate_with_a_wrong_sign_is_refused() {
        let formula = exists(vec![Atom::new(ipoly(&[-2, 0, 1]), Relation::Lt)]);
        let mut cert = as_true(decide_exists(&formula));
        assert_eq!(cert.verify(), Ok(()));
        cert.signs[0] = 1;
        assert_eq!(
            cert.verify(),
            Err(Fault::SignMismatch {
                index: 0,
                recorded: 1,
                recomputed: -1
            })
        );
    }

    #[test]
    fn forged_sample_certificate_whose_bracket_holds_two_roots_is_refused() {
        // (−2, 2] holds both roots of x² − 2, so it isolates nothing.
        let cert = SampleCertificate {
            atoms: vec![Atom::new(ipoly(&[-2, 0, 1]), Relation::Eq)],
            sample: SamplePoint::Algebraic {
                defining_poly: ipoly(&[-2, 0, 1]),
                lower: Rational::integer(-2),
                upper: Rational::integer(2),
            },
            signs: vec![0],
        };
        assert_eq!(
            cert.verify(),
            Err(Fault::NotIsolating {
                roots_in_bracket: 2
            })
        );
    }

    #[test]
    fn forged_sample_certificate_whose_relation_does_not_hold_is_refused() {
        // The sign is recorded correctly; the point simply does not satisfy `x > 0`.
        let cert = SampleCertificate {
            atoms: vec![Atom::new(x_poly(), Relation::Gt)],
            sample: SamplePoint::Rational(Rational::integer(-1)),
            signs: vec![-1],
        };
        assert_eq!(
            cert.verify(),
            Err(Fault::RelationFails { index: 0, sign: -1 })
        );
    }

    // --------------------------------------------------- forged refutations

    /// The valid refutation of `∃x. x³ − x = 0 ∧ x > 0 ∧ x < 1`, with roots
    /// `−1 < 0 < 1` and seven cells — the fixture the forgeries below mutate.
    fn cubic_refutation() -> RefutationCertificate {
        let formula = exists(vec![
            Atom::new(ipoly(&[0, -1, 0, 1]), Relation::Eq),
            Atom::new(x_poly(), Relation::Gt),
            Atom::new(ipoly(&[-1, 1]), Relation::Lt),
        ]);
        let cert = as_false(decide_exists(&formula));
        assert_eq!(cert.verify(), Ok(()));
        cert
    }

    #[test]
    fn forged_refutation_with_a_sample_outside_its_cell_is_refused() {
        let mut cert = cubic_refutation();
        // open_samples[1] must lie in (−1, 0); 5 lies above every root, so the
        // cells no longer cover ℝ in order.
        cert.open_samples[1] = Rational::integer(5);
        assert_eq!(cert.verify(), Err(Fault::CellOrderViolation { index: 1 }));
    }

    #[test]
    fn forged_refutation_that_drops_a_root_is_refused_as_an_incomplete_root_list() {
        let cert = cubic_refutation();
        // Drop the root at 0 together with its point cell, keeping every count
        // self-consistent and every remaining cell genuinely failing — only the
        // Sturm completeness recount can catch this.
        let forged = RefutationCertificate {
            atoms: cert.atoms.clone(),
            roots: vec![cert.roots[0].clone(), cert.roots[2].clone()],
            open_samples: vec![
                cert.open_samples[0],
                cert.open_samples[1],
                cert.open_samples[3],
            ],
            failures: vec![
                cert.failures[0],
                cert.failures[1],
                cert.failures[2],
                cert.failures[5],
                cert.failures[6],
            ],
        };
        assert_eq!(
            forged.verify(),
            Err(Fault::IncompleteRootList {
                atom: 0,
                sturm_count: 3,
                recorded: 2
            })
        );
    }

    #[test]
    fn forged_refutation_naming_a_conjunct_that_actually_holds_is_refused() {
        let mut cert = cubic_refutation();
        // In cell 0 (far left of every root) `x < 1` holds, so nominating it as
        // the failing conjunct — with its true sign — is a forgery.
        let sample = SamplePoint::Rational(cert.open_samples[0]);
        let sign = sign_at_sample(&cert.atoms[2].poly, &sample).expect("exact sign");
        cert.failures[0] = CellFailure { conjunct: 2, sign };
        assert_eq!(
            cert.verify(),
            Err(Fault::ConjunctDoesNotFail {
                cell: 0,
                index: 2,
                sign
            })
        );
    }

    #[test]
    fn forged_refutation_with_a_wrong_cell_sign_is_refused() {
        let mut cert = cubic_refutation();
        cert.failures[0] = CellFailure {
            conjunct: cert.failures[0].conjunct,
            sign: -cert.failures[0].sign,
        };
        assert!(
            matches!(cert.verify(), Err(Fault::SignMismatch { .. })),
            "a flipped cell sign must be caught by the recount"
        );
    }

    #[test]
    fn forged_refutation_naming_a_conjunct_the_formula_does_not_have_is_refused() {
        let mut cert = cubic_refutation();
        cert.failures[0] = CellFailure {
            conjunct: 99,
            sign: 0,
        };
        assert_eq!(
            cert.verify(),
            Err(Fault::ConjunctIndexOutOfRange { cell: 0, index: 99 })
        );
    }

    #[test]
    fn forged_refutation_with_the_wrong_number_of_cells_is_refused() {
        let mut cert = cubic_refutation();
        cert.failures.pop();
        assert_eq!(
            cert.verify(),
            Err(Fault::CellCountMismatch {
                recorded: 6,
                expected: 7
            })
        );
    }

    // ------------------------------------------------------------- declines

    #[test]
    fn coefficients_beyond_the_reused_i128_isolation_decline_to_unknown_not_a_verdict() {
        // Positive control: the same shape at a small coefficient decides.
        let small = exists(vec![Atom::new(ipoly(&[-2, 0, 1]), Relation::Eq)]);
        assert!(matches!(decide_exists(&small), Decision::True(_)));

        // `x² − 10³⁰` fits `i128` as a coefficient, but the reused Sturm
        // machinery evaluates near the Cauchy bound and overflows there.
        let huge = exists(vec![Atom::new(
            ipoly(&[-1_000_000_000_000_000_000_000_000_000_000, 0, 1]),
            Relation::Eq,
        )]);
        match decide_exists(&huge) {
            Decision::Unknown(reason) => assert!(!reason.is_empty()),
            other => panic!("an i128 overflow must decline, not decide: {other:?}"),
        }
        assert_eq!(eliminate(&huge), None);
    }
}
