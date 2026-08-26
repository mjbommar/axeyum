//! Cube-and-conquer certificate composition (ADR-0543).
//!
//! Sharding a hard `unsat` into cubes is only sound if the checker can verify
//! the composite **without trusting how the cubes were chosen**. This module's
//! whole design is aimed at that one property: [`check_cube_refutation`] is
//! handed nothing but the base formula and a plain list of cube literals, and
//! it builds every formula it checks — each cube's augmented formula, and the
//! covering formula — itself, before ever calling [`crate::check_drat`].
//! Neither `check_drat` nor the proof-producing core (`crate::proof_sat`) is
//! modified: a cube is refuted as ordinary unit clauses added to an ordinary
//! CNF formula (the proof-producing core has no assumption interface, so this
//! is also the only route that needs no change to it), and exhaustiveness is
//! itself an ordinary UNSAT instance, checked the same way.
//!
//! See ADR-0543 for the full soundness argument and the alternatives
//! (LRAT-style proof stitching, a bespoke tree-completeness certificate)
//! rejected in favor of this shape.

use std::fmt;
use std::io::BufRead;

use crate::{
    CnfAssignment, CnfClause, CnfError, CnfFormula, CnfLit, CnfVar, DratError, DratStep,
    ProofSolveOutcome, check_drat, check_drat_backward_reader, solve_with_drat_proof_with_limits,
};

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

/// A cube: a conjunction of literals, refuted as extra unit clauses against
/// the base formula. The empty cube is the trivial cube "true" (no
/// restriction) and is not useful on its own but is not rejected structurally
/// — a single-cube "split" degenerates to ordinary monolithic certification.
pub type Cube = Vec<CnfLit>;

/// Default per-cube conflict budget for [`certify_by_cubes`]. Deliberately
/// small relative to [`crate::DEFAULT_PROOF_SAT_CONFLICT_LIMIT`] — the point
/// of sharding is that most cubes close far below the monolithic budget, and a
/// cube that does not is exactly the signal that it needs re-splitting rather
/// than a bigger budget.
pub const DEFAULT_CUBE_CONFLICT_LIMIT: usize = 500_000;

/// Default conflict budget for the covering-formula proof (step 3 of
/// ADR-0543). The covering formula ranges only over the case-split variables,
/// never the full base formula, so this is independent of and much smaller
/// than [`DEFAULT_CUBE_CONFLICT_LIMIT`].
pub const DEFAULT_COVERING_CONFLICT_LIMIT: usize = 10_000;

/// Cap on the number of selector variables [`boolean_product_cubes`] will
/// expand into `2^k` cubes. This exists to catch a caller mistake (an
/// accidentally huge selector list), not to suggest `2^24` cubes is a
/// reasonable amount of work to schedule.
pub const MAX_PRODUCT_CUBE_SELECTORS: usize = 24;

/// Builds the augmented formula `F ∧ cube` by cloning `base` and appending one
/// unit clause per cube literal.
///
/// # Errors
///
/// Returns [`CnfError::InvalidVariable`] if a cube literal names a variable
/// outside `base` — checked by [`CnfFormula::add_clause`], not by this
/// function, so the bounds check cannot drift out of sync with it.
pub fn augmented_formula(base: &CnfFormula, cube: &[CnfLit]) -> Result<CnfFormula, CnfError> {
    let mut augmented = base.clone();
    for &lit in cube {
        augmented.add_clause(CnfClause::new(vec![lit]))?;
    }
    Ok(augmented)
}

/// Builds the covering formula `G = {¬cube_i : i}` (ADR-0543 step 3): one
/// clause per cube, the De Morgan negation of that cube's literal conjunction.
/// `G` is UNSAT exactly when every total assignment (over the variables the
/// cubes mention) satisfies at least one cube, i.e. exactly when `cubes`
/// exhausts the space it splits.
///
/// `G` is built over the same variable count as `base` so that cube literals
/// (which name `base`'s variables) are always in range; it does not otherwise
/// depend on `base`'s clauses.
///
/// # Errors
///
/// Returns [`CnfError::InvalidVariable`] if a cube literal names a variable
/// outside `base`.
pub fn covering_formula(base: &CnfFormula, cubes: &[Cube]) -> Result<CnfFormula, CnfError> {
    let mut covering = CnfFormula::new(base.variable_count());
    for cube in cubes {
        let negated: Vec<CnfLit> = cube.iter().map(|lit| lit.negated()).collect();
        covering.add_clause(CnfClause::new(negated))?;
    }
    Ok(covering)
}

/// The complete evidence that `base` is UNSAT, decomposed into cubes
/// (ADR-0543).
///
/// `cube_proofs[i]` is a DRAT proof of [`augmented_formula`]`(base,
/// cubes[i])`. `covering_proof` is a DRAT proof of
/// [`covering_formula`]`(base, cubes)`. Neither formula is stored — the whole
/// point of [`check_cube_refutation`] is that it rebuilds both from `base` and
/// `cubes` itself rather than trusting a formula supplied alongside the
/// proofs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CubeRefutation {
    /// The case split. `cubes[i]` is refuted by `cube_proofs[i]`.
    pub cubes: Vec<Cube>,
    /// Per-cube DRAT refutations, same length and order as `cubes`.
    pub cube_proofs: Vec<Vec<DratStep>>,
    /// The DRAT refutation of the covering formula (§3): proves `cubes` is
    /// exhaustive.
    pub covering_proof: Vec<DratStep>,
}

/// Why [`check_cube_refutation`] declined to confirm `base` is UNSAT.
///
/// Every variant is an **undecided** result, never "base is SAT" — a
/// refutation that fails to check tells you nothing about `base` itself,
/// exactly as [`ProofSolveOutcome::ResourceOut`]/`Interrupted` are undecided
/// rather than a guessed verdict.
#[derive(Debug)]
pub enum CubeCheckError {
    /// `cubes` was empty — there is nothing to check and no way to derive
    /// UNSAT from zero cases.
    EmptyCubeSet,
    /// `cubes` and `cube_proofs` had different lengths.
    CubeCountMismatch {
        /// Number of cubes.
        cubes: usize,
        /// Number of per-cube proofs.
        proofs: usize,
    },
    /// Cube `cube` named a variable outside `base` while building its
    /// augmented formula.
    InvalidCubeLiteral {
        /// Zero-based index into `cubes`/`cube_proofs`.
        cube: usize,
        /// The underlying error.
        source: CnfError,
    },
    /// Cube `cube`'s proof failed DRAT verification against `F ∧ cubes[cube]`.
    CubeProofInvalid {
        /// Zero-based index into `cubes`/`cube_proofs`.
        cube: usize,
        /// The underlying error.
        source: DratError,
    },
    /// Cube `cube`'s proof verified step-by-step but never derived the empty
    /// clause — it does not actually refute `F ∧ cubes[cube]`.
    CubeProofIncomplete {
        /// Zero-based index into `cubes`/`cube_proofs`.
        cube: usize,
    },
    /// A cube literal named a variable outside `base` while building the
    /// covering formula.
    CoveringFormulaInvalid {
        /// The underlying error.
        source: CnfError,
    },
    /// The covering proof failed DRAT verification against the covering
    /// formula — the cubes were not shown exhaustive.
    CoveringProofInvalid {
        /// The underlying error.
        source: DratError,
    },
    /// The covering proof verified step-by-step but never derived the empty
    /// clause — the covering formula was not shown UNSAT, so the cubes were
    /// not shown exhaustive.
    CoveringProofIncomplete,
}

impl fmt::Display for CubeCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CubeCheckError::EmptyCubeSet => write!(f, "cube refutation has no cubes"),
            CubeCheckError::CubeCountMismatch { cubes, proofs } => write!(
                f,
                "{cubes} cubes but {proofs} per-cube proofs (must match 1:1)"
            ),
            CubeCheckError::InvalidCubeLiteral { cube, source } => {
                write!(f, "cube {cube}: {source}")
            }
            CubeCheckError::CubeProofInvalid { cube, source } => {
                write!(f, "cube {cube}: proof does not verify: {source}")
            }
            CubeCheckError::CubeProofIncomplete { cube } => write!(
                f,
                "cube {cube}: proof verified but never derived the empty clause"
            ),
            CubeCheckError::CoveringFormulaInvalid { source } => {
                write!(f, "covering formula: {source}")
            }
            CubeCheckError::CoveringProofInvalid { source } => {
                write!(f, "covering proof does not verify: {source}")
            }
            CubeCheckError::CoveringProofIncomplete => write!(
                f,
                "covering proof verified but never derived the empty clause \
                 (the cubes were not shown to exhaust the space)"
            ),
        }
    }
}

impl core::error::Error for CubeCheckError {}

/// Independently verifies that `refutation` proves `base` UNSAT, **without
/// trusting how `refutation.cubes` was chosen**.
///
/// Rebuilds every formula it checks — each cube's [`augmented_formula`] and
/// the [`covering_formula`] — from `base` and `refutation.cubes` alone, then
/// checks each with the ordinary, unmodified [`crate::check_drat`]. See
/// ADR-0543 for why this suffices: a non-covering or mismatched cube set
/// cannot produce a DRAT proof for the checker's own construction, because
/// `check_drat` (ADR-0011/0012) is already trusted not to accept a forged
/// refutation of a satisfiable formula.
///
/// # Errors
///
/// Returns a [`CubeCheckError`] describing the first check that failed. Every
/// variant is an undecided result: `base` may still be UNSAT (via a different
/// refutation) or SAT — this function never reports SAT.
pub fn check_cube_refutation(
    base: &CnfFormula,
    refutation: &CubeRefutation,
) -> Result<(), CubeCheckError> {
    if refutation.cubes.is_empty() {
        return Err(CubeCheckError::EmptyCubeSet);
    }
    if refutation.cubes.len() != refutation.cube_proofs.len() {
        return Err(CubeCheckError::CubeCountMismatch {
            cubes: refutation.cubes.len(),
            proofs: refutation.cube_proofs.len(),
        });
    }

    for (index, (cube, proof)) in refutation
        .cubes
        .iter()
        .zip(refutation.cube_proofs.iter())
        .enumerate()
    {
        let augmented =
            augmented_formula(base, cube).map_err(|source| CubeCheckError::InvalidCubeLiteral {
                cube: index,
                source,
            })?;
        match check_drat(&augmented, proof) {
            Ok(true) => {}
            Ok(false) => return Err(CubeCheckError::CubeProofIncomplete { cube: index }),
            Err(source) => {
                return Err(CubeCheckError::CubeProofInvalid {
                    cube: index,
                    source,
                });
            }
        }
    }

    let covering = covering_formula(base, &refutation.cubes)
        .map_err(|source| CubeCheckError::CoveringFormulaInvalid { source })?;
    match check_drat(&covering, &refutation.covering_proof) {
        Ok(true) => Ok(()),
        Ok(false) => Err(CubeCheckError::CoveringProofIncomplete),
        Err(source) => Err(CubeCheckError::CoveringProofInvalid { source }),
    }
}

/// Checks a composite refutation from textual DRAT readers without first
/// materializing parsed proof-step vectors.
///
/// This is the retained-artifact route for large leaves. It rebuilds the same
/// `base AND cube` and covering formulas as [`check_cube_refutation`], then
/// delegates each ordinary proof to the file-backed backward checker.
///
/// # Errors
///
/// Returns a [`CubeCheckError`] for an empty cube set, a reader-count mismatch,
/// malformed cube literals, rejected/incomplete leaf proofs, or a rejected/
/// incomplete covering proof.
pub fn check_cube_refutation_backward_readers<R, I>(
    base: &CnfFormula,
    cubes: &[Cube],
    cube_proofs: I,
    covering_proof: R,
) -> Result<(), CubeCheckError>
where
    R: BufRead,
    I: IntoIterator<Item = R>,
{
    if cubes.is_empty() {
        return Err(CubeCheckError::EmptyCubeSet);
    }
    let mut proofs = cube_proofs.into_iter();
    for (index, cube) in cubes.iter().enumerate() {
        let Some(reader) = proofs.next() else {
            return Err(CubeCheckError::CubeCountMismatch {
                cubes: cubes.len(),
                proofs: index,
            });
        };
        let augmented =
            augmented_formula(base, cube).map_err(|source| CubeCheckError::InvalidCubeLiteral {
                cube: index,
                source,
            })?;
        match check_drat_backward_reader(&augmented, reader) {
            Ok(true) => {}
            Ok(false) => return Err(CubeCheckError::CubeProofIncomplete { cube: index }),
            Err(source) => {
                return Err(CubeCheckError::CubeProofInvalid {
                    cube: index,
                    source,
                });
            }
        }
    }
    if proofs.next().is_some() {
        return Err(CubeCheckError::CubeCountMismatch {
            cubes: cubes.len(),
            proofs: cubes.len() + 1 + proofs.count(),
        });
    }
    let covering = covering_formula(base, cubes)
        .map_err(|source| CubeCheckError::CoveringFormulaInvalid { source })?;
    match check_drat_backward_reader(&covering, covering_proof) {
        Ok(true) => Ok(()),
        Ok(false) => Err(CubeCheckError::CoveringProofIncomplete),
        Err(source) => Err(CubeCheckError::CoveringProofInvalid { source }),
    }
}

/// A recursively split, file-backed cube refutation.
///
/// A leaf carries an ordinary DRAT proof of the formula at that node. A split
/// carries an exhaustive set of child cubes, one recursively checkable child
/// per cube, and a DRAT proof that the child cubes cover the node. Formulas are
/// never supplied by the artifact: the checker rebuilds every child as
/// `parent AND cube` while descending.
pub enum CubeRefutationReaderTree<R> {
    /// An ordinary DRAT refutation of the current formula.
    Leaf(R),
    /// An exhaustive recursive split of the current formula.
    Split {
        /// Child cubes, in artifact order.
        cubes: Vec<Cube>,
        /// One proof tree per child cube.
        children: Vec<CubeRefutationReaderTree<R>>,
        /// DRAT refutation of the covering formula for `cubes`.
        covering_proof: R,
    },
}

/// Why a recursive cube refutation did not certify.
#[derive(Debug)]
pub enum CubeTreeCheckError {
    /// A split contained no cubes.
    EmptyCubeSet {
        /// Zero-based child-index path to the split.
        path: Vec<usize>,
    },
    /// The cube and child counts differ.
    ChildCountMismatch {
        /// Zero-based child-index path to the split.
        path: Vec<usize>,
        /// Number of declared cubes.
        cubes: usize,
        /// Number of supplied child trees.
        children: usize,
    },
    /// A child cube could not be appended to its parent formula.
    InvalidCube {
        /// Zero-based child-index path including the invalid child.
        path: Vec<usize>,
        /// Formula-construction error.
        source: CnfError,
    },
    /// A leaf proof parsed but did not derive the empty clause.
    LeafIncomplete {
        /// Zero-based child-index path to the leaf.
        path: Vec<usize>,
    },
    /// A leaf proof was invalid.
    LeafInvalid {
        /// Zero-based child-index path to the leaf.
        path: Vec<usize>,
        /// DRAT-checking error.
        source: DratError,
    },
    /// The covering formula could not be constructed.
    CoveringFormulaInvalid {
        /// Zero-based child-index path to the split.
        path: Vec<usize>,
        /// Formula-construction error.
        source: CnfError,
    },
    /// The covering proof parsed but did not derive the empty clause.
    CoveringProofIncomplete {
        /// Zero-based child-index path to the split.
        path: Vec<usize>,
    },
    /// The covering proof was invalid.
    CoveringProofInvalid {
        /// Zero-based child-index path to the split.
        path: Vec<usize>,
        /// DRAT-checking error.
        source: DratError,
    },
}

impl fmt::Display for CubeTreeCheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyCubeSet { path } => write!(f, "empty cube split at {path:?}"),
            Self::ChildCountMismatch {
                path,
                cubes,
                children,
            } => write!(
                f,
                "cube/child count mismatch at {path:?}: {cubes} cubes, {children} children"
            ),
            Self::InvalidCube { path, source } => {
                write!(f, "invalid cube at {path:?}: {source}")
            }
            Self::LeafIncomplete { path } => {
                write!(f, "leaf at {path:?} did not derive the empty clause")
            }
            Self::LeafInvalid { path, source } => {
                write!(f, "invalid leaf proof at {path:?}: {source}")
            }
            Self::CoveringFormulaInvalid { path, source } => {
                write!(f, "invalid covering formula at {path:?}: {source}")
            }
            Self::CoveringProofIncomplete { path } => {
                write!(
                    f,
                    "covering proof at {path:?} did not derive the empty clause"
                )
            }
            Self::CoveringProofInvalid { path, source } => {
                write!(f, "invalid covering proof at {path:?}: {source}")
            }
        }
    }
}

impl core::error::Error for CubeTreeCheckError {}

/// Checks a recursively split refutation with file-backed backward DRAT.
///
/// Every child formula and every covering formula is reconstructed from the
/// trusted root formula and the artifact's literal cubes. The `path` in an
/// error is the zero-based child-index path from the root, so a failed leaf in
/// a large adaptive tree is named precisely.
///
/// # Errors
///
/// Rejects an empty or malformed split, an out-of-range cube literal, or any
/// incomplete/invalid leaf or covering proof.
pub fn check_cube_refutation_reader_tree<R: BufRead>(
    base: &CnfFormula,
    tree: CubeRefutationReaderTree<R>,
) -> Result<(), CubeTreeCheckError> {
    fn visit<R: BufRead>(
        formula: &CnfFormula,
        tree: CubeRefutationReaderTree<R>,
        path: &mut Vec<usize>,
    ) -> Result<(), CubeTreeCheckError> {
        match tree {
            CubeRefutationReaderTree::Leaf(proof) => {
                match check_drat_backward_reader(formula, proof) {
                    Ok(true) => Ok(()),
                    Ok(false) => Err(CubeTreeCheckError::LeafIncomplete { path: path.clone() }),
                    Err(source) => Err(CubeTreeCheckError::LeafInvalid {
                        path: path.clone(),
                        source,
                    }),
                }
            }
            CubeRefutationReaderTree::Split {
                cubes,
                children,
                covering_proof,
            } => {
                if cubes.is_empty() {
                    return Err(CubeTreeCheckError::EmptyCubeSet { path: path.clone() });
                }
                if cubes.len() != children.len() {
                    return Err(CubeTreeCheckError::ChildCountMismatch {
                        path: path.clone(),
                        cubes: cubes.len(),
                        children: children.len(),
                    });
                }
                for (index, (cube, child)) in cubes.iter().zip(children).enumerate() {
                    path.push(index);
                    let child_formula = augmented_formula(formula, cube).map_err(|source| {
                        CubeTreeCheckError::InvalidCube {
                            path: path.clone(),
                            source,
                        }
                    })?;
                    visit(&child_formula, child, path)?;
                    path.pop();
                }
                let covering = covering_formula(formula, &cubes).map_err(|source| {
                    CubeTreeCheckError::CoveringFormulaInvalid {
                        path: path.clone(),
                        source,
                    }
                })?;
                match check_drat_backward_reader(&covering, covering_proof) {
                    Ok(true) => Ok(()),
                    Ok(false) => {
                        Err(CubeTreeCheckError::CoveringProofIncomplete { path: path.clone() })
                    }
                    Err(source) => Err(CubeTreeCheckError::CoveringProofInvalid {
                        path: path.clone(),
                        source,
                    }),
                }
            }
        }
    }

    visit(base, tree, &mut Vec::new())
}

/// Why [`boolean_product_cubes`] declined to generate a cube set.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CubeGenError {
    /// More selector variables were given than [`MAX_PRODUCT_CUBE_SELECTORS`]
    /// allows (`2^selectors` cubes would result).
    TooManySelectors {
        /// Number of selector variables requested.
        selectors: usize,
        /// The allowed maximum.
        max: usize,
    },
}

impl fmt::Display for CubeGenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CubeGenError::TooManySelectors { selectors, max } => write!(
                f,
                "{selectors} selector variables would expand to 2^{selectors} cubes; \
                 the cap is {max}"
            ),
        }
    }
}

impl core::error::Error for CubeGenError {}

/// Generates the full boolean product over `selectors`: all `2^k` sign
/// combinations, each one cube. Exhaustive by construction (every total
/// assignment fixes each selector one way or the other, so it satisfies
/// exactly one of these cubes) — the degenerate case of a balanced binary
/// decision tree, useful as a first cube generator because it needs no
/// splitting heuristic. [`check_cube_refutation`] does not special-case this
/// shape: exhaustiveness is still verified via the covering formula exactly
/// as for any other cube set.
///
/// # Errors
///
/// Returns [`CubeGenError::TooManySelectors`] if `selectors.len()` exceeds
/// [`MAX_PRODUCT_CUBE_SELECTORS`].
pub fn boolean_product_cubes(selectors: &[CnfVar]) -> Result<Vec<Cube>, CubeGenError> {
    let count = selectors.len();
    if count > MAX_PRODUCT_CUBE_SELECTORS {
        return Err(CubeGenError::TooManySelectors {
            selectors: count,
            max: MAX_PRODUCT_CUBE_SELECTORS,
        });
    }
    let total = 1usize << count;
    let mut cubes = Vec::with_capacity(total);
    for mask in 0..total {
        let mut cube = Vec::with_capacity(count);
        for (bit, &var) in selectors.iter().enumerate() {
            let positive = CnfLit::positive(var);
            cube.push(if (mask >> bit) & 1 == 1 {
                positive
            } else {
                positive.negated()
            });
        }
        cubes.push(cube);
    }
    Ok(cubes)
}

/// Per-cube outcome recorded by [`certify_by_cubes`], for measurement
/// (cube count, how many closed trivially, cost of the hardest one) without
/// needing conflict-count instrumentation inside `proof_sat.rs`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CubeOutcome {
    /// `F ∧ cube` was refuted; carries the DRAT proof's length (step count) as
    /// a proxy for how much search the cube cost.
    Unsat {
        /// Number of DRAT steps in the refutation.
        proof_len: usize,
    },
    /// `F ∧ cube` was satisfiable — since `F ∧ cube` entails `F`, this model
    /// also satisfies `F`, so [`certify_by_cubes`] reports the whole query
    /// SAT and does not examine remaining cubes.
    Sat,
    /// The conflict budget was exhausted before this cube decided.
    ResourceOut,
    /// The wall-clock deadline passed before this cube decided.
    Interrupted,
}

/// One cube's outcome plus which cube it was (index into the generator's
/// output) and how many literals it fixed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CubeStats {
    /// Index into the cube list this run was given.
    pub cube: usize,
    /// Number of literals fixed by this cube.
    pub literals: usize,
    /// What happened.
    pub outcome: CubeOutcome,
}

/// The end-to-end result of [`certify_by_cubes`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CubeCertifyOutcome {
    /// Every cube refuted, and the cube set was shown exhaustive: `base` is
    /// UNSAT, with a checkable [`CubeRefutation`].
    Unsat(CubeRefutation),
    /// Some cube was satisfiable; carries a model of `base` (see
    /// [`CubeOutcome::Sat`]).
    Sat(CnfAssignment),
    /// Every cube refuted, but the covering proof did not close within its
    /// budget — exhaustiveness was not established, so the composite verdict
    /// is undecided even though every individual cube is UNSAT.
    CoveringUndecided,
    /// At least one cube did not decide (`ResourceOut`/`Interrupted`) and none
    /// was SAT — undecided. Re-splitting the undecided cube(s) is the natural
    /// next step (not implemented by this function).
    Undecided,
}

/// Shards certification of `base` into `cubes`, each refuted independently
/// under its own conflict budget, then certifies the cube set is exhaustive.
///
/// Every cube is attempted (up to an early exit on the first SAT cube), so the
/// returned stats describe the whole batch even when the composite verdict is
/// [`CubeCertifyOutcome::Undecided`] — this is the measurement the sharding
/// exists to make possible: cube count, how many closed near-trivially, and
/// the cost of the hardest one, without waiting for a monolithic run to
/// finish.
///
/// `deadline` is an absolute wall-clock bound applied to every cube's solve
/// (and to the covering-formula solve), exactly as
/// [`solve_with_drat_proof_with_limits`] already applies it — this function
/// adds no new unbounded search.
pub fn certify_by_cubes(
    base: &CnfFormula,
    cubes: Vec<Cube>,
    deadline: Option<Instant>,
    max_conflicts_per_cube: usize,
    max_conflicts_covering: usize,
) -> (CubeCertifyOutcome, Vec<CubeStats>) {
    let mut stats = Vec::with_capacity(cubes.len());
    let mut proofs = Vec::with_capacity(cubes.len());
    let mut any_undecided = false;

    for (index, cube) in cubes.iter().enumerate() {
        // An out-of-range cube literal cannot be solved; record it as
        // undecided rather than panicking or guessing a verdict.
        let Ok(augmented) = augmented_formula(base, cube) else {
            stats.push(CubeStats {
                cube: index,
                literals: cube.len(),
                outcome: CubeOutcome::ResourceOut,
            });
            any_undecided = true;
            continue;
        };
        match solve_with_drat_proof_with_limits(&augmented, deadline, max_conflicts_per_cube) {
            ProofSolveOutcome::Unsat(proof) => {
                stats.push(CubeStats {
                    cube: index,
                    literals: cube.len(),
                    outcome: CubeOutcome::Unsat {
                        proof_len: proof.len(),
                    },
                });
                proofs.push(proof);
            }
            ProofSolveOutcome::Sat(model) => {
                stats.push(CubeStats {
                    cube: index,
                    literals: cube.len(),
                    outcome: CubeOutcome::Sat,
                });
                return (CubeCertifyOutcome::Sat(model), stats);
            }
            ProofSolveOutcome::ResourceOut => {
                stats.push(CubeStats {
                    cube: index,
                    literals: cube.len(),
                    outcome: CubeOutcome::ResourceOut,
                });
                any_undecided = true;
            }
            ProofSolveOutcome::Interrupted => {
                stats.push(CubeStats {
                    cube: index,
                    literals: cube.len(),
                    outcome: CubeOutcome::Interrupted,
                });
                any_undecided = true;
            }
        }
    }

    if any_undecided {
        return (CubeCertifyOutcome::Undecided, stats);
    }

    let Ok(covering) = covering_formula(base, &cubes) else {
        return (CubeCertifyOutcome::Undecided, stats);
    };
    match solve_with_drat_proof_with_limits(&covering, deadline, max_conflicts_covering) {
        ProofSolveOutcome::Unsat(covering_proof) => (
            CubeCertifyOutcome::Unsat(CubeRefutation {
                cubes,
                cube_proofs: proofs,
                covering_proof,
            }),
            stats,
        ),
        // A satisfiable covering formula means the cubes do not exhaust the
        // space; that is a splitter bug, not evidence about `base`, so it is
        // reported as undecided rather than as `base` being SAT.
        ProofSolveOutcome::Sat(_)
        | ProofSolveOutcome::ResourceOut
        | ProofSolveOutcome::Interrupted => (CubeCertifyOutcome::CoveringUndecided, stats),
    }
}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::*;
    use crate::{CnfClause, CnfFormula, CnfLit, CnfVar, write_drat};

    /// A base formula over `s0, s1` (free selectors) plus four payload
    /// variables `p00, p01, p10, p11`, one per `(s0, s1)` sign combination.
    /// For each combination `(a, b)`, two clauses pin `p_ab` both ways but
    /// only when `s0 == a ∧ s1 == b`:
    ///
    /// ```text
    /// (s0 != a) ∨ (s1 != b) ∨  p_ab
    /// (s0 != a) ∨ (s1 != b) ∨ ¬p_ab
    /// ```
    ///
    /// Fixing `(s0, s1)` to `(a, b)` unit-propagates both disjuncts away,
    /// forcing `p_ab` and `¬p_ab` -- a contradiction genuinely specific to
    /// that combination (the other three payload variables stay unconstrained
    /// by it, since their clauses are already satisfied by a selector
    /// disjunct). Every one of the four `(s0, s1)` sign combinations refutes,
    /// each via a *different* payload variable, so a per-cube proof cannot be
    /// silently replayed against a different cube's formula -- exactly what
    /// [`check_cube_refutation_rejects_a_proof_for_the_wrong_cube`] exercises.
    fn selector_gated_unsat() -> (CnfFormula, CnfVar, CnfVar, CnfVar) {
        // Variables: 0=s0, 1=s1, 2=p00, 3=p01, 4=p10, 5=p11.
        let mut formula = CnfFormula::new(6);
        let s0 = CnfVar::new(0).unwrap();
        let s1 = CnfVar::new(1).unwrap();
        let s0_lit = CnfLit::positive(s0);
        let s1_lit = CnfLit::positive(s1);
        for (index, &(a, b)) in [(false, false), (false, true), (true, false), (true, true)]
            .iter()
            .enumerate()
        {
            let p = CnfVar::new(2 + index).unwrap();
            let p_lit = CnfLit::positive(p);
            // Disjunct is false exactly when s0 == a (resp. s1 == b).
            let s0_disjunct = if a { s0_lit.negated() } else { s0_lit };
            let s1_disjunct = if b { s1_lit.negated() } else { s1_lit };
            formula
                .add_clause(CnfClause::new(vec![s0_disjunct, s1_disjunct, p_lit]))
                .unwrap();
            formula
                .add_clause(CnfClause::new(vec![
                    s0_disjunct,
                    s1_disjunct,
                    p_lit.negated(),
                ]))
                .unwrap();
        }
        // Fourth return slot kept for call-site compatibility; unused by
        // tests that don't need a specific payload variable.
        let p00 = CnfVar::new(2).unwrap();
        (formula, s0, s1, p00)
    }

    #[test]
    fn boolean_product_cubes_enumerates_all_signs() {
        let a = CnfVar::new(0).unwrap();
        let b = CnfVar::new(1).unwrap();
        let cubes = boolean_product_cubes(&[a, b]).unwrap();
        assert_eq!(cubes.len(), 4);
        let mut signs: Vec<(bool, bool)> = cubes
            .iter()
            .map(|cube| {
                let a_lit = cube.iter().find(|l| l.var() == a).unwrap();
                let b_lit = cube.iter().find(|l| l.var() == b).unwrap();
                (!a_lit.is_negated(), !b_lit.is_negated())
            })
            .collect();
        signs.sort_unstable();
        assert_eq!(
            signs,
            vec![(false, false), (false, true), (true, false), (true, true)]
        );
    }

    #[test]
    fn boolean_product_cubes_rejects_too_many_selectors() {
        let vars: Vec<CnfVar> = (0..=MAX_PRODUCT_CUBE_SELECTORS)
            .map(|i| CnfVar::new(i).unwrap())
            .collect();
        let err = boolean_product_cubes(&vars).unwrap_err();
        assert_eq!(
            err,
            CubeGenError::TooManySelectors {
                selectors: MAX_PRODUCT_CUBE_SELECTORS + 1,
                max: MAX_PRODUCT_CUBE_SELECTORS,
            }
        );
    }

    #[test]
    fn certify_by_cubes_produces_a_checkable_refutation() {
        let (base, s0, s1, _x) = selector_gated_unsat();
        let cubes = boolean_product_cubes(&[s0, s1]).unwrap();
        let (outcome, stats) = certify_by_cubes(&base, cubes, None, 10_000, 10_000);
        assert_eq!(stats.len(), 4, "every cube must be attempted");
        for stat in &stats {
            assert!(
                matches!(stat.outcome, CubeOutcome::Unsat { .. }),
                "every cube refutes regardless of the sibling selector: {stat:?}"
            );
        }
        let CubeCertifyOutcome::Unsat(refutation) = outcome else {
            panic!("expected Unsat, got {outcome:?}");
        };
        assert_eq!(refutation.cubes.len(), 4);
        check_cube_refutation(&base, &refutation)
            .expect("an honestly produced refutation must check");
    }

    #[test]
    fn file_backed_checker_accepts_the_same_composition() {
        let (base, s0, s1, _x) = selector_gated_unsat();
        let cubes = boolean_product_cubes(&[s0, s1]).unwrap();
        let (outcome, _stats) = certify_by_cubes(&base, cubes, None, 10_000, 10_000);
        let CubeCertifyOutcome::Unsat(refutation) = outcome else {
            panic!("expected Unsat");
        };
        let readers: Vec<_> = refutation
            .cube_proofs
            .iter()
            .map(|proof| Cursor::new(write_drat(proof).into_bytes()))
            .collect();
        let covering = Cursor::new(write_drat(&refutation.covering_proof).into_bytes());
        check_cube_refutation_backward_readers(&base, &refutation.cubes, readers, covering)
            .expect("textual file-backed composition must check");
    }

    #[test]
    fn recursive_file_backed_checker_rebuilds_every_level() {
        let (base, s0, s1, _x) = selector_gated_unsat();
        let root_cubes = boolean_product_cubes(&[s0]).unwrap();
        let (root_outcome, _) = certify_by_cubes(&base, root_cubes, None, 10_000, 10_000);
        let CubeCertifyOutcome::Unsat(root) = root_outcome else {
            panic!("expected root refutation");
        };

        let first_formula = augmented_formula(&base, &root.cubes[0]).unwrap();
        let nested_cubes = boolean_product_cubes(&[s1]).unwrap();
        let (nested_outcome, _) =
            certify_by_cubes(&first_formula, nested_cubes, None, 10_000, 10_000);
        let CubeCertifyOutcome::Unsat(nested) = nested_outcome else {
            panic!("expected nested refutation");
        };
        let nested_children = nested
            .cube_proofs
            .iter()
            .map(|proof| {
                CubeRefutationReaderTree::Leaf(Cursor::new(write_drat(proof).into_bytes()))
            })
            .collect();
        let tree = CubeRefutationReaderTree::Split {
            cubes: root.cubes.clone(),
            children: vec![
                CubeRefutationReaderTree::Split {
                    cubes: nested.cubes,
                    children: nested_children,
                    covering_proof: Cursor::new(write_drat(&nested.covering_proof).into_bytes()),
                },
                CubeRefutationReaderTree::Leaf(Cursor::new(
                    write_drat(&root.cube_proofs[1]).into_bytes(),
                )),
            ],
            covering_proof: Cursor::new(write_drat(&root.covering_proof).into_bytes()),
        };
        check_cube_refutation_reader_tree(&base, tree)
            .expect("recursive composition must check from the root formula");
    }

    #[test]
    fn recursive_file_backed_checker_rejects_a_missing_child() {
        let (base, s0, _s1, _x) = selector_gated_unsat();
        let cubes = boolean_product_cubes(&[s0]).unwrap();
        let tree = CubeRefutationReaderTree::Split {
            cubes,
            children: vec![CubeRefutationReaderTree::Leaf(Cursor::new(Vec::new()))],
            covering_proof: Cursor::new(Vec::new()),
        };
        assert!(matches!(
            check_cube_refutation_reader_tree(&base, tree),
            Err(CubeTreeCheckError::ChildCountMismatch { .. })
        ));
    }

    #[test]
    fn file_backed_checker_rejects_a_missing_reader() {
        let (base, s0, s1, _x) = selector_gated_unsat();
        let cubes = boolean_product_cubes(&[s0, s1]).unwrap();
        let (outcome, _stats) = certify_by_cubes(&base, cubes, None, 10_000, 10_000);
        let CubeCertifyOutcome::Unsat(refutation) = outcome else {
            panic!("expected Unsat");
        };
        let readers: Vec<_> = refutation
            .cube_proofs
            .iter()
            .take(refutation.cube_proofs.len() - 1)
            .map(|proof| Cursor::new(write_drat(proof).into_bytes()))
            .collect();
        let covering = Cursor::new(write_drat(&refutation.covering_proof).into_bytes());
        assert!(matches!(
            check_cube_refutation_backward_readers(&base, &refutation.cubes, readers, covering),
            Err(CubeCheckError::CubeCountMismatch { .. })
        ));
    }

    #[test]
    fn check_cube_refutation_rejects_a_dropped_cube() {
        let (base, s0, s1, _x) = selector_gated_unsat();
        let cubes = boolean_product_cubes(&[s0, s1]).unwrap();
        let (outcome, _stats) = certify_by_cubes(&base, cubes, None, 10_000, 10_000);
        let CubeCertifyOutcome::Unsat(mut refutation) = outcome else {
            panic!("expected Unsat");
        };
        // Drop one of the four cubes (and its proof): the remaining three no
        // longer cover the space of (s0, s1), so this must be rejected, not
        // silently accepted as a smaller valid refutation.
        refutation.cubes.pop();
        refutation.cube_proofs.pop();
        let err = check_cube_refutation(&base, &refutation).unwrap_err();
        assert!(
            matches!(
                err,
                CubeCheckError::CoveringProofInvalid { .. }
                    | CubeCheckError::CoveringProofIncomplete
            ),
            "dropping a cube must be caught by the covering check, got {err}"
        );
    }

    #[test]
    fn check_cube_refutation_rejects_mismatched_proof_count() {
        let (base, s0, s1, _x) = selector_gated_unsat();
        let cubes = boolean_product_cubes(&[s0, s1]).unwrap();
        let (outcome, _stats) = certify_by_cubes(&base, cubes, None, 10_000, 10_000);
        let CubeCertifyOutcome::Unsat(mut refutation) = outcome else {
            panic!("expected Unsat");
        };
        refutation.cube_proofs.pop();
        let err = check_cube_refutation(&base, &refutation).unwrap_err();
        assert!(matches!(err, CubeCheckError::CubeCountMismatch { .. }));
    }

    #[test]
    fn check_cube_refutation_rejects_an_empty_per_cube_proof() {
        let (base, s0, s1, _x) = selector_gated_unsat();
        let cubes = boolean_product_cubes(&[s0, s1]).unwrap();
        let (outcome, _stats) = certify_by_cubes(&base, cubes, None, 10_000, 10_000);
        let CubeCertifyOutcome::Unsat(mut refutation) = outcome else {
            panic!("expected Unsat");
        };
        // An adversarial (or buggy) producer submits no proof steps at all for
        // one cube. `check_drat` verifies trivially (nothing to fail) but
        // never derives the empty clause, so this must be caught as
        // incomplete, not silently accepted.
        refutation.cube_proofs[0] = Vec::new();
        let err = check_cube_refutation(&base, &refutation).unwrap_err();
        assert!(matches!(
            err,
            CubeCheckError::CubeProofIncomplete { cube: 0 }
        ));
    }

    #[test]
    fn check_cube_refutation_rejects_a_forged_proof_of_a_satisfiable_cube() {
        // `base` has no clauses at all -- unconditionally SAT, for every
        // value of every variable. Cube-splitting on `s` cannot make it
        // UNSAT, so a "proof" claiming the empty clause immediately is a
        // forgery, and `check_cube_refutation` must refuse it (this is the
        // ADR-0543 crux exercised directly: the checker never accepts a
        // formula it did not itself verify is UNSAT).
        let base = CnfFormula::new(2);
        let s = CnfVar::new(0).unwrap();
        let cubes = boolean_product_cubes(&[s]).unwrap();
        assert_eq!(cubes.len(), 2);
        let covering = covering_formula(&base, &cubes).unwrap();
        let ProofSolveOutcome::Unsat(covering_proof) =
            solve_with_drat_proof_with_limits(&covering, None, 10_000)
        else {
            panic!("¬s ∨ s exhausts the space and must refute");
        };
        let forged = CubeRefutation {
            cubes,
            // Both cubes "proved" by immediately claiming the empty clause --
            // false, since `base ∧ cube` is satisfiable for either cube.
            cube_proofs: vec![
                vec![DratStep::Add(Vec::new())],
                vec![DratStep::Add(Vec::new())],
            ],
            covering_proof,
        };
        let err = check_cube_refutation(&base, &forged).unwrap_err();
        assert!(matches!(
            err,
            CubeCheckError::CubeProofInvalid { cube: 0, .. }
        ));
    }

    #[test]
    fn check_cube_refutation_rejects_empty_cube_set() {
        let (base, _s0, _s1, _x) = selector_gated_unsat();
        let refutation = CubeRefutation {
            cubes: Vec::new(),
            cube_proofs: Vec::new(),
            covering_proof: Vec::new(),
        };
        let err = check_cube_refutation(&base, &refutation).unwrap_err();
        assert!(matches!(err, CubeCheckError::EmptyCubeSet));
    }

    #[test]
    fn check_cube_refutation_rejects_out_of_range_cube_literal() {
        let (base, s0, s1, _x) = selector_gated_unsat();
        let cubes = boolean_product_cubes(&[s0, s1]).unwrap();
        let (outcome, _stats) = certify_by_cubes(&base, cubes, None, 10_000, 10_000);
        let CubeCertifyOutcome::Unsat(mut refutation) = outcome else {
            panic!("expected Unsat");
        };
        let bogus = CnfVar::new(base.variable_count() + 5).unwrap();
        refutation.cubes[0] = vec![CnfLit::positive(bogus)];
        let err = check_cube_refutation(&base, &refutation).unwrap_err();
        assert!(matches!(
            err,
            CubeCheckError::InvalidCubeLiteral { cube: 0, .. }
        ));
    }

    #[test]
    fn certify_by_cubes_reports_a_sat_cube_as_sat() {
        // A satisfiable base formula (`y` is unconstrained) split into cubes
        // over an unrelated selector `s`. Neither cube refutes, so the whole
        // thing must come back Sat, carrying a model of `base`.
        let mut base = CnfFormula::new(2);
        let s = CnfVar::new(0).unwrap();
        let y = CnfVar::new(1).unwrap();
        base.add_clause(CnfClause::new(vec![
            CnfLit::positive(y),
            CnfLit::positive(y).negated(),
        ]))
        .unwrap();
        let cubes = boolean_product_cubes(&[s]).unwrap();
        let (outcome, stats) = certify_by_cubes(&base, cubes, None, 10_000, 10_000);
        assert!(matches!(outcome, CubeCertifyOutcome::Sat(_)));
        assert!(
            stats
                .iter()
                .any(|entry| matches!(entry.outcome, CubeOutcome::Sat))
        );
        if let CubeCertifyOutcome::Sat(model) = outcome {
            assert!(base.evaluate(model.values()).unwrap());
        }
    }

    #[test]
    fn augmented_formula_rejects_out_of_range_literal() {
        let base = CnfFormula::new(1);
        let bogus = CnfVar::new(3).unwrap();
        let err = augmented_formula(&base, &[CnfLit::positive(bogus)]).unwrap_err();
        assert!(matches!(err, CnfError::InvalidVariable { .. }));
    }

    #[test]
    fn covering_formula_negates_each_cube() {
        let base = CnfFormula::new(2);
        let a = CnfVar::new(0).unwrap();
        let b = CnfVar::new(1).unwrap();
        let cubes = vec![
            vec![CnfLit::positive(a), CnfLit::positive(b)],
            vec![CnfLit::positive(a).negated()],
        ];
        let covering = covering_formula(&base, &cubes).unwrap();
        assert_eq!(covering.clauses().len(), 2);
        assert_eq!(
            covering.clauses()[0].lits(),
            &[CnfLit::positive(a).negated(), CnfLit::positive(b).negated()]
        );
        assert_eq!(covering.clauses()[1].lits(), &[CnfLit::positive(a)]);
    }
}
