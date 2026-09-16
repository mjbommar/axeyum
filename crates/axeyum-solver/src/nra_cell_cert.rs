//! Checkable evidence for a **single-cell CAD** refutation over the reals
//! (ADR-2121, lane `NRA-SINGLE-CELL`).
//!
//! # What the certificate is
//!
//! [`crate::nra_single_cell`] refutes a conjunction of polynomial comparisons by
//! a *cylindrical algebraic covering*: at each level of a fixed variable order it
//! builds a finite set of **boundary polynomials**, and the real roots of that
//! set cut the line into cells on which every boundary polynomial has a constant
//! sign. Each cell is then killed for one of two reasons:
//!
//! * an atom of that level is violated on the whole cell, or
//! * one level down, *every* value of the next variable is already refuted — and
//!   the sub-covering that proves it is carried here, recursively.
//!
//! A [`CellRefutation`] is that tree, plus the atoms it claims to refute and the
//! variable order it used. It is a *retrospective receipt* (ADR-0602): the route
//! writes it while searching, and nothing in it is trusted.
//!
//! # What this module checks, and what it does not
//!
//! [`check_cell_refutation`] re-derives the refutation from the atoms alone. It
//! shares **no code** with the producer: root isolation here is Sturm bisection
//! over [`axeyum_ir::poly`], not [`crate::nra_real_root`]'s grid isolator, and
//! every polynomial is re-substituted from the multivariate form the certificate
//! carries rather than from a univariate form the route computed.
//!
//! Per covering it establishes, **exactly**:
//!
//! 1. the sample binds exactly `order[..level]`, and this covering's variable is
//!    `order[level]`;
//! 2. every atom of this level (under the order) appears in the boundary set —
//!    so no atom's sign changes inside a cell unseen;
//! 3. the cell list is exactly the arrangement of the boundary set's distinct
//!    real roots: `2m + 1` entries for `m` roots, alternating open / point /
//!    open, in ascending order, with `m` recomputed here;
//! 4. for an [`CellReason::Atom`] cell, that the named atom's polynomial has **no
//!    root strictly inside the cell** and that its sign at the cell's
//!    representative point violates its comparison — so it is violated on the
//!    *whole* cell, which is a theorem and not a sample;
//! 5. for a [`CellReason::Deeper`] cell, that the witness lies strictly inside
//!    the cell, that the sub-covering's sample is exactly this sample extended by
//!    that witness, and (recursively) that the sub-covering checks out.
//!
//! And — **exactly**, since ADR-2126 — the one property that makes a `Deeper`
//! cell generalise from its witness to the whole cell:
//!
//! 6. *delineability.* Write `t` for the cell's own variable and `v` for the
//!    sub-covering's. Every boundary polynomial of the sub-covering is
//!    re-substituted at the sample of the variables **before** `t`, leaving `t`
//!    itself free — which is the entire difference between this and a probe at a
//!    point. Over the open interval the cell denotes, three things are required,
//!    each by exact root counting (Sturm bisection) against the cell's own
//!    algebraic endpoints.
//!
//!    **(a)** The leading coefficient in `v` has no root strictly inside the
//!    cell — so `deg_v` cannot drop across it (no root escapes to infinity) and
//!    no polynomial can be nullified on it. **(b)** The discriminant
//!    `Res_v(p, ∂p/∂v)` has no root strictly inside — so no two roots of one
//!    polynomial merge there. **(c)** Every pairwise resultant `Res_v(p, q)` has
//!    no root strictly inside — so no root of one polynomial crosses a root of
//!    another.
//!
//!    (a) and (b) give each polynomial a *constant* distinct-real-root count over
//!    the cell; (c) gives the merged ordering of all of them. So the whole 1-D
//!    arrangement one level up is combinatorially the same above every point of
//!    the cell, and every boundary polynomial is sign-invariant on each
//!    2-dimensional piece over it.
//!
//! **No sample appears anywhere in that argument.** ADR-2121 shipped this route's
//! `unsat` half OFF for exactly one reason — check 6 was *sampling*, and sampling
//! can falsify delineability but never establish it. [`DELINEABILITY_SAMPLES`]
//! probing survives as check 6b, an independent cross-check that shares no code
//! with 6a, so a disagreement between the two implementations of one property is
//! a rejection rather than an invisible bug.
//!
//! # The scope boundary, named rather than assumed
//!
//! Check 6a carries an **atom** cell of the sub-covering across the whole cell,
//! because the atom is in the boundary set and is therefore sign-invariant on the
//! 2-dimensional piece. It does **not** carry a `Deeper` cell of the sub-covering
//! across: that would need the level below to be delineable over a
//! 2-dimensional region, and 6a is 1-dimensional. A *point* cell of the
//! sub-covering is no better — over an open parent cell a point cell is a
//! **curve**, not a point. So check 6c rejects a generalisation that rests on
//! another generalisation ([`CellCheckFailure::NestedOpenGeneralization`]).
//!
//! ADR-2121's sampling check had the same gap and named none of it: probing three
//! interior points says nothing about a level two down either. Naming it is what
//! makes the accepted set a set the argument actually covers.
//!
//! The mutation suite deletes the producer's delineability guard, and separately
//! makes 6a accept a non-delineable cell, and requires exactly one named fixture
//! to die for each.

use core::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::poly::{
    RatVec, count_roots_in, eval_rat_poly, rat_degree, rat_gcd, rat_trim, sign_of_rational,
    squarefree_part, sturm_chain, sylvester_determinant, sylvester_matrix,
};
use axeyum_ir::{Rational, Sign, SymbolId};

/// Degree cap for every Sturm chain built here. Matches
/// [`crate::nra_real_root`]'s own `MAX_DEGREE` so a polynomial the producer could
/// form is one this checker can examine.
const CERT_MAX_DEGREE: usize = 64;

/// Bisection depth cap for isolating one root, separating two roots, or refining
/// a bracket until a second polynomial is root-free on it. Exceeding it is a
/// [`CellCheckFailure::RefinementExhausted`] — a rejection, never an acceptance.
const REFINE_DEPTH: u32 = 64;

/// How many extra interior points of a [`CellReason::Deeper`] cell the
/// delineability CROSS-CHECK (6b) samples, beyond the witness itself.
///
/// Since ADR-2126 this is no longer load-bearing: check 6a establishes
/// delineability exactly and 6b only tries to falsify what 6a proved.
///
/// Three, not one: a single extra point can coincide with the witness's own
/// half of the cell for every polynomial at once, and two points cannot
/// distinguish "the root count is the same everywhere" from "the root count is
/// the same at the two points I happened to pick". The cost is linear and the
/// cells are small.
pub const DELINEABILITY_SAMPLES: usize = 3;

/// The six comparison shapes, oriented as `p ⋈ 0`. A standalone copy so the
/// certificate does not depend on the producer's private `Cmp`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CertCmp {
    /// `p = 0`
    Eq,
    /// `p ≠ 0`
    Ne,
    /// `p < 0`
    Lt,
    /// `p ≤ 0`
    Le,
    /// `p > 0`
    Gt,
    /// `p ≥ 0`
    Ge,
}

impl CertCmp {
    /// Whether the comparison holds for a value of sign `s`.
    #[must_use]
    pub const fn holds(self, s: Sign) -> bool {
        match self {
            Self::Eq => matches!(s, Sign::Zero),
            Self::Ne => !matches!(s, Sign::Zero),
            Self::Lt => matches!(s, Sign::Neg),
            Self::Le => matches!(s, Sign::Neg | Sign::Zero),
            Self::Gt => matches!(s, Sign::Pos),
            Self::Ge => matches!(s, Sign::Pos | Sign::Zero),
        }
    }

    /// The comparison that holds exactly when this one does not.
    ///
    /// A sign atom's negation is another sign atom over the SAME polynomial, so
    /// a Boolean layer above this never has to hand the theory a negation --
    /// which is what lets [`crate::nra_clause_loop`] turn a propositional model
    /// straight into a conjunction (ADR-2126).
    #[must_use]
    pub const fn negate(self) -> Self {
        match self {
            Self::Eq => Self::Ne,
            Self::Ne => Self::Eq,
            Self::Lt => Self::Ge,
            Self::Ge => Self::Lt,
            Self::Le => Self::Gt,
            Self::Gt => Self::Le,
        }
    }

    /// A stable, matchable key.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Eq => "=",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
        }
    }
}

/// A multivariate polynomial as a certificate carries it: a sorted, deduplicated
/// list of `(monomial, coefficient)` pairs with no zero coefficient. The monomial
/// is a sorted list of `(variable, exponent)` with no zero exponent; the empty
/// list is the constant monomial.
///
/// Deliberately a plain data type: the checker must be able to read a certificate
/// without the producer's polynomial representation, and a canonical form means
/// "this is the same polynomial as that atom" is a `==`.
pub type CertPoly = Vec<(Vec<(SymbolId, u32)>, Rational)>;

/// One atom of the conjunction being refuted, in certificate form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertAtom {
    cmp: CertCmp,
    poly: CertPoly,
}

impl CertAtom {
    /// Build an atom. The polynomial is canonicalized (sorted, zero coefficients
    /// and zero exponents dropped) so equality is structural.
    #[must_use]
    pub fn new(cmp: CertCmp, poly: CertPoly) -> Self {
        Self {
            cmp,
            poly: canonicalize(poly),
        }
    }

    /// The comparison.
    #[must_use]
    pub const fn cmp(&self) -> CertCmp {
        self.cmp
    }

    /// The polynomial, canonical.
    #[must_use]
    pub fn poly(&self) -> &CertPoly {
        &self.poly
    }
}

/// Why one cell of an arrangement holds no satisfying point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CellReason {
    /// Atom `atom_index` of the refutation is violated on this entire cell.
    Atom {
        /// Index into [`CellRefutation::atoms`].
        atom_index: usize,
    },
    /// Every value of the next variable is refuted above this cell. `witness` is
    /// the rational at which the sub-covering was built.
    ///
    /// On an **open** cell the witness must be strictly interior, and the
    /// sub-covering is generalised from it to the whole cell by the
    /// delineability check. On a **point** cell the witness must be the root
    /// itself, exactly — and then no generalisation is needed at all, because
    /// the cell IS that point. The checker decides which case applies from the
    /// arrangement it recomputed, so a producer cannot choose the cheaper one.
    Deeper {
        /// A rational of this cell: strictly interior if open, the root itself
        /// if the cell is a point.
        witness: Rational,
        /// The covering one level down.
        sub: Box<CellCovering>,
    },
    /// The producer could not decide this cell. Present so a route that gives up
    /// mid-covering can still *say so* in the certificate rather than omit the
    /// cell; [`check_cell_refutation`] rejects any refutation containing one.
    Undecided,
}

/// A covering of the real line in one variable, under a fixed rational sample of
/// the variables before it in the order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellCovering {
    var: SymbolId,
    sample: Vec<(SymbolId, Rational)>,
    boundary: Vec<CertPoly>,
    cells: Vec<CellReason>,
}

impl CellCovering {
    /// Build a covering. Boundary polynomials are canonicalized and deduplicated.
    #[must_use]
    pub fn new(
        var: SymbolId,
        sample: Vec<(SymbolId, Rational)>,
        boundary: Vec<CertPoly>,
        cells: Vec<CellReason>,
    ) -> Self {
        let mut b: Vec<CertPoly> = Vec::with_capacity(boundary.len());
        for p in boundary {
            let c = canonicalize(p);
            if !c.is_empty() && !b.contains(&c) {
                b.push(c);
            }
        }
        b.sort();
        Self {
            var,
            sample,
            boundary: b,
            cells,
        }
    }

    /// The variable this covering ranges over.
    #[must_use]
    pub const fn var(&self) -> SymbolId {
        self.var
    }

    /// The rational sample of the preceding variables.
    #[must_use]
    pub fn sample(&self) -> &[(SymbolId, Rational)] {
        &self.sample
    }

    /// The boundary polynomials whose roots cut the line.
    #[must_use]
    pub fn boundary(&self) -> &[CertPoly] {
        &self.boundary
    }

    /// One reason per cell of the arrangement, ascending.
    #[must_use]
    pub fn cells(&self) -> &[CellReason] {
        &self.cells
    }

    /// The cells, mutably.
    ///
    /// Exists for [`crate::nra_clause_cert::apply_mutation`], the adversarial
    /// fixtures' damage surface. Nothing in the producer uses it: a covering is
    /// built once and read many times, so a mutable view is only ever needed by
    /// something that is deliberately breaking one.
    pub fn cells_mut(&mut self) -> &mut [CellReason] {
        &mut self.cells
    }
}

/// A complete refutation: the atoms, the variable order, and the level-0
/// covering.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellRefutation {
    order: Vec<SymbolId>,
    atoms: Vec<CertAtom>,
    root: CellCovering,
}

impl CellRefutation {
    /// Assemble a refutation.
    #[must_use]
    pub fn new(order: Vec<SymbolId>, atoms: Vec<CertAtom>, root: CellCovering) -> Self {
        Self { order, atoms, root }
    }

    /// The variable order, outermost first.
    #[must_use]
    pub fn order(&self) -> &[SymbolId] {
        &self.order
    }

    /// The atoms claimed jointly unsatisfiable.
    #[must_use]
    pub fn atoms(&self) -> &[CertAtom] {
        &self.atoms
    }

    /// The level-0 covering.
    #[must_use]
    pub const fn root(&self) -> &CellCovering {
        &self.root
    }

    /// The level-0 covering, mutably. See [`CellCovering::cells_mut`] for why
    /// this exists.
    pub const fn root_mut(&mut self) -> &mut CellCovering {
        &mut self.root
    }
}

/// What [`check_cell_refutation`] counted while accepting.
///
/// The counts exist so a test can assert the checker *examined* something —
/// "accepted" with zero cells examined is the vacuous pass an acceptance-only
/// boolean cannot distinguish.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CellCheckStats {
    /// Coverings visited, including the root.
    pub coverings: usize,
    /// Cells whose reason was checked.
    pub cells: usize,
    /// Cells closed by an atom being violated across the whole cell.
    pub atom_cells: usize,
    /// Cells closed by a sub-covering.
    pub deeper_cells: usize,
    /// Of those, the ones that were POINT cells, where the delineability probe
    /// is skipped because a single point needs no generalisation. Counted apart
    /// so a test can tell "the probe did not need to run" from "the probe did
    /// not run".
    pub point_deeper_cells: usize,
    /// Of the [`Self::deeper_cells`], the ones over an OPEN cell, where the
    /// generalisation from the witness to the whole cell had to be earned.
    pub open_deeper_cells: usize,
    /// EXACT root-freeness tests the delineability check ran: one per leading
    /// coefficient, discriminant and pairwise resultant it required to have no
    /// root strictly inside the cell (check 6a).
    ///
    /// Counted so a test can assert the exact check EXAMINED something. An
    /// acceptance with zero exact tests over a covering that has open `Deeper`
    /// cells is the vacuous pass a boolean cannot distinguish (ADR-2126).
    pub delineability_exact_tests: usize,
    /// Root-count comparisons made by the delineability sampling cross-check
    /// (check 6b).
    pub delineability_probes: usize,
    /// The deepest level reached.
    pub max_level: usize,
}

/// Why a refutation was rejected. Every variant names one check, so a test can
/// assert which guard fired instead of only that something did.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CellCheckFailure {
    /// The refutation carries no atoms, or an empty variable order.
    Empty,
    /// A covering's variable is not `order[level]`, or its sample does not bind
    /// exactly `order[..level]` in order.
    SampleShape {
        /// The level at which the mismatch was found.
        level: usize,
    },
    /// An atom whose highest variable is this covering's variable is missing from
    /// the boundary set, so its sign could change inside a cell unseen.
    AtomNotInBoundary {
        /// The level.
        level: usize,
        /// The atom index.
        atom_index: usize,
    },
    /// The cell list is not `2m + 1` long for the `m` distinct roots this checker
    /// recomputed from the boundary set.
    CellCount {
        /// The level.
        level: usize,
        /// What the certificate listed.
        listed: usize,
        /// What the boundary set actually requires.
        expected: usize,
    },
    /// An [`CellReason::Atom`] cell names an atom whose polynomial is not
    /// sign-constant across the cell (it has a root strictly inside).
    AtomNotInvariant {
        /// The level.
        level: usize,
        /// The cell index.
        cell: usize,
        /// The atom index.
        atom_index: usize,
    },
    /// An [`CellReason::Atom`] cell names an atom that is *satisfied* at the
    /// cell's representative point, so the cell is not closed.
    AtomSatisfied {
        /// The level.
        level: usize,
        /// The cell index.
        cell: usize,
        /// The atom index.
        atom_index: usize,
    },
    /// An atom index is out of range, or its top variable is not this level's.
    AtomIndex {
        /// The level.
        level: usize,
        /// The offending index.
        atom_index: usize,
    },
    /// A [`CellReason::Deeper`] witness is not strictly inside its cell, or the
    /// cell is a point cell (which has no interior).
    WitnessOutsideCell {
        /// The level.
        level: usize,
        /// The cell index.
        cell: usize,
    },
    /// A sub-covering's sample is not this covering's sample extended by
    /// `(var, witness)`.
    SubSampleMismatch {
        /// The level.
        level: usize,
        /// The cell index.
        cell: usize,
    },
    /// Delineability sampling found a boundary polynomial of the sub-covering
    /// whose distinct-real-root count changes across the cell.
    DelineabilityBroken {
        /// The level.
        level: usize,
        /// The cell index.
        cell: usize,
        /// The root count at the witness.
        at_witness: usize,
        /// The root count at the probe point.
        at_probe: usize,
    },
    /// A boundary polynomial of the sub-covering loses degree in the next
    /// variable somewhere inside the cell: its LEADING coefficient, as a
    /// polynomial in the cell's own variable, has a root strictly inside. A root
    /// escapes to infinity there, so the arrangement above the cell is not the
    /// one the sub-covering was built from (ADR-2126). Exact, not sampled.
    DelineabilityDegreeDrop {
        /// The level.
        level: usize,
        /// The cell index.
        cell: usize,
        /// Which boundary polynomial of the sub-covering.
        boundary: usize,
    },
    /// Two roots of ONE boundary polynomial of the sub-covering merge somewhere
    /// inside the cell: its discriminant in the next variable has a root strictly
    /// inside. The distinct-real-root count can change there (ADR-2126).
    DelineabilityRootCollision {
        /// The level.
        level: usize,
        /// The cell index.
        cell: usize,
        /// Which boundary polynomial of the sub-covering.
        boundary: usize,
    },
    /// Roots of TWO boundary polynomials of the sub-covering cross somewhere
    /// inside the cell: their resultant in the next variable has a root strictly
    /// inside. Each keeps its own root count, but the ORDER of the merged
    /// arrangement changes, so the sub-covering's cell list is not the cell list
    /// above the whole cell (ADR-2126).
    DelineabilityCrossing {
        /// The level.
        level: usize,
        /// The cell index.
        cell: usize,
        /// The first boundary index.
        a: usize,
        /// The second boundary index.
        b: usize,
    },
    /// The exact delineability argument cannot even be FORMED here: a boundary
    /// polynomial vanishes identically over the whole strip, or a discriminant or
    /// resultant is identically zero (a shared factor for every value of the
    /// cell's variable). A check that cannot run is a rejection, never a pass
    /// (ADR-2126).
    DelineabilityDegenerate {
        /// The level.
        level: usize,
        /// The cell index.
        cell: usize,
        /// A short tag naming which form went degenerate.
        step: &'static str,
    },
    /// A generalisation over an open cell rests on ANOTHER generalisation over an
    /// open cell one level further down, and the exact delineability argument
    /// does not compose that far.
    ///
    /// Read this precisely. Over an open cell the checker proves the
    /// sub-covering's boundary set is delineable, so the arrangement one level up
    /// is invariant across the cell and every boundary polynomial is
    /// sign-invariant on each two-dimensional piece over it. That is enough to
    /// carry an ATOM cell of the sub-covering across the whole cell. It is NOT
    /// enough to carry a `Deeper` cell of the sub-covering across it: that would
    /// need the level below to be delineable over a two-dimensional region, and
    /// the check here is one-dimensional. A point cell of the sub-covering is no
    /// better — over an open parent cell a point cell is a CURVE, not a point.
    ///
    /// ADR-2121's sampling check had the same gap and named none of it: probing
    /// three interior points says nothing about a level two down either. This
    /// variant is the gap made visible, and it is the scope boundary of the exact
    /// check (ADR-2126).
    NestedOpenGeneralization {
        /// The level.
        level: usize,
        /// The cell index.
        cell: usize,
        /// The offending cell of the sub-covering.
        sub_cell: usize,
    },
    /// The certificate admits it did not decide a cell.
    UndecidedCell {
        /// The level.
        level: usize,
        /// The cell index.
        cell: usize,
    },
    /// A polynomial mentions a variable that is neither bound by the sample nor
    /// this covering's variable.
    FreeVariable {
        /// The level.
        level: usize,
    },
    /// Exact arithmetic ran out: an overflow, a degree past [`CERT_MAX_DEGREE`],
    /// or a Sturm chain that could not be built.
    ArithmeticExhausted {
        /// The level.
        level: usize,
        /// A short tag naming the step.
        step: &'static str,
    },
    /// Two roots could not be separated, or a bracket could not be refined, in
    /// [`REFINE_DEPTH`] bisections.
    RefinementExhausted {
        /// The level.
        level: usize,
    },
    /// The recursion went deeper than the variable order allows.
    LevelOverflow {
        /// The level.
        level: usize,
    },
}

impl CellCheckFailure {
    /// A stable, matchable key.
    #[must_use]
    pub const fn name(&self) -> &'static str {
        match self {
            Self::Empty => "empty",
            Self::SampleShape { .. } => "sample-shape",
            Self::AtomNotInBoundary { .. } => "atom-not-in-boundary",
            Self::CellCount { .. } => "cell-count",
            Self::AtomNotInvariant { .. } => "atom-not-invariant",
            Self::AtomSatisfied { .. } => "atom-satisfied",
            Self::AtomIndex { .. } => "atom-index",
            Self::WitnessOutsideCell { .. } => "witness-outside-cell",
            Self::SubSampleMismatch { .. } => "sub-sample-mismatch",
            Self::DelineabilityBroken { .. } => "delineability-broken",
            Self::DelineabilityDegreeDrop { .. } => "delineability-degree-drop",
            Self::DelineabilityRootCollision { .. } => "delineability-root-collision",
            Self::DelineabilityCrossing { .. } => "delineability-crossing",
            Self::DelineabilityDegenerate { .. } => "delineability-degenerate",
            Self::NestedOpenGeneralization { .. } => "nested-open-generalization",
            Self::UndecidedCell { .. } => "undecided-cell",
            Self::FreeVariable { .. } => "free-variable",
            Self::ArithmeticExhausted { .. } => "arithmetic-exhausted",
            Self::RefinementExhausted { .. } => "refinement-exhausted",
            Self::LevelOverflow { .. } => "level-overflow",
        }
    }
}

// ---------------------------------------------------------------------------
// Canonical polynomial form
// ---------------------------------------------------------------------------

/// Sort and normalize a [`CertPoly`]: drop zero coefficients and zero exponents,
/// sort each monomial by variable, merge repeats, sort the term list.
#[must_use]
pub fn canonicalize(poly: CertPoly) -> CertPoly {
    let mut acc: BTreeMap<Vec<(SymbolId, u32)>, Rational> = BTreeMap::new();
    for (mono, coeff) in poly {
        if coeff.is_zero() {
            continue;
        }
        let mut m: BTreeMap<SymbolId, u32> = BTreeMap::new();
        for (v, e) in mono {
            if e == 0 {
                continue;
            }
            *m.entry(v).or_insert(0) += e;
        }
        let key: Vec<(SymbolId, u32)> = m.into_iter().collect();
        let entry = acc.entry(key).or_insert_with(Rational::zero);
        match entry.checked_add(coeff) {
            Some(sum) => *entry = sum,
            // An overflow here cannot be represented; leave the term as it was
            // so the checker's later arithmetic-exhausted guard rejects rather
            // than this function silently dropping content.
            None => return Vec::new(),
        }
    }
    acc.into_iter().filter(|(_, c)| !c.is_zero()).collect()
}

/// The variables appearing in a polynomial.
fn poly_vars(p: &CertPoly) -> BTreeSet<SymbolId> {
    let mut out = BTreeSet::new();
    for (mono, _) in p {
        for &(v, e) in mono {
            if e > 0 {
                out.insert(v);
            }
        }
    }
    out
}

/// Substitute the rational `sample` into `p` and return the result as an
/// LSB-first univariate rational polynomial in `var`.
///
/// `None` if `p` mentions a variable that is neither in `sample` nor `var`, on a
/// degree past [`CERT_MAX_DEGREE`], or on any overflow.
fn substitute_to_univariate(
    p: &CertPoly,
    sample: &BTreeMap<SymbolId, Rational>,
    var: SymbolId,
) -> Option<RatVec> {
    let mut out: Vec<Rational> = Vec::new();
    for (mono, coeff) in p {
        let mut acc = *coeff;
        let mut deg: u32 = 0;
        for &(v, e) in mono {
            if v == var {
                deg = deg.checked_add(e)?;
                continue;
            }
            let value = *sample.get(&v)?;
            for _ in 0..e {
                acc = acc.checked_mul(value)?;
            }
        }
        let idx = usize::try_from(deg).ok()?;
        if idx > CERT_MAX_DEGREE {
            return None;
        }
        if out.len() <= idx {
            out.resize(idx + 1, Rational::zero());
        }
        out[idx] = out[idx].checked_add(acc)?;
    }
    Some(rat_trim(out))
}

// ---------------------------------------------------------------------------
// Independent real-root isolation (Sturm bisection)
// ---------------------------------------------------------------------------

/// One isolated real root: the unique root of `poly` (squarefree) in the
/// half-open bracket `(lo, hi]`, or an exactly-known rational.
#[derive(Clone, Debug)]
struct IsoRoot {
    /// Squarefree defining polynomial, LSB-first rational.
    poly: RatVec,
    /// Its Sturm chain, cached.
    chain: Vec<RatVec>,
    /// Bracket lower bound; the root is strictly above it.
    lo: Rational,
    /// Bracket upper bound; the root is at or below it.
    hi: Rational,
    /// `Some(q)` when the root is known to be exactly the rational `q`.
    exact: Option<Rational>,
}

impl IsoRoot {
    /// A rational strictly below the root, for cell-sample construction.
    fn strict_lower(&self) -> Rational {
        self.exact.unwrap_or(self.lo)
    }

    /// A rational at or above the root.
    fn upper(&self) -> Rational {
        self.exact.unwrap_or(self.hi)
    }
}

/// A Cauchy bound: every real root of `p` has magnitude `< bound`.
fn cauchy_bound(p: &[Rational]) -> Option<Rational> {
    let d = rat_degree(p)?;
    let lead = p[d];
    let mut worst = Rational::zero();
    for c in &p[..d] {
        let ratio = c.checked_div(lead)?;
        let mag = if sign_of_rational(ratio) == Sign::Neg {
            ratio.checked_neg()?
        } else {
            ratio
        };
        if mag.checked_cmp(&worst)? == Ordering::Greater {
            worst = mag;
        }
    }
    worst.checked_add(Rational::integer(2))
}

/// Isolate every distinct real root of `p` (any multiplicity) as disjoint
/// half-open brackets, ascending.
fn isolate_roots_sturm(p: &[Rational]) -> Option<Vec<IsoRoot>> {
    let sf = squarefree_part(p, CERT_MAX_DEGREE)?;
    let d = rat_degree(&sf)?;
    if d == 0 {
        return Some(Vec::new());
    }
    let chain = sturm_chain(&sf, CERT_MAX_DEGREE)?;
    let bound = cauchy_bound(&sf)?;
    let lo = bound.checked_neg()?;
    let mut out: Vec<IsoRoot> = Vec::new();
    let mut work: Vec<(Rational, Rational)> = vec![(lo, bound)];
    // Depth-bounded bisection. Each pop either isolates, discards, or splits.
    let mut budget = (d + 2) * (REFINE_DEPTH as usize + 2);
    while let Some((a, b)) = work.pop() {
        budget = budget.checked_sub(1)?;
        let n = count_roots_in(&chain, a, b)?;
        if n == 0 {
            continue;
        }
        if n == 1 {
            out.push(IsoRoot {
                poly: sf.clone(),
                chain: chain.clone(),
                lo: a,
                hi: b,
                exact: exact_if_rational_root(&sf, a, b),
            });
            continue;
        }
        let m = midpoint(a, b)?;
        // `count_roots_in` is over `(lo, hi]`, so splitting at `m` is exact even
        // when `m` is itself a root: it is counted in the lower half.
        work.push((m, b));
        work.push((a, m));
    }
    out.sort_by(|x, y| x.lo.wide_cmp(&y.lo));
    Some(out)
}

/// If the unique root of `sf` in `(a, b]` happens to be the rational `b`, say so.
/// (A root that is rational but not an endpoint is found later by refinement.)
fn exact_if_rational_root(sf: &[Rational], _a: Rational, b: Rational) -> Option<Rational> {
    match eval_rat_poly(sf, b) {
        Some(v) if v.is_zero() => Some(b),
        _ => None,
    }
}

/// The midpoint of two rationals.
fn midpoint(a: Rational, b: Rational) -> Option<Rational> {
    a.checked_add(b)?.checked_div(Rational::integer(2))
}

/// Narrow `r`'s bracket by one bisection, keeping the root inside.
fn refine(r: &mut IsoRoot) -> Option<()> {
    if r.exact.is_some() {
        return Some(());
    }
    let m = midpoint(r.lo, r.hi)?;
    if eval_rat_poly(&r.poly, m)?.is_zero() {
        r.exact = Some(m);
        r.lo = m;
        r.hi = m;
        return Some(());
    }
    if count_roots_in(&r.chain, r.lo, m)? == 1 {
        r.hi = m;
    } else {
        r.lo = m;
    }
    Some(())
}

/// Exact comparison of two isolated roots: separate the brackets, or prove the
/// roots equal through a common factor.
fn compare_iso(a: &IsoRoot, b: &IsoRoot) -> Option<Ordering> {
    if let (Some(x), Some(y)) = (a.exact, b.exact) {
        return x.checked_cmp(&y);
    }
    let mut left = a.clone();
    let mut right = b.clone();
    for _ in 0..REFINE_DEPTH {
        if let (Some(lq), Some(rq)) = (left.exact, right.exact) {
            return lq.checked_cmp(&rq);
        }
        // Disjoint brackets settle it. `(lo, hi]` half-open: `left.hi <= right.lo`
        // means left's root is at most left.hi and right's is strictly above
        // right.lo >= left.hi.
        if left.upper().checked_cmp(&right.strict_lower())? != Ordering::Greater {
            return Some(Ordering::Less);
        }
        if right.upper().checked_cmp(&left.strict_lower())? != Ordering::Greater {
            return Some(Ordering::Greater);
        }
        // Overlapping. A shared root would be a root of the gcd inside the
        // overlap; if the gcd has one there, the two roots ARE that root.
        let shared = rat_gcd(&left.poly, &right.poly, CERT_MAX_DEGREE)?;
        if rat_degree(&shared).is_some_and(|d| d >= 1) {
            let shared_sf = squarefree_part(&shared, CERT_MAX_DEGREE)?;
            let shared_chain = sturm_chain(&shared_sf, CERT_MAX_DEGREE)?;
            let lo = max_rat(left.strict_lower(), right.strict_lower())?;
            let hi = min_rat(left.upper(), right.upper())?;
            if lo.checked_cmp(&hi)? == Ordering::Less
                && count_roots_in(&shared_chain, lo, hi)? == 1
                // Both brackets hold exactly one root, and the overlap holds a
                // common root of both defining polynomials: that root is the
                // unique one in each bracket, so the two are equal.
                && count_roots_in(&left.chain, lo, hi)? == 1
                && count_roots_in(&right.chain, lo, hi)? == 1
            {
                return Some(Ordering::Equal);
            }
        }
        refine(&mut left)?;
        refine(&mut right)?;
    }
    None
}

fn max_rat(a: Rational, b: Rational) -> Option<Rational> {
    Some(if a.checked_cmp(&b)? == Ordering::Greater {
        a
    } else {
        b
    })
}

fn min_rat(a: Rational, b: Rational) -> Option<Rational> {
    Some(if a.checked_cmp(&b)? == Ordering::Less {
        a
    } else {
        b
    })
}

/// Refine every bracket until consecutive roots are STRICTLY disjoint.
///
/// Without this the merged list keeps whatever bracket each root was first
/// isolated in -- for a linear polynomial that is the whole Cauchy interval --
/// and every later step that needs a point between two roots has nowhere to put
/// one. `None` when [`REFINE_DEPTH`] bisections do not separate them.
fn separate_roots(roots: &mut [IsoRoot]) -> Option<()> {
    if roots.len() < 2 {
        return Some(());
    }
    for _ in 0..REFINE_DEPTH {
        let mut separated = true;
        for i in 0..roots.len() - 1 {
            if roots[i].upper().checked_cmp(&roots[i + 1].strict_lower())? != Ordering::Less {
                separated = false;
                break;
            }
        }
        if separated {
            return Some(());
        }
        for r in roots.iter_mut() {
            refine(r)?;
        }
    }
    None
}

/// Merge per-polynomial isolated roots into the ascending list of DISTINCT roots
/// of the union. `None` when two roots cannot be ordered within
/// [`REFINE_DEPTH`].
fn merge_roots(mut all: Vec<IsoRoot>) -> Option<Vec<IsoRoot>> {
    // Insertion sort with the exact comparator, dropping duplicates.
    let mut out: Vec<IsoRoot> = Vec::with_capacity(all.len());
    all.sort_by(|x, y| x.lo.wide_cmp(&y.lo));
    for r in all {
        let mut pos = out.len();
        let mut duplicate = false;
        for (i, existing) in out.iter().enumerate() {
            match compare_iso(&r, existing)? {
                Ordering::Less => {
                    pos = i;
                    break;
                }
                Ordering::Equal => {
                    duplicate = true;
                    break;
                }
                Ordering::Greater => {}
            }
        }
        if !duplicate {
            out.insert(pos, r);
        }
    }
    separate_roots(&mut out)?;
    Some(out)
}

/// The sign of `q` at the root isolated by `r`. Exact.
fn sign_at_root(q: &[Rational], r: &IsoRoot) -> Option<Sign> {
    if rat_degree(q).is_none() {
        // The zero polynomial.
        return Some(Sign::Zero);
    }
    if let Some(x) = r.exact {
        return Some(sign_of_rational(eval_rat_poly(q, x)?));
    }
    let q_sf = squarefree_part(q, CERT_MAX_DEGREE).unwrap_or_else(|| rat_trim(q.to_vec()));
    if rat_degree(&q_sf).is_none_or(|d| d == 0) {
        // Constant: its sign is its value.
        return Some(sign_of_rational(*q.last()?));
    }
    // Does `q` share the root? Only if the gcd does.
    let g = rat_gcd(&r.poly, &q_sf, CERT_MAX_DEGREE)?;
    let mut work = r.clone();
    if rat_degree(&g).is_some_and(|d| d >= 1) {
        let g_chain = sturm_chain(&squarefree_part(&g, CERT_MAX_DEGREE)?, CERT_MAX_DEGREE)?;
        if count_roots_in(&g_chain, work.lo, work.hi)? >= 1 {
            // The gcd's root inside the bracket is r's root (r's bracket holds
            // exactly one root of r.poly, and every gcd root is one).
            return Some(Sign::Zero);
        }
    }
    // `q` has no root equal to r's. Refine until `q` is root-free on the bracket;
    // then its sign is constant there and equals its value at the upper end.
    let q_chain = sturm_chain(&q_sf, CERT_MAX_DEGREE)?;
    for _ in 0..REFINE_DEPTH {
        if let Some(x) = work.exact {
            return Some(sign_of_rational(eval_rat_poly(q, x)?));
        }
        if count_roots_in(&q_chain, work.lo, work.hi)? == 0 {
            return Some(sign_of_rational(eval_rat_poly(q, work.hi)?));
        }
        refine(&mut work)?;
    }
    None
}

// ---------------------------------------------------------------------------
// The cells of an arrangement
// ---------------------------------------------------------------------------

/// A cell of the 1-D arrangement of a root list: `2m + 1` of them for `m` roots.
enum Cell<'a> {
    /// `(-inf, r0)`, `(r_i, r_{i+1})`, or `(r_{m-1}, +inf)`.
    Open {
        lo: Option<&'a IsoRoot>,
        hi: Option<&'a IsoRoot>,
    },
    /// The single point `r_i`.
    Point(&'a IsoRoot),
}

/// Enumerate the cells of the arrangement, ascending.
fn cells_of(roots: &[IsoRoot]) -> Vec<Cell<'_>> {
    let mut out: Vec<Cell<'_>> = Vec::with_capacity(2 * roots.len() + 1);
    for (i, r) in roots.iter().enumerate() {
        out.push(Cell::Open {
            lo: if i == 0 { None } else { Some(&roots[i - 1]) },
            hi: Some(r),
        });
        out.push(Cell::Point(r));
    }
    out.push(Cell::Open {
        lo: roots.last(),
        hi: None,
    });
    out
}

impl Cell<'_> {
    /// `n` distinct rationals strictly inside an open cell, ascending. Empty for
    /// a point cell.
    fn interior_points(&self, n: usize) -> Option<Vec<Rational>> {
        let Cell::Open { lo, hi } = self else {
            return Some(Vec::new());
        };
        // A safe open rational sub-interval: strictly above the lower root and
        // strictly below the upper one. The brackets give it directly --
        // `lo.upper()` is at or above the lower root, `hi.strict_lower()` is
        // strictly below the upper root -- so we start one unit outside and walk
        // in, which is exact and needs no refinement.
        let a = if let Some(r) = lo {
            r.upper()
        } else {
            let above = hi.map_or_else(Rational::zero, IsoRoot::strict_lower);
            above.checked_sub(Rational::integer(2))?
        };
        let b = if let Some(r) = hi {
            r.strict_lower()
        } else {
            let below = lo.map_or_else(Rational::zero, IsoRoot::upper);
            below.checked_add(Rational::integer(2))?
        };
        if a.checked_cmp(&b)? != Ordering::Less {
            // The bracket endpoints touch: the cell is too narrow to name a
            // rational interior without refinement. Report none; the caller
            // treats an empty interior as "cannot probe here".
            return Some(Vec::new());
        }
        let span = b.checked_sub(a)?;
        let mut pts = Vec::with_capacity(n);
        for k in 1..=n {
            let step = span.checked_mul(Rational::checked_new(
                i128::try_from(k).ok()?,
                i128::try_from(n + 1).ok()?,
            )?)?;
            pts.push(a.checked_add(step)?);
        }
        Some(pts)
    }

    /// Whether the rational `q` is this cell's witness point: strictly interior
    /// for an open cell, exactly the root for a point cell (which requires the
    /// root to BE that rational).
    fn admits_witness(&self, q: Rational) -> Option<bool> {
        match self {
            Cell::Point(r) => {
                if let Some(x) = r.exact {
                    Some(q.checked_cmp(&x)? == Ordering::Equal)
                } else {
                    // An irrational root is not any rational. Refine to try to
                    // discover the root is rational after all, then decide.
                    let mut work = (*r).clone();
                    for _ in 0..REFINE_DEPTH {
                        if let Some(x) = work.exact {
                            return Some(q.checked_cmp(&x)? == Ordering::Equal);
                        }
                        if q.checked_cmp(&work.strict_lower())? != Ordering::Greater
                            || q.checked_cmp(&work.upper())? == Ordering::Greater
                        {
                            return Some(false); // outside the bracket: not the root
                        }
                        refine(&mut work)?;
                    }
                    Some(false)
                }
            }
            Cell::Open { lo, hi } => {
                if let Some(r) = lo {
                    // q must be strictly above the root. `r.upper()` is at or
                    // above the root, so `q > r.upper()` is sufficient; when it
                    // is not, refine to decide.
                    if !rational_strictly_above_root(q, r)? {
                        return Some(false);
                    }
                }
                if let Some(r) = hi
                    && !rational_strictly_below_root(q, r)?
                {
                    return Some(false);
                }
                Some(true)
            }
        }
    }
}

/// Is the rational `q` strictly greater than the root `r` isolates? Exact.
fn rational_strictly_above_root(q: Rational, r: &IsoRoot) -> Option<bool> {
    if let Some(x) = r.exact {
        return Some(q.checked_cmp(&x)? == Ordering::Greater);
    }
    if q.checked_cmp(&r.upper())? != Ordering::Less {
        return Some(true); // q >= hi >= root, and q != root because ...
    }
    if q.checked_cmp(&r.strict_lower())? != Ordering::Greater {
        return Some(false); // q <= lo < root
    }
    // Inside the bracket: `q` is above the root iff the bracket's unique root
    // lies in `(lo, q]`.
    let below = count_roots_in(&r.chain, r.lo, q)?;
    Some(below == 1 && !eval_rat_poly(&r.poly, q)?.is_zero())
}

/// Is the rational `q` strictly less than the root `r` isolates? Exact.
fn rational_strictly_below_root(q: Rational, r: &IsoRoot) -> Option<bool> {
    if let Some(x) = r.exact {
        return Some(q.checked_cmp(&x)? == Ordering::Less);
    }
    if q.checked_cmp(&r.strict_lower())? != Ordering::Greater {
        return Some(true); // q <= lo < root
    }
    if q.checked_cmp(&r.upper())? == Ordering::Greater {
        return Some(false); // q > hi >= root
    }
    let below = count_roots_in(&r.chain, r.lo, q)?;
    Some(below == 0)
}

/// Does `q` (LSB-first rational) have a root strictly inside this cell?
///
/// For an open cell `(l, u)` this is `count_roots_in(q, l, u)` adjusted for the
/// half-open convention and for `l`/`u` possibly being roots of `q` themselves.
/// Bounds are handled by widening to the brackets and then subtracting the
/// endpoint roots we can account for exactly.
fn has_root_strictly_inside(q_sf: &[Rational], cell: &Cell<'_>) -> Option<bool> {
    let Cell::Open { lo, hi } = cell else {
        return Some(false);
    };
    if rat_degree(q_sf).is_none_or(|d| d == 0) {
        return Some(false); // constant (or zero) polynomial: no roots
    }
    let chain = sturm_chain(q_sf, CERT_MAX_DEGREE)?;
    // Narrow both bracket endpoints until they are strictly inside their own
    // bracket relative to `q`: i.e. until `q` has no root inside the bracket, or
    // until we can attribute the root to the cell boundary itself.
    let mut lower = lo.cloned();
    let mut upper = hi.cloned();
    for _ in 0..REFINE_DEPTH {
        // An UNBOUNDED side takes a Cauchy bound, and that bound knows nothing
        // about the cell's other endpoint -- so it can land at or inside it, and
        // then `(a, b]` is empty, there is nothing on the infinite side to
        // refine, and the loop spins to `REFINE_DEPTH` and REJECTS.
        //
        // ADR-2131 hit this on the cell `(2, +inf)` with `q = x`, whose Cauchy
        // bound is exactly 2. Pushing the infinite side PAST the finite one
        // costs nothing and cannot hide a root: every real root of `q` is
        // strictly inside `(-C, C)`, so counting over `(a, b]` with `b >= C` is
        // counting over `(a, +inf)`, which is the cell.
        let a_fin = lower.as_ref().map(IsoRoot::upper);
        let b_fin = upper.as_ref().map(IsoRoot::strict_lower);
        let (a, b) = match (a_fin, b_fin) {
            (Some(a), Some(b)) => (a, b),
            (Some(a), None) => {
                let c = bound_above(q_sf)?;
                let past = a.checked_add(Rational::integer(1))?;
                let b = if c.checked_cmp(&past)? == Ordering::Greater {
                    c
                } else {
                    past
                };
                (a, b)
            }
            (None, Some(b)) => {
                let c = bound_below(q_sf)?;
                let past = b.checked_sub(Rational::integer(1))?;
                let a = if c.checked_cmp(&past)? == Ordering::Less {
                    c
                } else {
                    past
                };
                (a, b)
            }
            (None, None) => (bound_below(q_sf)?, bound_above(q_sf)?),
        };
        if a.checked_cmp(&b)? != Ordering::Less {
            // Brackets still overlap the interior; refine and retry.
            if let Some(r) = lower.as_mut() {
                refine(r)?;
            }
            if let Some(r) = upper.as_mut() {
                refine(r)?;
            }
            continue;
        }
        // `(a, b]` is inside the open cell except that `b` may be at or below the
        // upper root. `count_roots_in(chain, a, b)` counts `q`'s roots in
        // `(a, b]`; every one of them is strictly inside the cell because
        // `a >= lower root` and `b <= upper root`, and equality at `b` would mean
        // `b` IS the upper root, which `strict_lower()` excludes unless the root
        // is exact -- handled by subtracting an exact endpoint root below.
        let mut n = count_roots_in(&chain, a, b)?;
        if let Some(r) = &upper
            && let Some(x) = r.exact
            && x.checked_cmp(&b)? == Ordering::Equal
            && eval_rat_poly(q_sf, x)?.is_zero()
        {
            n = n.saturating_sub(1);
        }
        // Roots of `q` in the slivers `(lower root, a]` and `(b, upper root)` are
        // missed by this count. Close the gap by refining until the slivers are
        // root-free -- EXCEPT for a root of `q` sitting exactly ON the cell's
        // boundary, which no amount of refinement removes and which is not
        // strictly inside the cell anyway.
        //
        // ADR-2131 measured why that exception has to be here. The boundary of a
        // cell is the root of a boundary polynomial, and the atom that CLOSES the
        // cell is very often one of those same polynomials -- so `q` and the
        // endpoint's polynomial share that root by construction. When the
        // endpoint is EXACT the subtraction below `n` already handles it; when it
        // is a bracket, the sliver count stays at 1 through every bisection and
        // the whole check exhausts `REFINE_DEPTH` and REJECTS. `x > 1 ∧ x < 0` --
        // as small an unsatisfiable conjunction as exists -- was rejected for
        // exactly this reason, because bisection from the Cauchy bracket never
        // lands on the rational 1 and so never marks that root exact.
        //
        // `sign_at_root` decides "does `q` vanish at this root" EXACTLY, using
        // the endpoint's own polynomial and Sturm chain. So this subtracts a root
        // it has PROVED is on the boundary, not one it has given up on. The
        // direction is safe: a root at a closed endpoint does not break sign
        // constancy on the OPEN cell, which is the property this function is
        // asked about.
        let sliver_low = match &lower {
            Some(r) if r.exact.is_none() => {
                let raw = count_roots_in(&chain, r.lo, a)?;
                if sign_at_root(q_sf, r)? == Sign::Zero {
                    raw.saturating_sub(1)
                } else {
                    raw
                }
            }
            _ => 0,
        };
        let sliver_high = match &upper {
            Some(r) if r.exact.is_none() => {
                let raw = count_roots_in(&chain, b, r.hi)?;
                if sign_at_root(q_sf, r)? == Sign::Zero {
                    raw.saturating_sub(1)
                } else {
                    raw
                }
            }
            _ => 0,
        };
        if sliver_low == 0 && sliver_high == 0 {
            return Some(n > 0);
        }
        if let Some(r) = lower.as_mut() {
            refine(r)?;
        }
        if let Some(r) = upper.as_mut() {
            refine(r)?;
        }
    }
    None
}

/// A rational strictly below every real root of `p`.
fn bound_below(p: &[Rational]) -> Option<Rational> {
    cauchy_bound(p)?.checked_neg()
}

/// A rational strictly above every real root of `p`.
fn bound_above(p: &[Rational]) -> Option<Rational> {
    cauchy_bound(p)
}

// ---------------------------------------------------------------------------
// The check
// ---------------------------------------------------------------------------

/// Re-derive and check a [`CellRefutation`].
///
/// Returns the counts examined on acceptance, or the single named check that
/// rejected. See the module docs for exactly what is established and what is
/// only sampled — in particular, **delineability is checked by sampling**, so an
/// accepted refutation is checked evidence and not a proof.
///
/// # Errors
///
/// Returns the [`CellCheckFailure`] naming the first check that failed.
pub fn check_cell_refutation(
    refutation: &CellRefutation,
) -> Result<CellCheckStats, CellCheckFailure> {
    if refutation.atoms.is_empty() || refutation.order.is_empty() {
        return Err(CellCheckFailure::Empty);
    }
    let mut stats = CellCheckStats::default();
    check_covering(refutation, &refutation.root, 0, &mut stats)?;
    Ok(stats)
}

/// The level of an atom under `order`: the index of its highest variable.
/// `None` for a variable-free atom (which the producer folds away) or one
/// mentioning a variable outside the order.
fn atom_level(atom: &CertAtom, order: &[SymbolId]) -> Option<usize> {
    let vars = poly_vars(&atom.poly);
    if vars.is_empty() {
        return None;
    }
    let mut level = 0usize;
    for v in &vars {
        let idx = order.iter().position(|o| o == v)?;
        level = level.max(idx);
    }
    Some(level)
}

#[allow(
    clippy::too_many_lines,
    reason = "one covering, one pass: splitting the six checks apart would put \
              the arrangement they all read behind a borrow dance"
)]
fn check_covering(
    refutation: &CellRefutation,
    cov: &CellCovering,
    level: usize,
    stats: &mut CellCheckStats,
) -> Result<(), CellCheckFailure> {
    stats.coverings += 1;
    stats.max_level = stats.max_level.max(level);
    let order = &refutation.order;
    if level >= order.len() {
        return Err(CellCheckFailure::LevelOverflow { level });
    }

    // --- Check 1: the sample binds exactly order[..level], and var is right. ---
    if cov.var != order[level] || cov.sample.len() != level {
        return Err(CellCheckFailure::SampleShape { level });
    }
    for (i, (v, _)) in cov.sample.iter().enumerate() {
        if *v != order[i] {
            return Err(CellCheckFailure::SampleShape { level });
        }
    }
    let sample: BTreeMap<SymbolId, Rational> = cov.sample.iter().copied().collect();

    // --- Check 2: every atom of this level is in the boundary set. ---
    for (i, atom) in refutation.atoms.iter().enumerate() {
        if atom_level(atom, order) == Some(level) && !cov.boundary.contains(&atom.poly) {
            return Err(CellCheckFailure::AtomNotInBoundary {
                level,
                atom_index: i,
            });
        }
    }

    // --- Check 3: the cell list IS the arrangement of the boundary set. ---
    let mut all_roots: Vec<IsoRoot> = Vec::new();
    for p in &cov.boundary {
        let vars = poly_vars(p);
        if !vars.iter().all(|v| *v == cov.var || sample.contains_key(v)) {
            return Err(CellCheckFailure::FreeVariable { level });
        }
        let uni = substitute_to_univariate(p, &sample, cov.var).ok_or(
            CellCheckFailure::ArithmeticExhausted {
                level,
                step: "boundary-substitute",
            },
        )?;
        if rat_degree(&uni).is_none_or(|d| d == 0) {
            continue; // constant after substitution: contributes no boundary
        }
        let roots = isolate_roots_sturm(&uni).ok_or(CellCheckFailure::ArithmeticExhausted {
            level,
            step: "boundary-isolate",
        })?;
        all_roots.extend(roots);
    }
    let roots = merge_roots(all_roots).ok_or(CellCheckFailure::RefinementExhausted { level })?;
    let expected = 2 * roots.len() + 1;
    if cov.cells.len() != expected {
        return Err(CellCheckFailure::CellCount {
            level,
            listed: cov.cells.len(),
            expected,
        });
    }
    let cells = cells_of(&roots);

    // --- Checks 4, 5 and 6, per cell. ---
    for (idx, (reason, cell)) in cov.cells.iter().zip(cells.iter()).enumerate() {
        stats.cells += 1;
        match reason {
            CellReason::Undecided => {
                return Err(CellCheckFailure::UndecidedCell { level, cell: idx });
            }
            CellReason::Atom { atom_index } => {
                stats.atom_cells += 1;
                let atom =
                    refutation
                        .atoms
                        .get(*atom_index)
                        .ok_or(CellCheckFailure::AtomIndex {
                            level,
                            atom_index: *atom_index,
                        })?;
                if atom_level(atom, order) != Some(level) {
                    return Err(CellCheckFailure::AtomIndex {
                        level,
                        atom_index: *atom_index,
                    });
                }
                let uni = substitute_to_univariate(&atom.poly, &sample, cov.var).ok_or(
                    CellCheckFailure::ArithmeticExhausted {
                        level,
                        step: "atom-substitute",
                    },
                )?;
                // 4a: sign-constant on the cell -- no root strictly inside.
                let sf = match squarefree_part(&uni, CERT_MAX_DEGREE) {
                    Some(s) => s,
                    None => rat_trim(uni.clone()), // constant: no roots, fine
                };
                let inside = has_root_strictly_inside(&sf, cell)
                    .ok_or(CellCheckFailure::RefinementExhausted { level })?;
                if inside {
                    return Err(CellCheckFailure::AtomNotInvariant {
                        level,
                        cell: idx,
                        atom_index: *atom_index,
                    });
                }
                // 4b: the sign at the cell's representative violates the cmp.
                let sign = match cell {
                    Cell::Point(r) => sign_at_root(&uni, r)
                        .ok_or(CellCheckFailure::RefinementExhausted { level })?,
                    Cell::Open { .. } => {
                        let pts = cell.interior_points(1).ok_or(
                            CellCheckFailure::ArithmeticExhausted {
                                level,
                                step: "cell-interior",
                            },
                        )?;
                        let p = *pts
                            .first()
                            .ok_or(CellCheckFailure::RefinementExhausted { level })?;
                        sign_of_rational(eval_rat_poly(&uni, p).ok_or(
                            CellCheckFailure::ArithmeticExhausted {
                                level,
                                step: "atom-eval",
                            },
                        )?)
                    }
                };
                if atom.cmp.holds(sign) {
                    return Err(CellCheckFailure::AtomSatisfied {
                        level,
                        cell: idx,
                        atom_index: *atom_index,
                    });
                }
            }
            CellReason::Deeper { witness, sub } => {
                stats.deeper_cells += 1;
                // 5a: the witness belongs to this cell -- strictly interior if
                // the cell is open, EXACTLY the root if it is a point. The cell
                // kind comes from the arrangement recomputed above, not from the
                // certificate, so this is not the producer's choice to make.
                let admitted = cell
                    .admits_witness(*witness)
                    .ok_or(CellCheckFailure::RefinementExhausted { level })?;
                if !admitted {
                    return Err(CellCheckFailure::WitnessOutsideCell { level, cell: idx });
                }
                // 5b: the sub-covering extends this sample by exactly (var, witness).
                let mut expected_sample = cov.sample.clone();
                expected_sample.push((cov.var, *witness));
                if sub.sample != expected_sample {
                    return Err(CellCheckFailure::SubSampleMismatch { level, cell: idx });
                }
                // 6: delineability -- and ONLY on an open cell. A point cell
                // has nothing to generalise over: the cell IS the single point
                // the sub-covering was built at, so refutation there IS
                // refutation on the whole cell. Skipping here is not a
                // weakening; running it would be vacuous.
                if matches!(cell, Cell::Open { .. }) {
                    stats.open_deeper_cells += 1;
                    // 6a: EXACT. Proves the sub-covering's boundary set is
                    // delineable over the whole cell. No sample anywhere in it.
                    check_delineability_exact(sub, cell, level, idx, stats)?;
                    // 6b: the sampling falsifier, KEPT as an independent
                    // cross-check. It shares no code with 6a, and once 6a has
                    // passed it can only fire on a disagreement between two
                    // implementations of the same property -- which is a bug in
                    // one of them, and a rejection either way.
                    check_delineability(sub, cell, level, idx, stats)?;
                    // 6c: the composition guard. 6a carries an ATOM cell of the
                    // sub-covering across the whole cell; it does not carry a
                    // `Deeper` cell across, because that needs delineability
                    // over a TWO-dimensional region and 6a is one-dimensional.
                    if let Some(sub_cell) = first_non_atom_cell(sub) {
                        return Err(CellCheckFailure::NestedOpenGeneralization {
                            level,
                            cell: idx,
                            sub_cell,
                        });
                    }
                } else {
                    stats.point_deeper_cells += 1;
                }
                // 5c: recurse.
                check_covering(refutation, sub, level + 1, stats)?;
            }
        }
    }
    Ok(())
}

/// The first cell of `cov` that is not an [`CellReason::Atom`] cell.
///
/// Used by check 6c: over an open parent cell, a sub-covering may close its
/// cells by atoms and nothing else, because that is exactly as far as the
/// one-dimensional delineability argument reaches.
fn first_non_atom_cell(cov: &CellCovering) -> Option<usize> {
    cov.cells
        .iter()
        .position(|c| !matches!(c, CellReason::Atom { .. }))
}

/// Substitute `vals` into `p`, keeping BOTH `keep` and `elim` free, and return
/// the result as a polynomial in `elim` (LSB-first by `elim`'s exponent) whose
/// coefficients are LSB-first univariate polynomials in `keep`.
///
/// Trailing zero coefficients are trimmed at both levels, so the last entry is
/// the true leading coefficient in `elim` and an EMPTY result is the zero
/// polynomial. `None` if `p` mentions a variable that is none of `vals`, `keep`
/// or `elim`, on a degree past [`CERT_MAX_DEGREE`], or on any overflow.
fn substitute_to_bivariate(
    p: &CertPoly,
    vals: &BTreeMap<SymbolId, Rational>,
    keep: SymbolId,
    elim: SymbolId,
) -> Option<Vec<RatVec>> {
    let mut out: Vec<RatVec> = Vec::new();
    for (mono, coeff) in p {
        let mut acc = *coeff;
        let mut e_deg: u32 = 0;
        let mut k_deg: u32 = 0;
        for &(v, e) in mono {
            if v == elim {
                e_deg = e_deg.checked_add(e)?;
                continue;
            }
            if v == keep {
                k_deg = k_deg.checked_add(e)?;
                continue;
            }
            let value = *vals.get(&v)?;
            for _ in 0..e {
                acc = acc.checked_mul(value)?;
            }
        }
        let ei = usize::try_from(e_deg).ok()?;
        let ki = usize::try_from(k_deg).ok()?;
        if ei > CERT_MAX_DEGREE || ki > CERT_MAX_DEGREE {
            return None;
        }
        if out.len() <= ei {
            out.resize(ei + 1, Vec::new());
        }
        let slot = &mut out[ei];
        if slot.len() <= ki {
            slot.resize(ki + 1, Rational::zero());
        }
        slot[ki] = slot[ki].checked_add(acc)?;
    }
    for c in &mut out {
        let trimmed = rat_trim(core::mem::take(c));
        *c = trimmed;
    }
    while out.last().is_some_and(|c| rat_degree(c).is_none()) {
        out.pop();
    }
    Some(out)
}

/// The formal derivative in the ELIMINATED variable of a polynomial held as
/// [`substitute_to_bivariate`] returns it: `∂/∂elim` maps the coefficient of
/// `elim^i` to `i ·` itself at `elim^(i-1)`. `None` on overflow.
fn derivative_in_elim(coeffs: &[RatVec]) -> Option<Vec<RatVec>> {
    let mut out: Vec<RatVec> = Vec::new();
    for (i, c) in coeffs.iter().enumerate().skip(1) {
        let k = Rational::integer(i128::try_from(i).ok()?);
        let mut scaled: RatVec = Vec::with_capacity(c.len());
        for r in c {
            scaled.push(r.checked_mul(k)?);
        }
        out.push(rat_trim(scaled));
    }
    while out.last().is_some_and(|c| rat_degree(c).is_none()) {
        out.pop();
    }
    Some(out)
}

/// `Res_elim(a, b)` for two polynomials in the eliminated variable whose
/// coefficients are univariate in the surviving variable: the Sylvester
/// determinant over ℚ[surviving], exact and with no floating point.
///
/// `None` when either argument has degree zero in the eliminated variable (there
/// is no Sylvester matrix to build) or on overflow.
fn bivariate_resultant(a: &[RatVec], b: &[RatVec]) -> Option<RatVec> {
    let mat = sylvester_matrix(a, b)?;
    Some(rat_trim(sylvester_determinant(&mat)?))
}

/// Does `q` -- a polynomial in the CELL'S OWN variable -- have a root strictly
/// inside the cell?
///
/// The zero polynomial vanishes everywhere, so it counts as vanishing inside;
/// callers that need to tell that case apart test for it first, because
/// "identically zero" and "has a root here" call for different rejections.
fn vanishes_inside(
    q: &[Rational],
    cell: &Cell<'_>,
    level: usize,
    stats: &mut CellCheckStats,
) -> Result<bool, CellCheckFailure> {
    stats.delineability_exact_tests += 1;
    let Some(d) = rat_degree(q) else {
        return Ok(true);
    };
    if d == 0 {
        return Ok(false); // a nonzero constant vanishes nowhere
    }
    if d > CERT_MAX_DEGREE {
        return Err(CellCheckFailure::ArithmeticExhausted {
            level,
            step: "delineability-degree",
        });
    }
    let sf = squarefree_part(q, CERT_MAX_DEGREE).ok_or(CellCheckFailure::ArithmeticExhausted {
        level,
        step: "delineability-squarefree",
    })?;
    has_root_strictly_inside(&sf, cell).ok_or(CellCheckFailure::RefinementExhausted { level })
}

/// Check 6a — **exact** delineability of `sub`'s boundary set over `cell`.
///
/// # What it establishes, and why that is the whole property
///
/// Write `t` for the cell's own variable and `v` for `sub.var`. Every boundary
/// polynomial of `sub` is re-substituted at the sample of the variables BEFORE
/// `t` -- and `t` itself is deliberately left free, which is the entire
/// difference between this and a probe at a point. What is left is a polynomial
/// in `v` whose coefficients are polynomials in `t`. Over the open interval the
/// cell denotes, all three of the following are required, each by exact root
/// counting (Sturm bisection) against the cell's own algebraic endpoints:
///
/// 1. the LEADING coefficient in `v` has no root strictly inside the cell. One
///    condition, two jobs: `deg_v` cannot drop across the cell (no root of the
///    polynomial escapes to infinity) and the polynomial cannot be nullified;
/// 2. the DISCRIMINANT `Res_v(p, ∂p/∂v)` has no root strictly inside the cell,
///    for every boundary polynomial of degree ≥ 2 in `v`: no two roots of one
///    polynomial may merge there;
/// 3. every PAIRWISE resultant `Res_v(p, q)` has no root strictly inside the
///    cell: no root of one boundary polynomial may cross a root of another.
///
/// Given 1 and 2, the `deg_v` complex roots of each boundary polynomial are
/// distinct and vary continuously over the (connected) cell; a real root can
/// leave the reals only by colliding with another root, which 2 excludes, and can
/// leave the picture only by escaping to infinity, which 1 excludes. So each
/// polynomial's distinct-real-root count is **constant** over the cell. Given 3,
/// the merged ordering of all those roots is constant too. Hence the whole
/// 1-D arrangement one level up is combinatorially the same above every point of
/// the cell, and every boundary polynomial is sign-invariant on each
/// 2-dimensional piece over it -- which is exactly what a `Deeper` cell needs to
/// carry its sub-covering from the witness to the whole cell.
///
/// # No sample appears anywhere in the argument
///
/// ADR-2121 shipped the `unsat` half OFF for one reason: the delineability test
/// was sampling, which can only FALSIFY delineability and never establish it.
/// Every quantity above is a polynomial this checker computes itself and then
/// counts roots of exactly. `None` from any step is a REJECTION, never a pass:
/// a check that cannot run must not be reported as one that ran.
///
/// # What it does not establish
///
/// Delineability over a 2-dimensional region. See
/// [`CellCheckFailure::NestedOpenGeneralization`], which is check 6c and is the
/// scope boundary of this one.
#[allow(
    clippy::too_many_lines,
    reason = "one delineability argument, three conditions: splitting them apart \
              would put the substituted boundary set they all read behind a \
              borrow dance, and the conditions are only meaningful together"
)]
fn check_delineability_exact(
    sub: &CellCovering,
    cell: &Cell<'_>,
    level: usize,
    cell_idx: usize,
    stats: &mut CellCheckStats,
) -> Result<(), CellCheckFailure> {
    let Some((parent_var, _)) = sub.sample.last().copied() else {
        return Err(CellCheckFailure::SubSampleMismatch {
            level,
            cell: cell_idx,
        });
    };
    // Everything BEFORE the parent variable is fixed. The parent variable ranges
    // over the cell, so it stays free.
    let base: BTreeMap<SymbolId, Rational> =
        sub.sample[..sub.sample.len() - 1].iter().copied().collect();

    let mut bi: Vec<Vec<RatVec>> = Vec::with_capacity(sub.boundary.len());
    for p in &sub.boundary {
        let coeffs = substitute_to_bivariate(p, &base, parent_var, sub.var).ok_or(
            CellCheckFailure::ArithmeticExhausted {
                level,
                step: "delineability-substitute",
            },
        )?;
        if coeffs.is_empty() {
            // Identically zero over the whole strip: its "roots" are the plane.
            return Err(CellCheckFailure::DelineabilityDegenerate {
                level,
                cell: cell_idx,
                step: "nullified-boundary",
            });
        }
        bi.push(coeffs);
    }

    // (1) The leading coefficient in `sub.var` must not vanish on the cell.
    for (i, coeffs) in bi.iter().enumerate() {
        let lead = coeffs
            .last()
            .ok_or(CellCheckFailure::RefinementExhausted { level })?
            .clone();
        // The test and the ACT are separate lines on purpose. `vanishes_inside`
        // is what bumps `delineability_exact_tests`, so a mutation that stops
        // acting on the answer must not also stop the counter -- otherwise the
        // fixture asserting "the exact check ran" dies alongside the fixture
        // asserting "the exact check refuses", and one mutation kills two tests
        // instead of naming one guard.
        let degree_drops = vanishes_inside(&lead, cell, level, stats)?;
        if degree_drops {
            return Err(CellCheckFailure::DelineabilityDegreeDrop {
                level,
                cell: cell_idx,
                boundary: i,
            });
        }
    }

    // (2) No two roots of one boundary polynomial may merge on the cell.
    for (i, coeffs) in bi.iter().enumerate() {
        if coeffs.len() < 3 {
            continue; // degree ≤ 1 in `sub.var`: at most one root, nothing to merge
        }
        let dp = derivative_in_elim(coeffs).ok_or(CellCheckFailure::ArithmeticExhausted {
            level,
            step: "delineability-derivative",
        })?;
        let disc =
            bivariate_resultant(coeffs, &dp).ok_or(CellCheckFailure::ArithmeticExhausted {
                level,
                step: "delineability-discriminant",
            })?;
        if rat_degree(&disc).is_none() {
            return Err(CellCheckFailure::DelineabilityDegenerate {
                level,
                cell: cell_idx,
                step: "discriminant-identically-zero",
            });
        }
        let roots_collide = vanishes_inside(&disc, cell, level, stats)?;
        if roots_collide {
            return Err(CellCheckFailure::DelineabilityRootCollision {
                level,
                cell: cell_idx,
                boundary: i,
            });
        }
    }

    // (3) No root of one boundary polynomial may cross a root of another.
    for i in 0..bi.len() {
        if bi[i].len() < 2 {
            continue; // constant in `sub.var`: contributes no root to cross
        }
        for j in (i + 1)..bi.len() {
            if bi[j].len() < 2 {
                continue;
            }
            let res = bivariate_resultant(&bi[i], &bi[j]).ok_or(
                CellCheckFailure::ArithmeticExhausted {
                    level,
                    step: "delineability-resultant",
                },
            )?;
            if rat_degree(&res).is_none() {
                return Err(CellCheckFailure::DelineabilityDegenerate {
                    level,
                    cell: cell_idx,
                    step: "resultant-identically-zero",
                });
            }
            let roots_cross = vanishes_inside(&res, cell, level, stats)?;
            if roots_cross {
                return Err(CellCheckFailure::DelineabilityCrossing {
                    level,
                    cell: cell_idx,
                    a: i,
                    b: j,
                });
            }
        }
    }
    Ok(())
}

/// Check 6b — the sampling FALSIFIER, kept as an independent cross-check on
/// [`check_delineability_exact`].
///
/// Re-substitute each boundary polynomial of `sub` at [`DELINEABILITY_SAMPLES`]
/// further interior points of `cell` (varying only `sub`'s parent variable) and
/// require the distinct-real-root count in the next variable to be the same as at
/// the witness.
///
/// This was load-bearing before ADR-2126 and is not any more: sampling can
/// falsify delineability but never establish it, which is the whole reason the
/// route's `unsat` half did not ship. It stays because it shares no code with
/// 6a -- root counts by Sturm isolation at points, against 6a's leading
/// coefficients, discriminants and resultants -- so once 6a has ACCEPTED, a
/// failure here is a disagreement between two independent implementations of one
/// property. That is a bug in one of them and a rejection either way, and a
/// checker that could not surface it would be the weaker artifact.
fn check_delineability(
    sub: &CellCovering,
    cell: &Cell<'_>,
    level: usize,
    cell_idx: usize,
    stats: &mut CellCheckStats,
) -> Result<(), CellCheckFailure> {
    let Some((parent_var, witness)) = sub.sample.last().copied() else {
        return Err(CellCheckFailure::SubSampleMismatch {
            level,
            cell: cell_idx,
        });
    };
    let base: BTreeMap<SymbolId, Rational> = sub.sample.iter().copied().collect();
    let probes = cell.interior_points(DELINEABILITY_SAMPLES).ok_or(
        CellCheckFailure::ArithmeticExhausted {
            level,
            step: "delineability-interior",
        },
    )?;
    for p in &sub.boundary {
        // The root count at the witness.
        let at_witness = distinct_root_count(p, &base, sub.var).ok_or(
            CellCheckFailure::ArithmeticExhausted {
                level,
                step: "delineability-witness",
            },
        )?;
        for probe in &probes {
            if probe.checked_cmp(&witness) == Some(Ordering::Equal) {
                continue;
            }
            let mut shifted = base.clone();
            shifted.insert(parent_var, *probe);
            let Some(at_probe) = distinct_root_count(p, &shifted, sub.var) else {
                // Exact arithmetic ran out at the probe. That is not a
                // delineability failure; it is a check that could not run, and a
                // check that cannot run must not be reported as a pass.
                return Err(CellCheckFailure::ArithmeticExhausted {
                    level,
                    step: "delineability-probe",
                });
            };
            stats.delineability_probes += 1;
            if at_probe != at_witness {
                return Err(CellCheckFailure::DelineabilityBroken {
                    level,
                    cell: cell_idx,
                    at_witness,
                    at_probe,
                });
            }
        }
    }
    Ok(())
}

/// Distinct real roots of `p` in `var` after substituting `vals`.
fn distinct_root_count(
    p: &CertPoly,
    vals: &BTreeMap<SymbolId, Rational>,
    var: SymbolId,
) -> Option<usize> {
    let uni = substitute_to_univariate(p, vals, var)?;
    if rat_degree(&uni).is_none_or(|d| d == 0) {
        return Some(0);
    }
    Some(isolate_roots_sturm(&uni)?.len())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Two real symbols from a throwaway arena. `SymbolId` has no public
    /// constructor, so the tests declare real ones rather than minting handles.
    fn two_syms() -> (SymbolId, SymbolId) {
        let mut a = axeyum_ir::TermArena::new();
        let x = a.declare("x", axeyum_ir::Sort::Real).expect("declare x");
        let y = a.declare("y", axeyum_ir::Sort::Real).expect("declare y");
        (x, y)
    }

    fn r(n: i128) -> Rational {
        Rational::integer(n)
    }

    /// `x^2 - 2` as a certificate polynomial in variable `v`.
    fn x2_minus(v: SymbolId, c: i128) -> CertPoly {
        canonicalize(vec![(vec![(v, 2)], r(1)), (Vec::new(), r(-c))])
    }

    /// `x` as a certificate polynomial.
    fn lin(v: SymbolId) -> CertPoly {
        canonicalize(vec![(vec![(v, 1)], r(1))])
    }

    #[test]
    fn isolation_finds_both_roots_of_x_squared_minus_two() {
        let p: RatVec = vec![r(-2), r(0), r(1)];
        let roots = isolate_roots_sturm(&p).expect("isolation");
        assert_eq!(roots.len(), 2, "±√2");
    }

    #[test]
    fn isolation_finds_the_rational_roots_of_x_squared_minus_one() {
        let p: RatVec = vec![r(-1), r(0), r(1)];
        let roots = isolate_roots_sturm(&p).expect("isolation");
        assert_eq!(roots.len(), 2);
    }

    #[test]
    fn a_squared_polynomial_has_one_distinct_root() {
        // (x-1)^2 = x^2 - 2x + 1
        let p: RatVec = vec![r(1), r(-2), r(1)];
        let roots = isolate_roots_sturm(&p).expect("isolation");
        assert_eq!(roots.len(), 1, "squarefree part has the same root SET");
    }

    #[test]
    fn sign_at_an_irrational_root_is_exact() {
        let p: RatVec = vec![r(-2), r(0), r(1)]; // x^2 - 2
        let roots = isolate_roots_sturm(&p).expect("isolation");
        let positive = roots.last().expect("a root");
        // q = x, so q(√2) > 0.
        let q: RatVec = vec![r(0), r(1)];
        assert_eq!(sign_at_root(&q, positive), Some(Sign::Pos));
        // q = x^2 - 2 vanishes there.
        assert_eq!(sign_at_root(&p, positive), Some(Sign::Zero));
    }

    /// The smallest honest refutation: `x > 0 ∧ x < 0` over one variable.
    fn one_var_refutation() -> CellRefutation {
        let (x, _y) = two_syms();
        let atoms = vec![
            CertAtom::new(CertCmp::Gt, lin(x)),
            CertAtom::new(CertCmp::Lt, lin(x)),
        ];
        // Arrangement of {x}: one root (0), three cells.
        let cov = CellCovering::new(
            x,
            Vec::new(),
            vec![lin(x)],
            vec![
                CellReason::Atom { atom_index: 0 }, // (-inf, 0): x > 0 fails
                CellReason::Atom { atom_index: 0 }, // {0}:       x > 0 fails
                CellReason::Atom { atom_index: 1 }, // (0, inf):  x < 0 fails
            ],
        );
        CellRefutation::new(vec![x], atoms, cov)
    }

    #[test]
    fn the_one_variable_refutation_checks_out() {
        let stats = check_cell_refutation(&one_var_refutation()).expect("accepted");
        assert_eq!(stats.cells, 3, "all three cells examined");
        assert_eq!(stats.atom_cells, 3);
        assert_eq!(stats.coverings, 1);
    }

    #[test]
    fn a_cell_blamed_on_an_atom_that_is_satisfied_there_is_rejected() {
        let mut ref_ = one_var_refutation();
        // Blame `x < 0` for the cell (-inf, 0), where it HOLDS.
        ref_.root.cells[0] = CellReason::Atom { atom_index: 1 };
        let err = check_cell_refutation(&ref_).expect_err("must reject");
        assert_eq!(err.name(), "atom-satisfied", "got {err:?}");
    }

    #[test]
    fn a_short_cell_list_is_rejected() {
        let mut ref_ = one_var_refutation();
        ref_.root.cells.pop();
        let err = check_cell_refutation(&ref_).expect_err("must reject");
        assert_eq!(err.name(), "cell-count", "got {err:?}");
    }

    #[test]
    fn an_atom_missing_from_the_boundary_is_rejected() {
        let (x, _y) = two_syms();
        let atoms = vec![
            CertAtom::new(CertCmp::Gt, lin(x)),
            // `x^2 - 2 < 0` -- its roots ±√2 are cell boundaries, and omitting it
            // from the boundary set would let a cell straddle them.
            CertAtom::new(CertCmp::Lt, x2_minus(x, 2)),
        ];
        let cov = CellCovering::new(
            x,
            Vec::new(),
            vec![lin(x)], // the quadratic is NOT here
            vec![
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
            ],
        );
        let err = check_cell_refutation(&CellRefutation::new(vec![x], atoms, cov))
            .expect_err("must reject");
        assert_eq!(err.name(), "atom-not-in-boundary", "got {err:?}");
    }

    #[test]
    fn an_undecided_cell_is_rejected() {
        let mut ref_ = one_var_refutation();
        ref_.root.cells[1] = CellReason::Undecided;
        let err = check_cell_refutation(&ref_).expect_err("must reject");
        assert_eq!(err.name(), "undecided-cell", "got {err:?}");
    }

    #[test]
    fn an_empty_refutation_is_rejected() {
        let (x, _y) = two_syms();
        let cov = CellCovering::new(x, Vec::new(), Vec::new(), vec![CellReason::Undecided]);
        let err = check_cell_refutation(&CellRefutation::new(vec![x], Vec::new(), cov))
            .expect_err("must reject");
        assert_eq!(err.name(), "empty", "got {err:?}");
    }

    #[test]
    fn a_sample_that_does_not_match_the_order_is_rejected() {
        let mut ref_ = one_var_refutation();
        ref_.root.sample.push((two_syms().0, r(1)));
        let err = check_cell_refutation(&ref_).expect_err("must reject");
        assert_eq!(err.name(), "sample-shape", "got {err:?}");
    }

    /// Two variables: `y > 0 ∧ y < 0`, refuted at every `x`. The level-0
    /// covering has ONE cell (no level-0 atoms, so no boundary), closed by a
    /// sub-covering at `x = 0`.
    fn two_var_refutation() -> CellRefutation {
        let (x, y) = two_syms();
        let atoms = vec![
            CertAtom::new(CertCmp::Gt, lin(y)),
            CertAtom::new(CertCmp::Lt, lin(y)),
        ];
        let sub = CellCovering::new(
            y,
            vec![(x, r(0))],
            vec![lin(y)],
            vec![
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 1 },
            ],
        );
        let root = CellCovering::new(
            x,
            Vec::new(),
            Vec::new(), // no level-0 boundary: one cell, all of R
            vec![CellReason::Deeper {
                witness: r(0),
                sub: Box::new(sub),
            }],
        );
        CellRefutation::new(vec![x, y], atoms, root)
    }

    #[test]
    fn the_two_variable_refutation_checks_out_and_probes_delineability() {
        let stats = check_cell_refutation(&two_var_refutation()).expect("accepted");
        assert_eq!(stats.coverings, 2);
        assert_eq!(stats.deeper_cells, 1);
        assert_eq!(stats.max_level, 1);
        // One boundary polynomial, and one of the three interior probes lands
        // exactly on the witness (the cell is all of R, so the probes are
        // -1, 0, 1 and the witness is 0) -- that one is skipped because it is
        // not a second point. Two genuine probes remain, and the assertion is
        // written against that rather than against the constant, so a checker
        // that silently stopped probing fails here.
        assert_eq!(
            stats.delineability_probes,
            DELINEABILITY_SAMPLES - 1,
            "the delineability cross-check must actually have run: {stats:?}"
        );
        // And the EXACT check must have examined something. `y` is the single
        // boundary polynomial, linear in `y`, so 6a runs exactly one
        // root-freeness test: its leading coefficient. Written against the
        // covering's own shape rather than against a constant, so a checker that
        // stopped running 6a fails here rather than passing with a zero.
        assert_eq!(stats.open_deeper_cells, 1, "{stats:?}");
        assert_eq!(
            stats.delineability_exact_tests, 1,
            "the EXACT delineability check must have run: {stats:?}"
        );
    }

    #[test]
    fn a_sub_sample_that_does_not_extend_the_parent_is_rejected() {
        let mut ref_ = two_var_refutation();
        if let CellReason::Deeper { sub, .. } = &mut ref_.root.cells[0] {
            sub.sample = vec![(two_syms().0, r(7))]; // witness says 0
        }
        let err = check_cell_refutation(&ref_).expect_err("must reject");
        assert_eq!(err.name(), "sub-sample-mismatch", "got {err:?}");
    }

    #[test]
    fn delineability_rejects_a_cell_whose_root_count_changes() {
        let (x, y) = two_syms();
        // `y^2 - x < 0 ∧ y^2 - x > 0` is unsatisfiable at every x, but the
        // boundary polynomial `y^2 - x` has 0 roots in y for x < 0 and 2 for
        // x > 0. A level-0 cell spanning ALL of R therefore is NOT delineable,
        // and a route that failed to project `x` down would build exactly this.
        let p: CertPoly = canonicalize(vec![(vec![(y, 2)], r(1)), (vec![(x, 1)], r(-1))]);
        let atoms = vec![
            CertAtom::new(CertCmp::Lt, p.clone()),
            CertAtom::new(CertCmp::Gt, p.clone()),
        ];
        // At x = 1 the polynomial has two roots (±1), so three cells.
        let sub = CellCovering::new(
            y,
            vec![(x, r(1))],
            vec![p.clone()],
            vec![
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
            ],
        );
        let root = CellCovering::new(
            x,
            Vec::new(),
            Vec::new(), // NO projection: the fatal omission
            vec![CellReason::Deeper {
                witness: r(1),
                sub: Box::new(sub),
            }],
        );
        let err = check_cell_refutation(&CellRefutation::new(vec![x, y], atoms, root))
            .expect_err("must reject");
        // Since ADR-2126 the EXACT check (6a) sees this first and names the
        // mechanism: the discriminant of `y^2 - x` in `y` is a nonzero multiple
        // of `x`, whose root 0 lies strictly inside the level-0 cell, so the two
        // roots merge there. The old `delineability-broken` was the sampling
        // check noticing the CONSEQUENCE.
        assert_eq!(err.name(), "delineability-root-collision", "got {err:?}");
    }

    /// The sampling cross-check (6b) still has its own teeth on the same cell.
    ///
    /// Asserted by calling it DIRECTLY, because 6a rejects first in the shipped
    /// order and would otherwise hide whether 6b still works. Deleting 6a kills
    /// the test above; deleting 6b kills this one. One guard, one killer.
    #[test]
    fn the_sampling_cross_check_also_rejects_the_root_count_change() {
        let (x, y) = two_syms();
        let p: CertPoly = canonicalize(vec![(vec![(y, 2)], r(1)), (vec![(x, 1)], r(-1))]);
        let sub = CellCovering::new(
            y,
            vec![(x, r(1))],
            vec![p],
            vec![
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
            ],
        );
        // The level-0 cell is all of R: no boundary, so no roots.
        let roots: Vec<IsoRoot> = Vec::new();
        let cells = cells_of(&roots);
        let mut stats = CellCheckStats::default();
        let err = check_delineability(&sub, &cells[0], 0, 0, &mut stats).expect_err("must reject");
        assert_eq!(err.name(), "delineability-broken", "got {err:?}");
    }

    /// **The fixture ADR-2126 exists for**: a cell the SAMPLING check accepts and
    /// the EXACT check refuses.
    ///
    /// `t·y − 1` has exactly one root in `y` for every `t ≠ 0` and none at all at
    /// `t = 0`, where it collapses to the constant `−1`. Its leading coefficient
    /// in `y` is `t`. So the root count is constant on the cell EXCEPT at the
    /// single point `t = 0` — and a check that looks at finitely many points
    /// misses a single point almost surely. The cell `(−1, 5)` is chosen so that
    /// none of the three probes lands on 0.
    ///
    /// Both halves are asserted. If the sampling half ever started rejecting,
    /// this fixture would stop demonstrating the gap, and a test that can go
    /// quietly vacuous is worse than no test — so it fails instead.
    #[test]
    fn a_sampled_check_passes_a_non_delineable_cell_and_the_exact_check_refuses() {
        let (t, y) = two_syms();
        // Parent boundary `(t + 1)(t - 5) = t^2 - 4t - 5`, cutting out `(-1, 5)`.
        let parent: RatVec = vec![r(-5), r(-4), r(1)];
        let roots = isolate_roots_sturm(&parent).expect("isolate");
        let roots = merge_roots(roots).expect("merge");
        assert_eq!(
            roots.len(),
            2,
            "the parent cell must be bounded on both sides"
        );
        let cells = cells_of(&roots);
        let cell = &cells[2]; // the open cell between the two roots

        // `t·y - 1`: leading coefficient in `y` is `t`, which vanishes at 0.
        let p: CertPoly = canonicalize(vec![(vec![(t, 1), (y, 1)], r(1)), (Vec::new(), r(-1))]);
        let sub = CellCovering::new(
            y,
            vec![(t, r(1))], // witness t = 1, strictly inside (-1, 5)
            vec![p],
            vec![
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
            ],
        );

        // The SAMPLING check accepts: every probe has the same root count as the
        // witness, because none of them is the single bad point.
        let mut sampled = CellCheckStats::default();
        let sampled_verdict = check_delineability(&sub, cell, 0, 2, &mut sampled);
        assert!(
            sampled_verdict.is_ok(),
            "the fixture stops showing the gap if sampling rejects: {sampled_verdict:?}"
        );
        assert!(
            sampled.delineability_probes > 0,
            "sampling must have actually probed: {sampled:?}"
        );

        // The EXACT check refuses, and names the mechanism.
        let mut exact = CellCheckStats::default();
        let err = check_delineability_exact(&sub, cell, 0, 2, &mut exact)
            .expect_err("the exact check must refuse a non-delineable cell");
        assert_eq!(err.name(), "delineability-degree-drop", "got {err:?}");
        assert!(
            exact.delineability_exact_tests > 0,
            "the exact check must have examined something: {exact:?}"
        );
    }

    /// **The second thing sampling cannot see**: two roots that CROSS.
    ///
    /// `y - t` and `y + t` each have exactly one root in `y` for every `t`, so
    /// every per-polynomial root count is 1 everywhere and the sampling check
    /// cannot fail no matter where it probes — it counts roots per polynomial
    /// and has no way to observe their ORDER. But the two roots swap at `t = 0`,
    /// so the merged arrangement above the cell `(-1, 5)` is not the arrangement
    /// at the witness, and a sub-covering built at `t = 1` does not describe
    /// `t = -1/2`.
    ///
    /// This is condition (3) of check 6a and NOTHING else can fire here: both
    /// leading coefficients are the constant 1, and both are linear in `y` so
    /// there is no discriminant. So the fixture isolates the pairwise resultant,
    /// which would otherwise be a guard with no test.
    ///
    /// Both halves are asserted, for the same reason as the degree-drop fixture:
    /// a test that stops demonstrating the gap must fail rather than go quiet.
    #[test]
    fn two_roots_that_cross_are_invisible_to_sampling_and_refused_by_the_exact_check() {
        let (t, y) = two_syms();
        let parent: RatVec = vec![r(-5), r(-4), r(1)]; // (t + 1)(t - 5)
        let roots = merge_roots(isolate_roots_sturm(&parent).expect("isolate")).expect("merge");
        assert_eq!(roots.len(), 2);
        let cells = cells_of(&roots);
        let cell = &cells[2]; // the open cell (-1, 5), which contains 0

        let minus: CertPoly = canonicalize(vec![(vec![(y, 1)], r(1)), (vec![(t, 1)], r(-1))]);
        let plus: CertPoly = canonicalize(vec![(vec![(y, 1)], r(1)), (vec![(t, 1)], r(1))]);
        let sub = CellCovering::new(
            y,
            vec![(t, r(1))],
            vec![minus, plus],
            // Two boundary polynomials with distinct roots at t = 1 give five cells.
            vec![
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
                CellReason::Atom { atom_index: 0 },
            ],
        );

        let mut sampled = CellCheckStats::default();
        let sampled_verdict = check_delineability(&sub, cell, 0, 2, &mut sampled);
        assert!(
            sampled_verdict.is_ok(),
            "the fixture stops showing the gap if sampling rejects: {sampled_verdict:?}"
        );
        assert!(sampled.delineability_probes > 0, "{sampled:?}");

        let mut exact = CellCheckStats::default();
        let err = check_delineability_exact(&sub, cell, 0, 2, &mut exact)
            .expect_err("two roots crossing inside the cell must be refused");
        assert_eq!(err.name(), "delineability-crossing", "got {err:?}");
        assert!(exact.delineability_exact_tests > 0, "{exact:?}");
    }

    /// A generalisation resting on another generalisation is refused, and the
    /// SAME shape over a point cell is not.
    ///
    /// The negative half alone would pass on a checker that refused every
    /// `Deeper` sub-cell, which would make the route answer nothing.
    #[test]
    fn a_generalisation_that_rests_on_another_generalisation_is_refused() {
        let (x, y) = two_syms();
        // A sub-covering whose single cell is itself a `Deeper` cell. The inner
        // covering is never reached: 6c rejects before the recursion.
        let inner = CellCovering::new(
            y,
            vec![(x, r(0)), (y, r(0))],
            Vec::new(),
            vec![CellReason::Atom { atom_index: 0 }],
        );
        let sub = CellCovering::new(
            y,
            vec![(x, r(0))],
            Vec::new(),
            vec![CellReason::Deeper {
                witness: r(0),
                sub: Box::new(inner),
            }],
        );
        let root = CellCovering::new(
            x,
            Vec::new(),
            Vec::new(), // one cell, all of R -- an OPEN cell
            vec![CellReason::Deeper {
                witness: r(0),
                sub: Box::new(sub),
            }],
        );
        let atoms = vec![CertAtom::new(CertCmp::Gt, lin(y))];
        let err = check_cell_refutation(&CellRefutation::new(vec![x, y], atoms, root))
            .expect_err("must reject");
        assert_eq!(err.name(), "nested-open-generalization", "got {err:?}");

        // The positive control: an all-atom sub-covering over the same open cell
        // is accepted, so the guard is not "refuse every `Deeper` cell".
        let ok = check_cell_refutation(&two_var_refutation());
        assert!(
            ok.is_ok(),
            "the guard must not refuse a sound covering: {ok:?}"
        );
    }

    /// Negation is an involution and disagrees with the original on EVERY sign.
    ///
    /// Derived over all six comparisons and all three signs, not spot-checked:
    /// this is the identity the clause loop turns a false propositional literal
    /// into a theory atom with, and a single wrong row would make the loop hand
    /// the theory a constraint the Boolean model did not ask for.
    #[test]
    fn negating_a_comparison_flips_it_at_every_sign() {
        let all = [
            CertCmp::Eq,
            CertCmp::Ne,
            CertCmp::Lt,
            CertCmp::Le,
            CertCmp::Gt,
            CertCmp::Ge,
        ];
        for cmp in all {
            assert_eq!(
                cmp.negate().negate(),
                cmp,
                "{} is not an involution",
                cmp.name()
            );
            for sign in [Sign::Neg, Sign::Zero, Sign::Pos] {
                assert_ne!(
                    cmp.holds(sign),
                    cmp.negate().holds(sign),
                    "{} and its negation agree at {sign:?}",
                    cmp.name()
                );
            }
        }
    }

    #[test]
    fn every_failure_variant_has_a_distinct_name() {
        // Derived from the authority (the variants themselves), not a literal
        // list a maintainer keeps in step by hand.
        let all = [
            CellCheckFailure::Empty,
            CellCheckFailure::SampleShape { level: 0 },
            CellCheckFailure::AtomNotInBoundary {
                level: 0,
                atom_index: 0,
            },
            CellCheckFailure::CellCount {
                level: 0,
                listed: 0,
                expected: 0,
            },
            CellCheckFailure::AtomNotInvariant {
                level: 0,
                cell: 0,
                atom_index: 0,
            },
            CellCheckFailure::AtomSatisfied {
                level: 0,
                cell: 0,
                atom_index: 0,
            },
            CellCheckFailure::AtomIndex {
                level: 0,
                atom_index: 0,
            },
            CellCheckFailure::WitnessOutsideCell { level: 0, cell: 0 },
            CellCheckFailure::SubSampleMismatch { level: 0, cell: 0 },
            CellCheckFailure::DelineabilityDegreeDrop {
                level: 0,
                cell: 0,
                boundary: 0,
            },
            CellCheckFailure::DelineabilityRootCollision {
                level: 0,
                cell: 0,
                boundary: 0,
            },
            CellCheckFailure::DelineabilityCrossing {
                level: 0,
                cell: 0,
                a: 0,
                b: 0,
            },
            CellCheckFailure::DelineabilityDegenerate {
                level: 0,
                cell: 0,
                step: "x",
            },
            CellCheckFailure::NestedOpenGeneralization {
                level: 0,
                cell: 0,
                sub_cell: 0,
            },
            CellCheckFailure::DelineabilityBroken {
                level: 0,
                cell: 0,
                at_witness: 0,
                at_probe: 0,
            },
            CellCheckFailure::UndecidedCell { level: 0, cell: 0 },
            CellCheckFailure::FreeVariable { level: 0 },
            CellCheckFailure::ArithmeticExhausted {
                level: 0,
                step: "x",
            },
            CellCheckFailure::RefinementExhausted { level: 0 },
            CellCheckFailure::LevelOverflow { level: 0 },
        ];
        let names: BTreeSet<&str> = all.iter().map(CellCheckFailure::name).collect();
        assert_eq!(names.len(), all.len(), "names must be distinct");
    }

    // -----------------------------------------------------------------------
    // ADR-2131: two coverings this checker used to REJECT, both reached by the
    // shipped conjunctive route.
    //
    // They live here rather than in `nra_clause_loop` deliberately. The clause
    // loop is what FOUND them, but neither needs it: both are plain
    // conjunctions that `decide_single_cell` -- the route ADR-2126 ships --
    // reaches and then drops with `certificate-rejected`. Putting them beside
    // the checker says whose defect it was.
    //
    // Each asserts `Some(Unsat)`, which on this path means the checker ACCEPTED:
    // `decide_single_cell` returns `None` and records `CertificateRejected` when
    // it does not. So reverting either fix turns exactly the corresponding test
    // red.
    // -----------------------------------------------------------------------

    fn conjunctive_unsat(script: &str) -> (bool, &'static str) {
        let parsed = axeyum_smtlib::parse_script(script).expect("parse");
        crate::nra_real_root::reset_cad_decline();
        let out = crate::nra_single_cell::decide_single_cell(
            &parsed.arena,
            &parsed.assertions,
            None,
            true,
            false,
        );
        (
            matches!(out, Some(crate::backend::CheckResult::Unsat)),
            crate::nra_real_root::cad_decline().name(),
        )
    }

    /// A root of the closing atom sitting exactly ON the cell's boundary.
    ///
    /// `x > 1 ∧ x < 0` is about as small as an unsatisfiable conjunction gets.
    /// The arrangement is cut by `x - 1` and `x`, and the cell `(0, 1)` is closed
    /// by `x - 1 > 0` -- whose root IS that cell's upper boundary. Bisection from
    /// the Cauchy bracket never lands on the rational 1, so the endpoint is never
    /// marked exact, so the sliver count at that endpoint stayed at 1 through
    /// every bisection and the check exhausted `REFINE_DEPTH`.
    ///
    /// The atom that closes a cell is very often one of the boundary
    /// polynomials, so this is not an exotic shape; it is the common one.
    #[test]
    fn a_closing_atom_whose_root_is_the_cell_boundary_is_accepted() {
        let (unsat, cause) = conjunctive_unsat(
            "(declare-fun x () Real)\n(assert (> x 1))\n(assert (< x 0))\n(check-sat)\n",
        );
        assert!(
            unsat,
            "the checker must accept this covering; it declined with {cause}"
        );
    }

    /// An unbounded cell whose Cauchy bound does not clear its finite endpoint.
    ///
    /// `x > 2 ∧ x < 0` cuts the line at 0 and 2, and the cell `(2, +inf)` is
    /// closed by `x < 0`. The Cauchy bound of `x` is exactly 2, so the counting
    /// interval came out EMPTY -- and there is nothing on the infinite side to
    /// refine, so the loop could only spin to `REFINE_DEPTH`.
    #[test]
    fn an_unbounded_cell_whose_cauchy_bound_meets_its_endpoint_is_accepted() {
        let (unsat, cause) = conjunctive_unsat(
            "(declare-fun x () Real)\n(assert (> x 2))\n(assert (< x 0))\n(check-sat)\n",
        );
        assert!(
            unsat,
            "the checker must accept this covering; it declined with {cause}"
        );
    }

    /// The control that stops the two fixes above from being read as "the
    /// checker got looser".
    ///
    /// A SATISFIABLE conjunction over the same shapes must never be refuted.
    /// Without this, a fix that made `has_root_strictly_inside` always answer
    /// "no root inside" would pass both tests above.
    #[test]
    fn the_boundary_fixes_do_not_refute_a_satisfiable_conjunction() {
        for script in [
            "(declare-fun x () Real)\n(assert (> x 1))\n(assert (< x 5))\n(check-sat)\n",
            "(declare-fun x () Real)\n(assert (> x 2))\n(assert (< x 3))\n(check-sat)\n",
            "(declare-fun x () Real)\n(assert (>= x 2))\n(assert (<= x 2))\n(check-sat)\n",
            "(declare-fun x () Real)\n(assert (> (* x x) 2))\n(assert (< x 5))\n(check-sat)\n",
        ] {
            let (unsat, cause) = conjunctive_unsat(script);
            assert!(
                !unsat,
                "a satisfiable conjunction was refuted ({cause}): {script}"
            );
        }
    }
}
