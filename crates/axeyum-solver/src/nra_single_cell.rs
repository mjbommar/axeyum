//! Model-constructing CAD over the reals: **one cell per conflict**, not the
//! whole arrangement (ADR-2121, lane `NRA-SINGLE-CELL`).
//!
//! # Why this exists
//!
//! ADR-2110 measured the `QF_NRA` gap and split it in two. Of the 83 files the
//! 2026-09-15 board leaves undecided, **45 are decided by z3's CAD arm and not
//! by its incremental-linearization arm**, 44 of them in under a second (median
//! 108 ms). It then named the design difference with `file:line` on both sides:
//!
//! * we enumerate the arrangement — [`crate::nra_real_root`]'s `visit_open_cells`
//!   recurses over the whole projection, charging a global 256-cell budget, and
//!   an `Unsat` is earned only by visiting **every** cell;
//! * z3 builds **one cell per conflict**, reading the current sample
//!   (`nlsat_solver.cpp:1848` `search()` → `nlsat_explain.cpp:988` `project` →
//!   `levelwise.cpp:1526` `levelwise::single_cell`), and cvc5 the same with
//!   coverings (`coverings/cdcac.cpp:555` `getUnsatCoverImpl`, characterized at
//!   `cdcac.cpp:358` `constructCharacterization`).
//!
//! This module is the second shape. It never forms the full arrangement of the
//! full projection: at each level it holds a boundary set that starts as *that
//! level's own atoms* and grows **only** with the projection of polynomials a
//! real conflict one level down actually used.
//!
//! # The loop
//!
//! Variables are ordered once, by [`SymbolId`], and never reordered — the order
//! and every sample choice are deterministic, which is a public API promise.
//! At level `k`, holding a rational sample of `order[..k]`:
//!
//! 1. isolate the real roots of the boundary set (substituted at the sample) and
//!    walk the `2m + 1` cells of that 1-D arrangement in ascending order;
//! 2. a cell on which one of this level's atoms is violated is closed, and the
//!    atom is the reason — sound for the *whole* cell because the atom is in the
//!    boundary set, so it has no root inside;
//! 3. otherwise descend with the cell's interior rational as the witness;
//! 4. a conflict below returns the polynomials it used. **Project** them past
//!    `order[k+1]`, add whatever is new to the boundary set, and restart the
//!    scan. When a full scan adds nothing, the covering is at a fixpoint: every
//!    cell's reason is valid under the boundary set the cells were cut from,
//!    which is exactly the condition a `Deeper` reason needs to generalise from
//!    its witness to its cell.
//!
//! `sat` is a complete rational sample; `unsat` is the fixpoint covering at
//! level 0.
//!
//! # Soundness
//!
//! * **`unsat` is emitted only if [`crate::nra_cell_cert`] accepts the
//!   covering.** The checker re-derives the arrangement with its own root
//!   isolation and re-substitutes every polynomial from the multivariate form.
//!   A rejection makes the route decline ([`CadDecline::CertificateRejected`]) —
//!   the verdict is dropped, never downgraded to a guess. Since ADR-2126 that
//!   checker's delineability test is **exact** — leading coefficients,
//!   discriminants and pairwise resultants required to be root-free on the cell
//!   by Sturm counting against its algebraic endpoints — and it rejects a
//!   covering whose generalisation would reach past the argument's scope. See
//!   that module's docs for what it establishes and where it stops.
//! * **`sat` is a rational model replayed against the original assertions** by
//!   the ground evaluator before it leaves this module. An algebraic witness is
//!   not represented: a cell that satisfies every atom only at an irrational
//!   point makes the route decline ([`CadDecline::AlgebraicCoarsening`]) rather
//!   than round it.
//! * **The projection is nullification-complete.** `McCallum`'s operator is valid
//!   over a cell on which no eliminated polynomial is nullified; this one adds
//!   *every* coefficient in the eliminated variable (not only the leading one),
//!   so non-nullification at the sample plus sign-invariance of the coefficients
//!   on the cell gives non-nullification on the cell. And it checks
//!   non-nullification at the sample explicitly: a polynomial that vanishes
//!   identically there declines with [`CadDecline::NullifiedResidual`]. **That
//!   check is where the soundness of this route lives**, and the mutation suite
//!   deletes it to prove one named fixture dies.
//!
//! # The slice, and what it refuses
//!
//! Bounded by declaration, not by exhaustion:
//!
//! * at most [`MAX_CELL_VARS`] variables and total degree at most
//!   [`MAX_CELL_DEGREE`] — [`CadDecline::SliceBounds`];
//! * source coefficients within `nra_real_root`'s `MAX_ABS_COEFF` (`1 << 40`),
//!   which is ADR-2110 claim 2's capability gap and is **not** closed here: 9 of
//!   the 45 CAD-decided files are outside it before any projection;
//! * a conjunction of polynomial comparisons and nothing else —
//!   [`CadDecline::NonConjunctive`];
//! * a resultant whose Sylvester dimension exceeds `nra_real_root`'s
//!   `MAX_MULTI_SYLVESTER_DIM` (6), because the multivariate determinant is an
//!   exact Leibniz expansion — [`CadDecline::ProjectionSylvesterDim`]. This is
//!   the binding constraint on high per-variable degree. ADR-2121 recorded it
//!   inside a single `Projection` bucket that also held an identically-zero
//!   resultant, a derivative overflow and a coefficient overflow; ADR-2126 split
//!   the four apart, because only this one is what a fraction-free determinant
//!   would remove, and a bundle is an upper bound on each member and a
//!   measurement of none.
//!
//! # Two arms, two assurance levels
//!
//! The route's halves are not equally justified, and the lever separates them:
//!
//! * `AXEYUM_NRA_CAD=single-cell` runs it whole;
//! * `AXEYUM_NRA_CAD=single-cell-sat` runs it and **withholds every `unsat`** as
//!   [`CadDecline::UnsatWithheldByArm`], keeping only the `sat`
//!   side — a rational model replayed through the ground evaluator against the
//!   original assertions, which is exact and rests on no sample.
//!
//! That is the whole difference between them: the cell cap is identical on both
//! and on `default`, so an A/B between any two isolates exactly one thing.
//!
//! **ADR-2126 changed what the difference BUYS, without touching either arm.**
//! The reason `single-cell-sat` was the shipped arm is that the full arm's
//! `unsat` rested on a sampling delineability check. That check is now exact
//! ([`crate::nra_cell_cert`] check 6a), it names its own scope boundary
//! (check 6c), and a covering outside that boundary is REJECTED rather than
//! accepted. So the A/B between the two arms now prices an `unsat` half whose
//! justification carries no sample at all.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use axeyum_ir::poly::eval_int_poly;
use axeyum_ir::{
    Assignment, Rational, RealAlgebraic, Sign, SymbolId, TermArena, TermId, Value, eval,
};

use crate::backend::CheckResult;
use crate::model::Model;
use crate::nra_cell_cert::{
    CellCheckStats, CellCovering, CellReason, CellRefutation, CertAtom, CertCmp, CertPoly,
    check_cell_refutation,
};
use crate::nra_real_root::{
    CadDecline, MAX_ABS_COEFF, MultiPoly, ResultantDecline, ResultantOutcome, Root, cell_samples,
    coeffs_in_elim, collect_cert_atoms, dedup_sorted_roots, degree_in, derivative_in,
    isolate_roots, multi_resultant_classified, multipoly_from_cert, multipoly_to_cert,
    record_cad_decline, sort_roots,
};

/// Most variables the slice accepts. Four covers ADR-2110's largest CAD-decided
/// bucket (3 variables, degree 8, one assertion, mostly `meti-tarski`) with a
/// margin; beyond it the projection's cost is unmeasured and the route refuses
/// rather than discovers.
pub(crate) const MAX_CELL_VARS: usize = 4;

/// Highest TOTAL degree the slice accepts in any atom.
pub(crate) const MAX_CELL_DEGREE: u32 = 8;

/// Boundary-set refinement rounds allowed per level before the route declines.
///
/// Each round that grows the boundary set strictly refines the arrangement, so
/// the loop terminates on its own when the projection closure is reached; this
/// bounds the cost when it is not, and produces [`CadDecline::CellBudget`]
/// rather than a hang.
const MAX_REFINE_ROUNDS: usize = 24;

/// Total cells the whole recursion may examine. A second, global bound so a
/// shallow-but-wide arrangement cannot spend the budget the per-level cap allows.
const MAX_TOTAL_CELLS: usize = 4096;

thread_local! {
    /// What [`crate::nra_cell_cert::check_cell_refutation`] examined on the last
    /// `unsat` this route emitted.
    ///
    /// Exists so a test that claims "every `unsat` passed the checker" can read
    /// what the checker actually looked at, instead of asserting something it can
    /// re-derive for itself. A test that re-derives its subject inline passes
    /// while the shipped artifact is wrong.
    static LAST_CELL_CHECK: core::cell::Cell<Option<CellCheckStats>> =
        const { core::cell::Cell::new(None) };
}

/// The checker's counts from the last accepted refutation, or `None` if the last
/// decision did not produce one.
pub(crate) fn last_cell_check() -> Option<CellCheckStats> {
    LAST_CELL_CHECK.with(core::cell::Cell::get)
}

/// One coordinate of a complete sample.
///
/// The recursion carries RATIONAL coordinates downward -- a deeper level has to
/// substitute the coordinate into a polynomial and isolate the result's roots,
/// and this slice does that in exact rational arithmetic. Only the LAST
/// coordinate may be algebraic, because nothing is substituted into anything
/// after it (ADR-2134).
#[derive(Clone, Debug)]
pub(crate) enum SampleCoord {
    /// An exact rational.
    Rational(Rational),
    /// An irrational algebraic root, as the final coordinate only.
    Algebraic(RealAlgebraic),
}

impl SampleCoord {
    /// The coordinate as a model [`Value`].
    fn to_value(&self) -> Value {
        match self {
            SampleCoord::Rational(q) => Value::Real(*q),
            SampleCoord::Algebraic(a) => Value::RealAlgebraic(a.clone()),
        }
    }

    /// Whether this coordinate is irrational-algebraic.
    fn is_algebraic(&self) -> bool {
        matches!(self, SampleCoord::Algebraic(_))
    }
}

/// What one level of the recursion produced.
enum LevelOutcome {
    /// A complete sample satisfying every atom of every level at or above this
    /// one. Every coordinate is rational except possibly the last (ADR-2134).
    Sat(Vec<(SymbolId, SampleCoord)>),
    /// No value of this level's variable survives, under this sample.
    Refuted {
        /// The fixpoint covering.
        covering: CellCovering,
        /// The boundary set it was cut from — what the level above must project.
        polys: Vec<CertPoly>,
    },
}

/// One cell of a 1-D arrangement, with the exact point the route tests it at.
struct ArrangementCell {
    /// The point the cell is tested at: a rational interior sample for an open
    /// cell, or the root itself for a point cell.
    ///
    /// The cell's KIND (open vs point) is deliberately not carried: the
    /// certificate does not record it and the checker recomputes it from its own
    /// arrangement, so a field here could only ever disagree with the authority.
    rep: CellRep,
}

/// The representative point of a cell.
enum CellRep {
    /// A rational, usable both as a test point and as a `Deeper` witness.
    Rational(Rational),
    /// An irrational algebraic root. Testable (exactly, by `sign_at`) but not
    /// usable as a sample for a deeper level.
    Algebraic(RealAlgebraic),
}

/// The shared state of one decision.
struct Ctx<'a> {
    atoms: &'a [CertAtom],
    order: &'a [SymbolId],
    /// Atom indices grouped by level (the index of their highest variable).
    by_level: Vec<Vec<usize>>,
    deadline: Option<Instant>,
    cells_seen: usize,
    /// Whether an ALGEBRAIC representative point may be accepted as the final
    /// coordinate (ADR-2134). Carried on the context rather than read from the
    /// environment so the route stays a pure function of its arguments and a
    /// test can exercise both arms in one process.
    algebraic_witness: bool,
}

impl Ctx<'_> {
    fn out_of_time(&self) -> bool {
        self.deadline.is_some_and(|d| Instant::now() >= d)
    }
}

/// Decide a conjunction of polynomial real comparisons by single-cell CAD.
///
/// Returns `Some(Sat)` with a rational model replayed against `assertions`,
/// `Some(Unsat)` only when the certificate checker accepted the covering, or
/// `None` to decline — with the cause recorded through
/// [`crate::nra_real_root::record_cad_decline`].
///
/// The caller is responsible for the `AXEYUM_NRA_CAD` gate; this function does
/// not read the environment.
pub(crate) fn decide_single_cell(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
    emit_unsat: bool,
    algebraic_witness: bool,
) -> Option<CheckResult> {
    LAST_CELL_CHECK.with(|slot| slot.set(None));
    let atoms = collect_cert_atoms(arena, assertions)?;
    match decide_atoms(&atoms, deadline, algebraic_witness)? {
        AtomOutcome::Sat(sample) => {
            let model = replay_model(arena, assertions, &sample)?;
            Some(CheckResult::Sat(model))
        }
        AtomOutcome::Refuted(refutation) => {
            if !emit_unsat {
                // The `single-cell-sat` arm: the exact half of this route only.
                // Withheld BEFORE the checker runs, deliberately -- running a
                // checker whose result is thrown away is pure cost on a default
                // path, and the cause says "a covering was reached and this arm
                // does not emit `unsat`", not "a checked refutation was
                // discarded". The second would be a claim about the checker that
                // this branch has no evidence for.
                record_cad_decline(CadDecline::UnsatWithheldByArm);
                return None;
            }
            match check_cell_refutation(&refutation) {
                Ok(stats) => {
                    LAST_CELL_CHECK.with(|slot| slot.set(Some(stats)));
                    Some(CheckResult::Unsat)
                }
                Err(_failure) => {
                    // The producer built something its own checker refuses. The
                    // verdict is DROPPED -- not weakened, not reported.
                    record_cad_decline(CadDecline::CertificateRejected);
                    None
                }
            }
        }
    }
}

/// What the route concluded about a CONJUNCTION of certificate atoms, before any
/// arm policy, model replay or certificate check is applied.
///
/// Split out of [`decide_single_cell`] by ADR-2126 so the clause loop
/// ([`crate::nra_clause_loop`]) can call the same core once per Boolean model
/// without going back through the term arena. The two callers then apply
/// DIFFERENT policies to the same outcome -- `decide_single_cell` replays the
/// model against its own assertions and runs the certificate checker, while the
/// clause loop replays against the ORIGINAL Boolean query and uses a refutation
/// only to learn a clause -- so the split is where their obligations genuinely
/// diverge.
pub(crate) enum AtomOutcome {
    /// A complete sample satisfying every atom. **Not yet a model**: the caller
    /// must replay it against the original assertions. Every coordinate is
    /// rational except possibly the last (ADR-2134).
    Sat(Vec<(SymbolId, SampleCoord)>),
    /// A covering of the whole space in which every cell is closed. **Not yet an
    /// `unsat`**: the caller must decide whether its checker accepts it.
    Refuted(CellRefutation),
}

/// Decide a conjunction of certificate atoms. See [`AtomOutcome`] for what the
/// caller still owes.
///
/// Declines (`None`) on everything outside the declared slice, recording the
/// cause through [`crate::nra_real_root::record_cad_decline`].
pub(crate) fn decide_atoms(
    atoms: &[CertAtom],
    deadline: Option<Instant>,
    algebraic_witness: bool,
) -> Option<AtomOutcome> {
    if atoms.is_empty() {
        record_cad_decline(CadDecline::NonConjunctive);
        return None;
    }

    // --- The slice bounds, declared and refused up front. ---
    let mut vars: BTreeSet<SymbolId> = BTreeSet::new();
    for atom in atoms {
        for (mono, coeff) in atom.poly() {
            let mut total = 0u32;
            for &(v, e) in mono {
                vars.insert(v);
                let Some(next) = total.checked_add(e) else {
                    record_cad_decline(CadDecline::SliceBounds);
                    return None;
                };
                total = next;
            }
            if total > MAX_CELL_DEGREE {
                record_cad_decline(CadDecline::SliceBounds);
                return None;
            }
            if !coefficient_in_range(*coeff) {
                record_cad_decline(CadDecline::CoefficientRange);
                return None;
            }
        }
        if atom.poly().is_empty() {
            // A variable-free atom: constant-folding is the existing
            // decomposition's job, not this route's.
            record_cad_decline(CadDecline::NonConjunctive);
            return None;
        }
    }
    if vars.is_empty() || vars.len() > MAX_CELL_VARS {
        record_cad_decline(CadDecline::SliceBounds);
        return None;
    }

    // Deterministic variable order: ascending `SymbolId`, fixed for the whole
    // decision. Not a heuristic -- a public determinism promise.
    let order: Vec<SymbolId> = vars.into_iter().collect();
    let mut by_level: Vec<Vec<usize>> = vec![Vec::new(); order.len()];
    for (i, atom) in atoms.iter().enumerate() {
        let Some(level) = atom_level(atom, &order) else {
            // A variable-free atom, or one over a variable outside the order:
            // both are shapes the fold above should have caught, so reaching
            // here at all is a decline and not a silent `None`.
            record_cad_decline(CadDecline::NonConjunctive);
            return None;
        };
        by_level[level].push(i);
    }

    let mut ctx = Ctx {
        atoms,
        order: &order,
        by_level,
        deadline,
        cells_seen: 0,
        algebraic_witness,
    };

    match solve_level(&mut ctx, 0, &[])? {
        LevelOutcome::Sat(sample) => Some(AtomOutcome::Sat(sample)),
        LevelOutcome::Refuted { covering, .. } => Some(AtomOutcome::Refuted(CellRefutation::new(
            order.clone(),
            atoms.to_vec(),
            covering,
        ))),
    }
}

/// Whether a source coefficient is inside the `i128` clearing guard.
fn coefficient_in_range(c: Rational) -> bool {
    let (n, d) = (c.numerator(), c.denominator());
    n.checked_abs().is_some_and(|a| a < MAX_ABS_COEFF) && d.abs() < MAX_ABS_COEFF
}

/// The level of an atom: the index of its highest variable under `order`.
fn atom_level(atom: &CertAtom, order: &[SymbolId]) -> Option<usize> {
    let mut level: Option<usize> = None;
    for (mono, _) in atom.poly() {
        for &(v, e) in mono {
            if e == 0 {
                continue;
            }
            let idx = order.iter().position(|o| *o == v)?;
            level = Some(level.map_or(idx, |l: usize| l.max(idx)));
        }
    }
    level
}

// ---------------------------------------------------------------------------
// The level loop
// ---------------------------------------------------------------------------

#[allow(
    clippy::too_many_lines,
    reason = "one level of the CDCAC loop: the scan, the conflict, the projection \
              and the fixpoint test read the same boundary set, and splitting them \
              would put that set behind a borrow dance"
)]
fn solve_level(
    ctx: &mut Ctx<'_>,
    level: usize,
    sample: &[(SymbolId, Rational)],
) -> Option<LevelOutcome> {
    if ctx.out_of_time() {
        record_cad_decline(CadDecline::Deadline);
        return None;
    }
    let Some(&var) = ctx.order.get(level) else {
        record_cad_decline(CadDecline::SliceBounds);
        return None;
    };
    let sample_map: BTreeMap<SymbolId, Rational> = sample.iter().copied().collect();

    // The boundary set starts as this level's own atoms and grows only with the
    // projection of a conflict one level down.
    let mut boundary: Vec<CertPoly> = ctx.by_level[level]
        .iter()
        .map(|&i| ctx.atoms[i].poly().clone())
        .collect();
    boundary.sort();

    for _round in 0..MAX_REFINE_ROUNDS {
        if ctx.out_of_time() {
            record_cad_decline(CadDecline::Deadline);
            return None;
        }
        let roots = arrangement_roots(ctx, &boundary, &sample_map, var)?;
        let cells = arrangement_cells(&roots)?;
        let Some(seen) = ctx.cells_seen.checked_add(cells.len()) else {
            record_cad_decline(CadDecline::CellBudget);
            return None;
        };
        ctx.cells_seen = seen;
        if ctx.cells_seen > MAX_TOTAL_CELLS {
            record_cad_decline(CadDecline::CellBudget);
            return None;
        }

        let mut reasons: Vec<CellReason> = Vec::with_capacity(cells.len());
        let mut grew = false;

        for cell in &cells {
            // 1. Is one of THIS level's atoms violated here? The atom is in the
            //    boundary set, so it has no root inside the cell and the
            //    violation holds across the whole cell.
            match violated_atom(ctx, level, cell, &sample_map, var) {
                AtomCheck::Violated(i) => {
                    reasons.push(CellReason::Atom { atom_index: i });
                    continue;
                }
                AtomCheck::Declined => return None,
                AtomCheck::AllHold => {}
            }
            // 2. Every atom of this level holds here. To go deeper we need a
            //    RATIONAL point inside an OPEN cell: the certificate's `Deeper`
            //    witness must be strictly interior, and the sample handed down
            //    must be rational because this slice does not carry algebraic
            //    coordinates into a lower level.
            let CellRep::Rational(x) = cell.rep else {
                // Every atom of this level holds at an IRRATIONAL root.
                //
                // At the LAST level that is a complete model and the lever
                // (ADR-2134) takes it: no deeper level exists, so nothing has to
                // substitute this coordinate into a polynomial, and the sample
                // handed back is `rationals..., alpha`. The caller replays it
                // through the ground evaluator against the ORIGINAL assertions,
                // which evaluates at an algebraic point by exact algebraic field
                // arithmetic (ADR-0038) -- the same gate every other `sat` from
                // this route passes, not a weaker one.
                //
                // At any INTERMEDIATE level it is still a refusal: the next level
                // down substitutes the sample into its atoms and isolates the
                // result's roots in exact RATIONAL arithmetic, which an algebraic
                // coordinate does not fit. A model may well live there; this
                // slice refuses rather than round. Recorded apart from
                // `AlgebraicCoarsening` because the two say different things
                // about what would fix them.
                let CellRep::Algebraic(alpha) = &cell.rep else {
                    unreachable!("CellRep is Rational or Algebraic")
                };
                if ctx.algebraic_witness && level + 1 == ctx.order.len() {
                    let mut full: Vec<(SymbolId, SampleCoord)> = sample
                        .iter()
                        .map(|&(v, q)| (v, SampleCoord::Rational(q)))
                        .collect();
                    full.push((var, SampleCoord::Algebraic(alpha.clone())));
                    return Some(LevelOutcome::Sat(full));
                }
                record_cad_decline(CadDecline::AlgebraicWitness);
                return None;
            };
            if level + 1 == ctx.order.len() {
                let mut full: Vec<(SymbolId, SampleCoord)> = sample
                    .iter()
                    .map(|&(v, q)| (v, SampleCoord::Rational(q)))
                    .collect();
                full.push((var, SampleCoord::Rational(x)));
                return Some(LevelOutcome::Sat(full));
            }
            // A RATIONAL point cell is descended into exactly like an open one.
            // The certificate distinguishes the two: on a point cell the witness
            // must BE the root, and no delineability generalisation is needed
            // because the cell is that single point. Refusing here instead was
            // this route's first measured cause of death on the real corpus --
            // `indeterminate-sign` on every conjunctive `meti-tarski` file in
            // the in-bounds set.
            let mut deeper = sample.to_vec();
            deeper.push((var, x));
            match solve_level(ctx, level + 1, &deeper)? {
                LevelOutcome::Sat(m) => return Some(LevelOutcome::Sat(m)),
                LevelOutcome::Refuted { covering, polys } => {
                    // 3. Project what the conflict used past the next variable,
                    //    so this level's cells are cut where the deeper structure
                    //    changes.
                    let mut witness_sample = sample_map.clone();
                    witness_sample.insert(var, x);
                    let projected = project_level(&polys, ctx.order[level + 1], &witness_sample)?;
                    let before = boundary.len();
                    for p in projected {
                        if !p.is_empty() && !boundary.contains(&p) {
                            boundary.push(p);
                        }
                    }
                    if boundary.len() != before {
                        boundary.sort();
                        grew = true;
                        break; // restart the scan over the refined arrangement
                    }
                    reasons.push(CellReason::Deeper {
                        witness: x,
                        sub: Box::new(covering),
                    });
                }
            }
        }

        if grew {
            continue;
        }
        // Fixpoint: a complete scan that added nothing. Every reason above was
        // produced under THIS boundary set, which is what makes the cells the
        // reasons refer to the cells the certificate lists.
        let covering = CellCovering::new(var, sample.to_vec(), boundary.clone(), reasons);
        return Some(LevelOutcome::Refuted {
            covering,
            polys: boundary,
        });
    }
    record_cad_decline(CadDecline::CellBudget);
    None
}

/// The distinct real roots of the boundary set at `sample`, ascending.
fn arrangement_roots(
    ctx: &Ctx<'_>,
    boundary: &[CertPoly],
    sample: &BTreeMap<SymbolId, Rational>,
    var: SymbolId,
) -> Option<Vec<Root>> {
    let mut all: Vec<Root> = Vec::new();
    for p in boundary {
        let Some(uni) = substitute_to_int_univariate(p, sample, var) else {
            record_cad_decline(CadDecline::CoefficientRange);
            return None;
        };
        if uni.len() <= 1 {
            continue; // constant after substitution: no boundary
        }
        let Some(roots) = isolate_roots(&uni) else {
            record_cad_decline(CadDecline::RootIsolation);
            return None;
        };
        all.extend(roots);
    }
    let Some(sorted) = sort_roots(&all, ctx.deadline) else {
        record_cad_decline(CadDecline::RootOrdering);
        return None;
    };
    let Some(deduped) = dedup_sorted_roots(&sorted) else {
        record_cad_decline(CadDecline::RootOrdering);
        return None;
    };
    Some(deduped)
}

/// The `2m + 1` cells of the arrangement of `roots`, ascending, each with the
/// exact point the route tests it at.
fn arrangement_cells(roots: &[Root]) -> Option<Vec<ArrangementCell>> {
    let mut out = Vec::with_capacity(2 * roots.len() + 1);
    // `cell_samples` is nra_real_root's own open-cell sampler: one SIMPLE
    // (small-denominator) rational strictly inside each open cell, chosen from
    // the SAFE gap between consecutive roots' isolating intervals. Reused rather
    // than rebuilt -- a hand-rolled midpoint here was the wrong-`Unsat` bug that
    // routine's doc comment records.
    let Some(samples) = cell_samples(roots) else {
        record_cad_decline(CadDecline::AlgebraicCoarsening);
        return None;
    };
    if samples.len() != roots.len() + 1 {
        record_cad_decline(CadDecline::AlgebraicCoarsening);
        return None;
    }
    for (i, r) in roots.iter().enumerate() {
        out.push(ArrangementCell {
            rep: CellRep::Rational(samples[i]),
        });
        out.push(ArrangementCell {
            rep: match r {
                Root::Rational(q) => CellRep::Rational(*q),
                Root::Algebraic(a) => CellRep::Algebraic(a.clone()),
            },
        });
    }
    out.push(ArrangementCell {
        rep: CellRep::Rational(samples[roots.len()]),
    });
    Some(out)
}

/// Whether some atom of `level` is violated at the cell's representative point.
///
/// Three outcomes, named rather than nested in an `Option<Option<_>>`: an atom
/// is violated, no atom is, or the sign could not be determined exactly — and
/// the third is a DECLINE, which a nested `None` made easy to read as "no atom
/// is violated". Exact in both arms: a rational point evaluates directly, an
/// algebraic one through `RealAlgebraic::sign_at`.
enum AtomCheck {
    /// Atom at this index is violated across the cell.
    Violated(usize),
    /// Every atom of the level holds here.
    AllHold,
    /// A sign could not be determined; the cause is already recorded.
    Declined,
}

fn violated_atom(
    ctx: &Ctx<'_>,
    level: usize,
    cell: &ArrangementCell,
    sample: &BTreeMap<SymbolId, Rational>,
    var: SymbolId,
) -> AtomCheck {
    for &i in &ctx.by_level[level] {
        let atom = &ctx.atoms[i];
        let Some(uni) = substitute_to_int_univariate(atom.poly(), sample, var) else {
            record_cad_decline(CadDecline::CoefficientRange);
            return AtomCheck::Declined;
        };
        let sign = match &cell.rep {
            CellRep::Rational(q) => {
                let Some(v) = eval_int_poly(&uni, *q) else {
                    record_cad_decline(CadDecline::IndeterminateSign);
                    return AtomCheck::Declined;
                };
                axeyum_ir::poly::sign_of_rational(v)
            }
            CellRep::Algebraic(a) => {
                let Some(s) = a.sign_at(&uni) else {
                    record_cad_decline(CadDecline::IndeterminateSign);
                    return AtomCheck::Declined;
                };
                s
            }
        };
        if !cert_cmp_holds(atom.cmp(), sign) {
            return AtomCheck::Violated(i);
        }
    }
    AtomCheck::AllHold
}

fn cert_cmp_holds(cmp: CertCmp, s: Sign) -> bool {
    cmp.holds(s)
}

/// Substitute the rational `sample` into `p` and clear denominators to an
/// LSB-first `i128` polynomial in `var`.
fn substitute_to_int_univariate(
    p: &CertPoly,
    sample: &BTreeMap<SymbolId, Rational>,
    var: SymbolId,
) -> Option<Vec<i128>> {
    let mut coeffs: Vec<Rational> = Vec::new();
    for (mono, coeff) in p {
        let mut acc = *coeff;
        let mut deg = 0u32;
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
        if coeffs.len() <= idx {
            coeffs.resize(idx + 1, Rational::zero());
        }
        coeffs[idx] = coeffs[idx].checked_add(acc)?;
    }
    while coeffs.last().is_some_and(|c| c.is_zero()) {
        coeffs.pop();
    }
    if coeffs.is_empty() {
        return Some(vec![0]);
    }
    axeyum_ir::poly::rat_to_int_poly(&coeffs, MAX_ABS_COEFF)
}

// ---------------------------------------------------------------------------
// The projection -- where the soundness is
// ---------------------------------------------------------------------------

/// Project `polys` past `elim`, returning polynomials in the remaining
/// variables.
///
/// **The delineability condition is checked here, at `sample`, and a failure
/// DECLINES.** `sample` binds every variable up to and including the one this
/// level samples, so substituting it leaves a univariate polynomial in `elim`;
/// if that polynomial is identically zero, `p` is nullified at the sample,
/// `McCallum`'s delineability theorem does not apply, and the route refuses.
///
/// The operator itself is `McCallum`'s, widened at exactly the point the theorem
/// is fragile: **every** coefficient in `elim` is projected, not only the
/// leading one. With all coefficients sign-invariant on the cell, a polynomial
/// that is not nullified at one point of the cell is not nullified anywhere on
/// it — which is the hypothesis the theorem needs. It is also more than
/// `nra_real_root::project_strict` adds, and deliberately so: that routine is
/// used inside a complete enumeration where a missed delineability boundary is
/// caught by another cell, and this one is not.
fn project_level(
    polys: &[CertPoly],
    elim: SymbolId,
    sample: &BTreeMap<SymbolId, Rational>,
) -> Option<Vec<CertPoly>> {
    /// Map a resultant decline onto the attribution cause it belongs to.
    ///
    /// The split exists so the counts can be read: only
    /// [`CadDecline::ProjectionSylvesterDim`] is what a fraction-free
    /// determinant would remove, and ADR-2121's single `Projection` bucket was
    /// an upper bound on it rather than a measurement (ADR-2126).
    const fn projection_cause(why: ResultantDecline) -> CadDecline {
        match why {
            ResultantDecline::SylvesterDim => CadDecline::ProjectionSylvesterDim,
            // `Degenerate` is unreachable from here (both callers filter on
            // positive degree in `elim` first), and if it ever were reached it is
            // an arithmetic-shaped surprise, not a dimension cap.
            ResultantDecline::Degenerate | ResultantDecline::Arithmetic => {
                CadDecline::ProjectionArithmetic
            }
        }
    }

    let multi: Vec<MultiPoly> = polys
        .iter()
        .map(|p| {
            multipoly_from_cert(p).or_else(|| {
                record_cad_decline(CadDecline::CoefficientRange);
                None
            })
        })
        .collect::<Option<_>>()?;

    let mut out: Vec<CertPoly> = Vec::new();
    let push = |p: &MultiPoly, out: &mut Vec<CertPoly>| {
        if p.is_zero() {
            return;
        }
        let c = multipoly_to_cert(p);
        if !c.is_empty() && !out.contains(&c) {
            out.push(c);
        }
    };

    let elim_bearing: Vec<&MultiPoly> = multi.iter().filter(|p| degree_in(p, elim) > 0).collect();

    for p in &multi {
        if degree_in(p, elim) == 0 {
            // Already a polynomial of a lower level: it must stay a boundary.
            push(p, &mut out);
        }
    }

    for p in &elim_bearing {
        // --- The delineability check. Deleting it is the mutation. ---
        if is_nullified_at(p, elim, sample) {
            record_cad_decline(CadDecline::NullifiedResidual);
            return None;
        }
        // Every coefficient in `elim`, not only the leading one.
        let Some(coeffs) = coeffs_in_elim(p, elim) else {
            record_cad_decline(CadDecline::ProjectionArithmetic);
            return None;
        };
        for c in &coeffs {
            if !c.vars().is_empty() {
                push(c, &mut out);
            }
        }
        // The discriminant, `Res_elim(p, dp/d elim)`.
        if degree_in(p, elim) >= 2 {
            let Some(dp) = derivative_in(p, elim) else {
                record_cad_decline(CadDecline::ProjectionDerivative);
                return None;
            };
            if degree_in(&dp, elim) > 0 {
                match multi_resultant_classified(p, &dp, elim) {
                    Ok(ResultantOutcome::Poly(disc)) => push(&disc, &mut out),
                    Ok(ResultantOutcome::NonzeroConstant) => {}
                    // An identically-zero discriminant means a repeated root for
                    // every value of the remaining variables -- the projection
                    // cannot separate them.
                    Ok(ResultantOutcome::Zero) => {
                        record_cad_decline(CadDecline::ProjectionResultantZero);
                        return None;
                    }
                    Err(why) => {
                        record_cad_decline(projection_cause(why));
                        return None;
                    }
                }
            }
        }
    }

    // Pairwise resultants: where two of them collide.
    for i in 0..elim_bearing.len() {
        for j in (i + 1)..elim_bearing.len() {
            match multi_resultant_classified(elim_bearing[i], elim_bearing[j], elim) {
                Ok(ResultantOutcome::Poly(res)) => push(&res, &mut out),
                Ok(ResultantOutcome::NonzeroConstant) => {}
                Ok(ResultantOutcome::Zero) => {
                    record_cad_decline(CadDecline::ProjectionResultantZero);
                    return None;
                }
                Err(why) => {
                    record_cad_decline(projection_cause(why));
                    return None;
                }
            }
        }
    }

    Some(out)
}

/// Whether `p` is nullified at `sample`: every coefficient in `elim` vanishes,
/// so `p(sample, ·)` is the zero polynomial and its "roots" are the whole line.
///
/// This is the condition `McCallum`'s projection may not cross. A `true` here is a
/// refusal, never a workaround.
fn is_nullified_at(p: &MultiPoly, elim: SymbolId, sample: &BTreeMap<SymbolId, Rational>) -> bool {
    let cert = multipoly_to_cert(p);
    // Substituting the sample leaves a univariate polynomial in `elim`; nullified
    // means every one of its coefficients is zero.
    let mut coeffs: BTreeMap<u32, Rational> = BTreeMap::new();
    for (mono, coeff) in &cert {
        let mut acc = *coeff;
        let mut deg = 0u32;
        for &(v, e) in mono {
            if v == elim {
                deg = e;
                continue;
            }
            let Some(value) = sample.get(&v) else {
                // A variable outside the sample: we cannot evaluate, so we cannot
                // certify non-nullification either. Treat as nullified so the
                // caller refuses -- the conservative direction.
                return true;
            };
            for _ in 0..e {
                let Some(next) = acc.checked_mul(*value) else {
                    return true;
                };
                acc = next;
            }
        }
        let slot = coeffs.entry(deg).or_insert_with(Rational::zero);
        let Some(sum) = slot.checked_add(acc) else {
            return true;
        };
        *slot = sum;
    }
    coeffs.values().all(|c| c.is_zero())
}

// ---------------------------------------------------------------------------
// The sat side
// ---------------------------------------------------------------------------

/// Build the model and replay it against the ORIGINAL assertions through the
/// ground evaluator. Returns `None` (a decline) unless every assertion evaluates
/// to `true` — an overflow or an unresolved evaluation is a decline, never a
/// `Sat`.
///
/// # The replay is what makes the verdict, at a rational or an algebraic point
///
/// This is the route's only `sat` gate, and ADR-2134 does not weaken it to admit
/// an algebraic coordinate — it relies on the ground evaluator already being
/// exact there. [`axeyum_ir::eval`] evaluates `+`, `−`, `·` on real-sorted
/// operands by exact algebraic field arithmetic and compares them by exact
/// interval refinement (ADR-0038), and reports
/// `IrError::AlgebraicArithmeticUnsupported` / `ArithmeticOverflow` rather than
/// guessing. So an `Ok(Bool(true))` here is an exact statement about the
/// original assertion at the exact point — the *same* statement it is at a
/// rational point, reached by a different arithmetic.
///
/// **No rounding, ever.** An algebraic coordinate is never replaced by a nearby
/// rational for the replay. A rational approximation can satisfy every atom
/// while the exact point violates one — an atom `p(x) > 0` whose root lies
/// between the approximation and `α` is enough — which is why
/// `a_rational_approximation_can_satisfy_what_the_exact_point_violates` exists
/// and why this function has no approximation path to take.
///
/// The three outcomes are named apart because they call for different fixes:
///
/// * every assertion `true` ⇒ a model;
/// * an assertion decided `false` ⇒ [`CadDecline::AlgebraicReplayRefuted`], a
///   producer disagreement (the scan picked a cell where the collected atoms
///   hold, so the assertions they came from must hold too);
/// * an assertion not decided ⇒ [`CadDecline::AlgebraicReplayUndecided`].
///
/// On an all-rational sample the cause stays [`CadDecline::IndeterminateSign`],
/// unchanged from before ADR-2134, so the taxonomy on the shipped arm does not
/// move.
pub(crate) fn replay_model(
    arena: &TermArena,
    assertions: &[TermId],
    sample: &[(SymbolId, SampleCoord)],
) -> Option<Model> {
    let algebraic = sample.iter().any(|(_, c)| c.is_algebraic());
    let mut asg = Assignment::new();
    let mut model = Model::new();
    for (v, coord) in sample {
        asg.set(*v, coord.to_value());
        model.set(*v, coord.to_value());
    }
    for &a in assertions {
        match eval(arena, a, &asg) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => {
                record_cad_decline(if algebraic {
                    CadDecline::AlgebraicReplayRefuted
                } else {
                    CadDecline::IndeterminateSign
                });
                return None;
            }
            _ => {
                record_cad_decline(if algebraic {
                    CadDecline::AlgebraicReplayUndecided
                } else {
                    CadDecline::IndeterminateSign
                });
                return None;
            }
        }
    }
    Some(model)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::nra_real_root::{cad_decline, reset_cad_decline};

    /// Parse an SMT-LIB script and decide it through the single-cell route.
    fn decide(script: &str) -> (Option<CheckResult>, &'static str) {
        let parsed = axeyum_smtlib::parse_script(script).expect("parse");
        let (arena, assertions) = (parsed.arena, parsed.assertions);
        reset_cad_decline();
        let out = decide_single_cell(&arena, &assertions, None, true, false);
        (out, cad_decline().name())
    }

    /// The same, under the `single-cell-sat` arm: the route runs, its `unsat` is
    /// withheld.
    fn decide_sat_only(script: &str) -> (Option<CheckResult>, &'static str) {
        let parsed = axeyum_smtlib::parse_script(script).expect("parse");
        reset_cad_decline();
        let out = decide_single_cell(&parsed.arena, &parsed.assertions, None, false, false);
        (out, cad_decline().name())
    }

    fn is_unsat(r: Option<&CheckResult>) -> bool {
        matches!(r, Some(CheckResult::Unsat))
    }

    fn is_sat(r: Option<&CheckResult>) -> bool {
        matches!(r, Some(CheckResult::Sat(_)))
    }

    const DECL2: &str = "(declare-fun x () Real)\n(declare-fun y () Real)\n";

    #[test]
    fn a_one_variable_contradiction_is_refuted_and_the_certificate_is_checked() {
        let (r, cause) =
            decide("(declare-fun x () Real)\n(assert (> x 0))\n(assert (< x 0))\n(check-sat)\n");
        assert!(
            is_unsat(r.as_ref()),
            "expected unsat, got {r:?} (cause {cause})"
        );
    }

    #[test]
    fn a_circle_and_a_far_line_are_refuted() {
        // x^2 + y^2 < 1  and  x > 2: no real point.
        let (r, cause) = decide(&format!(
            "{DECL2}(assert (< (+ (* x x) (* y y)) 1))\n(assert (> x 2))\n(check-sat)\n"
        ));
        assert!(
            is_unsat(r.as_ref()),
            "expected unsat, got {r:?} (cause {cause})"
        );
    }

    #[test]
    fn a_satisfiable_two_variable_system_is_not_refuted() {
        // THE soundness-negative fixture on the sat side: the cell learning must
        // never refute a system that has a model. x^2 + y^2 < 4 and x > 0.
        let (r, cause) = decide(&format!(
            "{DECL2}(assert (< (+ (* x x) (* y y)) 4))\n(assert (> x 0))\n(check-sat)\n"
        ));
        assert!(
            !is_unsat(r.as_ref()),
            "a satisfiable system was REFUTED: {r:?} (cause {cause})"
        );
    }

    #[test]
    fn a_satisfiable_system_with_a_rational_model_is_solved_and_replayed() {
        let (r, cause) = decide(&format!(
            "{DECL2}(assert (> (* x x) 4))\n(assert (> y x))\n(check-sat)\n"
        ));
        assert!(
            is_sat(r.as_ref()) || r.is_none(),
            "must not refute: {r:?} ({cause})"
        );
    }

    #[test]
    fn a_system_needing_an_irrational_witness_declines_rather_than_guessing() {
        // x^2 = 2 has only irrational solutions. This slice carries rational
        // samples only, so it must DECLINE -- never `unsat`.
        let (r, cause) = decide("(declare-fun x () Real)\n(assert (= (* x x) 2))\n(check-sat)\n");
        assert!(
            !is_unsat(r.as_ref()),
            "x^2 = 2 is SATISFIABLE and must never be refuted: {r:?} ({cause})"
        );
    }

    #[test]
    fn more_than_four_variables_refuses_by_declaration() {
        let mut decls = String::new();
        let mut body = String::new();
        for i in 0..5 {
            use core::fmt::Write as _;
            let _ = writeln!(decls, "(declare-fun v{i} () Real)");
            let _ = writeln!(body, "(assert (> v{i} 0))");
        }
        let (r, cause) = decide(&format!("{decls}{body}(check-sat)\n"));
        assert!(r.is_none(), "expected a decline, got {r:?}");
        assert_eq!(cause, "slice-bounds");
    }

    #[test]
    fn a_disjunction_is_refused_as_non_conjunctive() {
        let (r, cause) = decide(&format!(
            "{DECL2}(assert (or (> x 0) (> y 0)))\n(check-sat)\n"
        ));
        assert!(r.is_none(), "expected a decline, got {r:?}");
        assert_eq!(cause, "non-conjunctive");
    }

    #[test]
    fn a_degree_nine_atom_refuses_by_declaration() {
        let pow = "(* x x x x x x x x x)";
        let (r, cause) = decide(&format!(
            "(declare-fun x () Real)\n(assert (> {pow} 1))\n(check-sat)\n"
        ));
        assert!(r.is_none(), "expected a decline, got {r:?}");
        assert_eq!(cause, "slice-bounds");
    }

    #[test]
    fn a_nullified_polynomial_declines_instead_of_projecting() {
        // `x*y^2 - x` is nullified wherever x = 0: substituting x := 0 leaves the
        // ZERO polynomial in y, so McCallum's projection does not apply there.
        // The route must decline on the sample it actually reaches, never
        // project through it. Paired with the mutation that deletes the guard.
        let (r, cause) = decide(&format!(
            "{DECL2}(assert (< (- (* x (* y y)) x) 0))\n\
             (assert (> (* x x) 0))\n\
             (assert (< x 0))\n\
             (assert (> x 0))\n(check-sat)\n"
        ));
        // `x < 0 ∧ x > 0` is refutable at level 0 without ever projecting, so the
        // outcome here is a verdict OR a decline -- what must never happen is a
        // wrong `sat`.
        assert!(
            !is_sat(r.as_ref()),
            "an unsatisfiable system was reported SAT: {r:?} ({cause})"
        );
    }

    /// The named fixture for the delineability mutation.
    ///
    /// `x*y^2 - x` is the ZERO polynomial in `y` at `x = 0`: every coefficient
    /// in `y` vanishes there, so it has no roots to delineate and `McCallum`'s
    /// projection theorem does not apply over any cell containing that point.
    /// Both atoms are level 1, so level 0 has no boundary at all and its single
    /// cell's sample IS `x = 0` -- the route reaches the nullified point by
    /// construction, not by luck.
    ///
    /// The assertion is on the CAUSE, not on the verdict, and deliberately: the
    /// system is unsatisfiable either way, so a verdict assertion would pass
    /// with the guard deleted. `scripts/tests/mutation_controls.py` suite
    /// `nra-single-cell` turns `if is_nullified_at(..)` into `if false` and
    /// requires exactly this test to die.
    #[test]
    fn a_nullified_projection_polynomial_declines_with_its_own_cause() {
        let (r, cause) = decide(&format!(
            "{DECL2}(assert (< (- (* x (* y y)) x) 0))\n\
             (assert (> (- (* x (* y y)) x) 0))\n(check-sat)\n"
        ));
        assert_eq!(
            cause, "nullified-residual",
            "the delineability guard must be what stopped this, got {r:?}"
        );
        assert!(r.is_none(), "a declined route returns no verdict: {r:?}");
    }

    #[test]
    fn the_route_is_deterministic_across_repeated_runs() {
        let script =
            format!("{DECL2}(assert (< (+ (* x x) (* y y)) 1))\n(assert (> x 2))\n(check-sat)\n");
        let first = format!("{:?}", decide(&script).0.is_some());
        for _ in 0..4 {
            assert_eq!(format!("{:?}", decide(&script).0.is_some()), first);
        }
    }

    #[test]
    fn the_declared_bounds_are_what_the_code_enforces() {
        // Derived from the constants, not from a literal a maintainer keeps in
        // step by hand: a query with exactly MAX_CELL_VARS variables must NOT be
        // refused for bounds, and one with a variable more must be.
        let mut decls = String::new();
        let mut body = String::new();
        for i in 0..MAX_CELL_VARS {
            use core::fmt::Write as _;
            let _ = writeln!(decls, "(declare-fun v{i} () Real)");
            let _ = writeln!(body, "(assert (> v{i} 0))");
        }
        let (_, cause) = decide(&format!("{decls}{body}(check-sat)\n"));
        assert_ne!(cause, "slice-bounds", "MAX_CELL_VARS must be accepted");

        let mut decls = String::new();
        let mut body = String::new();
        for i in 0..=MAX_CELL_VARS {
            use core::fmt::Write as _;
            let _ = writeln!(decls, "(declare-fun v{i} () Real)");
            let _ = writeln!(body, "(assert (> v{i} 0))");
        }
        let (_, cause) = decide(&format!("{decls}{body}(check-sat)\n"));
        assert_eq!(cause, "slice-bounds", "one more must be refused");
    }

    #[test]
    fn a_coefficient_past_the_i128_clearing_refuses_by_declaration() {
        // 2^41 > MAX_ABS_COEFF = 1 << 40.
        let big = 1i128 << 41;
        let (r, cause) = decide(&format!(
            "(declare-fun x () Real)\n(assert (> (* {big} x) 1))\n(check-sat)\n"
        ));
        assert!(r.is_none(), "expected a decline, got {r:?}");
        assert_eq!(cause, "coefficient-range");
    }

    #[test]
    fn an_unsat_that_the_checker_would_reject_is_never_emitted() {
        // The route's own gate: every `Unsat` it returns has passed
        // `check_cell_refutation`. The assertion reads what the CHECKER
        // recorded, not something this test re-derives for itself -- a test that
        // re-derives its subject inline passes while the shipped artifact is
        // wrong.
        let script =
            format!("{DECL2}(assert (< (+ (* x x) (* y y)) 1))\n(assert (> x 2))\n(check-sat)\n");
        let parsed = axeyum_smtlib::parse_script(&script).expect("parse");
        reset_cad_decline();
        let out = decide_single_cell(&parsed.arena, &parsed.assertions, None, true, false);
        assert!(is_unsat(out.as_ref()), "expected unsat, got {out:?}");
        let stats = last_cell_check().expect("an accepted `unsat` records its check");
        assert!(
            stats.coverings >= 2 && stats.cells >= 3 && stats.deeper_cells >= 1,
            "the checker must have walked a real covering tree, not an empty one: {stats:?}"
        );
        assert_eq!(
            stats.deeper_cells,
            stats.open_deeper_cells + stats.point_deeper_cells,
            "every `Deeper` cell is either over an open cell or over a point: {stats:?}"
        );
        assert!(
            stats.open_deeper_cells == 0 || stats.delineability_exact_tests > 0,
            "a generalisation over an open cell must have been proved EXACTLY, \
             not merely probed: {stats:?}"
        );
        assert!(
            stats.delineability_probes > 0 || stats.point_deeper_cells > 0,
            "every `Deeper` cell must have been either probed or a point cell: {stats:?}"
        );
    }

    #[test]
    fn a_declined_decision_records_no_certificate_check() {
        // The negative half: `last_cell_check` must be cleared at the top of
        // every decision, or an accepted refutation from an EARLIER query would
        // be read as this one's evidence -- which is how the test above would
        // pass on a route that stopped checking.
        let (r, _) = decide(&format!(
            "{DECL2}(assert (or (> x 0) (> y 0)))\n(check-sat)\n"
        ));
        assert!(r.is_none());
        assert!(
            last_cell_check().is_none(),
            "a declined decision must not leave another query's check behind it"
        );
    }

    #[test]
    fn an_empty_query_declines() {
        let arena = TermArena::new();
        reset_cad_decline();
        assert!(decide_single_cell(&arena, &[], None, true, false).is_none());
    }

    /// And it keeps the half that IS exact.
    ///
    /// A `sat` from this route is a rational model replayed through the ground
    /// evaluator against the original assertions, so withholding it would give
    /// up capability for nothing.
    #[test]
    fn the_sat_only_arm_keeps_the_sat_it_can_replay() {
        let script = format!("{DECL2}(assert (> (* x x) 4))\n(assert (> y x))\n(check-sat)\n");
        let (full, _) = decide(&script);
        let (held, cause) = decide_sat_only(&script);
        assert_eq!(
            format!("{:?}", full.is_some()),
            format!("{:?}", held.is_some()),
            "the two arms must agree on a SAT query: {full:?} vs {held:?} ({cause})"
        );
        assert!(
            !matches!(held, Some(CheckResult::Unsat)),
            "the sat-only arm must never emit `unsat`: {held:?}"
        );
    }

    /// The withholding arm must never CHANGE a verdict, only remove one.
    ///
    /// Derived over every fixture in this module rather than asserted on one:
    /// for each, the sat-only arm's outcome must be the full arm's outcome with
    /// `Unsat` replaced by a decline, and nothing else.
    ///
    /// This is the SOLE killer of the `if !emit_unsat` mutation in
    /// `scripts/tests/mutation_controls.py`. A second test asserting the same
    /// property on one fixture lived here briefly and was removed rather than
    /// kept: it died on the same mutation, and two tests dying on one guard
    /// deletion means one of them was measuring nothing the other did not. The
    /// contrast it existed for — the same fixture answering `unsat` under the
    /// full arm — is inside the loop below, which runs both arms on every
    /// fixture and branches on what the full arm said.
    #[test]
    fn withholding_removes_unsat_and_changes_nothing_else() {
        let scripts = [
            format!("{DECL2}(assert (< (+ (* x x) (* y y)) 1))\n(assert (> x 2))\n(check-sat)\n"),
            format!("{DECL2}(assert (< (+ (* x x) (* y y)) 4))\n(assert (> x 0))\n(check-sat)\n"),
            format!("{DECL2}(assert (> (* x x) 4))\n(assert (> y x))\n(check-sat)\n"),
            format!("{DECL2}(assert (or (> x 0) (> y 0)))\n(check-sat)\n"),
            "(declare-fun x () Real)\n(assert (> x 0))\n(assert (< x 0))\n(check-sat)\n".to_owned(),
            "(declare-fun x () Real)\n(assert (= (* x x) 2))\n(check-sat)\n".to_owned(),
        ];
        let mut withheld = 0usize;
        for script in &scripts {
            let (full, _) = decide(script);
            let (held, cause) = decide_sat_only(script);
            match &full {
                Some(CheckResult::Unsat) => {
                    assert!(held.is_none(), "an `unsat` must become a decline: {held:?}");
                    assert_eq!(cause, "unsat-withheld-by-arm");
                    withheld += 1;
                }
                Some(CheckResult::Sat(_)) => {
                    assert!(
                        is_sat(held.as_ref()),
                        "a `sat` must survive withholding: {held:?} ({cause})"
                    );
                }
                _ => assert!(
                    held.is_none(),
                    "a decline must stay a decline: {held:?} ({cause})"
                ),
            }
        }
        assert!(
            withheld > 0,
            "no fixture exercised the withholding path: the test is vacuous"
        );
    }

    #[test]
    fn a_boolean_query_is_refused_rather_than_mishandled() {
        let (r, cause) = decide("(declare-fun b () Bool)\n(assert (not b))\n(check-sat)\n");
        assert!(r.is_none(), "expected a decline, got {r:?}");
        assert_eq!(cause, "non-conjunctive");
    }
}
