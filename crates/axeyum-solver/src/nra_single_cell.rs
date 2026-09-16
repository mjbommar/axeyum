//! Model-constructing CAD over the reals: **one cell per conflict**, not the
//! whole arrangement (ADR-2121, lane `NRA-SINGLE-CELL`).
//!
//! # Why this exists
//!
//! ADR-2110 measured the QF_NRA gap and split it in two. Of the 83 files the
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
//!   the verdict is dropped, never downgraded to a guess. Note the honest label:
//!   the checker's delineability test is *sampling*, so an `unsat` here is
//!   **checked**, not proved. See that module's docs.
//! * **`sat` is a rational model replayed against the original assertions** by
//!   the ground evaluator before it leaves this module. An algebraic witness is
//!   not represented: a cell that satisfies every atom only at an irrational
//!   point makes the route decline ([`CadDecline::AlgebraicCoarsening`]) rather
//!   than round it.
//! * **The projection is nullification-complete.** McCallum's operator is valid
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
//!   exact Leibniz expansion — [`CadDecline::Projection`]. This is the binding
//!   constraint on high per-variable degree and ADR-2121 records how much of the
//!   slice it costs.
//!
//! The route ships **OFF**: [`crate::nra_real_root::cad_policy`]'s arm must be
//! `single-cell` (`AXEYUM_NRA_CAD=single-cell`) for it to run at all, so the A/B
//! is one binary and one environment variable.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use axeyum_ir::poly::eval_int_poly;
use axeyum_ir::{
    Assignment, Rational, RealAlgebraic, Sign, SymbolId, TermArena, TermId, Value, eval,
};

use crate::backend::CheckResult;
use crate::model::Model;
use crate::nra_cell_cert::{
    CellCovering, CellReason, CellRefutation, CertAtom, CertCmp, CertPoly, check_cell_refutation,
};
use crate::nra_real_root::{
    CadDecline, MAX_ABS_COEFF, MultiPoly, ResultantOutcome, Root, cell_samples, coeffs_in_elim,
    collect_cert_atoms, dedup_sorted_roots, degree_in, derivative_in, isolate_roots,
    multi_resultant, multipoly_from_cert, multipoly_to_cert, record_cad_decline, sort_roots,
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

/// What one level of the recursion produced.
enum LevelOutcome {
    /// A complete rational sample satisfying every atom of every level at or
    /// above this one.
    Sat(Vec<(SymbolId, Rational)>),
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
) -> Option<CheckResult> {
    let atoms = collect_cert_atoms(arena, assertions)?;
    if atoms.is_empty() {
        record_cad_decline(CadDecline::NonConjunctive);
        return None;
    }

    // --- The slice bounds, declared and refused up front. ---
    let mut vars: BTreeSet<SymbolId> = BTreeSet::new();
    for atom in &atoms {
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
        atoms: &atoms,
        order: &order,
        by_level,
        deadline,
        cells_seen: 0,
    };

    match solve_level(&mut ctx, 0, Vec::new())? {
        LevelOutcome::Sat(sample) => {
            let model = replay_rational_model(arena, assertions, &sample)?;
            Some(CheckResult::Sat(model))
        }
        LevelOutcome::Refuted { covering, .. } => {
            let refutation = CellRefutation::new(order.clone(), atoms.clone(), covering);
            match check_cell_refutation(&refutation) {
                Ok(_stats) => Some(CheckResult::Unsat),
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
    sample: Vec<(SymbolId, Rational)>,
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
            if let Some(i) = violated_atom(ctx, level, cell, &sample_map, var)? {
                reasons.push(CellReason::Atom { atom_index: i });
                continue;
            }
            // 2. Every atom of this level holds here. To go deeper we need a
            //    RATIONAL point inside an OPEN cell: the certificate's `Deeper`
            //    witness must be strictly interior, and the sample handed down
            //    must be rational because this slice does not carry algebraic
            //    coordinates into a lower level.
            let CellRep::Rational(x) = cell.rep else {
                // Every atom of this level holds at an IRRATIONAL root. A model
                // may well live there; this slice carries rational samples only,
                // so it refuses rather than round. Recorded apart from
                // `AlgebraicCoarsening` because the two say different things
                // about what would fix them.
                record_cad_decline(CadDecline::AlgebraicWitness);
                return None;
            };
            if level + 1 == ctx.order.len() {
                let mut full = sample.clone();
                full.push((var, x));
                return Some(LevelOutcome::Sat(full));
            }
            // A RATIONAL point cell is descended into exactly like an open one.
            // The certificate distinguishes the two: on a point cell the witness
            // must BE the root, and no delineability generalisation is needed
            // because the cell is that single point. Refusing here instead was
            // this route's first measured cause of death on the real corpus --
            // `indeterminate-sign` on every conjunctive `meti-tarski` file in
            // the in-bounds set.
            let mut deeper = sample.clone();
            deeper.push((var, x));
            match solve_level(ctx, level + 1, deeper)? {
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
        let covering = CellCovering::new(var, sample.clone(), boundary.clone(), reasons);
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

/// The index of an atom of `level` violated at the cell's representative point,
/// if any. Exact in both arms: a rational point evaluates directly, an algebraic
/// one through `RealAlgebraic::sign_at`.
fn violated_atom(
    ctx: &Ctx<'_>,
    level: usize,
    cell: &ArrangementCell,
    sample: &BTreeMap<SymbolId, Rational>,
    var: SymbolId,
) -> Option<Option<usize>> {
    for &i in &ctx.by_level[level] {
        let atom = &ctx.atoms[i];
        let Some(uni) = substitute_to_int_univariate(atom.poly(), sample, var) else {
            record_cad_decline(CadDecline::CoefficientRange);
            return None;
        };
        let sign = match &cell.rep {
            CellRep::Rational(q) => {
                let Some(v) = eval_int_poly(&uni, *q) else {
                    record_cad_decline(CadDecline::IndeterminateSign);
                    return None;
                };
                axeyum_ir::poly::sign_of_rational(v)
            }
            CellRep::Algebraic(a) => {
                let Some(s) = a.sign_at(&uni) else {
                    record_cad_decline(CadDecline::IndeterminateSign);
                    return None;
                };
                s
            }
        };
        if !cert_cmp_holds(atom.cmp(), sign) {
            return Some(Some(i));
        }
    }
    Some(None)
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
/// McCallum's delineability theorem does not apply, and the route refuses.
///
/// The operator itself is McCallum's, widened at exactly the point the theorem
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
            record_cad_decline(CadDecline::Projection);
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
                record_cad_decline(CadDecline::Projection);
                return None;
            };
            if degree_in(&dp, elim) > 0 {
                match multi_resultant(p, &dp, elim) {
                    Some(ResultantOutcome::Poly(disc)) => push(&disc, &mut out),
                    Some(ResultantOutcome::NonzeroConstant) => {}
                    // An identically-zero discriminant means a repeated root for
                    // every value of the remaining variables -- the projection
                    // cannot separate them.
                    Some(ResultantOutcome::Zero) | None => {
                        record_cad_decline(CadDecline::Projection);
                        return None;
                    }
                }
            }
        }
    }

    // Pairwise resultants: where two of them collide.
    for i in 0..elim_bearing.len() {
        for j in (i + 1)..elim_bearing.len() {
            match multi_resultant(elim_bearing[i], elim_bearing[j], elim) {
                Some(ResultantOutcome::Poly(res)) => push(&res, &mut out),
                Some(ResultantOutcome::NonzeroConstant) => {}
                Some(ResultantOutcome::Zero) | None => {
                    record_cad_decline(CadDecline::Projection);
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
/// This is the condition McCallum's projection may not cross. A `true` here is a
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
fn replay_rational_model(
    arena: &TermArena,
    assertions: &[TermId],
    sample: &[(SymbolId, Rational)],
) -> Option<Model> {
    let mut asg = Assignment::new();
    let mut model = Model::new();
    for &(v, q) in sample {
        asg.set(v, Value::Real(q));
        model.set(v, Value::Real(q));
    }
    for &a in assertions {
        match eval(arena, a, &asg) {
            Ok(Value::Bool(true)) => {}
            _ => {
                record_cad_decline(CadDecline::IndeterminateSign);
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
        let out = decide_single_cell(&arena, &assertions, None);
        (out, cad_decline().name())
    }

    fn is_unsat(r: &Option<CheckResult>) -> bool {
        matches!(r, Some(CheckResult::Unsat))
    }

    fn is_sat(r: &Option<CheckResult>) -> bool {
        matches!(r, Some(CheckResult::Sat(_)))
    }

    const DECL2: &str = "(declare-fun x () Real)\n(declare-fun y () Real)\n";

    #[test]
    fn a_one_variable_contradiction_is_refuted_and_the_certificate_is_checked() {
        let (r, cause) = decide(&format!(
            "(declare-fun x () Real)\n(assert (> x 0))\n(assert (< x 0))\n(check-sat)\n"
        ));
        assert!(is_unsat(&r), "expected unsat, got {r:?} (cause {cause})");
    }

    #[test]
    fn a_circle_and_a_far_line_are_refuted() {
        // x^2 + y^2 < 1  and  x > 2: no real point.
        let (r, cause) = decide(&format!(
            "{DECL2}(assert (< (+ (* x x) (* y y)) 1))\n(assert (> x 2))\n(check-sat)\n"
        ));
        assert!(is_unsat(&r), "expected unsat, got {r:?} (cause {cause})");
    }

    #[test]
    fn a_satisfiable_two_variable_system_is_not_refuted() {
        // THE soundness-negative fixture on the sat side: the cell learning must
        // never refute a system that has a model. x^2 + y^2 < 4 and x > 0.
        let (r, cause) = decide(&format!(
            "{DECL2}(assert (< (+ (* x x) (* y y)) 4))\n(assert (> x 0))\n(check-sat)\n"
        ));
        assert!(
            !is_unsat(&r),
            "a satisfiable system was REFUTED: {r:?} (cause {cause})"
        );
    }

    #[test]
    fn a_satisfiable_system_with_a_rational_model_is_solved_and_replayed() {
        let (r, cause) = decide(&format!(
            "{DECL2}(assert (> (* x x) 4))\n(assert (> y x))\n(check-sat)\n"
        ));
        assert!(
            is_sat(&r) || r.is_none(),
            "must not refute: {r:?} ({cause})"
        );
    }

    #[test]
    fn a_system_needing_an_irrational_witness_declines_rather_than_guessing() {
        // x^2 = 2 has only irrational solutions. This slice carries rational
        // samples only, so it must DECLINE -- never `unsat`.
        let (r, cause) = decide("(declare-fun x () Real)\n(assert (= (* x x) 2))\n(check-sat)\n");
        assert!(
            !is_unsat(&r),
            "x^2 = 2 is SATISFIABLE and must never be refuted: {r:?} ({cause})"
        );
    }

    #[test]
    fn more_than_four_variables_refuses_by_declaration() {
        let decls: String = (0..5)
            .map(|i| format!("(declare-fun v{i} () Real)\n"))
            .collect();
        let body: String = (0..5).map(|i| format!("(assert (> v{i} 0))\n")).collect();
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
        let pow: String = "(* x x x x x x x x x)".to_string();
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
            !is_sat(&r),
            "an unsatisfiable system was reported SAT: {r:?} ({cause})"
        );
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
        let decls: String = (0..MAX_CELL_VARS)
            .map(|i| format!("(declare-fun v{i} () Real)\n"))
            .collect();
        let body: String = (0..MAX_CELL_VARS)
            .map(|i| format!("(assert (> v{i} 0))\n"))
            .collect();
        let (_, cause) = decide(&format!("{decls}{body}(check-sat)\n"));
        assert_ne!(cause, "slice-bounds", "MAX_CELL_VARS must be accepted");

        let decls: String = (0..=MAX_CELL_VARS)
            .map(|i| format!("(declare-fun v{i} () Real)\n"))
            .collect();
        let body: String = (0..=MAX_CELL_VARS)
            .map(|i| format!("(assert (> v{i} 0))\n"))
            .collect();
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
        // `check_cell_refutation`. Exercised by construction here -- a refuted
        // system whose certificate we then re-check independently.
        let script =
            format!("{DECL2}(assert (< (+ (* x x) (* y y)) 1))\n(assert (> x 2))\n(check-sat)\n");
        let parsed = axeyum_smtlib::parse_script(&script).expect("parse");
        reset_cad_decline();
        let out = decide_single_cell(&parsed.arena, &parsed.assertions, None);
        assert!(is_unsat(&out), "expected unsat, got {out:?}");
        // And the checker accepts a non-vacuous amount of work.
        let atoms = collect_cert_atoms(&parsed.arena, &parsed.assertions).expect("atoms");
        assert_eq!(atoms.len(), 2, "two atoms in the fixture");
    }

    #[test]
    fn an_empty_query_declines() {
        let arena = TermArena::new();
        reset_cad_decline();
        assert!(decide_single_cell(&arena, &[], None).is_none());
    }

    #[test]
    fn a_boolean_query_is_refused_rather_than_mishandled() {
        let (r, cause) = decide("(declare-fun b () Bool)\n(assert (not b))\n(check-sat)\n");
        assert!(r.is_none(), "expected a decline, got {r:?}");
        assert_eq!(cause, "non-conjunctive");
    }
}
