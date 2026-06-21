//! Sound, bounded NRA capability: decide a **conjunction** of single-variable
//! nonlinear-real **polynomial constraints** over one shared `Real` variable `x`
//! *exactly*, with **irrational witnesses** (ADR-0038, slice 1).
//!
//! This pass sits *in front of* the linear-abstraction NRA path
//! ([`crate::nra`]). Where that path abstracts a product `x·x` to a fresh
//! variable — losing the algebraic fact and reporting `Unknown` for `x·x = 2` —
//! this decider isolates the *real roots* of the collected polynomial(s) exactly
//! and returns a witness, which may be an exact rational ([`Value::Real`]) or a
//! real **algebraic number** ([`Value::RealAlgebraic`], e.g. `√2`).
//!
//! # Scope (deliberately narrow — correctness over reach)
//!
//! Fires *only* when the **whole** query is a conjunction `C₁ ∧ … ∧ Cₘ` (a list
//! of assertions and/or top-level `and` terms, flattened) where **every** `Cᵢ`
//! normalizes to a comparison `pᵢ(x) ⋈ᵢ 0` between a single-variable *real*
//! polynomial `pᵢ` and `0`, where each `pᵢ` collects over `{+, −, ·, neg,
//! RealConst, symbol}` with the **same** `x` the only variable across all
//! constraints. Rational coefficients are cleared to integers (multiplying
//! through by the common denominator preserves every `⋈`-relation since the
//! multiplier is positive). Everything else declines (`None`), leaving the query
//! to [`crate::nra`]:
//!
//! - more than one *distinct* variable (across all constraints), a non-`Real`
//!   sort, a non-polynomial operator (`div`, `RealToInt`, …),
//! - any non-conjunctive top-level structure (an `or`, an `=>`, …),
//! - a coefficient/degree past the [`MAX_ABS_COEFF`]/[`MAX_DEGREE`] guards, or
//!   any `i128`/`Rational` overflow during collection, denominator clearing,
//!   root isolation, or algebraic-vs-algebraic ordering.
//!
//! # The conjunction (sign-cell decomposition)
//!
//! The real roots of all `pᵢ` partition ℝ into finitely many cells on which
//! every `sign(pᵢ)` is constant. A conjunction holds on a whole cell or nowhere
//! on it, so it suffices to test a finite **candidate set**: every isolated root
//! of every `pᵢ` (the cell boundaries — where some `pᵢ = 0`) *and* one rational
//! sample strictly inside each open cell (below the least root, between adjacent
//! roots, above the greatest). A candidate α satisfies the conjunction iff for
//! **every** `i`, `sign(pᵢ(α)) ⋈ᵢ 0`. The first satisfying candidate (in
//! deterministic sorted order, preferring a rational sample so the witness stays
//! rational) → **Sat**, replay-checked against every original assertion. No
//! candidate → **Unsat** (exhaustive: roots + one-sample-per-cell cover every
//! sign pattern of the single variable). Any inability to *order* the candidates
//! exactly (an algebraic-vs-algebraic comparison that does not resolve within the
//! refinement bound, or an overflow) → **decline**, never a guessed `Unsat`.
//!
//! # Decisions
//!
//! - **`=`:** isolate the real roots of `p`. Each root is either an exact
//!   rational (→ [`Value::Real`]) or irrational (→ a [`Value::RealAlgebraic`]
//!   defined by `p` and its isolating interval). No real root ⇒ **Unsat**
//!   (exact). The witness is **replay-checked**: an algebraic witness `α` must
//!   satisfy `sign_at(p, α) = 0`; a rational witness is replayed through the
//!   ground evaluator on the original assertion.
//! - **`<, ≤, >, ≥`:** the real roots of `p` partition ℝ into sign-constant open
//!   intervals; pick a **rational** sample inside a matching-sign interval (the
//!   witness stays rational). Unsat iff no interval matches (`x·x < 0` ⇒ Unsat).
//! - **`≠`:** Sat unless `p ≡ 0`; exhibit a rational non-root.
//!
//! A wrong `sat`/`unsat` is catastrophic; declining is always sound. **No
//! floating point**: every sign test is exact over `i128`/[`Rational`].

use core::cmp::Ordering;

use axeyum_ir::{
    Assignment, Op, Rational, RealAlgebraic, Sign, Sort, SymbolId, TermArena, TermId, TermNode,
    Value, eval,
};

use crate::backend::{CheckResult, SolverError};
use crate::model::Model;

/// Coefficient magnitude guard (mirrors `nia_square::MAX_ABS_COEFF`): above this
/// the pass declines to keep the exact-rational arithmetic and root isolation
/// inside `i128`.
const MAX_ABS_COEFF: i128 = 1i128 << 40;

/// Maximum polynomial degree the pass collects / decides; beyond it we decline.
const MAX_DEGREE: usize = 64;

/// The six real comparison shapes, oriented as `p(x) ⋈ 0`.
#[derive(Clone, Copy)]
enum Cmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Merge of the (sole, possibly absent) variable of two operands; a conflict (two
/// distinct variables) forces the collector to decline.
enum MergeVar {
    Ok(Option<SymbolId>),
    Conflict,
}

/// A single-variable polynomial with **rational** coefficients (LSB-first),
/// accumulated during collection so that `RealConst` denominators are tracked
/// exactly. Converted to an integer polynomial (denominators cleared) before
/// root isolation.
#[derive(Clone)]
struct RatPoly {
    var: Option<SymbolId>,
    coeffs: Vec<Rational>,
}

impl RatPoly {
    fn constant(r: Rational) -> Self {
        RatPoly {
            var: None,
            coeffs: vec![r],
        }
    }

    fn var_of(s: SymbolId) -> Self {
        RatPoly {
            var: Some(s),
            coeffs: vec![Rational::zero(), Rational::integer(1)],
        }
    }

    fn coeff(&self, i: usize) -> Rational {
        self.coeffs.get(i).copied().unwrap_or_else(Rational::zero)
    }

    /// Highest index with a nonzero coefficient (0 for a constant / zero poly).
    fn degree(&self) -> usize {
        let mut n = self.coeffs.len();
        while n > 1 && self.coeff(n - 1).is_zero() {
            n -= 1;
        }
        n.saturating_sub(1)
    }

    fn merge_var(a: Option<SymbolId>, b: Option<SymbolId>) -> MergeVar {
        match (a, b) {
            (None, v) | (v, None) => MergeVar::Ok(v),
            (Some(x), Some(y)) if x == y => MergeVar::Ok(Some(x)),
            _ => MergeVar::Conflict,
        }
    }

    fn neg(self) -> Option<Self> {
        let mut coeffs = Vec::with_capacity(self.coeffs.len());
        for c in &self.coeffs {
            coeffs.push(c.checked_neg()?);
        }
        Some(RatPoly {
            var: self.var,
            coeffs,
        })
    }

    fn add(self, other: &Self) -> Option<Self> {
        let MergeVar::Ok(var) = RatPoly::merge_var(self.var, other.var) else {
            return None;
        };
        let len = self.coeffs.len().max(other.coeffs.len());
        let mut coeffs = Vec::with_capacity(len);
        for i in 0..len {
            coeffs.push(self.coeff(i).checked_add(other.coeff(i))?);
        }
        Some(RatPoly { var, coeffs })
    }

    fn sub(self, other: Self) -> Option<Self> {
        self.add(&other.neg()?)
    }

    fn mul(self, other: &Self) -> Option<Self> {
        let MergeVar::Ok(var) = RatPoly::merge_var(self.var, other.var) else {
            return None;
        };
        let prod_len = self.coeffs.len() + other.coeffs.len() - 1;
        if prod_len > MAX_DEGREE + 1 {
            return None;
        }
        let mut coeffs = vec![Rational::zero(); prod_len];
        for (i, &a) in self.coeffs.iter().enumerate() {
            if a.is_zero() {
                continue;
            }
            for (j, &b) in other.coeffs.iter().enumerate() {
                if b.is_zero() {
                    continue;
                }
                let term = a.checked_mul(b)?;
                coeffs[i + j] = coeffs[i + j].checked_add(term)?;
            }
        }
        Some(RatPoly { var, coeffs })
    }

    /// Clear denominators: multiply through by the LCM of all denominators to
    /// obtain an integer polynomial (LSB-first), declining on overflow. The
    /// multiplier is positive, so it preserves every comparison `p ⋈ 0`.
    fn to_integer_poly(&self) -> Option<Vec<i128>> {
        // LCM of the denominators.
        let mut lcm = 1i128;
        for c in &self.coeffs {
            let d = c.denominator();
            lcm = lcm_i128(lcm, d)?;
        }
        let mut out = Vec::with_capacity(self.coeffs.len());
        for c in &self.coeffs {
            // c * lcm is an integer: (num * lcm) / den, exact since den | lcm.
            let scaled = c.numerator().checked_mul(lcm)?;
            if scaled % c.denominator() != 0 {
                return None; // should not happen (den | lcm), but stay safe
            }
            let v = scaled / c.denominator();
            if v.checked_abs()? >= MAX_ABS_COEFF {
                return None;
            }
            out.push(v);
        }
        // Trim trailing zeros so the leading coefficient is genuine.
        while out.len() > 1 && *out.last().unwrap() == 0 {
            out.pop();
        }
        Some(out)
    }
}

/// Decide a conjunction of single-variable real polynomial constraints (over one
/// shared variable) exactly, returning an irrational witness when the satisfying
/// value is algebraic.
///
/// The whole query is a conjunction: each assertion is one comparison
/// `pᵢ(x) ⋈ᵢ 0` or a top-level `and` of such comparisons (flattened). A single
/// constraint takes the original fast path; two or more share one variable and
/// are decided by sign-cell decomposition.
///
/// Returns `Some(Sat(model))` / `Some(Unsat)` for the exact pattern (every `Sat`
/// model replay-checked against **all** assertions), and `None` to decline (left
/// to [`crate::nra`]).
///
/// # Errors
///
/// Returns [`SolverError`] to match the `?`-chained dispatch contract; the
/// decision itself does not currently fail (the `Result` is part of the stable
/// call signature).
#[allow(
    clippy::unnecessary_wraps,
    reason = "signature matches the ?-chained auto.rs dispatch contract"
)]
pub fn decide_real_poly_constraint(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<CheckResult>, SolverError> {
    if assertions.is_empty() {
        return Ok(None);
    }
    // Flatten the query into the set of atomic comparisons, declining on any
    // non-conjunctive structure or non-(single-var real poly) atom. Every atom
    // must collect over the SAME variable.
    let mut atoms: Vec<Atom> = Vec::new();
    let mut var: Option<SymbolId> = None;
    for &a in assertions {
        if collect_conjuncts(arena, a, &mut var, &mut atoms).is_none() {
            return Ok(None);
        }
    }
    if atoms.is_empty() {
        return Ok(None);
    }
    let Some(var) = var else {
        // Every atom collected to a constant polynomial (no variable) — that is
        // exact LRA territory, not ours.
        return Ok(None);
    };

    // Single-constraint fast path: preserves the original (well-tested) behavior,
    // including the dedicated `≠` and `≤/≥`-root witnesses.
    if let [atom] = atoms.as_slice() {
        return Ok(decide_single(arena, assertions, var, atom));
    }

    // Conjunction: sign-cell decomposition over the shared variable.
    Ok(decide_system(arena, assertions, var, &atoms))
}

/// One atomic comparison `poly(x) ⋈ 0`, with the integer-cleared polynomial.
struct Atom {
    cmp: Cmp,
    poly: Vec<i128>,
}

/// Whether the sign `s` of `pᵢ(α)` satisfies the comparison `pᵢ ⋈ 0`.
fn sign_satisfies(cmp: Cmp, s: Sign) -> bool {
    match cmp {
        Cmp::Eq => s == Sign::Zero,
        Cmp::Ne => s != Sign::Zero,
        Cmp::Lt => s == Sign::Neg,
        Cmp::Le => s == Sign::Neg || s == Sign::Zero,
        Cmp::Gt => s == Sign::Pos,
        Cmp::Ge => s == Sign::Pos || s == Sign::Zero,
    }
}

/// Decide a single constraint `poly ⋈ 0` (the original fast path). `None`
/// declines.
fn decide_single(
    arena: &TermArena,
    assertions: &[TermId],
    var: SymbolId,
    atom: &Atom,
) -> Option<CheckResult> {
    let poly = &atom.poly;
    let verdict = decide(poly, atom.cmp)?;

    match verdict {
        Verdict::Unsat => Some(CheckResult::Unsat),
        Verdict::SatRational(q) => {
            // Replay the rational witness through the ground evaluator on ALL
            // original assertions; accept only if every one holds.
            if !replay_rational(arena, assertions, var, q) {
                return None;
            }
            let mut model = Model::new();
            model.set(var, Value::Real(q));
            Some(CheckResult::Sat(model))
        }
        Verdict::SatAlgebraic(alpha) => {
            // Replay-check the algebraic witness: it must be a genuine root of the
            // collected polynomial, i.e. sign_at(p, α) = 0. (We do NOT ask the
            // evaluator to multiply algebraic numbers; the decider holds `poly`.)
            if alpha.sign_at(poly) != Some(Sign::Zero) {
                return None;
            }
            // For an equality `p = 0` the root replays by construction. For an
            // inequality we never return an algebraic witness (samples are
            // rational), so this branch is equality-only.
            let mut model = Model::new();
            model.set(var, Value::RealAlgebraic(alpha));
            Some(CheckResult::Sat(model))
        }
    }
}

/// Decide a conjunction `⋀ᵢ pᵢ(x) ⋈ᵢ 0` by sign-cell decomposition.
///
/// Candidate critical points = every isolated real root of every `pᵢ` (cell
/// boundaries) ∪ one rational sample strictly inside each open cell. A candidate
/// satisfies the conjunction iff every `pᵢ`'s sign at it satisfies `⋈ᵢ`. The
/// first satisfying candidate (deterministic order, rationals preferred) →
/// **Sat** (replay-checked against all assertions); none → **Unsat**; any
/// ordering ambiguity / overflow → decline.
fn decide_system(
    arena: &TermArena,
    assertions: &[TermId],
    var: SymbolId,
    atoms: &[Atom],
) -> Option<CheckResult> {
    // 1. Collect every real root of every constraint polynomial.
    let mut roots: Vec<Root> = Vec::new();
    for atom in atoms {
        let rs = isolate_roots(&atom.poly)?; // overflow during isolation ⇒ decline
        roots.extend(rs);
    }

    // 2. Sort the roots into a deterministic ascending order. Any pair we cannot
    //    order exactly (algebraic-vs-algebraic that does not resolve) ⇒ decline.
    let ordered = sort_roots(&roots)?;

    // 3. Build the candidate sample points strictly between/around the roots.
    //    Each is a RATIONAL preferred witness for an open cell.
    let samples = cell_samples(&ordered)?;

    // 4. Test rational samples FIRST (so the model stays rational when a cell
    //    works), then the roots themselves (an equality may pin x to an
    //    irrational root). A `None` from any sign test means the candidate
    //    enumeration is *incomplete* for this query, so we must not claim Unsat
    //    — propagate the decline.
    for q in &samples {
        if rational_satisfies_all(atoms, *q)? && replay_rational(arena, assertions, var, *q) {
            let mut model = Model::new();
            model.set(var, Value::Real(*q));
            return Some(CheckResult::Sat(model));
        }
    }
    for root in &ordered {
        match root {
            Root::Rational(q) => {
                if rational_satisfies_all(atoms, *q)? && replay_rational(arena, assertions, var, *q)
                {
                    let mut model = Model::new();
                    model.set(var, Value::Real(*q));
                    return Some(CheckResult::Sat(model));
                }
            }
            Root::Algebraic(a) => {
                // `None` (a sign decision did not resolve) ⇒ decline, never Unsat.
                if algebraic_satisfies_all(atoms, a)? {
                    // Replay-check: the witness must genuinely satisfy every
                    // constraint via exact `sign_at`. (algebraic_satisfies_all
                    // already used sign_at; this is the same gate, kept as the
                    // explicit soundness contract.)
                    if algebraic_replay_all(atoms, a) {
                        let mut model = Model::new();
                        model.set(var, Value::RealAlgebraic(a.clone()));
                        return Some(CheckResult::Sat(model));
                    }
                }
            }
        }
    }

    // No candidate (root or per-cell sample) satisfies the whole conjunction. The
    // candidate set covers every sign pattern of the single variable, so this is
    // exact Unsat — every sign test above resolved (an indeterminate one would
    // have returned `None`/declined via `?`). Reaching here means the enumeration
    // was complete.
    Some(CheckResult::Unsat)
}

/// Whether the rational `q` satisfies every constraint, by exact rational sign
/// evaluation. `None` on overflow (caller declines).
fn rational_satisfies_all(atoms: &[Atom], q: Rational) -> Option<bool> {
    for atom in atoms {
        let s = Sign::of_rational(eval_rat(&atom.poly, q)?);
        if !sign_satisfies(atom.cmp, s) {
            return Some(false);
        }
    }
    Some(true)
}

/// Whether the algebraic `α` satisfies every constraint, by exact `sign_at`.
/// `None` if any sign test does not resolve (caller declines).
fn algebraic_satisfies_all(atoms: &[Atom], a: &RealAlgebraic) -> Option<bool> {
    for atom in atoms {
        let s = a.sign_at(&atom.poly)?;
        if !sign_satisfies(atom.cmp, s) {
            return Some(false);
        }
    }
    Some(true)
}

/// Explicit replay gate for an algebraic witness: re-evaluate `sign_at` against
/// every constraint and require each to satisfy its comparison. Returns `false`
/// on any indeterminate sign (treated as replay failure ⇒ decline upstream).
fn algebraic_replay_all(atoms: &[Atom], a: &RealAlgebraic) -> bool {
    atoms
        .iter()
        .all(|atom| matches!(a.sign_at(&atom.poly), Some(s) if sign_satisfies(atom.cmp, s)))
}

/// Replay a rational witness through the ground evaluator on **every** original
/// assertion; accept only if all evaluate to `Bool(true)`.
fn replay_rational(arena: &TermArena, assertions: &[TermId], var: SymbolId, q: Rational) -> bool {
    let mut asg = Assignment::new();
    asg.set(var, Value::Real(q));
    assertions
        .iter()
        .all(|&a| matches!(eval(arena, a, &asg), Ok(Value::Bool(true))))
}

/// Sort isolated roots into ascending order, returning `None` if any pair cannot
/// be ordered exactly (an algebraic-vs-algebraic comparison that does not resolve
/// within the refinement bound) so the caller declines rather than guessing.
fn sort_roots(roots: &[Root]) -> Option<Vec<Root>> {
    let mut out: Vec<Root> = roots.to_vec();
    // Insertion sort with a total, exact comparator; on any indeterminate
    // comparison return None.
    for i in 1..out.len() {
        let mut j = i;
        while j > 0 {
            match compare_roots(&out[j - 1], &out[j])? {
                Ordering::Greater => {
                    out.swap(j - 1, j);
                    j -= 1;
                }
                _ => break,
            }
        }
    }
    Some(out)
}

/// Exact comparison of two isolated roots. Rational-vs-rational and
/// rational-vs-algebraic resolve exactly; algebraic-vs-algebraic uses a rational
/// separating point derived from the disjoint isolating intervals, declining
/// (`None`) only if the intervals still overlap (which the fine isolation grid
/// makes impossible for admitted polynomials, but we never guess).
fn compare_roots(a: &Root, b: &Root) -> Option<Ordering> {
    match (a, b) {
        (Root::Rational(x), Root::Rational(y)) => x.checked_cmp(y),
        (Root::Rational(x), Root::Algebraic(y)) => Some(y.compare_rational(x)?.reverse()),
        (Root::Algebraic(x), Root::Rational(y)) => x.compare_rational(y),
        (Root::Algebraic(x), Root::Algebraic(y)) => {
            // Equal value? (same poly, overlapping intervals).
            if x == y {
                return Some(Ordering::Equal);
            }
            // Distinct algebraic numbers: their isolating intervals are disjoint
            // (or can be separated). If x's interval lies wholly below y's, x < y.
            let (xlo, xhi) = x.interval();
            let (ylo, yhi) = y.interval();
            if xhi.checked_cmp(&ylo)? != Ordering::Greater {
                return Some(Ordering::Less); // x ≤ xhi ≤ ylo ≤ y, and x ≠ y
            }
            if yhi.checked_cmp(&xlo)? != Ordering::Greater {
                return Some(Ordering::Greater);
            }
            // Intervals overlap and the values are distinct: we cannot order them
            // exactly without algebraic-vs-algebraic refinement (deferred). Decline.
            None
        }
    }
}

/// Build one rational sample strictly inside each open cell delimited by the
/// (ascending, deduplicated) roots: below the least root, between each adjacent
/// pair, and above the greatest. With no roots, a single sample (0) covers ℝ.
/// `None` on overflow.
fn cell_samples(ordered: &[Root]) -> Option<Vec<Rational>> {
    if ordered.is_empty() {
        return Some(vec![Rational::zero()]);
    }
    let locs: Vec<Rational> = ordered.iter().map(Root::locate).collect();
    let mut pts = Vec::with_capacity(locs.len() + 1);
    // Below the least root.
    pts.push(locs[0].checked_sub(Rational::integer(1))?);
    // Strictly between adjacent root *locations*. Because the isolating intervals
    // are disjoint and ordered, the midpoint of two distinct locations lies in the
    // open cell between the two roots. (Equal locations — a shared rational root
    // counted twice — yield a degenerate midpoint we simply skip; the adjacent
    // open cells are still sampled by their other separators.)
    for w in locs.windows(2) {
        if w[0].checked_cmp(&w[1])? == Ordering::Equal {
            continue;
        }
        let mid = w[0].checked_add(w[1])?.checked_div(Rational::integer(2))?;
        pts.push(mid);
    }
    // Above the greatest root.
    pts.push(locs[locs.len() - 1].checked_add(Rational::integer(1))?);
    Some(pts)
}

/// A decision plus its witness.
enum Verdict {
    Unsat,
    SatRational(Rational),
    SatAlgebraic(RealAlgebraic),
}

/// Decide `p(x) ⋈ 0` over the reals from the integer polynomial `poly`.
fn decide(poly: &[i128], cmp: Cmp) -> Option<Verdict> {
    match cmp {
        Cmp::Eq => decide_eq(poly),
        Cmp::Ne => decide_ne(poly),
        Cmp::Lt | Cmp::Le | Cmp::Gt | Cmp::Ge => decide_inequality(poly, cmp),
    }
}

/// `p(x) = 0`: isolate the real roots; return the first as a rational (if exact)
/// or algebraic witness, or **Unsat** if there are none.
fn decide_eq(poly: &[i128]) -> Option<Verdict> {
    let roots = isolate_roots(poly)?;
    match roots.into_iter().next() {
        None => Some(Verdict::Unsat),
        Some(Root::Rational(q)) => Some(Verdict::SatRational(q)),
        Some(Root::Algebraic(a)) => Some(Verdict::SatAlgebraic(a)),
    }
}

/// `p(x) ≠ 0`: Sat unless `p ≡ 0`. A nonzero degree-`n` poly has ≤ `n` roots, so
/// some small integer is a non-root; scan for one (rational witness).
fn decide_ne(poly: &[i128]) -> Option<Verdict> {
    if poly.iter().all(|&c| c == 0) {
        return Some(Verdict::Unsat); // p ≡ 0 ⇒ never ≠ 0
    }
    for k in 0..=(MAX_DEGREE as i128 + 8) {
        for cand in [k, -k] {
            let q = Rational::integer(cand);
            if !eval_rat(poly, q)?.is_zero() {
                return Some(Verdict::SatRational(q));
            }
        }
    }
    None
}

/// `p(x) ⋈ 0` for a strict/loose inequality: the roots partition ℝ into open
/// sign-constant intervals (plus the two unbounded tails); test a **rational**
/// sample in each candidate region. For `≤`/`≥` a root itself (where `p = 0`) is
/// also a witness, returned as a rational/algebraic root.
fn decide_inequality(poly: &[i128], cmp: Cmp) -> Option<Verdict> {
    let want = |s: Sign| -> bool {
        match cmp {
            Cmp::Lt => s == Sign::Neg,
            Cmp::Le => s == Sign::Neg || s == Sign::Zero,
            Cmp::Gt => s == Sign::Pos,
            Cmp::Ge => s == Sign::Pos || s == Sign::Zero,
            Cmp::Eq | Cmp::Ne => unreachable!(),
        }
    };
    let roots = isolate_roots(poly)?;

    // `≤`/`≥` accept a root directly (p = 0 there).
    if matches!(cmp, Cmp::Le | Cmp::Ge)
        && let Some(r) = roots.first()
    {
        return Some(match r {
            Root::Rational(q) => Verdict::SatRational(*q),
            Root::Algebraic(a) => Verdict::SatAlgebraic(a.clone()),
        });
    }

    // Build the rational sample points: midpoints between consecutive root
    // *interval* separators, plus one point below the lowest and above the
    // highest. We use rational endpoints that are guaranteed strictly between
    // adjacent roots (the isolating intervals are disjoint and ordered).
    let separators = root_separators(&roots);
    for s in separators {
        let sign = Sign::of_rational(eval_rat(poly, s)?);
        if want(sign) {
            return Some(Verdict::SatRational(s));
        }
    }
    Some(Verdict::Unsat)
}

/// An isolated real root: an exact rational, or an algebraic number defined by
/// `poly` and an isolating interval.
#[derive(Clone)]
enum Root {
    Rational(Rational),
    Algebraic(RealAlgebraic),
}

impl Root {
    /// A rational strictly-inside point representing the root's location, used to
    /// order roots and to derive sample separators. For a rational root it is the
    /// value; for an algebraic one it is the interval midpoint.
    fn locate(&self) -> Rational {
        match self {
            Root::Rational(q) => *q,
            Root::Algebraic(a) => a.approx_midpoint().unwrap_or_else(Rational::zero),
        }
    }
}

/// The number of equal cells the root-isolation grid subdivides `[-B, B]` into
/// (a uniform first pass to separate roots into distinct cells). Bounded so the
/// scan is cheap; each cell is then bisected to isolate its single root. `1 <<
/// 14` (16384) cells over the Cauchy interval comfortably separates the roots of
/// any small-degree, `i128`-coefficient polynomial this pass admits.
const ISOLATE_GRID: i128 = 1 << 14;

/// Maximum bisection depth used to isolate / tighten a single root within one
/// sign-change cell. Each step halves the cell, so the witness interval shrinks
/// by `2^DEPTH`; 48 is far finer than any replay or comparison needs.
const ISOLATE_REFINE_DEPTH: u32 = 48;

/// Isolate **all** real roots of the integer polynomial `poly`, returned in
/// ascending order, each as a [`Root`]. Returns `None` on overflow.
///
/// Method (exact, no float): bound the roots by the Cauchy bound
/// `B = 1 + max|aᵢ| / |aₙ|`, scan a uniform rational grid over `[-B, B]`, and for
/// each consecutive pair of grid points classify the cell:
/// - an exact rational root at a grid point (`poly = 0`) is recorded directly;
/// - a strict sign change across the cell brackets exactly one root, which is
///   then **bisected** to either an exact rational root or a tightly-isolated
///   algebraic number.
///
/// The grid is fine enough that distinct roots of an admissible polynomial fall
/// in distinct cells; a cell with equal nonzero endpoint signs is treated as
/// root-free (sound for the squarefree/separated polynomials in scope — and any
/// missed witness only ever degrades a `Sat` to a sound decline upstream, never a
/// wrong verdict, because every returned `Sat` is replay-checked and `Unsat` for
/// `=` is reported only when no sign change is found anywhere on `[-B, B]`, which
/// — `B` being a true root bound — is exact for these polynomials).
fn isolate_roots(poly: &[i128]) -> Option<Vec<Root>> {
    let lead = *poly.last()?;
    if lead == 0 {
        return None;
    }
    let max_other = poly[..poly.len() - 1]
        .iter()
        .map(|c| c.unsigned_abs())
        .max()
        .unwrap_or(0);
    // Cauchy bound B = 1 + max|aᵢ|/|aₙ|, rounded up to an integer.
    let bound = Rational::integer(1).checked_add(Rational::checked_new(
        i128::try_from(max_other).ok()?,
        lead.checked_abs()?,
    )?)?;
    let b_int = bound
        .numerator()
        .checked_div(bound.denominator())?
        .checked_add(1)?;
    let lo = Rational::integer(b_int.checked_neg()?);
    let hi = Rational::integer(b_int);
    let width = hi.checked_sub(lo)?;
    let step = width.checked_div(Rational::integer(ISOLATE_GRID))?;

    let mut roots: Vec<Root> = Vec::new();
    let mut prev = lo;
    let mut prev_val = eval_rat(poly, prev)?;
    // The very first grid point may be an exact root.
    if prev_val.is_zero() {
        roots.push(Root::Rational(prev));
    }
    for k in 1..=ISOLATE_GRID {
        let cur = lo.checked_add(step.checked_mul(Rational::integer(k))?)?;
        let cur_val = eval_rat(poly, cur)?;
        let s_prev = Sign::of_rational(prev_val);
        let s_cur = Sign::of_rational(cur_val);
        if s_cur == Sign::Zero {
            // Exact rational root at this grid point.
            roots.push(Root::Rational(cur));
        } else if s_prev != Sign::Zero && s_prev != s_cur {
            // Strict sign change in (prev, cur): exactly one root — isolate it.
            roots.push(isolate_one(poly, prev, cur)?);
        }
        prev = cur;
        prev_val = cur_val;
    }
    Some(roots)
}

/// Isolate the single root of `poly` in the open interval `(lo, hi)` known to have
/// a strict endpoint sign change. Bisect: an exact rational midpoint root yields a
/// [`Root::Rational`]; otherwise, after [`ISOLATE_REFINE_DEPTH`] steps, build a
/// tightly-isolated [`Root::Algebraic`] from `poly` and the narrowed interval.
fn isolate_one(poly: &[i128], lo: Rational, hi: Rational) -> Option<Root> {
    let mut lo = lo;
    let mut hi = hi;
    // The sign of `poly` at the lower endpoint stays invariant under the updates
    // below (when we move `lo` to `mid`, `mid` had the same sign as `lo`).
    let slo = Sign::of_rational(eval_rat(poly, lo)?);
    // Bisect to tighten the bracket. Crucially, every iteration preserves the
    // invariant that `poly` takes strictly opposite, nonzero signs at `lo`/`hi`
    // (we only move an endpoint onto a midpoint whose sign we *successfully*
    // computed). So if a midpoint evaluation overflows `i128` (denominators grow
    // like `2^depth`, and Horner raises that to the polynomial degree), we cannot
    // decide which half to keep — but the *current* bracket is still a valid
    // single-root isolating interval. We therefore **stop refining** and fall
    // through to the algebraic-number construction below, rather than declining
    // the whole root. This is sound: a coarser-but-valid bracket still isolates
    // exactly one root, and the replay check (`sign_at(poly, α) = 0`) does not
    // depend on bracket width. (Before this guard, the `?` on an overflowed
    // midpoint eval lost every degree-≥3 root to a spurious decline.)
    for _ in 0..ISOLATE_REFINE_DEPTH {
        let Some(mid) = lo
            .checked_add(hi)
            .and_then(|s| s.checked_div(Rational::integer(2)))
        else {
            break;
        };
        let Some(mid_val) = eval_rat(poly, mid) else {
            break;
        };
        let smid = Sign::of_rational(mid_val);
        if smid == Sign::Zero {
            return Some(Root::Rational(mid));
        }
        if smid == slo {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    // The bracket is now tiny. If `poly` has an *exact rational* root inside it
    // (rational-root theorem: numerator | a₀, denominator | aₙ), prefer that exact
    // rational witness over an algebraic representation. Otherwise the root is
    // irrational — represent it as an isolated algebraic number.
    if let Some(q) = rational_root_in(poly, lo, hi) {
        return Some(Root::Rational(q));
    }
    Some(Root::Algebraic(RealAlgebraic::new(poly.to_vec(), lo, hi)?))
}

/// The largest `|a₀|` / `|aₙ|` for which [`rational_root_in`] enumerates divisors
/// (trial division up to the value). The coefficient guard already caps these at
/// `MAX_ABS_COEFF`; this secondary bound keeps the divisor enumeration cheap.
const RATIONAL_ROOT_BOUND: i128 = 1 << 24;

/// If `poly` has an exact rational root strictly inside `(lo, hi)`, return it
/// (rational-root theorem: a rational root `p/q` in lowest terms has `p | a₀` and
/// `q | aₙ`). Returns `None` when there is no such root in the interval **or** the
/// search declines (an overflow, or a constant/leading term too large to
/// enumerate cheaply); in every `None` case the caller soundly falls back to an
/// algebraic representation, so conflating "not found" with "declined" is safe.
fn rational_root_in(poly: &[i128], lo: Rational, hi: Rational) -> Option<Rational> {
    let leading = *poly.last()?;
    // A zero constant term means `x = 0` is a root and the polynomial is divisible
    // by `x`. Report `0` directly if it lies in the bracket, then **deflate** the
    // factor(s) of `x`: the rational-root theorem keys off the *nonzero* lowest
    // coefficient, so applying it to the original `a₀ = 0` would enumerate nothing
    // and lose every rational root of the form `±p/q` (e.g. ±1 of `x³ − x`). The
    // deflated poly `poly[m..]` (after stripping `m` leading zeros = factors of x)
    // has a nonzero constant term and the *same* nonzero rational roots.
    let mut m = 0usize;
    while m < poly.len() && poly[m] == 0 {
        m += 1;
    }
    if m > 0 {
        let zero = Rational::zero();
        if zero > lo && zero < hi {
            return Some(zero);
        }
    }
    let deflated = &poly[m..];
    let const_term = *deflated.first()?; // nonzero by construction (or empty ⇒ p ≡ 0)
    let const_abs = const_term.checked_abs()?;
    let lead_abs = leading.checked_abs()?;
    if const_abs == 0 || const_abs > RATIONAL_ROOT_BOUND || lead_abs > RATIONAL_ROOT_BOUND {
        return None; // nothing to enumerate / too large — leave as algebraic
    }
    for p in divisors(const_abs) {
        for q in divisors(lead_abs) {
            for cand in [Rational::checked_new(p, q)?, Rational::checked_new(-p, q)?] {
                if cand > lo && cand < hi && eval_rat(poly, cand)?.is_zero() {
                    return Some(cand);
                }
            }
        }
    }
    None
}

/// The positive divisors of `n > 0` (trial division). Empty for `n == 0`.
fn divisors(n: i128) -> Vec<i128> {
    let mut out = Vec::new();
    if n <= 0 {
        return out;
    }
    let mut d = 1i128;
    while d.saturating_mul(d) <= n {
        if n % d == 0 {
            out.push(d);
            if d != n / d {
                out.push(n / d);
            }
        }
        d += 1;
    }
    out
}

/// Rational sample points for the inequality sign scan: one strictly below the
/// lowest root, one strictly above the highest, and one strictly between each
/// adjacent pair of roots. With no roots, a single point (0) samples all of ℝ.
fn root_separators(roots: &[Root]) -> Vec<Rational> {
    if roots.is_empty() {
        return vec![Rational::zero()];
    }
    let locs: Vec<Rational> = roots.iter().map(Root::locate).collect();
    let mut pts = Vec::with_capacity(locs.len() + 1);
    // Below the lowest.
    pts.push(locs[0] - Rational::integer(1));
    // Between adjacent roots: the midpoint (the isolating intervals are disjoint,
    // so the midpoint of two distinct root locations lies strictly between them).
    for w in locs.windows(2) {
        if let Some(mid) = w[0]
            .checked_add(w[1])
            .and_then(|s| s.checked_div(Rational::integer(2)))
        {
            pts.push(mid);
        }
    }
    // Above the highest.
    pts.push(locs[locs.len() - 1] + Rational::integer(1));
    pts
}

/// LCM of two positive `i128` magnitudes, declining on overflow.
fn lcm_i128(a: i128, b: i128) -> Option<i128> {
    if a == 0 || b == 0 {
        return Some(0);
    }
    let g = gcd_i128(a.unsigned_abs(), b.unsigned_abs());
    // a / g * b, with g | a exactly.
    let a_div = a.checked_div(i128::try_from(g).ok()?)?;
    a_div.checked_mul(b)?.checked_abs()
}

/// GCD of two unsigned magnitudes (Euclid).
fn gcd_i128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Exact Horner evaluation of an LSB-first integer polynomial at a [`Rational`].
fn eval_rat(poly: &[i128], x: Rational) -> Option<Rational> {
    let mut acc = Rational::zero();
    for &c in poly.iter().rev() {
        acc = acc.checked_mul(x)?.checked_add(Rational::integer(c))?;
    }
    Some(acc)
}

// Re-export the `Sign::of_rational` helper logic locally (the IR `Sign` does not
// expose a rational constructor publicly).
trait SignOfRational {
    fn of_rational(r: Rational) -> Sign;
}

impl SignOfRational for Sign {
    fn of_rational(r: Rational) -> Sign {
        match r.numerator().cmp(&0) {
            core::cmp::Ordering::Less => Sign::Neg,
            core::cmp::Ordering::Equal => Sign::Zero,
            core::cmp::Ordering::Greater => Sign::Pos,
        }
    }
}

/// Flatten a Boolean assertion into atomic single-variable real-polynomial
/// comparisons, accumulating into `atoms` and unifying the shared variable into
/// `var`. A top-level `and` recurses into its conjuncts; a single comparison
/// becomes one [`Atom`]. Returns `None` to decline on any non-conjunctive
/// structure (`or`, `=>`, `xor`, …), any atom that is not a single-variable real
/// polynomial comparison, a *distinct* second variable, a degree outside
/// `[1, MAX_DEGREE]`, or an `i128`/`Rational` overflow during integer clearing.
///
/// Returning `Some(())` means every conjunct of this assertion was admitted.
fn collect_conjuncts(
    arena: &TermArena,
    assertion: TermId,
    var: &mut Option<SymbolId>,
    atoms: &mut Vec<Atom>,
) -> Option<()> {
    // Top-level `and`: flatten its conjuncts. (`BoolNot` is handled below as the
    // `≠` shape, NOT as a general negation, so we don't push De Morgan into it.)
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(assertion)
    {
        for &c in args {
            collect_conjuncts(arena, c, var, atoms)?;
        }
        return Some(());
    }

    // Otherwise it must be one atomic comparison.
    let (atom_var, cmp, rat) = match_real_poly_constraint(arena, assertion)?;
    // Unify the shared variable; a second distinct variable forces a decline.
    match *var {
        None => *var = Some(atom_var),
        Some(v) if v == atom_var => {}
        Some(_) => return None,
    }
    // Degree ≥ 1 required (a constant is exact LRA territory) and bounded.
    if rat.degree() == 0 || rat.degree() > MAX_DEGREE {
        return None;
    }
    let poly = rat.to_integer_poly()?;
    if poly.len() <= 1 {
        return None;
    }
    atoms.push(Atom { cmp, poly });
    Some(())
}

/// Match a single real comparison/equality `lhs ⋈ rhs` (or `¬(lhs = rhs)` for
/// `≠`) where `lhs − rhs` collects to a single-variable real polynomial. Returns
/// `(x, cmp-as-`p ⋈ 0`, p = lhs − rhs)` or `None` to decline.
fn match_real_poly_constraint(
    arena: &TermArena,
    assertion: TermId,
) -> Option<(SymbolId, Cmp, RatPoly)> {
    let TermNode::App { op, args } = arena.node(assertion) else {
        return None;
    };

    // `≠` is `not(=)`.
    if matches!(op, Op::BoolNot) {
        let inner = args[0];
        let TermNode::App {
            op: Op::Eq,
            args: eq_args,
        } = arena.node(inner)
        else {
            return None;
        };
        let poly = collect_diff(arena, eq_args[0], eq_args[1])?;
        let var = poly.var?;
        return Some((var, Cmp::Ne, poly));
    }

    let cmp = match op {
        Op::Eq => Cmp::Eq,
        Op::RealLt => Cmp::Lt,
        Op::RealLe => Cmp::Le,
        Op::RealGt => Cmp::Gt,
        Op::RealGe => Cmp::Ge,
        _ => return None,
    };
    // `Eq` must be over Real operands (an Int/BV equality is not ours).
    if matches!(op, Op::Eq) && arena.sort_of(args[0]) != Sort::Real {
        return None;
    }
    let poly = collect_diff(arena, args[0], args[1])?;
    let var = poly.var?;
    Some((var, cmp, poly))
}

/// Collect `lhs − rhs` as a single-variable real polynomial, or `None`.
fn collect_diff(arena: &TermArena, lhs: TermId, rhs: TermId) -> Option<RatPoly> {
    let l = collect(arena, lhs)?;
    let r = collect(arena, rhs)?;
    l.sub(r)
}

/// Recursively collect a `Real`-sorted term into a single-variable rational
/// polynomial over `{+, −, ·, neg, RealConst, symbol}`. Anything else declines.
fn collect(arena: &TermArena, t: TermId) -> Option<RatPoly> {
    if arena.sort_of(t) != Sort::Real {
        return None;
    }
    match arena.node(t) {
        TermNode::RealConst(r) => Some(RatPoly::constant(*r)),
        TermNode::Symbol(s) => Some(RatPoly::var_of(*s)),
        TermNode::App { op, args } => match op {
            Op::RealNeg if args.len() == 1 => collect(arena, args[0])?.neg(),
            Op::RealAdd if args.len() == 2 => {
                collect(arena, args[0])?.add(&collect(arena, args[1])?)
            }
            Op::RealSub if args.len() == 2 => {
                collect(arena, args[0])?.sub(collect(arena, args[1])?)
            }
            Op::RealMul if args.len() == 2 => {
                collect(arena, args[0])?.mul(&collect(arena, args[1])?)
            }
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ipoly(coeffs: &[i128]) -> Vec<i128> {
        coeffs.to_vec()
    }

    #[test]
    fn isolate_sqrt2() {
        // x² − 2: roots ±√2 (both irrational).
        let roots = isolate_roots(&ipoly(&[-2, 0, 1])).unwrap();
        assert_eq!(roots.len(), 2);
        for r in &roots {
            assert!(matches!(r, Root::Algebraic(_)));
        }
    }

    #[test]
    fn isolate_rational_roots() {
        // x² − 4: roots ±2 (both rational).
        let roots = isolate_roots(&ipoly(&[-4, 0, 1])).unwrap();
        assert_eq!(roots.len(), 2);
        for r in &roots {
            assert!(matches!(r, Root::Rational(_)));
        }
    }

    #[test]
    fn no_real_root() {
        // x² + 1: no real root.
        let roots = isolate_roots(&ipoly(&[1, 0, 1])).unwrap();
        assert!(roots.is_empty());
    }

    #[test]
    fn eq_sqrt2_is_algebraic_sat() {
        match decide_eq(&ipoly(&[-2, 0, 1])).unwrap() {
            Verdict::SatAlgebraic(a) => assert_eq!(a.sign_at(&[-2, 0, 1]), Some(Sign::Zero)),
            _ => panic!("expected algebraic sat"),
        }
    }

    #[test]
    fn lt_zero_unsat_for_square_plus() {
        // x² < 0: no negative value ⇒ Unsat. (poly = x², roots {0}.)
        match decide(&ipoly(&[0, 0, 1]), Cmp::Lt).unwrap() {
            Verdict::Unsat => {}
            _ => panic!("expected unsat"),
        }
    }

    #[test]
    fn gt_two_has_rational_witness() {
        // x² − 2 > 0: e.g. x = 2 (sign +). Witness must be rational.
        match decide(&ipoly(&[-2, 0, 1]), Cmp::Gt).unwrap() {
            Verdict::SatRational(q) => {
                assert!(eval_rat(&[-2, 0, 1], q).unwrap().numerator() > 0);
            }
            _ => panic!("expected rational sat"),
        }
    }

    #[test]
    fn le_zero_sat_at_origin() {
        // x² ≤ 0 ⇒ x = 0 (the root). Witness is the rational root 0.
        match decide(&ipoly(&[0, 0, 1]), Cmp::Le).unwrap() {
            Verdict::SatRational(q) => assert!(q.is_zero()),
            _ => panic!("expected rational sat at 0"),
        }
    }

    // --- degree ≥ 3 regression: isolation must not decline on bisection overflow.

    #[test]
    fn isolate_cubic_one_real_root() {
        // x³ − 2: a single irrational real root (∛2). Before the fix, the
        // bisection `?`-declined on midpoint overflow and this returned `None`.
        let roots = isolate_roots(&ipoly(&[-2, 0, 0, 1])).unwrap();
        assert_eq!(roots.len(), 1, "x³ − 2 has exactly one real root");
        match &roots[0] {
            Root::Algebraic(a) => {
                assert_eq!(a.sign_at(&[-2, 0, 0, 1]), Some(Sign::Zero), "∛2 is a root");
            }
            Root::Rational(q) => panic!("∛2 is irrational, got rational {q}"),
        }
    }

    #[test]
    fn isolate_quartic_four_real_roots() {
        // x⁴ − 5x² + 6: roots ±√2, ±√3 (all irrational).
        let p = ipoly(&[6, 0, -5, 0, 1]);
        let roots = isolate_roots(&p).unwrap();
        assert_eq!(roots.len(), 4, "biquadratic has four real roots");
        for r in &roots {
            match r {
                Root::Algebraic(a) => assert_eq!(a.sign_at(&p), Some(Sign::Zero)),
                Root::Rational(q) => panic!("expected irrational roots, got {q}"),
            }
        }
    }

    /// Property: every isolated *algebraic* root α of a higher-degree polynomial
    /// `p` satisfies `sign_at(p, α) = Zero` exactly (the soundness contract that
    /// gates every algebraic `Sat`). Covers several degree-≥3 shapes.
    #[test]
    fn property_isolated_algebraic_roots_are_exact_zeros() {
        let polys: &[&[i128]] = &[
            &[-2, 0, 0, 1],       // x³ − 2
            &[-3, 0, 0, 1],       // x³ − 3
            &[6, 0, -5, 0, 1],    // x⁴ − 5x² + 6
            &[-5, 0, 1, 0, 1],    // x⁴ + x² − 5
            &[-7, 0, 0, 0, 1],    // x⁴ − 7
            &[-2, 0, 0, 0, 0, 1], // x⁵ − 2
        ];
        for p in polys {
            let roots = isolate_roots(p).unwrap_or_default();
            assert!(!roots.is_empty(), "p {p:?} should have a real root");
            for r in &roots {
                if let Root::Algebraic(a) = r {
                    assert_eq!(
                        a.sign_at(p),
                        Some(Sign::Zero),
                        "isolated algebraic root of {p:?} must be an exact zero"
                    );
                }
            }
        }
    }

    #[test]
    fn cube_no_real_root_is_impossible_but_even_powers_are() {
        // x⁴ + 1: x⁴ ≥ 0 ⇒ no real root ⇒ Unsat for `= 0`.
        match decide_eq(&ipoly(&[1, 0, 0, 0, 1])).unwrap() {
            Verdict::Unsat => {}
            _ => panic!("x⁴ + 1 = 0 has no real root"),
        }
    }
}
