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

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{
    Assignment, Op, Rational, RealAlgebraic, Sign, Sort, SymbolId, TermArena, TermId, TermNode,
    Value, eval,
};

use crate::backend::{CheckResult, SolverError, UnknownKind, UnknownReason};
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
    let mut single_var_ok = true;
    for &a in assertions {
        if collect_conjuncts(arena, a, &mut var, &mut atoms).is_none() {
            single_var_ok = false;
            break;
        }
    }

    if single_var_ok {
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
        return Ok(decide_system(arena, assertions, var, &atoms));
    }

    // The single-variable collector declined (most often because a *second*
    // distinct variable appears). Try the sound, bounded **multivariate
    // decomposition** path (linear-substitution fixpoint + connected components
    // of single-variable sub-systems). It declines (`None`) on any genuinely
    // coupled / nonlinear-multivariate / non-polynomial / overflow shape, leaving
    // the query to the NRA layer.
    Ok(decompose_multivariate(arena, assertions))
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

/// The outcome of deciding a single-variable system **without** the
/// per-assertion replay (used by the multivariate decomposition, which replays
/// the assembled full model against all original assertions once at the end).
enum SystemVerdict {
    Unsat,
    Sat(Value),
}

/// Decide a single-variable system `⋀ᵢ pᵢ(x) ⋈ᵢ 0` and return just the witness
/// **value** (a rational [`Value::Real`] or irrational [`Value::RealAlgebraic`])
/// or `Unsat`, with **no** assertion-level replay. Same sign-cell decomposition
/// as [`decide_system`]; `None` declines (ordering ambiguity / overflow).
fn decide_system_value(atoms: &[Atom]) -> Option<SystemVerdict> {
    let mut roots: Vec<Root> = Vec::new();
    for atom in atoms {
        roots.extend(isolate_roots(&atom.poly)?);
    }
    let ordered = sort_roots(&roots)?;
    let samples = cell_samples(&ordered)?;

    for q in &samples {
        if rational_satisfies_all(atoms, *q)? {
            return Some(SystemVerdict::Sat(Value::Real(*q)));
        }
    }
    for root in &ordered {
        match root {
            Root::Rational(q) => {
                if rational_satisfies_all(atoms, *q)? {
                    return Some(SystemVerdict::Sat(Value::Real(*q)));
                }
            }
            Root::Algebraic(a) => {
                if algebraic_satisfies_all(atoms, a)? && algebraic_replay_all(atoms, a) {
                    return Some(SystemVerdict::Sat(Value::RealAlgebraic(a.clone())));
                }
            }
        }
    }
    Some(SystemVerdict::Unsat)
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
    // Below the lowest. On overflow skip this separator (a sound omission: a
    // missed sample can only degrade a `Sat` to a decline upstream, never a
    // wrong verdict — every `Sat` is replay-checked).
    if let Some(below) = locs[0].checked_sub(Rational::integer(1)) {
        pts.push(below);
    }
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
    // Above the highest. On overflow skip (sound omission, as above).
    if let Some(above) = locs[locs.len() - 1].checked_add(Rational::integer(1)) {
        pts.push(above);
    }
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

// ============================================================================
// Multivariate decomposition (sound, bounded): linear-substitution fixpoint +
// connected-components of single-variable sub-systems.
// ============================================================================
//
// `decide_real_poly_constraint` routes here when the single-variable collector
// declines (typically: ≥ 2 distinct variables). We re-collect the whole query
// as **multivariate** polynomial comparisons, then reduce to single-variable
// sub-problems by two sound transformations:
//
//   1. **Linear-defined-variable substitution.** An equality atom that
//      isolates one variable `y` as `y = L(other vars)` (L linear, y-free) is
//      removed and `y := L` substituted (exact Rational arithmetic) into every
//      other atom. Iterated to a fixpoint, bounded by the variable count.
//
//   2. **Connected components.** After substitution the remaining atoms are
//      partitioned by variable-sharing. If *every* component mentions exactly
//      one variable, each is a single-variable system decided by the existing
//      machinery; the witnesses combine because the components are disjoint.
//
// Anything else — a component with ≥ 2 distinct variables (genuinely coupled),
// a non-polynomial atom, a degree/coefficient/overflow guard trip — DECLINES.
// Every `Sat` is replay-checked: the assembled full model is evaluated against
// **every** original assertion (rational vars through the ground evaluator;
// for an atom containing the single algebraic var, the rational vars are
// substituted into the atom polynomial and the residual single-variable
// polynomial's sign at the algebraic value is checked exactly via `sign_at`).

/// The substitution fixpoint is bounded by the number of distinct variables;
/// this is a hard ceiling guarding against any non-termination.
const MAX_SUBST_ITERS: usize = 256;

/// A monomial: a sorted product of `var^exp` factors (empty ⇒ the constant
/// monomial `1`). Stored as a `BTreeMap` for a canonical key.
type Monomial = BTreeMap<SymbolId, u32>;

/// A multivariate polynomial with **rational** coefficients: a canonical map
/// from monomial to nonzero coefficient. The empty map is the zero polynomial.
#[derive(Clone, Default)]
struct MultiPoly {
    terms: BTreeMap<MonoKey, Rational>,
}

/// An orderable key for a monomial (the `BTreeMap` of a monomial is not itself
/// `Ord` in a way we can nest; we serialize it to a sorted `Vec`).
type MonoKey = Vec<(SymbolId, u32)>;

fn mono_key(m: &Monomial) -> MonoKey {
    m.iter().map(|(&s, &e)| (s, e)).collect()
}

impl MultiPoly {
    fn zero() -> Self {
        MultiPoly {
            terms: BTreeMap::new(),
        }
    }

    fn constant(r: Rational) -> Self {
        let mut p = MultiPoly::zero();
        if !r.is_zero() {
            p.terms.insert(Vec::new(), r);
        }
        p
    }

    fn var(s: SymbolId) -> Self {
        let mut p = MultiPoly::zero();
        p.terms.insert(vec![(s, 1)], Rational::integer(1));
        p
    }

    /// Insert `coeff * monomial`, merging into any existing term and dropping a
    /// resulting zero coefficient. `None` on overflow.
    fn add_term(&mut self, key: MonoKey, coeff: Rational) -> Option<()> {
        if coeff.is_zero() {
            return Some(());
        }
        match self.terms.get(&key).copied() {
            None => {
                self.terms.insert(key, coeff);
            }
            Some(existing) => {
                let sum = existing.checked_add(coeff)?;
                if sum.is_zero() {
                    self.terms.remove(&key);
                } else {
                    self.terms.insert(key, sum);
                }
            }
        }
        Some(())
    }

    fn add(&self, other: &Self) -> Option<Self> {
        let mut out = self.clone();
        for (k, &c) in &other.terms {
            out.add_term(k.clone(), c)?;
        }
        Some(out)
    }

    fn neg(&self) -> Option<Self> {
        let mut out = MultiPoly::zero();
        for (k, &c) in &self.terms {
            out.terms.insert(k.clone(), c.checked_neg()?);
        }
        Some(out)
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        self.add(&other.neg()?)
    }

    fn mul(&self, other: &Self) -> Option<Self> {
        let mut out = MultiPoly::zero();
        for (ka, &ca) in &self.terms {
            for (kb, &cb) in &other.terms {
                let coeff = ca.checked_mul(cb)?;
                let key = mul_mono(ka, kb)?;
                // Total-degree guard.
                if mono_total_degree(&key) > MAX_DEGREE {
                    return None;
                }
                out.add_term(key, coeff)?;
            }
        }
        Some(out)
    }

    /// The set of variables actually appearing (with nonzero exponent).
    fn vars(&self) -> BTreeSet<SymbolId> {
        let mut s = BTreeSet::new();
        for k in self.terms.keys() {
            for &(v, _) in k {
                s.insert(v);
            }
        }
        s
    }

    /// `Some(c)` when this polynomial has NO variables (it is the constant `c`,
    /// `0` for the zero polynomial); `None` when a variable appears. A no-variable
    /// polynomial has at most one term (the empty monomial), so the value is that
    /// term's coefficient. This is exact (the term was built by checked arithmetic).
    fn as_constant(&self) -> Option<Rational> {
        if self.vars().is_empty() {
            Some(
                self.terms
                    .values()
                    .next()
                    .copied()
                    .unwrap_or_else(Rational::zero),
            )
        } else {
            None
        }
    }

    fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Substitute `var := repl` (a polynomial) into this polynomial. Each
    /// occurrence `var^e` is replaced by `repl^e`. `None` on overflow.
    fn substitute(&self, var: SymbolId, repl: &MultiPoly) -> Option<Self> {
        let mut out = MultiPoly::zero();
        for (key, &coeff) in &self.terms {
            // Split the monomial into the `var^e` factor and the rest.
            let mut exp = 0u32;
            let mut rest: MonoKey = Vec::new();
            for &(v, e) in key {
                if v == var {
                    exp = e;
                } else {
                    rest.push((v, e));
                }
            }
            // term = coeff * rest * repl^exp.
            let mut factor = MultiPoly::constant(coeff);
            if !rest.is_empty() {
                let mut rp = MultiPoly::zero();
                rp.terms.insert(rest, Rational::integer(1));
                factor = factor.mul(&rp)?;
            }
            for _ in 0..exp {
                factor = factor.mul(repl)?;
            }
            out = out.add(&factor)?;
        }
        Some(out)
    }

    /// If this polynomial is **linear** and isolates one variable with
    /// coefficient `±1` so that an equality `poly = 0` rearranges to
    /// `y = L(other vars)` with `L` linear and y-free, return `(y, L)`.
    ///
    /// The polynomial is `c0 + Σ cᵢ·vᵢ`. We require it linear (every monomial
    /// degree ≤ 1) and pick a variable `y` whose coefficient is exactly `±1`.
    /// Then `poly = 0` ⇒ `y = −(rest)/cᵧ`, and since `cᵧ = ±1`, `L` has exact
    /// rational coefficients with no division blow-up.
    fn as_linear_definition(&self) -> Option<(SymbolId, MultiPoly)> {
        // Reject any nonlinear monomial.
        for k in self.terms.keys() {
            if mono_total_degree(k) > 1 {
                return None;
            }
        }
        // Find a variable with coefficient ±1.
        let mut chosen: Option<(SymbolId, Rational)> = None;
        for (k, &c) in &self.terms {
            if let [(v, 1)] = k.as_slice()
                && (c == Rational::integer(1) || c == Rational::integer(-1))
            {
                chosen = Some((*v, c));
                break;
            }
        }
        let (y, cy) = chosen?;
        // L = −(poly − cy·y) / cy. Build `poly` with the y-term removed, then
        // scale by `−1/cy`. Since cy = ±1, −1/cy = ∓1.
        let scale = cy.checked_neg()?; // −cy = ∓1 (because cy=±1 ⇒ −1/cy = −cy)
        let mut l = MultiPoly::zero();
        for (k, &c) in &self.terms {
            if k.as_slice() == [(y, 1)] {
                continue;
            }
            let nc = c.checked_mul(scale)?;
            l.add_term(k.clone(), nc)?;
        }
        // `L` must be y-free (it is, by construction) and linear (it is).
        Some((y, l))
    }

    /// Reduce a single-variable multivariate polynomial to the LSB-first integer
    /// polynomial layout the single-variable decider consumes. Requires exactly
    /// one variable. `None` on overflow / coefficient guard.
    fn to_single_var_integer_poly(&self, var: SymbolId) -> Option<Vec<i128>> {
        // Gather rational coefficients by exponent.
        let mut by_exp: BTreeMap<u32, Rational> = BTreeMap::new();
        let mut max_exp = 0u32;
        for (k, &c) in &self.terms {
            let exp = match k.as_slice() {
                [] => 0,
                [(v, e)] if *v == var => *e,
                _ => return None, // not single-variable in `var`
            };
            max_exp = max_exp.max(exp);
            let slot = by_exp.entry(exp).or_insert_with(Rational::zero);
            *slot = slot.checked_add(c)?;
        }
        if usize::try_from(max_exp).ok()? > MAX_DEGREE {
            return None;
        }
        let rat: Vec<Rational> = (0..=max_exp)
            .map(|e| by_exp.get(&e).copied().unwrap_or_else(Rational::zero))
            .collect();
        rat_coeffs_to_integer(&rat)
    }
}

/// Multiply two monomial keys, summing exponents. `None` on `u32` overflow.
fn mul_mono(a: &MonoKey, b: &MonoKey) -> Option<MonoKey> {
    let mut m: Monomial = BTreeMap::new();
    for &(v, e) in a.iter().chain(b.iter()) {
        let slot = m.entry(v).or_insert(0);
        *slot = slot.checked_add(e)?;
    }
    m.retain(|_, &mut e| e != 0);
    Some(mono_key(&m))
}

/// Total degree of a monomial key (sum of exponents).
fn mono_total_degree(k: &MonoKey) -> usize {
    k.iter().map(|&(_, e)| e as usize).sum()
}

/// Clear denominators of a LSB-first rational coefficient vector to an integer
/// polynomial (multiply by the positive LCM of denominators), mirroring
/// `RatPoly::to_integer_poly`. `None` on overflow / coefficient guard.
fn rat_coeffs_to_integer(coeffs: &[Rational]) -> Option<Vec<i128>> {
    let mut lcm = 1i128;
    for c in coeffs {
        lcm = lcm_i128(lcm, c.denominator())?;
    }
    let mut out = Vec::with_capacity(coeffs.len());
    for c in coeffs {
        let scaled = c.numerator().checked_mul(lcm)?;
        if scaled % c.denominator() != 0 {
            return None;
        }
        let v = scaled / c.denominator();
        if v.checked_abs()? >= MAX_ABS_COEFF {
            return None;
        }
        out.push(v);
    }
    while out.len() > 1 && *out.last().unwrap() == 0 {
        out.pop();
    }
    Some(out)
}

/// A multivariate atomic comparison `poly(vars) ⋈ 0`.
struct MultiAtom {
    cmp: Cmp,
    poly: MultiPoly,
}

/// Drive the sound multivariate decomposition. Returns `Some(Sat/Unsat)` only
/// when the query reduces (via linear substitution + single-variable
/// components) to a decision whose full model replays against every original
/// assertion; `None` declines on any coupling / nonlinear-multivariate /
/// non-polynomial / overflow shape.
fn decompose_multivariate(arena: &TermArena, assertions: &[TermId]) -> Option<CheckResult> {
    // 1. Re-collect every assertion as a multivariate comparison.
    let mut atoms: Vec<MultiAtom> = Vec::new();
    for &a in assertions {
        collect_multi_conjuncts(arena, a, &mut atoms)?;
    }
    if atoms.is_empty() {
        return None;
    }
    // Decide CONSTANT atoms directly. An atom whose polynomial has no variables
    // (e.g. a polynomial identity like `(x+y)² − (x²+2xy+y²)` collapses to `0`) is
    // a constant comparison `c ⋈ 0`: a FALSE one (`0 ≠ 0`, `0 < 0`, …) makes the
    // whole conjunction UNSAT — this is what *proves* a polynomial identity (its
    // negation reduces to `0 ≠ 0`); a TRUE one (`0 = 0`, `0 ≤ 0`, …) is dropped as
    // satisfied. This is exact (the constant is exact) and bypasses the abstraction
    // search entirely.
    let mut nonconstant: Vec<MultiAtom> = Vec::with_capacity(atoms.len());
    for atom in atoms {
        if let Some(c) = atom.poly.as_constant() {
            if !sign_satisfies(atom.cmp, Sign::of_rational(c)) {
                return Some(CheckResult::Unsat);
            }
            // true constant ⇒ satisfied, drop it.
        } else {
            nonconstant.push(atom);
        }
    }
    atoms = nonconstant;
    if atoms.is_empty() {
        // Every atom was a satisfied constant ⇒ trivially satisfiable; leave the
        // (variable-free) sat to the existing arithmetic path rather than fabricate
        // a model here.
        return None;
    }
    // Require at least two distinct variables overall — otherwise the single-var
    // path already owns this (and we must not double-handle / diverge).
    let all_vars: BTreeSet<SymbolId> = atoms.iter().flat_map(|a| a.poly.vars()).collect();
    if all_vars.len() < 2 {
        return None;
    }

    // 2. Substitution fixpoint. `subst[y] = L` records each eliminated variable's
    //    definition (in terms of the *remaining* variables at elimination time;
    //    back-substitution at the end resolves these to concrete values).
    let mut subst: Vec<(SymbolId, MultiPoly)> = Vec::new();
    for _ in 0..MAX_SUBST_ITERS {
        // Find an equality atom that defines a variable linearly.
        let mut found: Option<(usize, SymbolId, MultiPoly)> = None;
        for (i, atom) in atoms.iter().enumerate() {
            if matches!(atom.cmp, Cmp::Eq)
                && let Some((y, l)) = atom.poly.as_linear_definition()
            {
                found = Some((i, y, l));
                break;
            }
        }
        let Some((idx, y, l)) = found else { break };
        // Substitute `y := L` into every *other* atom; drop the defining atom.
        let mut next: Vec<MultiAtom> = Vec::with_capacity(atoms.len() - 1);
        for (i, atom) in atoms.iter().enumerate() {
            if i == idx {
                continue;
            }
            let poly = atom.poly.substitute(y, &l)?;
            next.push(MultiAtom {
                cmp: atom.cmp,
                poly,
            });
        }
        atoms = next;
        // Also rewrite earlier definitions that referenced `y` (so back-subst is
        // independent of evaluation order).
        for (_, def) in &mut subst {
            *def = def.substitute(y, &l)?;
        }
        subst.push((y, l));
        if atoms.is_empty() {
            break;
        }
    }

    // 3. Connected components over the remaining (post-substitution) atoms. A
    //    constant atom (no vars) is checked directly: false ⇒ Unsat, true ⇒ drop.
    let mut live: Vec<&MultiAtom> = Vec::new();
    for atom in &atoms {
        if atom.poly.vars().is_empty() {
            // Constant comparison: evaluate its sign exactly.
            let c = atom.poly.terms.get(&Vec::new()).copied();
            let val = c.unwrap_or_else(Rational::zero);
            let s = Sign::of_rational(val);
            if !sign_satisfies(atom.cmp, s) {
                return Some(CheckResult::Unsat);
            }
            // Tautology — contributes nothing.
        } else {
            live.push(atom);
        }
    }

    // Partition `live` atoms into connected components by shared variables.
    let components = connected_components(&live);

    // Decide each component (single-variable by the sign-cell decider, or a
    // two-variable coupled component by resultant elimination), assembling the
    // model. Any in-component `Unsat`/`Unknown` short-circuits the whole query.
    let mut model = Model::new();
    for comp in &components {
        match decide_component(comp)? {
            ComponentOutcome::Unsat => return Some(CheckResult::Unsat),
            ComponentOutcome::Unknown => {
                // Sound short-circuit (resultant slice committed but could not
                // certify): return `Unknown` rather than decline into a possibly
                // non-terminating NRA re-derivation of the same coupled system.
                return Some(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail: "nra: 2-variable resultant elimination could not certify \
                             (algebraic-x lift or inequality region)"
                        .to_string(),
                }));
            }
            ComponentOutcome::Sat(bindings) => {
                for (v, val) in bindings {
                    model.set(v, val);
                }
            }
        }
    }

    // 4. Back-substitute eliminated variables (reverse order). Each `y = L` with
    //    L in already-resolved variables; evaluate L under the current model.
    for (y, l) in subst.iter().rev() {
        let v = eval_multipoly_under_model(l, &model)?;
        model.set(*y, v);
    }

    // 5. Replay-check the full model against EVERY original assertion. The
    //    eliminated-variable definitions (`subst`) are applied back into each atom
    //    first, so a linear *defining* equation (which couples two algebraic vars,
    //    e.g. `y = −x` with both ±√2) collapses to an identity in the surviving
    //    component variable rather than needing algebraic field arithmetic.
    if !replay_multivariate(arena, assertions, &model, &subst) {
        return None;
    }
    Some(CheckResult::Sat(model))
}

// ============================================================================
// Two-variable resultant elimination (sound, bounded coupled-system slice).
// ============================================================================
//
// A connected component with **exactly two** variables {x, y} that is genuinely
// coupled (the substitution fixpoint already failed to break it). If at least
// two of its atoms are **equalities** `p(x,y)=0`, `q(x,y)=0` that both genuinely
// mention the eliminated variable, we eliminate one variable by the **Sylvester
// resultant** `Res_y(p, q)` — a univariate integer polynomial in x whose real
// roots are *exactly* the x-coordinates at which p and q share a y-root. Thus the
// isolated real roots of the resultant are an **exhaustive** set of x-candidates
// for the common solutions of the two equalities.
//
// Pipeline: **eliminate** (Sylvester determinant over `Rational`, overflow →
// decline) → **isolate** the resultant's real x-roots (reusing `isolate_roots`)
// → **lift** each *rational* x-candidate α by substituting x:=α into p and q
// (exact rational coefficients in y) and finding a common y-root (rational or a
// single algebraic number) → **replay-check** the full (x,y) model against EVERY
// original assertion.
//
// Soundness:
// - The resultant is exact (Sylvester determinant over `Rational`; any overflow
//   declines). `Res_y(p,q)(α) = 0 ⟺ p(α,·)` and `q(α,·)` share a y-root, so the
//   x-candidates miss no common solution of the two equalities.
// - Every `Sat` is replay-checked against all original assertions, so a spurious
//   candidate fails replay → never a wrong `Sat`.
// - `Unsat` is claimed **only** when the candidate enumeration is provably
//   exhaustive for the constraint shape: every atom in the component is an
//   equality (no inequality region could escape the common-root set) AND every
//   resultant root is rational (so the lift is complete). A real x-root that is
//   algebraic, or any inequality in the component, makes the enumeration possibly
//   incomplete ⇒ we **decline** rather than risk a wrong `Unsat`.
//   - The one exact exception: if the resultant has **no** real root at all, the
//     two equalities have no common real solution ⇒ the whole system is `Unsat`,
//     regardless of any inequalities (an empty equality variety stays empty).
// - No floating point; the Sylvester matrix is a fixed determinant and isolation
//   is bounded.

/// The outcome of deciding one connected component of the multivariate query.
enum ComponentOutcome {
    /// The component is unsatisfiable ⇒ the whole query is `Unsat`.
    Unsat,
    /// The component is satisfiable; these bindings extend the shared model.
    Sat(Vec<(SymbolId, Value)>),
    /// Sound short-circuit to `Unknown` (a committed-but-uncertifiable 2-var
    /// resultant component).
    Unknown,
}

/// Decide one connected component: a single-variable component via the sign-cell
/// decider, a two-variable coupled component via resultant elimination, anything
/// larger (≥ 3 vars) declines (`None`). The bindings it returns must still be
/// replay-checked against the full original query by the caller.
fn decide_component(comp: &[&MultiAtom]) -> Option<ComponentOutcome> {
    let comp_vars: BTreeSet<SymbolId> = comp.iter().flat_map(|a| a.poly.vars()).collect();
    if comp_vars.len() == 2 {
        // Two coupled variables: the resultant-elimination slice (≥ 2 equalities ⇒
        // eliminate one variable, isolate x-candidates, lift to y, replay-check).
        return Some(match decide_two_var_component(comp, &comp_vars)? {
            TwoVarVerdict::Unsat => ComponentOutcome::Unsat,
            TwoVarVerdict::Sat(b) => ComponentOutcome::Sat(b),
            TwoVarVerdict::Unknown => ComponentOutcome::Unknown,
        });
    }
    if comp_vars.len() != 1 {
        // ≥ 3 distinct variables that share a constraint ⇒ genuinely coupled
        // (the deferred CAD slice). Decline.
        return None;
    }
    let var = *comp_vars.iter().next().unwrap();
    // Convert this component's atoms to single-variable integer polynomials.
    let mut single_atoms: Vec<Atom> = Vec::with_capacity(comp.len());
    for atom in comp {
        let poly = atom.poly.to_single_var_integer_poly(var)?;
        if poly.len() <= 1 {
            // Degenerate (became constant after substitution): a single-variable
            // component should retain its variable; decline to stay safe.
            return None;
        }
        single_atoms.push(Atom {
            cmp: atom.cmp,
            poly,
        });
    }
    Some(match decide_system_value(&single_atoms)? {
        SystemVerdict::Unsat => ComponentOutcome::Unsat,
        SystemVerdict::Sat(v) => ComponentOutcome::Sat(vec![(var, v)]),
    })
}

/// The verdict of the two-variable resultant slice for one connected component.
enum TwoVarVerdict {
    /// The component is unsatisfiable (exhaustively, for its shape).
    Unsat,
    /// The component is satisfiable; bind these variables in the shared model.
    /// (Replay against the full original query happens once at the end.)
    Sat(Vec<(SymbolId, Value)>),
    /// Could not certify Sat or Unsat (an algebraic-x lift, or a real common root
    /// the inequalities could not be replay-confirmed against). A **sound**
    /// `Unknown` short-circuit: we have *committed* to the resultant slice
    /// (a ≥ 2-equality coupled component) and resolved the elimination, so handing
    /// the same nonlinear system to the outer NRA layer would only risk a
    /// (potentially non-terminating) re-derivation of the same indeterminacy.
    Unknown,
}

/// The outcome of lifting one x-candidate to a (keep, elim) witness.
enum LiftOutcome {
    /// A full-component-satisfying binding (replay-checked against every atom).
    Found(Vec<(SymbolId, Value)>),
    /// This x-candidate has no satisfying common y (sound — search continues).
    None,
    /// The lift could not be completed exactly (overflow): the candidate can be
    /// neither ruled in nor ruled out, so no `Unsat` may be claimed from it.
    Overflow,
}

/// Hard ceiling on the Sylvester matrix dimension (= `deg_y(p) + deg_y(q)`). The
/// determinant is computed by Leibniz permutation expansion (`dim!` terms over a
/// polynomial ring), so the cap keeps it bounded; beyond it we decline.
const MAX_SYLVESTER_DIM: usize = 6;

/// Decide a 2-variable coupled component by resultant elimination. Returns
/// `Some(verdict)` only for the in-scope shape (≥ 2 equalities, rational-x lifts,
/// replay-confirmed); `None` declines (region-only, algebraic-x lift, overflow,
/// no eliminable equality pair, any doubt).
fn decide_two_var_component(
    comp: &[&MultiAtom],
    comp_vars: &BTreeSet<SymbolId>,
) -> Option<TwoVarVerdict> {
    debug_assert_eq!(comp_vars.len(), 2);
    let mut vit = comp_vars.iter();
    let v0 = *vit.next().unwrap();
    let v1 = *vit.next().unwrap();

    // Gather the equality atoms of this component.
    let equalities: Vec<&MultiPoly> = comp
        .iter()
        .filter(|a| matches!(a.cmp, Cmp::Eq))
        .map(|a| &a.poly)
        .collect();
    if equalities.len() < 2 {
        // No eliminable equality pair (e.g. a region-only inequality system like
        // `x*y > 1 ∧ x > 0`): the satisfying set can be a 2-D region a resultant
        // cannot certify. Decline — the outer engine may still decide it.
        return None;
    }

    // Whether *every* atom in the component is an equality (no inequality region
    // can escape the common-root enumeration ⇒ a complete `Unsat` is possible).
    let all_equalities = comp.iter().all(|a| matches!(a.cmp, Cmp::Eq));

    // Try eliminating each variable. A definitive verdict (Sat / Unsat) from
    // either orientation wins immediately; otherwise we keep the weakest sound
    // outcome (`Unknown` if a resultant was computed but could not be certified;
    // `None`/decline if no orientation even had an eliminable pair).
    let mut soft: Option<TwoVarVerdict> = None;
    for &(elim, keep) in &[(v1, v0), (v0, v1)] {
        // Pick two equalities that both have positive degree in `elim` (so the
        // Sylvester matrix is well-formed and the elimination is meaningful).
        let mut pair: Option<(&MultiPoly, &MultiPoly)> = None;
        'outer: for i in 0..equalities.len() {
            if degree_in(equalities[i], elim) == 0 {
                continue;
            }
            for &q in equalities.iter().skip(i + 1) {
                if degree_in(q, elim) == 0 {
                    continue;
                }
                pair = Some((equalities[i], q));
                break 'outer;
            }
        }
        let Some((p, q)) = pair else { continue };

        // Eliminate `elim` → a univariate integer polynomial in `keep`.
        let Some(res_int) = resultant_univariate(p, q, elim, keep) else {
            // Overflow, dimension cap, or a degenerate (identically-zero)
            // resultant: this orientation cannot certify ⇒ remember `Unknown`,
            // try the other orientation.
            soft = Some(TwoVarVerdict::Unknown);
            continue;
        };
        if res_int.len() <= 1 {
            // The resultant collapsed to a constant. A *nonzero* constant means the
            // two equalities share no common root anywhere ⇒ Unsat. A zero constant
            // (every coefficient vanished) means a non-trivial common factor /
            // shared curve — we cannot enumerate that finitely ⇒ `Unknown`.
            if res_int.first().copied().unwrap_or(0) != 0 {
                return Some(TwoVarVerdict::Unsat);
            }
            soft = Some(TwoVarVerdict::Unknown);
            continue;
        }

        // Isolate the real x-roots of the resultant. These keep-variable values are
        // EXHAUSTIVE for the common (keep, elim) solutions of the two equalities.
        let Some(roots) = isolate_roots(&res_int) else {
            soft = Some(TwoVarVerdict::Unknown);
            continue;
        };

        if roots.is_empty() {
            // No real common x ⇒ the two equalities have no common real solution ⇒
            // the whole system is Unsat (exact: an empty equality variety stays
            // empty under any additional constraint).
            return Some(TwoVarVerdict::Unsat);
        }

        // Lift each candidate. We require RATIONAL x-candidates: an algebraic α
        // would make the substituted y-coefficients algebraic (field arithmetic,
        // deferred ⇒ skip that candidate). Track whether every candidate was a
        // clean rational lift, which is required to claim a complete `Unsat`.
        let mut all_rational_x = true;
        let mut lift_overflow = false;
        for root in &roots {
            let Root::Rational(alpha) = root else {
                all_rational_x = false;
                continue;
            };
            // Substitute keep := α into p and q ⇒ univariate polys in `elim`.
            match lift_candidate(comp, *alpha, keep, elim, p, q) {
                LiftOutcome::Found(bindings) => return Some(TwoVarVerdict::Sat(bindings)),
                LiftOutcome::None => {}
                LiftOutcome::Overflow => {
                    // Cannot rule the candidate in or out.
                    lift_overflow = true;
                }
            }
        }

        // No candidate produced a full-component-satisfying (keep, elim). This is a
        // complete enumeration ⇒ Unsat **only** when (a) the component is all
        // equalities (no inequality region can hide a solution outside the common
        // roots), (b) every x-candidate was a clean rational lift (no algebraic α
        // was skipped), and (c) no lift overflowed. Otherwise the enumeration is
        // not provably exhaustive ⇒ a sound `Unknown` short-circuit.
        if all_equalities && all_rational_x && !lift_overflow {
            return Some(TwoVarVerdict::Unsat);
        }
        soft = Some(TwoVarVerdict::Unknown);
    }

    // Either an orientation computed a resultant but could not certify (`soft`
    // holds `Unknown`), or no orientation even had an eliminable equality pair
    // (`soft` is `None` ⇒ decline back to the outer engine).
    soft
}

/// Substitute `keep := α` (rational) into `p` and `q`, then find a common root of
/// the two resulting univariate polynomials in `elim`. For each candidate root β
/// (rational or a single algebraic number), assemble the model `{keep→α, elim→β}`
/// and check it against **every** atom of the component. Returns `Some(Some(..))`
/// on the first satisfying binding, `Some(None)` if none of this α's β candidates
/// satisfy the component, `None` to decline (overflow / unsupported shape).
fn lift_candidate(
    comp: &[&MultiAtom],
    alpha: Rational,
    keep: SymbolId,
    elim: SymbolId,
    p: &MultiPoly,
    q: &MultiPoly,
) -> LiftOutcome {
    let mut subst: BTreeMap<SymbolId, Rational> = BTreeMap::new();
    subst.insert(keep, alpha);
    // p(α, elim) and q(α, elim) as single-variable integer polynomials in `elim`.
    let Some(p_alpha) = substitute_rationals(p, &subst) else {
        return LiftOutcome::Overflow;
    };
    let Some(q_alpha) = substitute_rationals(q, &subst) else {
        return LiftOutcome::Overflow;
    };
    let Some(p_poly) = p_alpha.to_single_var_integer_poly(elim) else {
        return LiftOutcome::Overflow;
    };
    let Some(q_poly) = q_alpha.to_single_var_integer_poly(elim) else {
        return LiftOutcome::Overflow;
    };
    // A degenerate (constant) residual after substitution means the resultant root
    // did not actually pin a y via this polynomial; require genuine univariate
    // polys so the common-root search is well-defined.
    if p_poly.len() <= 1 && q_poly.len() <= 1 {
        return LiftOutcome::None;
    }

    // Candidate β values: the real roots of p(α,·) (or q(α,·) if p degenerated).
    let base_poly = if p_poly.len() > 1 { &p_poly } else { &q_poly };
    let other_poly = if p_poly.len() > 1 { &q_poly } else { &p_poly };
    let Some(beta_roots) = isolate_roots(base_poly) else {
        return LiftOutcome::Overflow;
    };

    for broot in &beta_roots {
        // β must also be a root of the *other* equality (the common solution).
        let beta_val = match broot {
            Root::Rational(b) => {
                // Check the other equality vanishes at β (if it is non-constant).
                if other_poly.len() > 1 {
                    match eval_rat(other_poly, *b) {
                        Some(v) if !v.is_zero() => continue,
                        Some(_) => {}
                        None => return LiftOutcome::Overflow,
                    }
                }
                Value::Real(*b)
            }
            Root::Algebraic(a) => {
                // The other equality must vanish at this algebraic β.
                if other_poly.len() > 1 {
                    match a.sign_at(other_poly) {
                        Some(Sign::Zero) => {}
                        Some(_) => continue,
                        None => return LiftOutcome::Overflow,
                    }
                }
                Value::RealAlgebraic(a.clone())
            }
        };

        // Build the candidate component model and check it against EVERY atom of
        // the component (equalities and any inequalities), exactly.
        let mut model = Model::new();
        model.set(keep, Value::Real(alpha));
        model.set(elim, beta_val.clone());
        if two_var_model_satisfies(comp, &model) {
            return LiftOutcome::Found(vec![(keep, Value::Real(alpha)), (elim, beta_val)]);
        }
    }
    LiftOutcome::None
}

/// Exact check that the (at most two-variable) `model` satisfies every atom of the
/// component, reusing the algebraic-aware single-atom replay. Returns `false` on
/// any failure or unsupported shape (the caller then keeps searching / declines).
fn two_var_model_satisfies(comp: &[&MultiAtom], model: &Model) -> bool {
    comp.iter().all(|atom| {
        let ma = MultiAtom {
            cmp: atom.cmp,
            poly: atom.poly.clone(),
        };
        replay_multi_atom(&ma, model)
    })
}

/// The degree of a [`MultiPoly`] in one variable `v` (highest exponent of `v`
/// across its monomials; 0 if `v` does not appear).
fn degree_in(p: &MultiPoly, v: SymbolId) -> u32 {
    let mut d = 0u32;
    for k in p.terms.keys() {
        for &(s, e) in k {
            if s == v {
                d = d.max(e);
            }
        }
    }
    d
}

/// View the bivariate `p` as a univariate polynomial in `elim` whose coefficients
/// are univariate **rational** polynomials in `keep` (LSB-first). The outer `Vec`
/// is indexed by the exponent of `elim`; each inner `Vec<Rational>` is LSB-first
/// in `keep`. Returns `None` if `p` mentions any variable other than {elim, keep}
/// or on a degree overflow.
fn poly_in_elim_over_keep(
    p: &MultiPoly,
    elim: SymbolId,
    keep: SymbolId,
) -> Option<Vec<Vec<Rational>>> {
    let dy = usize::try_from(degree_in(p, elim)).ok()?;
    let dx = usize::try_from(degree_in(p, keep)).ok()?;
    let mut out: Vec<Vec<Rational>> = vec![vec![Rational::zero(); dx + 1]; dy + 1];
    for (k, &c) in &p.terms {
        let mut ey = 0u32;
        let mut ex = 0u32;
        for &(s, e) in k {
            if s == elim {
                ey = e;
            } else if s == keep {
                ex = e;
            } else {
                return None; // foreign variable
            }
        }
        let iy = usize::try_from(ey).ok()?;
        let ix = usize::try_from(ex).ok()?;
        out[iy][ix] = out[iy][ix].checked_add(c)?;
    }
    Some(out)
}

/// Multiply two LSB-first rational univariate polynomials. `None` on overflow.
fn ratpoly_mul(a: &[Rational], b: &[Rational]) -> Option<Vec<Rational>> {
    if a.is_empty() || b.is_empty() {
        return Some(vec![Rational::zero()]);
    }
    let mut out = vec![Rational::zero(); a.len() + b.len() - 1];
    for (i, &ca) in a.iter().enumerate() {
        if ca.is_zero() {
            continue;
        }
        for (j, &cb) in b.iter().enumerate() {
            let term = ca.checked_mul(cb)?;
            out[i + j] = out[i + j].checked_add(term)?;
        }
    }
    Some(out)
}

/// Add two LSB-first rational univariate polynomials. `None` on overflow.
fn ratpoly_add(a: &[Rational], b: &[Rational]) -> Option<Vec<Rational>> {
    let n = a.len().max(b.len());
    let mut out = vec![Rational::zero(); n];
    for (i, slot) in out.iter_mut().enumerate() {
        let ca = a.get(i).copied().unwrap_or_else(Rational::zero);
        let cb = b.get(i).copied().unwrap_or_else(Rational::zero);
        *slot = ca.checked_add(cb)?;
    }
    Some(out)
}

/// Negate an LSB-first rational univariate polynomial. `None` on overflow.
fn ratpoly_neg(a: &[Rational]) -> Option<Vec<Rational>> {
    let mut out = Vec::with_capacity(a.len());
    for &c in a {
        out.push(c.checked_neg()?);
    }
    Some(out)
}

/// `Res_elim(p, q)` as a univariate **integer** polynomial in `keep`, by the
/// Sylvester determinant. Entries are univariate rational polynomials in `keep`;
/// the determinant is computed by Leibniz permutation expansion over that
/// polynomial ring (exact, bounded by `MAX_SYLVESTER_DIM`). Denominators are then
/// cleared to integers (LSB-first). Returns `None` on a foreign variable, a
/// dimension over the cap, an identically-zero resultant, or any overflow.
fn resultant_univariate(
    p: &MultiPoly,
    q: &MultiPoly,
    elim: SymbolId,
    keep: SymbolId,
) -> Option<Vec<i128>> {
    let pc = poly_in_elim_over_keep(p, elim, keep)?;
    let qc = poly_in_elim_over_keep(q, elim, keep)?;
    let m = pc.len() - 1; // deg_elim(p)
    let n = qc.len() - 1; // deg_elim(q)
    if m == 0 || n == 0 {
        return None; // not genuinely bivariate in `elim`; cannot eliminate
    }
    let dim = m + n;
    if dim > MAX_SYLVESTER_DIM {
        return None;
    }
    // Build the (m+n)×(m+n) Sylvester matrix. Rows 0..n are shifted copies of p's
    // coefficient row (highest elim-degree first); rows n..n+m are shifted copies
    // of q's. Each cell is an LSB-first rational polynomial in `keep`.
    let zero_cell = || vec![Rational::zero()];
    let mut mat: Vec<Vec<Vec<Rational>>> = vec![vec![zero_cell(); dim]; dim];
    // p's coefficients, MSB(elim)-first: index 0 ↔ elim^m.
    for (row, slot) in mat.iter_mut().take(n).enumerate() {
        for (j, coeff) in pc.iter().rev().enumerate() {
            slot[row + j].clone_from(coeff);
        }
    }
    for (i, slot) in mat.iter_mut().skip(n).take(m).enumerate() {
        for (j, coeff) in qc.iter().rev().enumerate() {
            slot[i + j].clone_from(coeff);
        }
    }

    // Determinant by Leibniz expansion over permutations (dim ≤ MAX_SYLVESTER_DIM).
    let det = sylvester_determinant(&mat)?;
    // Clear denominators → integer poly. A genuinely-zero determinant declines.
    if det.iter().all(|c| c.is_zero()) {
        return None;
    }
    rat_coeffs_to_integer(&det)
}

/// Determinant of a square matrix whose entries are LSB-first rational univariate
/// polynomials, by Leibniz permutation expansion (exact; bounded dimension).
/// Returns the determinant polynomial (LSB-first). `None` on overflow.
fn sylvester_determinant(mat: &[Vec<Vec<Rational>>]) -> Option<Vec<Rational>> {
    let n = mat.len();
    let mut perm: Vec<usize> = (0..n).collect();
    let mut acc = vec![Rational::zero()];
    let mut used = vec![false; n];
    leibniz_recurse(mat, &mut perm, 0, &mut used, &mut acc)?;
    Some(acc)
}

/// One step of the Leibniz determinant expansion: choose the row for column `col`,
/// recurse, and at a complete permutation accumulate the signed entry product (the
/// sign from inversion parity). `None` on any polynomial-arithmetic overflow.
fn leibniz_recurse(
    mat: &[Vec<Vec<Rational>>],
    perm: &mut [usize],
    col: usize,
    used: &mut [bool],
    acc: &mut Vec<Rational>,
) -> Option<()> {
    let n = mat.len();
    if col == n {
        let mut prod = vec![Rational::integer(1)];
        for (i, &c) in perm.iter().enumerate() {
            prod = ratpoly_mul(&prod, &mat[i][c])?;
        }
        if permutation_sign(perm) < 0 {
            prod = ratpoly_neg(&prod)?;
        }
        *acc = ratpoly_add(acc, &prod)?;
        return Some(());
    }
    for r in 0..n {
        if used[r] {
            continue;
        }
        used[r] = true;
        perm[col] = r;
        leibniz_recurse(mat, perm, col + 1, used, acc)?;
        used[r] = false;
    }
    Some(())
}

/// The sign (+1 / −1) of a permutation given as a slice mapping position → value,
/// by counting inversions.
fn permutation_sign(perm: &[usize]) -> i32 {
    let mut inv = 0usize;
    for i in 0..perm.len() {
        for j in (i + 1)..perm.len() {
            if perm[i] > perm[j] {
                inv += 1;
            }
        }
    }
    if inv % 2 == 0 { 1 } else { -1 }
}

/// Union-find root with path-halving.
fn uf_find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

/// Connected components of `atoms` under the "share a variable" relation,
/// returned as groups of atom references (deterministic order).
fn connected_components<'a>(atoms: &[&'a MultiAtom]) -> Vec<Vec<&'a MultiAtom>> {
    let n = atoms.len();
    let mut parent: Vec<usize> = (0..n).collect();
    // Union atoms that share any variable.
    let var_sets: Vec<BTreeSet<SymbolId>> = atoms.iter().map(|a| a.poly.vars()).collect();
    for i in 0..n {
        for j in (i + 1)..n {
            if !var_sets[i].is_disjoint(&var_sets[j]) {
                let ri = uf_find(&mut parent, i);
                let rj = uf_find(&mut parent, j);
                if ri != rj {
                    parent[ri] = rj;
                }
            }
        }
    }
    // Group by root, preserving first-appearance order for determinism.
    let mut order: Vec<usize> = Vec::new();
    let mut groups: BTreeMap<usize, Vec<&MultiAtom>> = BTreeMap::new();
    for (i, atom) in atoms.iter().enumerate() {
        let r = uf_find(&mut parent, i);
        if !groups.contains_key(&r) {
            order.push(r);
        }
        groups.entry(r).or_default().push(atom);
    }
    order
        .into_iter()
        .map(|r| groups.remove(&r).unwrap())
        .collect()
}

/// Evaluate a multivariate polynomial under a model that binds every variable
/// it mentions to a concrete [`Value`] (rational or algebraic). Returns the
/// resulting value. `None` on overflow, an unbound variable, or a case that
/// would require multiplying two *distinct* algebraic values (the deferred
/// field-arithmetic case).
fn eval_multipoly_under_model(p: &MultiPoly, model: &Model) -> Option<Value> {
    // Partition variables into rational-valued and algebraic-valued.
    let vars = p.vars();
    let mut rationals: BTreeMap<SymbolId, Rational> = BTreeMap::new();
    let mut algebraic: Option<SymbolId> = None;
    for v in &vars {
        match model.get(*v)? {
            Value::Real(q) => {
                rationals.insert(*v, q);
            }
            Value::RealAlgebraic(_) => {
                if algebraic.is_some() && algebraic != Some(*v) {
                    // Two distinct algebraic variables in one polynomial: the
                    // deferred algebraic-product case. Decline.
                    return None;
                }
                algebraic = Some(*v);
            }
            _ => return None,
        }
    }

    match algebraic {
        None => {
            // Fully rational: evaluate exactly.
            let q = eval_multipoly_rational(p, &rationals)?;
            Some(Value::Real(q))
        }
        Some(av) => {
            // Substitute the rational variables, leaving a single-variable
            // polynomial in `av`. If the residual is constant, the value is that
            // rational; if it is *affine* in `av` (`a·av + b`, a ≠ 0) we build the
            // exact derived algebraic value by an affine transform of `av`'s
            // defining polynomial and isolating interval (sound: it is one
            // algebraic number mapped through an affine map, not a product of two
            // distinct algebraic numbers). Anything higher-degree in `av` would
            // need genuine algebraic field arithmetic — decline.
            let alg = model.get(av)?.as_real_algebraic()?.clone();
            let residual = substitute_rationals(p, &rationals)?; // single-var in `av`
            classify_residual(&residual, av, &alg)
        }
    }
}

/// Evaluate a fully-rational multivariate polynomial. `None` on overflow.
fn eval_multipoly_rational(p: &MultiPoly, vals: &BTreeMap<SymbolId, Rational>) -> Option<Rational> {
    let mut acc = Rational::zero();
    for (k, &c) in &p.terms {
        let mut term = c;
        for &(v, e) in k {
            let base = *vals.get(&v)?;
            for _ in 0..e {
                term = term.checked_mul(base)?;
            }
        }
        acc = acc.checked_add(term)?;
    }
    Some(acc)
}

/// Substitute the rational-valued variables into `p`, returning a polynomial in
/// the remaining (algebraic) variable(s). `None` on overflow.
fn substitute_rationals(p: &MultiPoly, vals: &BTreeMap<SymbolId, Rational>) -> Option<MultiPoly> {
    let mut out = p.clone();
    for (&v, &q) in vals {
        out = out.substitute(v, &MultiPoly::constant(q))?;
    }
    Some(out)
}

/// Classify a residual single-variable polynomial (in `av`, whose value is the
/// algebraic number `alg`) into the value it denotes, for the shapes slice 1 can
/// represent exactly without algebraic *field* arithmetic:
///
/// - a constant → that rational;
/// - an **affine** form `a·av + b` (a ≠ 0) → the exact derived algebraic value
///   obtained by affine-transforming `alg` (sound: an affine image of a single
///   algebraic number, not a product/sum of two distinct algebraic numbers).
///   A degenerate affine image that lands on a rational (only possible if `alg`
///   were rational, which it is not) does not arise.
///
/// Anything of degree ≥ 2 in `av` declines (it would need field arithmetic).
fn classify_residual(residual: &MultiPoly, av: SymbolId, alg: &RealAlgebraic) -> Option<Value> {
    if residual.is_zero() {
        return Some(Value::Real(Rational::zero()));
    }
    // Constant?
    if residual.vars().is_empty() {
        let q = residual.terms.get(&Vec::new()).copied()?;
        return Some(Value::Real(q));
    }
    // Extract the affine coefficients: residual = a·av + b, rejecting any term of
    // degree ≥ 2 or in any other variable.
    let mut a = Rational::zero();
    let mut b = Rational::zero();
    for (k, &c) in &residual.terms {
        match k.as_slice() {
            [] => b = c,
            [(v, 1)] if *v == av => a = c,
            _ => return None, // nonlinear or foreign variable
        }
    }
    if a.is_zero() {
        return None;
    }
    // Build the affine image y = a·α + b as an exact algebraic number.
    affine_algebraic(alg, a, b).map(Value::RealAlgebraic)
}

/// The exact algebraic number `y = a·α + b` (`a ≠ 0`) given `α` as a
/// [`RealAlgebraic`]. If `α` is the unique root of `p(t)` in `(lo, hi)`, then `y`
/// is the unique root of `p((t − b)/a)` (denominators cleared to integers) in the
/// affine-mapped interval `(a·lo + b, a·hi + b)` (endpoints swapped when `a < 0`).
/// `None` on any overflow / coefficient-guard trip.
fn affine_algebraic(alpha: &RealAlgebraic, a: Rational, b: Rational) -> Option<RealAlgebraic> {
    // q(t) = p((t − b)/a): substitute the linear argument `(t − b)/a` into p.
    // Represent p as a single-variable MultiPoly over a placeholder, then compose
    // with the linear map, then integer-clear.
    let p = alpha.defining_poly();
    // arg(t) = (1/a)·t + (−b/a).
    let inv_a = Rational::integer(1).checked_div(a)?;
    let neg_b_over_a = b.checked_neg()?.checked_div(a)?;
    // Horner-compose: q = (((pₙ·arg + pₙ₋₁)·arg + …)·arg + p₀), as rational coeffs
    // in `t` (LSB-first), where `arg = inv_a·t + neg_b_over_a`.
    let mut acc: Vec<Rational> = vec![Rational::zero()];
    for &c in p.iter().rev() {
        // acc := acc * arg + c.
        acc = poly_mul_linear(&acc, inv_a, neg_b_over_a)?;
        acc[0] = acc[0].checked_add(Rational::integer(c))?;
    }
    let qpoly = rat_coeffs_to_integer(&acc)?;
    // Map the isolating interval.
    let (lo, hi) = alpha.interval();
    let mlo = a.checked_mul(lo)?.checked_add(b)?;
    let mhi = a.checked_mul(hi)?.checked_add(b)?;
    let (nlo, nhi) = if mlo.checked_cmp(&mhi)? == Ordering::Less {
        (mlo, mhi)
    } else {
        (mhi, mlo)
    };
    RealAlgebraic::new(qpoly, nlo, nhi)
}

/// Multiply an LSB-first rational polynomial `acc` by the linear `(m·t + k)`,
/// returning the product coefficients. `None` on overflow.
fn poly_mul_linear(acc: &[Rational], m: Rational, k: Rational) -> Option<Vec<Rational>> {
    let mut out = vec![Rational::zero(); acc.len() + 1];
    for (i, &c) in acc.iter().enumerate() {
        // c·t^i · (m·t + k) = (c·m)·t^{i+1} + (c·k)·t^i.
        let cm = c.checked_mul(m)?;
        let ck = c.checked_mul(k)?;
        out[i + 1] = out[i + 1].checked_add(cm)?;
        out[i] = out[i].checked_add(ck)?;
    }
    Some(out)
}

/// Replay the assembled full model against every original assertion. Rational
/// vars evaluate through the ground evaluator; an assertion that mentions the
/// (at most one, after applying the eliminated-variable definitions `subst`)
/// algebraic var is checked by exact polynomial sign evaluation.
///
/// Each eliminated variable's definition `y = L` is substituted back into every
/// atom before checking. This is exactly the same algebra used to build the
/// model, so it cannot introduce error, and it guarantees no atom retains more
/// than the single component algebraic variable — sidestepping algebraic field
/// arithmetic. Returns `false` on any failure, indeterminate sign, or
/// unsupported shape (the caller then declines — never a wrong `Sat`).
fn replay_multivariate(
    arena: &TermArena,
    assertions: &[TermId],
    model: &Model,
    subst: &[(SymbolId, MultiPoly)],
) -> bool {
    // Does the model bind any variable to an algebraic value?
    let has_algebraic = model_has_algebraic(model);
    if !has_algebraic {
        // Pure-rational model: the ground evaluator decides every assertion.
        let asg = model.to_assignment();
        return assertions
            .iter()
            .all(|&a| matches!(eval(arena, a, &asg), Ok(Value::Bool(true))));
    }
    // The model has algebraic variables. Re-collect the (multivariate) atoms,
    // apply the back-substitutions (so a defining equation coupling two algebraic
    // vars collapses to its surviving component variable), and check each exactly.
    let mut atoms: Vec<MultiAtom> = Vec::new();
    for &a in assertions {
        if collect_multi_conjuncts(arena, a, &mut atoms).is_none() {
            return false;
        }
    }
    for atom in &atoms {
        // Apply every elimination definition, in elimination order, into the atom.
        let mut poly = atom.poly.clone();
        for (y, l) in subst {
            let Some(next) = poly.substitute(*y, l) else {
                return false;
            };
            poly = next;
        }
        let reduced = MultiAtom {
            cmp: atom.cmp,
            poly,
        };
        if !replay_multi_atom(&reduced, model) {
            return false;
        }
    }
    true
}

/// Whether the model binds at least one variable to an algebraic value.
fn model_has_algebraic(model: &Model) -> bool {
    model
        .iter()
        .any(|(_, v)| matches!(v, Value::RealAlgebraic(_)))
}

/// Exact replay of one multivariate atom `poly ⋈ 0` under a model. Rational
/// vars are substituted; the residual must be constant (→ rational sign) or
/// single-variable in one algebraic var (→ `sign_at`). Two distinct algebraic
/// vars in one atom ⇒ `false` (decline). Returns `true` iff the comparison holds.
fn replay_multi_atom(atom: &MultiAtom, model: &Model) -> bool {
    // Collect the rational bindings for this atom's variables; detect a sole
    // algebraic variable.
    let vars = atom.poly.vars();
    let mut rationals: BTreeMap<SymbolId, Rational> = BTreeMap::new();
    let mut algebraic: Option<SymbolId> = None;
    for v in &vars {
        match model.get(*v) {
            Some(Value::Real(q)) => {
                rationals.insert(*v, q);
            }
            Some(Value::RealAlgebraic(_)) => {
                if algebraic.is_some() {
                    return false; // two algebraic vars in one atom: decline
                }
                algebraic = Some(*v);
            }
            _ => return false,
        }
    }
    let Some(residual) = substitute_rationals(&atom.poly, &rationals) else {
        return false;
    };
    match algebraic {
        None => {
            // Constant residual: check the comparison directly.
            let q = residual
                .terms
                .get(&Vec::new())
                .copied()
                .unwrap_or_else(Rational::zero);
            sign_satisfies(atom.cmp, Sign::of_rational(q))
        }
        Some(av) => {
            // Single-variable residual in `av`: integer-clear and use `sign_at`.
            let Some(alg) = model.get(av).and_then(|v| v.as_real_algebraic().cloned()) else {
                return false;
            };
            let Some(ipoly) = residual.to_single_var_integer_poly(av) else {
                return false;
            };
            match alg.sign_at(&ipoly) {
                Some(s) => sign_satisfies(atom.cmp, s),
                None => false,
            }
        }
    }
}

/// Multivariate analogue of [`collect_conjuncts`]: flatten a Boolean assertion
/// into multivariate polynomial comparisons, **allowing multiple variables**.
/// Declines (`None`) on any non-conjunctive structure or non-polynomial atom.
fn collect_multi_conjuncts(
    arena: &TermArena,
    assertion: TermId,
    atoms: &mut Vec<MultiAtom>,
) -> Option<()> {
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(assertion)
    {
        for &c in args {
            collect_multi_conjuncts(arena, c, atoms)?;
        }
        return Some(());
    }
    let (cmp, poly) = match_multi_constraint(arena, assertion)?;
    atoms.push(MultiAtom { cmp, poly });
    Some(())
}

/// Multivariate analogue of [`match_real_poly_constraint`]: a real comparison
/// whose `lhs − rhs` collects to a multivariate polynomial.
fn match_multi_constraint(arena: &TermArena, assertion: TermId) -> Option<(Cmp, MultiPoly)> {
    let TermNode::App { op, args } = arena.node(assertion) else {
        return None;
    };
    if matches!(op, Op::BoolNot) {
        let inner = args[0];
        let TermNode::App {
            op: Op::Eq,
            args: eq_args,
        } = arena.node(inner)
        else {
            return None;
        };
        if arena.sort_of(eq_args[0]) != Sort::Real {
            return None;
        }
        let poly = collect_multi_diff(arena, eq_args[0], eq_args[1])?;
        return Some((Cmp::Ne, poly));
    }
    let cmp = match op {
        Op::Eq => Cmp::Eq,
        Op::RealLt => Cmp::Lt,
        Op::RealLe => Cmp::Le,
        Op::RealGt => Cmp::Gt,
        Op::RealGe => Cmp::Ge,
        _ => return None,
    };
    if matches!(op, Op::Eq) && arena.sort_of(args[0]) != Sort::Real {
        return None;
    }
    let poly = collect_multi_diff(arena, args[0], args[1])?;
    Some((cmp, poly))
}

fn collect_multi_diff(arena: &TermArena, lhs: TermId, rhs: TermId) -> Option<MultiPoly> {
    let l = collect_multi(arena, lhs)?;
    let r = collect_multi(arena, rhs)?;
    l.sub(&r)
}

/// Recursively collect a `Real`-sorted term into a multivariate rational
/// polynomial over `{+, −, ·, neg, RealConst, symbol}`. Anything else declines.
fn collect_multi(arena: &TermArena, t: TermId) -> Option<MultiPoly> {
    if arena.sort_of(t) != Sort::Real {
        return None;
    }
    match arena.node(t) {
        TermNode::RealConst(r) => Some(MultiPoly::constant(*r)),
        TermNode::Symbol(s) => Some(MultiPoly::var(*s)),
        TermNode::App { op, args } => match op {
            Op::RealNeg if args.len() == 1 => collect_multi(arena, args[0])?.neg(),
            Op::RealAdd if args.len() == 2 => {
                collect_multi(arena, args[0])?.add(&collect_multi(arena, args[1])?)
            }
            Op::RealSub if args.len() == 2 => {
                collect_multi(arena, args[0])?.sub(&collect_multi(arena, args[1])?)
            }
            Op::RealMul if args.len() == 2 => {
                collect_multi(arena, args[0])?.mul(&collect_multi(arena, args[1])?)
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
