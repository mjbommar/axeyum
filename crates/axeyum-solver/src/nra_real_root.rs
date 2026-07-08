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
use std::time::Instant;

use axeyum_ir::{
    Assignment, Op, Rational, RealAlgebraic, Sign, Sort, SymbolId, TermArena, TermId, TermNode,
    Value, eval,
};

use crate::backend::{CheckResult, SolverError, UnknownKind, UnknownReason};
use crate::model::Model;

/// Whether the shared wall-clock `deadline` (if any) has passed.
///
/// The sign-cell / decomposition decision below is otherwise a single un-clocked
/// computation — on a large lazy-SMT cube (100+ polynomial atoms) its root
/// isolation and cell enumeration can run many seconds past a configured budget
/// with no interception point. Polling this at the head of each expensive loop
/// lets the decision bail near the budget with a timely `Unknown` instead of
/// overrunning it. A poll that fires only turns a would-be-slow decision into
/// `Unknown`; it never changes a `sat`/`unsat` verdict, so it is soundness-neutral
/// (and, because a poll only fires when the clock is actually exhausted, it is
/// behavior-identical for any caller with a generous / absent timeout).
fn deadline_reached(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|d| Instant::now() >= d)
}

/// The `Unknown` returned when a decision loop bails at [`deadline_reached`].
fn cad_timeout_unknown() -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::ResourceLimit,
        detail: "nra sign-cell decomposition: wall-clock timeout reached".to_owned(),
    })
}

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
        self.to_integer_poly_bounded(MAX_ABS_COEFF)
    }

    /// As [`RatPoly::to_integer_poly`] but with the coefficient-magnitude guard
    /// left at the natural `i128` overflow bound (`max_abs_coeff = i128::MAX`).
    /// Used by the **equality-anchored** bignum-aware fallback
    /// ([`decide_anchored`]), which never isolates the roots of a big-coefficient
    /// atom (only *evaluates* its sign at an already-isolated anchor root, exactly
    /// and in bignum via [`RealAlgebraic::sign_at`]), so the tight rational
    /// coefficients of e.g. `approx-sqrt` no longer force a decline. Still returns
    /// `None` on a genuine `i128` overflow (denominators that do not fit — the
    /// caller declines soundly).
    fn to_integer_poly_unguarded(&self) -> Option<Vec<i128>> {
        // Clear denominators with a **bignum intermediate** so a large-denominator
        // coefficient (e.g. the 28-digit `approx-sqrt-unsat` rational) does not
        // overflow the i128 `numerator × lcm` product even when the *result*
        // coefficients fit i128. Only the result must fit i128 (root isolation is
        // never run on these polynomials — only exact bignum sign evaluation).
        axeyum_ir::poly::rat_to_int_poly_wide(&self.coeffs, i128::MAX)
    }

    /// Shared clearing routine: multiply through by the LCM of all denominators to
    /// obtain an integer polynomial (LSB-first), declining (`None`) on `i128`
    /// overflow or a coefficient reaching `max_abs_coeff`. The multiplier is
    /// positive, so it preserves every comparison `p ⋈ 0`.
    fn to_integer_poly_bounded(&self, max_abs_coeff: i128) -> Option<Vec<i128>> {
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
            if v.checked_abs()? >= max_abs_coeff {
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
    deadline: Option<Instant>,
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
        return Ok(decide_system(arena, assertions, var, &atoms, deadline));
    }

    // The single-variable collector declined. If that decline was because an atom's
    // **tight/large rational coefficient** exceeded the `i128` `MAX_ABS_COEFF` entry
    // guard (not a structural decline), try the **equality-anchored** fallback: the
    // conjunction contains an equality `p_eq(x) = 0`, so every model pins `x` to a
    // root of `p_eq`; isolate only those (small-coefficient) roots and test *all*
    // atoms — including the big-coefficient ones — by exact `sign_at` (which lifts
    // to bignum internally). This decides the algebraic-√2 rows (`approx-sqrt`)
    // without ever isolating a big-coefficient polynomial.
    if let Some(res) = decide_anchored(arena, assertions) {
        return Ok(Some(res));
    }

    // The single-variable collector declined (most often because a *second*
    // distinct variable appears). Try the sound, bounded **multivariate
    // decomposition** path (linear-substitution fixpoint + connected components
    // of single-variable sub-systems). It declines (`None`) on any genuinely
    // coupled / nonlinear-multivariate / non-polynomial / overflow shape, leaving
    // the query to the NRA layer.
    Ok(decompose_multivariate(arena, assertions, deadline))
}

/// Equality-anchored decision for a single-variable polynomial conjunction whose
/// tight/large rational coefficients exceed the `i128` `MAX_ABS_COEFF` CAD-entry
/// guard (e.g. `approx-sqrt`: `x²=2 ∧ x>0 ∧` three 13-digit-coefficient strict
/// inequalities).
///
/// **Soundness / completeness.** The conjunction contains an equality atom
/// `p_eq(x) = 0`. Any satisfying assignment makes `p_eq(x)` vanish, so the witness
/// set is a *subset of the real roots of `p_eq`*. We isolate **every** real root of
/// `p_eq` (exactly, via [`isolate_roots`] — Sturm/grid, exhaustive or `None` →
/// decline) and test each root against **all** atoms by exact sign evaluation
/// ([`rational_satisfies_all`] for a rational root, [`algebraic_satisfies_all`]'s
/// `sign_at` for an algebraic root — the latter evaluates the big-coefficient
/// polynomials in bignum, exactly). A root that satisfies every atom → **Sat**
/// (replay-checked against the original assertions / re-checked by `sign_at`); no
/// root satisfying every atom → **Unsat** (complete: cell interiors between the
/// roots cannot satisfy the equality). Any unresolved sign / overflow / ordering →
/// `None` (decline), never a guessed verdict.
///
/// This never isolates the roots of a big-coefficient atom, so the `i128`
/// `MAX_ABS_COEFF` guard on root isolation is not exercised for those atoms; only
/// the small-coefficient anchor equality is isolated.
/// Collect the equality-anchor polynomials of a conjunction: every `Cmp::Eq`
/// atom's polynomial, plus every polynomial `p` that appears as a **pinning pair**
/// `p ≤ 0 ∧ p ≥ 0` (the two order atoms the DPLL abstractor emits for `a = b`).
/// Each anchor forces `p(x) = 0`, so a satisfying `x` is a root of it. Comparison
/// is up to sign (`p` and `−p` denote the same zero-set); the returned polynomials
/// are as stored (LSB-first, integer-cleared).
fn anchor_polys(atoms: &[Atom]) -> Vec<Vec<i128>> {
    let mut out: Vec<Vec<i128>> = Vec::new();
    // Explicit equalities.
    for atom in atoms {
        if matches!(atom.cmp, Cmp::Eq) {
            out.push(atom.poly.clone());
        }
    }
    // Pinning pairs `p ≤ 0 ∧ p ≥ 0` (non-strict only — a strict pair `p < 0 ∧ p > 0`
    // is contradictory, not an equality). Match `p` against `p'` up to a positive
    // scaling / sign flip via [`same_zero_set`].
    for (i, ai) in atoms.iter().enumerate() {
        if !matches!(ai.cmp, Cmp::Le) {
            continue;
        }
        for aj in &atoms[i + 1..] {
            if matches!(aj.cmp, Cmp::Ge) && same_zero_set(&ai.poly, &aj.poly) {
                out.push(ai.poly.clone());
            }
        }
    }
    out
}

/// Whether two integer polynomials define the same real zero set as an
/// **equality boundary**, i.e. one is a nonzero scalar multiple of the other.
/// A conservative sufficient test: equal after dividing each by the gcd of its
/// coefficients and normalizing the leading sign. (`p` and `−p`, or `p` and `2p`,
/// all match.) `false` on any degree mismatch or the zero polynomial.
fn same_zero_set(a: &[i128], b: &[i128]) -> bool {
    match (normalize_int_poly(a), normalize_int_poly(b)) {
        (Some(na), Some(nb)) => na == nb,
        _ => false,
    }
}

/// Primitive-part normalization of an integer polynomial (LSB-first): divide by the
/// gcd of the coefficient magnitudes and flip the sign so the leading coefficient is
/// positive. `None` for the zero polynomial (no genuine leading term).
fn normalize_int_poly(p: &[i128]) -> Option<Vec<i128>> {
    // Trim trailing zeros.
    let mut end = p.len();
    while end > 0 && p[end - 1] == 0 {
        end -= 1;
    }
    let p = &p[..end];
    if p.is_empty() {
        return None;
    }
    let mut g: u128 = 0;
    for &c in p {
        g = gcd_i128(g, c.unsigned_abs());
    }
    if g == 0 {
        return None;
    }
    let g = i128::try_from(g).ok()?;
    let sign = if *p.last()? < 0 { -1 } else { 1 };
    let mut out = Vec::with_capacity(p.len());
    for &c in p {
        out.push(c.checked_div(g)?.checked_mul(sign)?);
    }
    Some(out)
}

fn decide_anchored(arena: &TermArena, assertions: &[TermId]) -> Option<CheckResult> {
    // Re-collect the conjunction with the coefficient guard relaxed to the natural
    // i128 bound. A structural decline (`or`/`=>`, a second variable, a
    // non-polynomial atom, a genuine i128 overflow) still returns `None`.
    let mut atoms: Vec<Atom> = Vec::new();
    let mut var: Option<SymbolId> = None;
    for &a in assertions {
        collect_conjuncts_unguarded(arena, a, &mut var, &mut atoms)?;
    }
    let var = var?;
    if atoms.is_empty() {
        return None;
    }

    // Only engage when at least one atom genuinely exceeds the i128 CAD-entry guard
    // — otherwise the ordinary (fully-general) `decide_system` path already applies
    // and we must not shadow it (it also decides pure-inequality conjunctions this
    // anchored path deliberately cannot).
    let exceeds_guard = atoms.iter().any(|a| {
        a.poly
            .iter()
            .any(|&c| c.checked_abs().is_none_or(|v| v >= MAX_ABS_COEFF))
    });
    if !exceeds_guard {
        return None;
    }

    // Pick an equality anchor whose (small-coefficient) polynomial isolates in i128.
    // An equality on `p` is either an explicit `Cmp::Eq` atom (the flat-conjunction
    // shape, e.g. `approx-sqrt`) OR a **pinning pair** `p ≤ 0 ∧ p ≥ 0` on the SAME
    // oriented polynomial — the shape the `check_with_nra_dpll` abstractor produces
    // when it rewrites `a = b` into `(a ≤ b) ∧ (a ≥ b)` (e.g. each cube of
    // `approx-sqrt-unsat`). Both force `p(x) = 0`, so every model pins `x` to a root
    // of `p`. Prefer a small-coefficient anchor so root isolation never trips the
    // i128 arithmetic.
    let anchors = anchor_polys(&atoms);
    let mut anchor_roots: Option<Vec<Root>> = None;
    for poly in &anchors {
        if poly
            .iter()
            .any(|&c| c.checked_abs().is_none_or(|v| v >= MAX_ABS_COEFF))
        {
            continue; // a big-coefficient equality: do not isolate it here.
        }
        if let Some(roots) = isolate_roots(poly) {
            anchor_roots = Some(roots);
            break;
        }
    }
    let roots = anchor_roots?;

    // Test every anchor root against every atom (rational sign eval / exact
    // `sign_at`), then replay a candidate before accepting `Sat`.
    for root in &roots {
        match root {
            Root::Rational(q) => {
                if rational_satisfies_all(&atoms, *q)? {
                    match replay_rational(arena, assertions, var, *q) {
                        Some(true) => {
                            let mut model = Model::new();
                            model.set(var, Value::Real(*q));
                            return Some(CheckResult::Sat(model));
                        }
                        _ => return None,
                    }
                }
            }
            Root::Algebraic(a) => {
                if algebraic_satisfies_all(&atoms, a)? && algebraic_replay_all(&atoms, a) {
                    let mut model = Model::new();
                    model.set(var, Value::RealAlgebraic(a.clone()));
                    return Some(CheckResult::Sat(model));
                }
            }
        }
    }

    // No anchor root satisfies the whole conjunction. The equality restricts the
    // witness set to exactly these roots, so the enumeration is complete ⇒ Unsat.
    // (Every sign test above resolved; an indeterminate one returned `None`.)
    Some(CheckResult::Unsat)
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
            // original assertions; accept only if every one definitely holds (a
            // `None`/overflow or a definite `false` ⇒ decline, never a wrong Sat).
            if replay_rational(arena, assertions, var, q) != Some(true) {
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
    deadline: Option<Instant>,
) -> Option<CheckResult> {
    // 1. Collect every real root of every constraint polynomial. Poll the deadline
    //    per atom: a large lazy-SMT cube (100+ atoms) can spend seconds here, so we
    //    bail to a timely `Unknown` rather than overrun the budget (soundness-neutral).
    let mut roots: Vec<Root> = Vec::new();
    for atom in atoms {
        if deadline_reached(deadline) {
            return Some(cad_timeout_unknown());
        }
        let rs = isolate_roots(&atom.poly)?; // overflow during isolation ⇒ decline
        roots.extend(rs);
    }

    // 2. Sort the roots into a deterministic ascending order. Any pair we cannot
    //    order exactly (algebraic-vs-algebraic that does not resolve) ⇒ decline.
    //    `sort_roots` polls `deadline` per outer iteration — the O(n²) exact
    //    comparator was the single un-clocked step that overran the budget (#84);
    //    a `None` on a reached deadline surfaces as a sound `unknown`.
    let Some(ordered) = sort_roots(&roots, deadline) else {
        return if deadline_reached(deadline) {
            Some(cad_timeout_unknown())
        } else {
            None // an indeterminate exact comparison ⇒ decline
        };
    };

    // 3. Build the candidate sample points strictly between/around the roots.
    //    Each is a RATIONAL preferred witness for an open cell.
    if deadline_reached(deadline) {
        return Some(cad_timeout_unknown());
    }
    let samples = cell_samples(&ordered)?;

    // 4. Test rational samples FIRST (so the model stays rational when a cell
    //    works), then the roots themselves (an equality may pin x to an
    //    irrational root). A `None` from any sign test means the candidate
    //    enumeration is *incomplete* for this query, so we must not claim Unsat
    //    — propagate the decline.
    for q in &samples {
        if deadline_reached(deadline) {
            return Some(cad_timeout_unknown());
        }
        if rational_satisfies_all(atoms, *q)? {
            // The exact integer-polynomial check already proves `q` satisfies every
            // constraint. Confirm via the original terms; a `None` (overflow ⇒ could
            // not re-eval) or a definite `false` (an inconsistency) means we cannot
            // soundly certify — DECLINE rather than continue toward a wrong `Unsat`.
            match replay_rational(arena, assertions, var, *q) {
                Some(true) => {
                    let mut model = Model::new();
                    model.set(var, Value::Real(*q));
                    return Some(CheckResult::Sat(model));
                }
                _ => return None,
            }
        }
    }
    for root in &ordered {
        if deadline_reached(deadline) {
            return Some(cad_timeout_unknown());
        }
        match root {
            Root::Rational(q) => {
                if rational_satisfies_all(atoms, *q)? {
                    match replay_rational(arena, assertions, var, *q) {
                        Some(true) => {
                            let mut model = Model::new();
                            model.set(var, Value::Real(*q));
                            return Some(CheckResult::Sat(model));
                        }
                        _ => return None,
                    }
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
    let ordered = sort_roots(&roots, None)?;
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
/// Replay the original assertions at `var := q`: `Some(true)` = all hold,
/// `Some(false)` = some assertion is definitely false, `None` = a replay did not
/// resolve (e.g. the exact-rational evaluation OVERFLOWED `i128` at a
/// high-denominator witness). A `None` must make the caller DECLINE — treating an
/// unresolved replay as "witness invalid" and continuing to `Unsat` was a
/// wrong-`Unsat` soundness bug (the witness genuinely satisfied the constraints by
/// the exact integer-polynomial check; only the term-level re-eval overflowed).
fn replay_rational(
    arena: &TermArena,
    assertions: &[TermId],
    var: SymbolId,
    q: Rational,
) -> Option<bool> {
    let mut asg = Assignment::new();
    asg.set(var, Value::Real(q));
    let mut all_true = true;
    for &a in assertions {
        match eval(arena, a, &asg) {
            Ok(Value::Bool(true)) => {}
            Ok(Value::Bool(false)) => return Some(false),
            _ => all_true = false, // overflow / non-Bool ⇒ inconclusive
        }
    }
    if all_true { Some(true) } else { None }
}

/// Sort isolated roots into ascending order, returning `None` if any pair cannot
/// be ordered exactly (an algebraic-vs-algebraic comparison that does not resolve
/// within the refinement bound) so the caller declines rather than guessing.
fn sort_roots(roots: &[Root], deadline: Option<Instant>) -> Option<Vec<Root>> {
    let mut out: Vec<Root> = roots.to_vec();
    // Insertion sort with a total, exact comparator; on any indeterminate
    // comparison return None. The comparator is exact-algebraic and can be
    // expensive, so this O(n²) loop is the single un-clocked step that overran
    // the budget on large cubes (task #84): poll the deadline per outer iteration
    // and bail with `None` (⇒ the caller declines to a sound `unknown`) — never a
    // changed verdict.
    for i in 1..out.len() {
        if deadline_reached(deadline) {
            return None;
        }
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
            let (xlo, xhi) = x.interval_big();
            let (ylo, yhi) = y.interval_big();
            if xhi <= ylo {
                return Some(Ordering::Less); // x ≤ xhi ≤ ylo ≤ y, and x ≠ y
            }
            if yhi <= xlo {
                return Some(Ordering::Greater);
            }
            // Intervals overlap and the values are distinct: we cannot order them
            // exactly without algebraic-vs-algebraic refinement (deferred). Decline.
            None
        }
    }
}

/// The isolating lower/upper rational bounds of a root: the true value lies in
/// `[lo, hi]` (`lo == hi` for a rational root). `None` if an algebraic root cannot
/// expose its interval.
fn root_bounds(r: &Root) -> Option<(Rational, Rational)> {
    match r {
        Root::Rational(q) => Some((*q, *q)),
        Root::Algebraic(a) => a.interval(),
    }
}

/// `floor(r)` as an `i128` (`den > 0` is a `Rational` invariant, so `div_euclid`
/// is the floor).
fn floor_i128(r: Rational) -> i128 {
    r.numerator().div_euclid(r.denominator())
}

/// `ceil(r)` as an `i128`. `None` on the `i128::MIN` negation edge.
fn ceil_i128(r: Rational) -> Option<i128> {
    Some(-(r.numerator().checked_neg()?.div_euclid(r.denominator())))
}

/// Depth bound for [`coarsest_rational_in`]'s denominator doublings (`2^52` finely
/// separates the roots of any admissible polynomial; beyond it the caller falls
/// back to the exact midpoint).
const COARSEN_SAMPLE_DEPTH: u32 = 52;

/// The smallest-denominator dyadic strictly inside the open interval `(a, b)`
/// (`a < b`). Tries denominators `1, 2, 4, …`, taking `m = floor(a·den)+1` (the
/// least numerator with `m/den > a`) and returning the first `m/den < b`. A
/// SIMPLE in-cell sample keeps the witness's denominator small so it evaluates
/// without `i128` overflow (a deep-bisection dyadic from `Root::locate` would
/// overflow the exact-rational replay — the wrong-`Unsat` bug). `None` on overflow
/// or if no dyadic is found within the bound.
fn coarsest_rational_in(a: Rational, b: Rational) -> Option<Rational> {
    let mut den: i128 = 1;
    for _ in 0..=COARSEN_SAMPLE_DEPTH {
        let scaled = a.checked_mul(Rational::integer(den))?;
        let m = floor_i128(scaled).checked_add(1)?;
        let cand = Rational::checked_new(m, den)?;
        if cand.checked_cmp(&b)? == Ordering::Less {
            return Some(cand);
        }
        den = den.checked_mul(2)?;
    }
    None
}

/// Build one rational sample strictly inside each open cell delimited by the
/// (ascending, deduplicated) roots: below the least root, between each adjacent
/// pair, and above the greatest. With no roots, a single sample (0) covers ℝ.
/// `None` on overflow.
///
/// Samples are chosen SIMPLE (small denominator): an integer below/above the
/// extreme roots, and the coarsest dyadic in the SAFE gap `(hi_i, lo_{i+1})`
/// between consecutive roots' isolating intervals — which is guaranteed strictly
/// between the two roots (`hi_i ≥ root_i`, `lo_{i+1} ≤ root_{i+1}`). This keeps
/// witnesses eval-checkable: a `Root::locate` midpoint is a depth-48 dyadic whose
/// exact-rational evaluation overflows `i128`, which previously made the replay
/// reject a valid witness and the system wrongly report `Unsat`.
fn cell_samples(ordered: &[Root]) -> Option<Vec<Rational>> {
    if ordered.is_empty() {
        return Some(vec![Rational::zero()]);
    }
    let bounds: Vec<(Rational, Rational)> =
        ordered.iter().map(root_bounds).collect::<Option<_>>()?;
    let mut pts = Vec::with_capacity(bounds.len() + 1);
    // Below the least root: the integer floor(lo) − 1 < root (small, eval-clean).
    pts.push(Rational::integer(floor_i128(bounds[0].0).checked_sub(1)?));
    // Between adjacent roots: the simplest rational in the safe gap (hi_i, lo_{i+1}).
    for i in 0..bounds.len() - 1 {
        let hi_i = bounds[i].1;
        let lo_j = bounds[i + 1].0;
        match hi_i.checked_cmp(&lo_j)? {
            Ordering::Less => {
                // Disjoint brackets ⇒ a guaranteed-between, simple sample exists.
                let s = match coarsest_rational_in(hi_i, lo_j) {
                    Some(s) => s,
                    None => hi_i.checked_add(lo_j)?.checked_div(Rational::integer(2))?,
                };
                pts.push(s);
            }
            Ordering::Equal => {
                // Touching brackets: the locate midpoint of the two (distinct) roots
                // still lies strictly between them.
                let (li, lj) = (ordered[i].locate(), ordered[i + 1].locate());
                if li.checked_cmp(&lj)? != Ordering::Equal {
                    pts.push(li.checked_add(lj)?.checked_div(Rational::integer(2))?);
                }
            }
            Ordering::Greater => {
                // Overlapping brackets (e.g. a shared root counted twice): skip; the
                // adjacent open cells are still sampled by their other separators.
            }
        }
    }
    // Above the greatest root: the integer ceil(hi) + 1 > root (small, eval-clean).
    pts.push(Rational::integer(
        ceil_i128(bounds[bounds.len() - 1].1)?.checked_add(1)?,
    ));
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

// ============================================================================
// Sturm sequences: an EXACT count of distinct real roots in an interval.
//
// Sturm's theorem: for a squarefree polynomial `p`, the number of *distinct*
// real roots in the half-open interval `(a, b]` equals `V(a) − V(b)`, where
// `V(t)` is the number of sign changes (ignoring zeros) in the Sturm chain
//
//     S₀ = p,  S₁ = p',  S_{k+1} = −rem(S_{k−1}, S_k),
//
// continued until the remainder is zero. The count is *exact*, so we use it to
// drive root isolation: subdivide the Cauchy interval until every subinterval
// holds exactly one root, then bisect it. This NEVER misses a root — unlike a
// fixed grid, which silently drops a root when two fall in one cell (their
// endpoint signs match, so the cell looks root-free).
//
// All arithmetic is exact `Rational`; every step is `checked_*`. ANY overflow
// returns `None`, and the caller falls back to the (sound) grid path. For a
// non-squarefree `p` we first divide out `gcd(p, p')` to obtain the squarefree
// part, whose roots are the SAME SET — so the distinct-root count is unchanged.
// ============================================================================

// The exact-rational polynomial + Sturm primitives now live in the dependency-free
// leaf crate `axeyum-ir::poly` (shared with the real-algebraic *value* layer's
// field arithmetic). Re-imported here; the few that take the solver's degree /
// coefficient guards are wrapped so existing call sites pass `MAX_DEGREE` /
// `MAX_ABS_COEFF` implicitly.
use axeyum_ir::poly::{
    RatVec, count_roots_in, gcd_i128, lcm_i128, rat_from_int, sylvester_determinant,
};

/// The squarefree part of `p`, bounded by [`MAX_DEGREE`]
/// ([`axeyum_ir::poly::squarefree_part`] with the solver's degree guard).
fn squarefree_part(p: &[Rational]) -> Option<RatVec> {
    axeyum_ir::poly::squarefree_part(p, MAX_DEGREE)
}

/// Clear denominators of a rational polynomial to an integer polynomial, capped
/// at [`MAX_ABS_COEFF`] ([`axeyum_ir::poly::rat_to_int_poly`] with the guard).
fn rat_to_int_poly(p: &[Rational]) -> Option<Vec<i128>> {
    axeyum_ir::poly::rat_to_int_poly(p, MAX_ABS_COEFF)
}

/// The Sturm chain of a squarefree `p`, bounded by [`MAX_DEGREE`]
/// ([`axeyum_ir::poly::sturm_chain`] with the solver's degree guard).
fn sturm_chain(p: &[Rational]) -> Option<Vec<RatVec>> {
    axeyum_ir::poly::sturm_chain(p, MAX_DEGREE)
}

/// Maximum recursion *depth* for the Sturm-driven interval subdivision. Each
/// level halves the interval; `2^SUBDIVIDE_DEPTH` cells comfortably separate the
/// roots of any admissible polynomial. Hitting the bound ⇒ decline (fall back to
/// the grid), never an incomplete result.
const STURM_SUBDIVIDE_DEPTH: u32 = 60;

/// Recursively subdivide `(lo, hi]` using the EXACT Sturm count to drive the
/// split, pushing each isolated single root into `out`. `count` is the precomputed
/// `count_roots_in(chain, lo, hi)` (passed so the parent's count is reused).
///
/// Invariant on return `Some(())`: EVERY distinct root in `(lo, hi]` is
/// represented in `out` (completeness). `None` ⇒ overflow or the depth bound was
/// hit ⇒ the whole isolation declines (the caller falls back to the grid, which
/// stays sound). This never silently drops a root.
#[allow(clippy::too_many_arguments)]
fn sturm_isolate_rec(
    int_poly: &[i128],
    chain: &[RatVec],
    lo: Rational,
    hi: Rational,
    count: usize,
    depth: u32,
    out: &mut Vec<Root>,
) -> Option<()> {
    if count == 0 {
        return Some(());
    }
    if count == 1 {
        // Exactly one root in (lo, hi]. The endpoint `hi` itself may be that root
        // (the interval is half-open). Test it exactly first.
        let vhi = eval_rat(int_poly, hi)?;
        if vhi.is_zero() {
            out.push(Root::Rational(hi));
            return Some(());
        }
        // Otherwise the single root lies in the OPEN (lo, hi). But `lo` may ITSELF
        // be a root (e.g. it is the `mid` carried in from a parent split where mid
        // was a root and we recursed on `(mid, hi]`). `isolate_one` needs a
        // STRICT, opposite-sign bracket with both endpoints non-roots, so we first
        // narrow to a clean bracket via Sturm before handing off.
        out.push(sturm_isolate_single(int_poly, chain, lo, hi, depth)?);
        return Some(());
    }
    // count ≥ 2: split at the midpoint and recurse on each HALF-OPEN half. The two
    // half-open intervals `(lo, mid]` and `(mid, hi]` ALWAYS partition `(lo, hi]`
    // exactly — whether or not `mid` is a root — so `count_roots_in(lo, mid) +
    // count_roots_in(mid, hi) == count` holds unconditionally, and each child's
    // count matches its interval's exact half-open count (the recursion's
    // contract). A root exactly at `mid` belongs to the LEFT half `(lo, mid]` and
    // is recorded there by the `count == 1` leaf (`eval(hi=mid) == 0`); it must NOT
    // be recorded here, else it is double-counted while the genuine left root is
    // missed (the historical wrong-`Unsat` bug: e.g. `−3x²−3x` split at the root
    // `mid = 0` returned `{0, 0}` instead of `{−1, 0}`).
    if depth >= STURM_SUBDIVIDE_DEPTH {
        return None; // bound hit ⇒ decline (never an incomplete set)
    }
    let mid = lo.checked_add(hi)?.checked_div(Rational::integer(2))?;
    // Guard against a degenerate (collapsed) interval.
    if mid.checked_cmp(&lo)? != Ordering::Greater || mid.checked_cmp(&hi)? != Ordering::Less {
        return None;
    }
    let lo_count = count_roots_in(chain, lo, mid)?; // (lo, mid] — includes a root AT mid
    let hi_count = count_roots_in(chain, mid, hi)?; // (mid, hi]
    // The half-open halves partition (lo, hi]; their counts must sum to `count`.
    // A mismatch signals overflow/inconsistency ⇒ decline.
    if lo_count.checked_add(hi_count)? != count {
        return None;
    }
    sturm_isolate_rec(int_poly, chain, lo, mid, lo_count, depth + 1, out)?;
    sturm_isolate_rec(int_poly, chain, mid, hi, hi_count, depth + 1, out)?;
    Some(())
}

/// Isolate the SINGLE root known (by the exact Sturm count) to lie in the
/// half-open `(lo, hi]`, where `lo` MAY itself be a root (so the interval is not
/// yet a clean opposite-sign bracket). Narrow with the Sturm count until both
/// endpoints are non-roots straddling the root with opposite signs, then hand off
/// to [`isolate_one`]; an exact rational midpoint root short-circuits. `None` on
/// overflow or the depth bound (⇒ decline). The squarefree `int_poly` has only
/// SIMPLE roots, so a non-root bracket ALWAYS exhibits a strict sign change.
fn sturm_isolate_single(
    int_poly: &[i128],
    chain: &[RatVec],
    lo: Rational,
    hi: Rational,
    depth: u32,
) -> Option<Root> {
    let mut lo = lo;
    let mut hi = hi;
    let mut depth = depth;
    // We maintain the invariant: exactly one root lies in (lo, hi], and `hi` is
    // NOT a root (checked by the caller / re-established below). We bisect until
    // `lo` is also a non-root and the bracket has a strict sign change.
    loop {
        // If `lo` is non-root and `hi` is non-root with opposite signs, the open
        // (lo, hi) is a clean isolating bracket ⇒ hand off.
        let slo = Sign::of_rational(eval_rat(int_poly, lo)?);
        let shi = Sign::of_rational(eval_rat(int_poly, hi)?);
        if slo != Sign::Zero && shi != Sign::Zero && slo != shi {
            return isolate_one(int_poly, lo, hi);
        }
        if depth >= STURM_SUBDIVIDE_DEPTH {
            return None; // bound hit ⇒ decline
        }
        let mid = lo.checked_add(hi)?.checked_div(Rational::integer(2))?;
        if mid.checked_cmp(&lo)? != Ordering::Greater || mid.checked_cmp(&hi)? != Ordering::Less {
            return None; // collapsed interval ⇒ decline
        }
        if eval_rat(int_poly, mid)?.is_zero() {
            return Some(Root::Rational(mid)); // exact rational root
        }
        // The single root is in (lo, hi]; use the half-open Sturm count to keep
        // the half that contains it, discarding the (root-free) other half. This
        // also walks `lo` rightward off a root endpoint.
        let lo_count = count_roots_in(chain, lo, mid)?; // roots in (lo, mid]
        if lo_count >= 1 {
            hi = mid;
        } else {
            lo = mid;
        }
        depth += 1;
    }
}

/// Isolate **all** distinct real roots of the integer polynomial `poly` using
/// Sturm's theorem — the COMPLETE, never-miss path. Returns `Some(roots)` with
/// every distinct real root represented exactly once (ascending order not
/// guaranteed; the caller re-sorts), or `None` to DECLINE (overflow, a
/// constant/degenerate shape, or the recursion bound) so the caller falls back to
/// the sound grid scan.
///
/// Method: lift `poly` to rational, take its squarefree part `q = poly/gcd(poly,
/// poly')` (same root set, all roots simple), build the Sturm chain of `q`, count
/// the distinct roots over the Cauchy interval `(−B, B]`, and recursively
/// subdivide by exact count until each subinterval holds exactly one root, then
/// bisect it (via `isolate_one` on the ORIGINAL integer `poly`, so the returned
/// `Root::Algebraic` carries the original defining polynomial). Because the
/// count is exact, NO root is ever missed; on any overflow/bound the whole path
/// declines and the grid takes over.
fn isolate_roots_sturm(poly: &[i128]) -> Option<Vec<Root>> {
    if poly.last().copied()? == 0 {
        return None;
    }
    // Squarefree part over the rationals (SAME root SET, every root now SIMPLE),
    // cleared back to an integer polynomial `sqf`. Working with `sqf` everywhere
    // below is what makes the never-miss guarantee hold even for non-squarefree
    // input: each distinct root of `poly` is a SIGN-CHANGING root of `sqf`, so
    // `isolate_one`'s bracket-and-bisect always applies (a double root of `poly`
    // would have NO sign change and defeat bracketing). The returned algebraic
    // numbers carry `sqf` as their defining polynomial — a genuine defining poly
    // for the same real value — and the caller's replay still checks the ORIGINAL
    // `poly` via `sign_at`, which vanishes at the (multiple) root too.
    let rat = rat_from_int(poly);
    let sqfree = squarefree_part(&rat)?;
    let sqf = rat_to_int_poly(&sqfree)?;
    let lead = *sqf.last()?;
    if lead == 0 {
        return None;
    }
    // Cauchy bound B = 1 + max|aᵢ|/|aₙ| of `sqf`, rounded UP to an integer ⇒ a
    // strict bound: every real root satisfies |root| < B, so ±B are NOT roots.
    let max_other = sqf[..sqf.len() - 1]
        .iter()
        .map(|c| c.unsigned_abs())
        .max()
        .unwrap_or(0);
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

    // The endpoints must not be roots (strict Cauchy bound guarantees this, but
    // verify exactly — if an endpoint were a root the half-open count would be off).
    if eval_rat(&sqf, lo)?.is_zero() || eval_rat(&sqf, hi)?.is_zero() {
        return None;
    }
    let chain = sturm_chain(&sqfree)?;
    let total = count_roots_in(&chain, lo, hi)?;
    let mut out: Vec<Root> = Vec::new();
    sturm_isolate_rec(&sqf, &chain, lo, hi, total, 0, &mut out)?;
    // Completeness invariant: `out` now holds exactly `total` distinct roots — the
    // exact Sturm count over the full Cauchy interval. (Each leaf pushes exactly
    // one Root for a count-1 cell or the recorded rational root at a split point;
    // count-0 cells push none.) If this does not hold, something is inconsistent
    // ⇒ decline rather than return a possibly-incomplete set.
    if out.len() != total {
        return None;
    }
    Some(out)
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
///
/// COMPLETENESS: this dispatcher tries the exact **Sturm-sequence** path first
/// ([`isolate_roots_sturm`]), which provably finds EVERY distinct real root (the
/// Sturm count is exact, so two roots in one would-be grid cell are still both
/// found). Only if Sturm declines (overflow, a constant/degenerate shape, or the
/// recursion bound) do we fall back to the uniform grid scan
/// ([`isolate_roots_grid`]). The grid stays sound — a missed root only degrades a
/// `Sat` to a decline upstream — but the Sturm path removes that gap entirely for
/// every polynomial it admits. The returned set is therefore COMPLETE (every real
/// root represented) whenever Sturm succeeds, and the grid's sound behavior is
/// preserved otherwise. A whole-isolation `None` makes the caller decline.
fn isolate_roots(poly: &[i128]) -> Option<Vec<Root>> {
    if let Some(mut roots) = isolate_roots_sturm(poly) {
        // Sturm yields distinct roots but not necessarily in ascending order;
        // sort to match the documented contract (callers rely on ascending order
        // for `decide_eq`'s first-root and the inequality separators). If the
        // sort cannot order a pair exactly, fall through to the grid.
        if let Some(sorted) = sort_roots(&roots, None) {
            roots = sorted;
            return Some(roots);
        }
    }
    isolate_roots_grid(poly)
}

/// The original uniform-grid root isolation (now the fallback when the exact
/// Sturm path declines). See [`isolate_roots`] for the completeness contract.
fn isolate_roots_grid(poly: &[i128]) -> Option<Vec<Root>> {
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
    collect_conjuncts_inner(arena, assertion, var, atoms, true)
}

/// As [`collect_conjuncts`] but with the `i128` `MAX_ABS_COEFF` coefficient guard
/// relaxed to the natural overflow bound (see [`RatPoly::to_integer_poly_unguarded`]).
/// Used by [`decide_anchored`], which never isolates a big-coefficient atom.
fn collect_conjuncts_unguarded(
    arena: &TermArena,
    assertion: TermId,
    var: &mut Option<SymbolId>,
    atoms: &mut Vec<Atom>,
) -> Option<()> {
    collect_conjuncts_inner(arena, assertion, var, atoms, false)
}

fn collect_conjuncts_inner(
    arena: &TermArena,
    assertion: TermId,
    var: &mut Option<SymbolId>,
    atoms: &mut Vec<Atom>,
    guarded: bool,
) -> Option<()> {
    // Top-level `and`: flatten its conjuncts. (`BoolNot` is handled below as the
    // `≠` shape, NOT as a general negation, so we don't push De Morgan into it.)
    if let TermNode::App {
        op: Op::BoolAnd,
        args,
    } = arena.node(assertion)
    {
        for &c in args {
            collect_conjuncts_inner(arena, c, var, atoms, guarded)?;
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
    let poly = if guarded {
        rat.to_integer_poly()?
    } else {
        rat.to_integer_poly_unguarded()?
    };
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

    // A negated real (in)equality dualizes to its complementary relation, so a
    // single-variable goal refutation `¬(a ⋈ b)` reaches the exact decider rather
    // than the abstraction (mirrors `match_multi_constraint`). `≠` is `¬(=)`.
    if matches!(op, Op::BoolNot) {
        let inner = args[0];
        let TermNode::App {
            op: inner_op,
            args: inner_args,
        } = arena.node(inner)
        else {
            return None;
        };
        let cmp = match inner_op {
            Op::Eq => Cmp::Ne,     // ¬(a = b) ⇔ a ≠ b
            Op::RealLt => Cmp::Ge, // ¬(a < b) ⇔ a ≥ b
            Op::RealLe => Cmp::Gt, // ¬(a ≤ b) ⇔ a > b
            Op::RealGt => Cmp::Le, // ¬(a > b) ⇔ a ≤ b
            Op::RealGe => Cmp::Lt, // ¬(a ≥ b) ⇔ a < b
            _ => return None,
        };
        let poly = collect_diff(arena, inner_args[0], inner_args[1])?;
        let var = poly.var?;
        return Some((var, cmp, poly));
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
            // `to_real` is the exact ring embedding ℤ ↪ ℝ, so an integer
            // sub-term denotes the same real value as its collected rational
            // polynomial. Collecting through it lets an integer numeral written
            // in a real context — e.g. `(- 2)` in `(= (* a a) (- 2))`, which the
            // SMT-LIB front end parses as `(to_real (- 2))` — reach the exact
            // real decider instead of the coercion-relaxation fall-through.
            Op::IntToReal if args.len() == 1 => collect_int(arena, args[0]),
            _ => None,
        },
        _ => None,
    }
}

/// Recursively collect an `Int`-sorted term into a single-variable rational
/// polynomial over `{+, −, ·, neg, IntConst, symbol}`, mirroring [`collect`].
///
/// This is only ever reached under a [`Op::IntToReal`] node, whose semantics
/// are the **exact** embedding ℤ ↪ ℝ. That embedding is a ring homomorphism
/// (`to_real(a+b)=to_real a+to_real b`, `to_real(a·b)=to_real a·to_real b`,
/// `to_real(-a)=-to_real a`, `to_real k = k`), so the collected polynomial
/// denotes the same real value as `(to_real t)` — the coercion is
/// value-preserving and the resulting constraint is semantically identical.
fn collect_int(arena: &TermArena, t: TermId) -> Option<RatPoly> {
    if arena.sort_of(t) != Sort::Int {
        return None;
    }
    match arena.node(t) {
        TermNode::IntConst(k) => Some(RatPoly::constant(Rational::integer(*k))),
        TermNode::Symbol(s) => Some(RatPoly::var_of(*s)),
        TermNode::App { op, args } => match op {
            Op::IntNeg if args.len() == 1 => collect_int(arena, args[0])?.neg(),
            Op::IntAdd if args.len() == 2 => {
                collect_int(arena, args[0])?.add(&collect_int(arena, args[1])?)
            }
            Op::IntSub if args.len() == 2 => {
                collect_int(arena, args[0])?.sub(collect_int(arena, args[1])?)
            }
            Op::IntMul if args.len() == 2 => {
                collect_int(arena, args[0])?.mul(&collect_int(arena, args[1])?)
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

    /// If this polynomial is **linear** and isolates one variable with **any**
    /// nonzero coefficient so that an equality `poly = 0` rearranges to
    /// `y = L(other vars)` with `L` linear and y-free, return `(y, L)`.
    ///
    /// The polynomial is `c0 + Σ cᵢ·vᵢ`. We require it linear (every monomial
    /// degree ≤ 1) and pick a variable `y` whose coefficient `cᵧ` is nonzero.
    /// Then `poly = 0` ⇒ `y = −(poly − cᵧ·y)/cᵧ`, so each remaining term is
    /// scaled by `−1/cᵧ` via **exact rational division** — e.g. `−3·x = 0`
    /// ⇒ `x = 0`, `2·x − 6 = 0` ⇒ `x = 3`, `a·x + L(rest) = 0` ⇒ `x = −L/a`.
    ///
    /// A `±1` coefficient is *preferred* when one exists (it keeps `L` integer,
    /// minimizing denominator growth in the substitution fixpoint), but is no
    /// longer required: any nonzero coefficient yields an exact definition,
    /// which closes the cases that algebraically collapse to linear/constant.
    fn as_linear_definition(&self) -> Option<(SymbolId, MultiPoly)> {
        // Reject any nonlinear monomial.
        for k in self.terms.keys() {
            if mono_total_degree(k) > 1 {
                return None;
            }
        }
        // Prefer a variable with coefficient ±1 (keeps `L` integer); otherwise
        // fall back to the first variable with ANY nonzero coefficient. Both
        // passes iterate the canonical `BTreeMap` order, so the choice is
        // deterministic.
        let mut chosen: Option<(SymbolId, Rational)> = None;
        for (k, &c) in &self.terms {
            if let [(v, 1)] = k.as_slice()
                && (c == Rational::integer(1) || c == Rational::integer(-1))
            {
                chosen = Some((*v, c));
                break;
            }
        }
        if chosen.is_none() {
            for (k, &c) in &self.terms {
                if let [(v, 1)] = k.as_slice()
                    && !c.is_zero()
                {
                    chosen = Some((*v, c));
                    break;
                }
            }
        }
        let (y, cy) = chosen?;
        // L = −(poly − cy·y) / cy. Build `poly` with the y-term removed, then
        // scale each surviving term by `−1/cy` (exact rational division).
        let scale = Rational::integer(-1).checked_div(cy)?; // −1/cy (cy ≠ 0)
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
/// Decide and strip the CONSTANT atoms of a multivariate conjunction. An atom
/// whose polynomial has no variables (e.g. a polynomial identity like
/// `(x+y)² − (x²+2xy+y²)` collapses to `0`) is a constant comparison `c ⋈ 0`: a
/// FALSE one (`0 ≠ 0`, `0 < 0`, …) makes the whole conjunction UNSAT — this is
/// what *proves* a polynomial identity (its negation reduces to `0 ≠ 0`); a TRUE
/// one (`0 = 0`, `0 ≤ 0`, …) is dropped as satisfied. Exact (the constant is
/// exact) and bypasses the abstraction search entirely.
///
/// Returns `Ok(nonconstant_atoms)` for the surviving variable-bearing atoms, or
/// `Err(verdict)` to short-circuit: `Err(Some(Unsat))` for a false constant, and
/// `Err(None)` (decline) when every atom was a satisfied constant (leave the
/// variable-free sat to the existing arithmetic path).
fn fold_constant_atoms(atoms: Vec<MultiAtom>) -> Result<Vec<MultiAtom>, Option<CheckResult>> {
    let mut nonconstant: Vec<MultiAtom> = Vec::with_capacity(atoms.len());
    for atom in atoms {
        if let Some(c) = atom.poly.as_constant() {
            if !sign_satisfies(atom.cmp, Sign::of_rational(c)) {
                return Err(Some(CheckResult::Unsat));
            }
            // true constant ⇒ satisfied, drop it.
        } else {
            nonconstant.push(atom);
        }
    }
    if nonconstant.is_empty() {
        return Err(None);
    }
    Ok(nonconstant)
}

#[allow(clippy::too_many_lines)] // coherent multivariate-CAD routine; deadline polls added (#84)
fn decompose_multivariate(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Option<CheckResult> {
    // 1. Re-collect every assertion as a multivariate comparison.
    let mut atoms: Vec<MultiAtom> = Vec::new();
    for &a in assertions {
        collect_multi_conjuncts(arena, a, &mut atoms)?;
    }
    if atoms.is_empty() {
        return None;
    }
    // Every Real symbol appearing in the ORIGINAL assertion *terms* (not the
    // normalized polynomials). A variable can vanish from the normalized form yet
    // still occur in the raw term the replay evaluator reads — e.g.
    // `−2xy + 2xy + x = 0` normalizes to `x`, but `y` remains a symbol of the
    // original equality, and the ground evaluator needs every symbol bound. Such a
    // variable is genuinely unconstrained (its coefficient cancelled), so binding it
    // to `0` before replay (step 4a') yields a concrete, evaluator-checkable witness.
    let all_original_vars = real_symbols_of(arena, assertions);
    // Degree-2 SOS/PSD refutation (sound, possibly incomplete): a single STRICT
    // inequality atom whose quadratic form is globally one-signed refutes the
    // conjunction everywhere ⇒ `Unsat`. See `sos_refute_multivariate`.
    if let Some(verdict) = sos_refute_multivariate(&atoms) {
        return Some(verdict);
    }
    // Decide CONSTANT atoms directly (see `fold_constant_atoms`): a false constant
    // comparison ⇒ Unsat; a true one is dropped; an all-constant query declines.
    atoms = match fold_constant_atoms(atoms) {
        Ok(rest) => rest,
        Err(verdict) => return verdict,
    };
    // Require at least one variable in the NORMALIZED atoms. We reach
    // `decompose_multivariate` only after the single-variable collector declined
    // (`decide_real_poly_constraint`'s else branch) — typically because a *raw*
    // term mentions a second variable. After normalization that variable may
    // CANCEL, leaving a genuinely single-variable system (e.g. the single atom
    // `−2xy + 2xy + x = 0` collapses to `x = 0`, with `y` free). Such a system is
    // ours to decide — the single-var collector never saw the normalized form — so
    // we no longer decline at one variable; the component decision handles the live
    // variable and the free-variable binding (step 4a') handles any cancelled one.
    // (Zero variables means every atom folded to a constant, already handled by
    // `fold_constant_atoms` above, so this guard only rejects the empty residue.)
    let all_vars: BTreeSet<SymbolId> = atoms.iter().flat_map(|a| a.poly.vars()).collect();
    if all_vars.is_empty() {
        return None;
    }

    // 2. Substitution fixpoint. `subst[y] = L` records each eliminated variable's
    //    definition (in terms of the *remaining* variables at elimination time;
    //    back-substitution at the end resolves these to concrete values).
    let mut subst: Vec<(SymbolId, MultiPoly)> = Vec::new();
    for _ in 0..MAX_SUBST_ITERS {
        if deadline_reached(deadline) {
            return Some(cad_timeout_unknown());
        }
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
        if deadline_reached(deadline) {
            return Some(cad_timeout_unknown());
        }
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

    // 4a'. Bind any ORIGINAL variable left free (never entered a component nor a
    //      back-substitution — e.g. `y` once `x = 0` collapses `−3xy − x = 0` to
    //      `0 = 0`) to `0`. It is genuinely unconstrained, so any value works; `0`
    //      gives a concrete witness for the evaluator-backed replay below. Sound:
    //      the choice is replay-checked against every original assertion.
    for v in &all_original_vars {
        if model.get(*v).is_none() {
            model.set(*v, Value::Real(Rational::zero()));
        }
    }

    // 4b. Coarsen every algebraic model value to a small-denominator isolating
    //     interval (value-preserving — same root), so the witness replays under the
    //     independent ground evaluator. See [`coarsen_model_algebraics`].
    coarsen_model_algebraics(&mut model);

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
    if comp_vars.len() >= 3 {
        // ≥ 3 distinct variables that share a constraint ⇒ genuinely coupled. The
        // ALL-STRICT case is decided by the recursive N-variable cylindrical
        // decomposition (the solution set is open ⇒ rational interior samples of
        // open cells suffice at every recursion level). A definitive verdict wins;
        // any completeness doubt declines (`None`), as does any non-strict atom.
        if comp
            .iter()
            .all(|a| matches!(a.cmp, Cmp::Lt | Cmp::Gt | Cmp::Ne))
            && let Some(verdict) = decide_strict_cad_nvar(comp, &comp_vars)
        {
            return Some(match verdict {
                TwoVarVerdict::Unsat => ComponentOutcome::Unsat,
                TwoVarVerdict::Sat(b) => ComponentOutcome::Sat(b),
                TwoVarVerdict::Unknown => ComponentOutcome::Unknown,
            });
        }
        // A MIXED / NON-STRICT (at least one `=`/`≤`/`≥`) ≥3-var component is decided
        // by the recursive non-strict cylindrical decomposition, which samples both
        // the open cells AND the RATIONAL critical 0-cells at every level (a non-strict
        // solution can live exactly on a boundary section). A definitive verdict wins;
        // any completeness doubt — esp. an ALGEBRAIC critical value — declines (`None`)
        // to the outer engine, never a wrong verdict. See [`decide_nonstrict_cad_nvar`].
        if comp
            .iter()
            .any(|a| matches!(a.cmp, Cmp::Eq | Cmp::Le | Cmp::Ge))
        {
            // First the (faster) rational-critical decomposition; if it declines
            // (Unknown) — typically because some critical value is ALGEBRAIC — fall
            // back to the algebraic-capable decomposition, which DECIDES algebraic
            // critical coordinates via the `Res(min-poly, p)` elimination + exact
            // field arithmetic. The fallback can only upgrade Unknown→{Sat,Unsat}; it
            // is never consulted once the rational path returns a definite verdict, so
            // it can never flip an existing sat/unsat.
            if let Some(verdict) = decide_nonstrict_cad_nvar(comp, &comp_vars)
                .or_else(|| decide_nonstrict_cad_nvar_algebraic(comp, &comp_vars))
            {
                return Some(match verdict {
                    TwoVarVerdict::Unsat => ComponentOutcome::Unsat,
                    TwoVarVerdict::Sat(b) => ComponentOutcome::Sat(b),
                    TwoVarVerdict::Unknown => ComponentOutcome::Unknown,
                });
            }
        }
        // Any decline is left to the outer engine.
        return None;
    }
    if comp_vars.len() != 1 {
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
/// determinant is now computed by exact evaluation–interpolation (`O(D · dim³)`
/// over the polynomial ring, in [`axeyum_ir::poly`]), NOT factorial Leibniz
/// expansion, so the dimension is no longer factorially constrained. The cap
/// stays a bounded-cost guard (and the underlying `i128` arithmetic still declines
/// gracefully on overflow); raised from 6 to 24 so higher-degree coupled systems
/// decide instead of declining, while a genuinely huge input still declines fast.
const MAX_SYLVESTER_DIM: usize = 24;

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

    // ALL-STRICT-inequality component (every atom `<`, `>`, or `≠`): the solution
    // set is OPEN in ℝ², so a complete cylindrical decomposition with one RATIONAL
    // interior sample per open x-cell decides it exactly (Sat with a rational
    // witness, or an exhaustive Unsat). See [`decide_strict_cad_two_var`]. A
    // definitive verdict wins; a decline falls through to the equality path below
    // (which itself declines for an inequality-only component).
    if comp
        .iter()
        .all(|a| matches!(a.cmp, Cmp::Lt | Cmp::Gt | Cmp::Ne))
        && let Some(verdict) = decide_strict_cad_two_var(comp, v0, v1)
    {
        return Some(verdict);
    }

    // MIXED / NON-STRICT component (at least one `=`/`≤`/`≥` atom, NOT all-equality):
    // a complete cylindrical decomposition that samples BOTH the open `keep`-cell
    // interiors AND each RATIONAL critical `keep`-value (the 0-cells where a
    // non-strict atom may hold on a boundary) decides it exactly — provided every
    // critical `keep`-value is rational (else it declines this orientation, trying
    // the other axis, then the outer layer). See [`decide_nonstrict_cad_two_var`]. A
    // definitive verdict wins; a decline falls through to the equality/resultant path
    // below. An ALL-EQUALITY component is left to the grid lift (its regression
    // anchor) — it is excluded here.
    let has_nonstrict = comp
        .iter()
        .any(|a| matches!(a.cmp, Cmp::Eq | Cmp::Le | Cmp::Ge));
    let all_eq = comp.iter().all(|a| matches!(a.cmp, Cmp::Eq));
    if has_nonstrict
        && !all_eq
        && let Some(verdict) = decide_nonstrict_cad_two_var(comp, v0, v1)
    {
        return Some(verdict);
    }

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

    // ALGEBRAIC (α, β) grid lift (the CAD/nlsat ladder, step 3). For an
    // all-equality component, decide via the grid `x-candidates × y-candidates`
    // (each axis's complete real-root candidate set, from a univariate equality or
    // a resultant) tested by exact field arithmetic — this resolves ALGEBRAIC
    // coordinates that the rational-only per-orientation lift below declines on. A
    // definitive verdict wins immediately; a decline falls through to the existing
    // path (which also handles the non-grid shapes). See `decide_grid_two_var`.
    if all_equalities
        && let Some(verdict) = decide_grid_two_var(comp, v0, v1, &equalities, all_equalities)
    {
        return Some(verdict);
    }

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

// ============================================================================
// Complete CAD for an ALL-STRICT-inequality 2-variable component
// (the CAD/nlsat ladder, step 3 — strict-only slice).
// ============================================================================
//
// Scope: a connected 2-variable component {x, y} in which EVERY atom is a STRICT
// inequality (`<`, `>`, or `≠`). (A component with any `=`/`≤`/`≥` is OUT of
// scope here — equalities go to the grid lift, and a mixed/non-strict component
// is left to the outer layer; this routine is only entered when all atoms are
// strict, and otherwise declines.)
//
// Why one RATIONAL interior sample per open x-cell is EXHAUSTIVE (soundness +
// completeness of both Sat and Unsat):
//
//   The solution set `S ⊆ ℝ²` of a conjunction of STRICT inequalities is OPEN:
//   each `pᵢ(x,y) < 0` / `> 0` / `≠ 0` defines an open set, and a finite
//   intersection of open sets is open. So if `S ≠ ∅` it contains an open ball,
//   hence an open box `(a,b) × (c,d) ⊆ S`. Its projection to the x-axis is the
//   open interval `(a,b)`.
//
//   PROJECTION (sign-invariance): let `Proj` be the univariate-in-x polynomials
//   — for each `p ∈ P`: its leading coefficient in y `lc_y(p)`, its discriminant
//   in y `disc_y(p) = Res_y(p, ∂p/∂y)`, and for every pair `p ≠ q` the resultant
//   `Res_y(p, q)`. Off the real zeros `α₁ < … < α_k` of `Proj` (the "critical"
//   x-values), the number and the y-order of the real y-roots of every `p ∈ P`
//   are CONSTANT (McCallum/Collins sign-invariance over a sign-invariant section:
//   lc_y ≠ 0 keeps deg_y(p) fixed, disc_y ≠ 0 keeps p's y-roots simple and
//   distinct, and Res_y(p,q) ≠ 0 keeps p and q from sharing a y-root). Hence on
//   each open x-cell `(αᵢ, αᵢ₊₁)` (and the two unbounded tails) the truth of the
//   whole strict system, as a function of y, is the SAME at every x in the cell.
//   Therefore the system is satisfiable over an open x-cell `C` iff it is
//   satisfiable at ANY single `x* ∈ C` — and because `S` is open and (if
//   nonempty) projects onto an open interval, that open interval is a union of
//   whole open x-cells, so some open x-cell carries a solution iff `S ≠ ∅`.
//
//   RATIONAL SAMPLES: a rational strictly between two consecutive critical
//   x-values (resp. below the least / above the greatest, and `0` when there are
//   none) is an interior point of an open x-cell. Choosing it RATIONAL is exact
//   (`cell_samples`, refined midpoints of disjoint isolating intervals), so the
//   substitution `x := x*` yields a conjunction of single-variable STRICT
//   constraints in y with RATIONAL coefficients — decided COMPLETELY by
//   [`decide_system_value`] (the sign-cell decider) with NO algebraic-coordinate
//   substitution.
//
//   VERDICTS:
//     • SAT — some x-sample's y-system is `Sat(y*)` ⇒ the component is Sat with
//       the binding `(x→x*, y→y*)` (the caller replay-checks the full model
//       against the ORIGINAL assertions). The sample is interior to an open
//       x-cell, so no solution hides only on a measure-zero critical x.
//     • UNSAT — EVERY open x-cell's y-system returns a definite Unsat (none
//       Unknown) ⇒ the component is Unsat, COMPLETE by the open-cell argument: a
//       strict solution would lie in an open box whose x-projection meets some
//       sampled open cell, contradicting that cell's Unsat.
//
// We DECLINE (`None`) on ANY completeness doubt: an empty/degenerate projection
// (a `p` constant in y, so its critical x-set is not captured), an incomplete
// root isolation, an unresolved sample separation, a per-cell `decide_system_value`
// that returns `None` (Unknown), or the cell cap. A sound `Unknown` always beats
// a wrong verdict; we never claim Unsat with a gap, nor Sat without a replayable
// witness.

/// Hard ceiling on the number of critical x-values (and hence open x-cells +1)
/// the strict-CAD enumerates; beyond it we decline (bounded — no OOM / hang).
const MAX_CAD_CELLS: usize = 256;

/// Decide an ALL-STRICT-inequality 2-variable component `comp` (variables
/// `v0`=x, `v1`=y; every atom `<`, `>`, or `≠`) by a complete cylindrical
/// decomposition: project onto x (sign-invariant set), isolate the critical
/// x-values, sample ONE rational interior point per open x-cell, and decide each
/// cell's rational-coefficient univariate-in-y strict system.
///
/// Returns `Some(Sat(bindings))` / `Some(Unsat)` when the decomposition is
/// provably complete, or `None` to DECLINE (any projection/isolation/sample/cell
/// indeterminacy, or the cell cap) — never a wrong verdict. Sat bindings are
/// replay-checked against the original query by the caller.
fn decide_strict_cad_two_var(
    comp: &[&MultiAtom],
    v0: SymbolId,
    v1: SymbolId,
) -> Option<TwoVarVerdict> {
    // The component must genuinely have both variables (a degenerate single-var
    // component is decided elsewhere); guard so the projection is meaningful.
    debug_assert!(
        comp.iter()
            .all(|a| matches!(a.cmp, Cmp::Lt | Cmp::Gt | Cmp::Ne))
    );

    // 1. The distinct constraint polynomials `P`, coprime-split so a shared factor
    //    does not make a pairwise resultant vanish and force a decline (the split
    //    preserves the cell arrangement and every atom's per-cell sign; the atoms are
    //    still evaluated on their ORIGINAL polynomials). See [`coprime_split`].
    let owned: Vec<MultiPoly> = comp.iter().map(|a| a.poly.clone()).collect();
    let split = coprime_split(&owned);
    let polys: Vec<&MultiPoly> = split.iter().collect();
    if polys.is_empty() {
        return None;
    }

    // 2. Try eliminating y (project onto x) AND eliminating x (project onto y),
    //    deciding along whichever axis yields a complete, in-bounds decomposition.
    //    Both orientations are sound and complete by the same open-cell argument
    //    (x and y are symmetric); trying both rescues a shape where one axis hits
    //    a `p` constant in the eliminated variable (degenerate projection ⇒ that
    //    orientation declines) while the other is clean.
    for &(elim, keep) in &[(v1, v0), (v0, v1)] {
        if let Some(v) = strict_cad_along(comp, &polys, elim, keep) {
            return Some(v);
        }
    }
    None
}

/// One orientation of [`decide_strict_cad_two_var`]: eliminate `elim`, sample the
/// open `keep`-cells, decide each cell's univariate-in-`elim` strict system.
/// `None` declines this orientation (the caller tries the other / falls through).
fn strict_cad_along(
    comp: &[&MultiAtom],
    polys: &[&MultiPoly],
    elim: SymbolId,
    keep: SymbolId,
) -> Option<TwoVarVerdict> {
    // 2a. PROJECTION onto `keep`: the sign-invariant set of univariate-in-`keep`
    //     polynomials. For each `p`: leading coeff in `elim`, discriminant in
    //     `elim`; for each pair: their resultant in `elim`. Every `p` MUST have
    //     positive degree in `elim` (else its sign as a function of `elim` is not
    //     captured by an `elim`-resultant ⇒ the projection would miss its critical
    //     `keep`-values; decline this orientation).
    let mut proj: Vec<Vec<i128>> = Vec::new();
    for p in polys {
        if degree_in(p, elim) == 0 {
            // `p` is constant in `elim`: its sign depends only on `keep`. Its real
            // zeros in `keep` ARE critical `keep`-values (the strict atom can flip
            // there), and they are not produced by any `elim`-resultant. We could
            // add them directly (p is already univariate in `keep`), so do so —
            // this keeps the projection complete rather than declining.
            let ipoly = p.to_single_var_integer_poly(keep)?;
            if ipoly.len() > 1 {
                proj.push(ipoly);
            }
            // A constant-in-both `p` contributes no critical value (it never flips).
            continue;
        }
        // Leading coefficient of `p` in `elim`, as a univariate integer poly in
        // `keep`: its zeros are where deg_{elim}(p) drops (a delineability boundary).
        let pc = poly_in_elim_over_keep(p, elim, keep)?;
        let lead = pc.last()?; // Vec<Rational> in `keep`
        if let Some(ip) = rat_coeffs_to_integer(lead) {
            if ip.len() > 1 {
                proj.push(ip);
            }
        } else {
            return None; // overflow ⇒ decline (cannot guarantee sign-invariance)
        }
        // Discriminant of `p` in `elim` = Res_{elim}(p, ∂p/∂elim).
        let dp = derivative_in(p, elim)?;
        if degree_in(&dp, elim) == 0 {
            // ∂p/∂elim constant in `elim` ⇒ p is linear in `elim`; no discriminant
            // boundary (its single `elim`-root never collides). Nothing to add.
        } else {
            let disc = resultant_univariate(p, &dp, elim, keep)?;
            if disc.len() > 1 {
                proj.push(disc);
            } else if disc.first().copied().unwrap_or(0) == 0 {
                // A vanishing discriminant means p has a repeated `elim`-root for
                // ALL `keep` (a non-isolated boundary) ⇒ this orientation cannot
                // guarantee sign-invariance via finitely many critical points.
                return None;
            }
            // A nonzero-constant discriminant ⇒ no critical `keep`-value from it.
        }
    }
    // Pairwise resultants Res_{elim}(p, q).
    for i in 0..polys.len() {
        for j in (i + 1)..polys.len() {
            if degree_in(polys[i], elim) == 0 || degree_in(polys[j], elim) == 0 {
                continue; // a constant-in-elim factor shares no elim-root to track
            }
            let res = resultant_univariate(polys[i], polys[j], elim, keep)?;
            if res.len() > 1 {
                proj.push(res);
            } else if res.first().copied().unwrap_or(0) == 0 {
                // Identically-zero resultant: p and q share a common `elim`-factor
                // for all `keep` ⇒ a non-isolated coincidence ⇒ cannot delineate.
                return None;
            }
        }
    }

    // 2b. ISOLATE all real roots of every projection polynomial; merge + sort the
    //     distinct critical `keep`-values. `isolate_roots` is complete-or-None.
    let mut roots: Vec<Root> = Vec::new();
    for pp in &proj {
        roots.extend(isolate_roots(pp)?);
    }
    let ordered = sort_roots(&roots, None)?;
    // Deduplicate equal critical values (a shared root from two projection polys)
    // so the cell samples land in genuinely distinct open cells.
    let mut crit: Vec<Root> = Vec::new();
    for r in ordered {
        match crit.last() {
            Some(prev) if compare_roots(prev, &r)? == Ordering::Equal => {}
            _ => crit.push(r),
        }
    }
    if crit.len() > MAX_CAD_CELLS {
        return None; // bounded — never OOM / hang
    }

    // 2c. RATIONAL sample, one interior point per open `keep`-cell (below the
    //     least critical value, between each consecutive pair, above the greatest;
    //     `0` when there are none). `cell_samples` picks exact rationals strictly
    //     inside the open cells.
    let samples = cell_samples(&crit)?;

    // 2d. Decide each cell's univariate-in-`elim` STRICT system. Substituting a
    //     RATIONAL `keep := s` gives rational-coefficient single-variable atoms in
    //     `elim` with the SAME strict comparators. `decide_system_value` decides
    //     them completely (or returns `None` ⇒ we decline; never claim Unsat with
    //     a gap).
    for &s in &samples {
        match decide_strict_cell(comp, keep, elim, s)? {
            CellOutcome::Sat(elim_val) => {
                // Interior sample of an open cell ⇒ a genuine solution. The caller
                // replay-checks the full (keep, elim) model against the original
                // assertions.
                return Some(TwoVarVerdict::Sat(vec![
                    (keep, Value::Real(s)),
                    (elim, elim_val),
                ]));
            }
            CellOutcome::Unsat => {}
        }
    }

    // Every open `keep`-cell's strict system was definitely Unsat (an Unknown cell
    // would have declined via `?` above). By the open-cell completeness argument
    // (the solution set is open; if nonempty its x-projection contains a whole
    // open cell we sampled), the component is Unsat — EXHAUSTIVELY.
    Some(TwoVarVerdict::Unsat)
}

/// The outcome of deciding one open `keep`-cell's univariate-in-`elim` strict
/// system at the rational sample `keep := s`.
enum CellOutcome {
    /// The cell's strict system is satisfiable; bind `elim` to this witness value.
    Sat(Value),
    /// The cell's strict system is (definitely) unsatisfiable.
    Unsat,
}

/// Substitute the RATIONAL `keep := s` into every atom of the strict component,
/// producing a conjunction of single-variable strict constraints in `elim`, and
/// decide it with the sign-cell decider [`decide_system_value`]. `None` declines
/// (overflow during substitution, a degenerate residual that loses `elim`, or an
/// indeterminate sub-decision ⇒ we never claim Unsat with a gap).
fn decide_strict_cell(
    comp: &[&MultiAtom],
    keep: SymbolId,
    elim: SymbolId,
    s: Rational,
) -> Option<CellOutcome> {
    let mut subst: BTreeMap<SymbolId, Rational> = BTreeMap::new();
    subst.insert(keep, s);
    let mut single_atoms: Vec<Atom> = Vec::with_capacity(comp.len());
    for atom in comp {
        let residual = substitute_rationals(&atom.poly, &subst)?;
        // After fixing `keep`, the atom is univariate in `elim` (or constant).
        if residual.vars().is_empty() {
            // A constant strict comparison `c ⋈ 0`: false ⇒ the whole cell is
            // Unsat; true ⇒ the atom is vacuous and dropped.
            let c = residual
                .terms
                .get(&Vec::new())
                .copied()
                .unwrap_or_else(Rational::zero);
            if !sign_satisfies(atom.cmp, Sign::of_rational(c)) {
                return Some(CellOutcome::Unsat);
            }
            continue;
        }
        let poly = residual.to_single_var_integer_poly(elim)?;
        if poly.len() <= 1 {
            // Should not happen (residual has `elim`), but stay safe.
            return None;
        }
        single_atoms.push(Atom {
            cmp: atom.cmp,
            poly,
        });
    }
    if single_atoms.is_empty() {
        // Every atom collapsed to a satisfied constant ⇒ the cell is satisfiable;
        // any rational `elim` value (0) is a witness for the surviving (empty)
        // constraint set.
        return Some(CellOutcome::Sat(Value::Real(Rational::zero())));
    }
    match decide_system_value(&single_atoms)? {
        SystemVerdict::Unsat => Some(CellOutcome::Unsat),
        SystemVerdict::Sat(v) => Some(CellOutcome::Sat(v)),
    }
}

// ============================================================================
// Complete CAD for a MIXED / NON-STRICT 2-variable component
// (the CAD/nlsat ladder, step 5 — non-strict slice, RATIONAL critical points).
// ============================================================================
//
// Scope: a connected 2-variable component {x, y} in which AT LEAST ONE atom is
// NON-STRICT (`=`, `≤`, or `≥`) — strict atoms (`<`, `>`, `≠`) may appear
// alongside. (An ALL-STRICT component is owned by `decide_strict_cad_two_var`
// above; an ALL-EQUALITY component is owned by the grid lift; this routine is the
// remaining mixed/non-strict case, and otherwise declines.)
//
// Why a non-strict component needs MORE than open cells:
//
//   The solution set `S ⊆ ℝ²` of a conjunction that contains a non-strict atom is
//   generally NOT open: a `≤`/`≥`/`=` atom is satisfied ON the boundary where its
//   polynomial vanishes — a CRITICAL point of the projection (a 0-cell), not only
//   in an open cell's interior. So a solution can live EXACTLY on a critical
//   `keep`-value (the section over `x = α`), which the strict path (open cells
//   only) would miss ⇒ a wrong `Unsat`. We therefore additionally sample EACH
//   critical `keep`-value itself.
//
// THE COMPLETENESS ARGUMENT (soundness of BOTH Sat and Unsat):
//
//   PROJECTION (identical to the strict path): let `Proj` be the univariate-in-
//   `keep` polynomials — for each `p`: its leading coeff in `elim` `lc_elim(p)`,
//   its discriminant in `elim` `disc_elim(p) = Res_elim(p, ∂p/∂elim)`, every
//   pairwise resultant `Res_elim(p, q)`, and any `p` constant in `elim` contributed
//   as itself (its `elim`-independent zero set is still a critical `keep`-locus).
//   Off the real zeros `α₁ < … < α_k` of `Proj` (the critical `keep`-values), the
//   number and `elim`-order of the real `elim`-roots of every `p` are CONSTANT
//   (McCallum/Collins sign-invariance), so on each open `keep`-cell `(αᵢ, αᵢ₊₁)`
//   (and the two tails) the truth of the WHOLE system as a function of `elim` is
//   the same at every `keep` in the cell.
//
//   The solution set `S` is a finite union of CELLS of this decomposition: the
//   open `keep`-cells (where it is sign-invariant) AND the critical `keep`-sections
//   `keep = αᵢ` (the 0-cells where a non-strict atom may hold on a boundary).
//   Therefore `S ≠ ∅` iff SOME open `keep`-cell OR SOME critical `keep`-value
//   carries a satisfying `elim`. We sample BOTH:
//     (a) one RATIONAL interior point per open `keep`-cell (via `cell_samples`,
//         representative by sign-invariance), AND
//     (b) each RATIONAL critical `keep`-value itself (the 0-cells).
//   At each sampled rational `keep := s` the system becomes a conjunction of
//   single-variable constraints in `elim` with RATIONAL coefficients, decided
//   COMPLETELY by `decide_system_value` (which handles ALGEBRAIC `elim`-roots, so
//   the `elim` axis needs no restriction).
//
//   VERDICTS:
//     • SAT — the first sampled `keep := s` whose `elim`-system is `Sat(elim*)` ⇒
//       the component is Sat with `(keep→s, elim→elim*)`; the caller replay-checks
//       the full model against the ORIGINAL assertions. (`s` is rational; `elim*`
//       may be rational or algebraic.)
//     • UNSAT — EVERY sampled `keep := s` (open-cell points AND every rational
//       critical value) yields a definite Unsat `elim`-system, AND the
//       decomposition was complete (all critical `keep`-values RATIONAL, isolation
//       complete, within the cell cap) ⇒ the component is Unsat, EXHAUSTIVELY.
//
//   ALGEBRAIC critical `keep`-values are now DECIDED (not declined): at an algebraic
//   `α` the slice `keep = α` is decomposed along `elim` by the roots of
//   `Res_keep(m, p)` (m = α's integer min-poly), a SUPERSET of the true elim-cell
//   boundaries ⇒ sign-invariant cells; every atom's sign at `(α, β*)` is then
//   evaluated EXACTLY by algebraic field arithmetic (no substitution into a number
//   field — `α` and `β*` are bound as exact `Value`s and the poly is evaluated
//   through the field operations). See [`decide_nonstrict_cell_algebraic`].
//
// We DECLINE (`None`) on ANY completeness doubt: a degenerate projection, an
// incomplete root isolation, an unresolved separation, an algebraic min-poly /
// interval that does not fit the `i128` bound, an indeterminate field-arithmetic
// sign, a per-cell `decide_system_value` that returns `None` (Unknown), overflow,
// or the cell cap. We NEVER claim Unsat with a gap, nor Sat without a replayable
// witness.

/// Decide a MIXED / NON-STRICT 2-variable component `comp` (variables `v0`, `v1`;
/// at least one atom `=`/`≤`/`≥`) by a complete cylindrical decomposition: project
/// onto a `keep` axis, isolate the critical `keep`-values, then sample one rational
/// interior point per open `keep`-cell AND each critical `keep`-value 0-cell. A
/// RATIONAL critical value is decided by substitution; an ALGEBRAIC critical value
/// `α` is decided by the `Res_keep(m, p)` elim-decomposition + exact field
/// arithmetic (no number-field substitution).
///
/// Returns `Some(Sat(bindings))` / `Some(Unsat)` when the decomposition is provably
/// complete, or `None` to DECLINE (any projection/isolation/sample/cell
/// indeterminacy, an algebraic min-poly past the `i128` bound, an indeterminate
/// field-arithmetic sign, or the cell cap) — never a wrong verdict. Sat bindings are
/// replay-checked by the caller.
fn decide_nonstrict_cad_two_var(
    comp: &[&MultiAtom],
    v0: SymbolId,
    v1: SymbolId,
) -> Option<TwoVarVerdict> {
    // Only entered for a mixed/non-strict component; an all-strict one is owned by
    // `decide_strict_cad_two_var`, so guard against double-handling.
    debug_assert!(
        comp.iter()
            .any(|a| matches!(a.cmp, Cmp::Eq | Cmp::Le | Cmp::Ge))
    );

    // The distinct constraint polynomials, coprime-split so a shared factor does not
    // make a pairwise resultant vanish and force a decline (the split preserves the
    // cell arrangement and every atom's per-cell sign; atoms are still evaluated on
    // their ORIGINAL polynomials). See [`coprime_split`].
    let owned: Vec<MultiPoly> = comp.iter().map(|a| a.poly.clone()).collect();
    let split = coprime_split(&owned);
    let polys: Vec<&MultiPoly> = split.iter().collect();
    if polys.is_empty() {
        return None;
    }

    // Try projecting onto v0 (eliminate v1) AND onto v1 (eliminate v0). Either
    // orientation is sound and complete by the same cell argument; trying both
    // rescues a shape one orientation declines on (e.g. a degenerate projection or
    // an `i128`-overflowing algebraic critical value along one axis but not the other).
    for &(elim, keep) in &[(v1, v0), (v0, v1)] {
        if let Some(v) = nonstrict_cad_along(comp, &polys, elim, keep) {
            return Some(v);
        }
    }
    None
}

/// One orientation of [`decide_nonstrict_cad_two_var`]: eliminate `elim`, isolate
/// the critical `keep`-values (RATIONAL and ALGEBRAIC), sample the open `keep`-cells
/// AND each critical 0-cell, decide each slice — rational 0-cells by substitution
/// ([`decide_nonstrict_cell`]), algebraic 0-cells by the `Res_keep(m, p)`
/// elim-decomposition + field arithmetic ([`decide_nonstrict_cell_algebraic`]).
/// `None` declines this orientation.
fn nonstrict_cad_along(
    comp: &[&MultiAtom],
    polys: &[&MultiPoly],
    elim: SymbolId,
    keep: SymbolId,
) -> Option<TwoVarVerdict> {
    // PROJECTION onto `keep` — IDENTICAL to the strict path (`strict_cad_along`):
    // leading coeff in `elim`, discriminant in `elim`, pairwise resultants, and any
    // `p` constant in `elim` contributed as itself. A degenerate/non-isolable
    // boundary (vanishing discriminant / resultant) ⇒ decline.
    let mut proj: Vec<Vec<i128>> = Vec::new();
    for p in polys {
        if degree_in(p, elim) == 0 {
            // `p` constant in `elim`: its real zeros in `keep` ARE critical
            // `keep`-values (a non-strict atom can hold exactly there). It is
            // already univariate in `keep`; add it directly.
            let ipoly = p.to_single_var_integer_poly(keep)?;
            if ipoly.len() > 1 {
                proj.push(ipoly);
            }
            // constant-in-both ⇒ no critical value.
            continue;
        }
        let pc = poly_in_elim_over_keep(p, elim, keep)?;
        let lead = pc.last()?;
        if let Some(ip) = rat_coeffs_to_integer(lead) {
            if ip.len() > 1 {
                proj.push(ip);
            }
        } else {
            return None; // overflow ⇒ decline (cannot guarantee sign-invariance)
        }
        let dp = derivative_in(p, elim)?;
        if degree_in(&dp, elim) == 0 {
            // p linear in `elim`: no discriminant boundary.
        } else {
            let disc = resultant_univariate(p, &dp, elim, keep)?;
            if disc.len() > 1 {
                proj.push(disc);
            } else if disc.first().copied().unwrap_or(0) == 0 {
                return None; // repeated `elim`-root for all `keep` ⇒ cannot delineate
            }
        }
    }
    for i in 0..polys.len() {
        for j in (i + 1)..polys.len() {
            if degree_in(polys[i], elim) == 0 || degree_in(polys[j], elim) == 0 {
                continue;
            }
            let res = resultant_univariate(polys[i], polys[j], elim, keep)?;
            if res.len() > 1 {
                proj.push(res);
            } else if res.first().copied().unwrap_or(0) == 0 {
                return None; // shared `elim`-factor for all `keep` ⇒ cannot delineate
            }
        }
    }

    // ISOLATE all real roots of every projection polynomial; merge, sort, dedup the
    // distinct critical `keep`-values. `isolate_roots` is complete-or-None.
    let mut roots: Vec<Root> = Vec::new();
    for pp in &proj {
        roots.extend(isolate_roots(pp)?);
    }
    let crit = dedup_sorted_roots(&roots)?;
    if crit.len() > MAX_CAD_CELLS {
        return None; // bounded — never OOM / hang
    }

    // The critical `keep`-values come in two flavors. The RATIONAL 0-cells are
    // decided by substituting `keep := q` and running the existing rational cell
    // decider. The ALGEBRAIC 0-cells are decided by the `Res_keep(m, p)`
    // elim-decomposition + exact field arithmetic (see `decide_nonstrict_cell_algebraic`).
    // Both flavors, plus the open `keep`-cell interiors (always rational, from
    // `cell_samples`), together partition the WHOLE `keep`-axis — so Unsat reached
    // below is EXHAUSTIVE only if every one of them is decided definitively.
    let mut crit_rationals: Vec<Rational> = Vec::new();
    let mut crit_algebraics: Vec<&RealAlgebraic> = Vec::new();
    for r in &crit {
        match r {
            Root::Rational(q) => crit_rationals.push(*q),
            Root::Algebraic(a) => crit_algebraics.push(a),
        }
    }

    // SAMPLE: one rational interior point per open `keep`-cell (the open cells). The
    // open cells plus ALL critical 0-cells (rational and algebraic) cover EVERY
    // `keep`-cell of the decomposition.
    let open_samples = cell_samples(&crit)?;

    // Decide each open-cell interior and each RATIONAL critical 0-cell (open-cell
    // interiors first so a SAT witness stays as simple as possible).
    for &s in open_samples.iter().chain(crit_rationals.iter()) {
        match decide_nonstrict_cell(comp, keep, elim, s)? {
            CellOutcome::Sat(elim_val) => {
                // A genuine solution at the rational `keep = s` (an open-cell interior
                // or a rational critical 0-cell). The caller replay-checks the full
                // model against the ORIGINAL assertions.
                return Some(TwoVarVerdict::Sat(vec![
                    (keep, Value::Real(s)),
                    (elim, elim_val),
                ]));
            }
            CellOutcome::Unsat => {}
        }
    }

    // Decide each ALGEBRAIC critical 0-cell `keep := α` by the `Res_keep(m, p)`
    // elim-decomposition + exact field-arithmetic sign tests. A `None` here
    // (incomplete isolation / field-arithmetic indeterminacy / a bound) ⇒ DECLINE
    // the whole orientation — never claim Unsat with an undecided algebraic cell.
    for a in &crit_algebraics {
        match decide_nonstrict_cell_algebraic(comp, keep, elim, a)? {
            CellOutcome::Sat(elim_val) => {
                // A genuine solution at the algebraic `keep = α`. The witness binds
                // `keep` to the algebraic value and `elim` to the (rational or
                // algebraic) elim-sample; the caller replay-checks via the exact
                // field-arithmetic evaluator on the ORIGINAL assertions.
                return Some(TwoVarVerdict::Sat(vec![
                    (keep, Value::RealAlgebraic((*a).clone())),
                    (elim, elim_val),
                ]));
            }
            CellOutcome::Unsat => {}
        }
    }

    // Every open `keep`-cell sample, every rational critical 0-cell, AND every
    // algebraic critical 0-cell gave a definite Unsat `elim`-system (an Unknown one
    // would have declined via `?`). The keep-axis is FULLY decomposed (open cells +
    // ALL critical 0-cells, rational and algebraic), the isolation was complete, and
    // we stayed within the cap, so the decomposition is COMPLETE — by the cell
    // argument (open cells + 0-cells partition the solution set), the component is
    // Unsat, EXHAUSTIVELY.
    Some(TwoVarVerdict::Unsat)
}

/// Substitute the RATIONAL `keep := s` into every atom of the (possibly non-strict)
/// component, producing a conjunction of single-variable constraints in `elim`
/// (with their ORIGINAL comparators, strict or non-strict), and decide it COMPLETELY
/// with [`decide_system_value`]. `None` declines (overflow, a degenerate residual
/// that loses `elim`, or an indeterminate sub-decision ⇒ never Unsat with a gap).
fn decide_nonstrict_cell(
    comp: &[&MultiAtom],
    keep: SymbolId,
    elim: SymbolId,
    s: Rational,
) -> Option<CellOutcome> {
    let mut subst: BTreeMap<SymbolId, Rational> = BTreeMap::new();
    subst.insert(keep, s);
    let mut single_atoms: Vec<Atom> = Vec::with_capacity(comp.len());
    for atom in comp {
        let residual = substitute_rationals(&atom.poly, &subst)?;
        if residual.vars().is_empty() {
            // A constant comparison `c ⋈ 0`: false ⇒ the whole cell is Unsat;
            // true ⇒ the atom is vacuous and dropped.
            let c = residual
                .terms
                .get(&Vec::new())
                .copied()
                .unwrap_or_else(Rational::zero);
            if !sign_satisfies(atom.cmp, Sign::of_rational(c)) {
                return Some(CellOutcome::Unsat);
            }
            continue;
        }
        let poly = residual.to_single_var_integer_poly(elim)?;
        if poly.len() <= 1 {
            return None; // residual mentions `elim` yet collapsed ⇒ decline
        }
        single_atoms.push(Atom {
            cmp: atom.cmp,
            poly,
        });
    }
    if single_atoms.is_empty() {
        // Every atom collapsed to a satisfied constant ⇒ the cell is satisfiable;
        // any rational `elim` value (0) witnesses the (empty) residual system.
        return Some(CellOutcome::Sat(Value::Real(Rational::zero())));
    }
    match decide_system_value(&single_atoms)? {
        SystemVerdict::Unsat => Some(CellOutcome::Unsat),
        SystemVerdict::Sat(v) => Some(CellOutcome::Sat(v)),
    }
}

// ============================================================================
// Algebraic critical `keep`-value: decide the slice `keep = α` (α irrational).
//
// At an algebraic critical `keep`-value `α` with integer min-poly
// `m(x) = α.defining_poly()`, the elim-cell boundaries of the slice are the `β`
// with some atom `p(α, β) = 0`. Every such `β` is a root of the RATIONAL
// univariate
//
//     R_p(y) = Res_x(m(x), p(x, y))          (eliminate x = `keep`, keep y = `elim`)
//
// because a common point `(α, β)` with `m(α)=0` and `p(α,β)=0` forces
// `Res_x(m, p)(β) = 0`. `Res_x(m, p)` may carry EXTRA `β`-roots coming from `m`'s
// other (conjugate) roots — that is SOUND: a SUPERSET of the true boundaries only
// REFINES the elim-cells (each remains sign-invariant for every atom at this fixed
// `α`), it never MISSES a boundary. For a `p` CONSTANT in `keep` (it does not
// mention `α`) we take its `elim`-roots directly (`p(β) = 0`), which is the same
// boundary set without a resultant.
//
// PROCEDURE:
//   1. For each atom poly `p`, collect its `β`-boundary candidates: the real roots
//      of `R_p` (or of `p` itself if `p` is constant in `keep`).
//   2. Merge/sort/dedup all atoms' `β`-candidates ⇒ the elim-critical points at `α`.
//      Build elim-cells: one RATIONAL interior sample per open elim-cell (via the
//      existing `cell_samples` logic over these β) PLUS each β itself (the 0-cells).
//   3. For each elim-sample `β*` (rational or algebraic) evaluate the SIGN of every
//      atom poly `p` at `(keep = α, elim = β*)` EXACTLY via the algebraic field
//      arithmetic (`multipoly_sign_at`). A point satisfies the slice iff every
//      atom's sign satisfies its comparator.
//
// VERDICT: the slice is **Sat** if some elim-sample satisfies all atoms (witness
// `(α, β*)`, replay-checked by the caller), **Unsat** if none does, and DECLINES
// (`None`) if any field-arithmetic sign is indeterminate / overflows, any isolation
// is incomplete, or a bound is hit — never Unsat with a gap.
// ============================================================================

/// Decide the slice `keep = α` (α an ALGEBRAIC critical `keep`-value) of a
/// mixed/non-strict 2-variable component, via the `Res_keep(m, p)` elim-decomposition
/// plus exact field-arithmetic sign tests. `None` declines (see the module block
/// above) — never Unsat with an undecided cell, never Sat without a checkable witness.
fn decide_nonstrict_cell_algebraic(
    comp: &[&MultiAtom],
    keep: SymbolId,
    elim: SymbolId,
    alpha: &RealAlgebraic,
) -> Option<CellOutcome> {
    // α's integer min-poly, lifted into a univariate `MultiPoly` in the `keep`
    // variable so the existing `resultant_univariate(m, p, keep, elim)` (which
    // eliminates `keep` and keeps `elim`) applies directly.
    let m_i128 = alpha.defining_poly_i128()?; // i128-bound ⇒ decline (sound Unknown)
    let m_poly = univariate_multipoly(&m_i128, keep)?;
    if degree_in(&m_poly, keep) == 0 {
        return None; // α irrational ⇒ min-poly has positive keep-degree; defensive
    }

    // 1. Collect every `β`-boundary candidate (the elim-critical points at `α`).
    let mut beta_polys: Vec<Vec<i128>> = Vec::new();
    for p in distinct_polys(comp) {
        if degree_in(p, elim) == 0 {
            // `p` constant in `elim`: it imposes no `elim`-boundary (its zero set, if
            // any, is a `keep`-only condition already captured by the `keep`-axis
            // decomposition that produced `α`). Nothing to add to the elim-axis.
            continue;
        }
        if degree_in(p, keep) == 0 {
            // `p` constant in `keep` (it does not mention `α`): its `elim`-boundaries
            // are exactly the roots of `p(β)` — take them directly, no resultant.
            let ipoly = p.to_single_var_integer_poly(elim)?;
            if ipoly.len() > 1 {
                beta_polys.push(ipoly);
            }
            continue;
        }
        // Genuinely bivariate: R_p(y) = Res_x(m(x), p(x, y)), eliminating `keep`.
        // `resultant_univariate` declines (`None`) on an identically-zero resultant
        // (m and p share a `keep`-factor for all `elim` — an over-constrained
        // degeneracy we decline on rather than guess).
        let res = resultant_univariate(&m_poly, p, keep, elim)?;
        if res.len() > 1 {
            beta_polys.push(res);
        }
        // A constant nonzero resultant ⇒ no `elim`-boundary from this atom at α.
    }

    // 2. Merge the `β`-candidates → the elim-critical points; build the elim-cells:
    //    one rational interior per open cell PLUS each β as a 0-cell.
    let mut beta_roots: Vec<Root> = Vec::new();
    for bp in &beta_polys {
        beta_roots.extend(isolate_roots(bp)?); // complete-or-None
    }
    let beta_crit = dedup_sorted_roots(&beta_roots)?;
    if beta_crit.len() > MAX_CAD_CELLS {
        return None; // bounded — never OOM / hang
    }
    let beta_open = cell_samples(&beta_crit)?;

    // The α binding is fixed for the whole slice; build it once.
    let alpha_val = Value::RealAlgebraic(alpha.clone());

    // 3. Test each elim-sample (open-cell interiors first — a rational `β*` keeps the
    //    witness simpler; then the 0-cells, which a non-strict atom may need exactly).
    for q in &beta_open {
        let mut point: BTreeMap<SymbolId, Value> = BTreeMap::new();
        point.insert(keep, alpha_val.clone());
        point.insert(elim, Value::Real(*q));
        if cell_point_satisfies_all(comp, &point)? {
            return Some(CellOutcome::Sat(Value::Real(*q)));
        }
    }
    for r in &beta_crit {
        let beta_val = match r {
            Root::Rational(q) => Value::Real(*q),
            // Coarsen the algebraic `β` to a small-denominator bracket so the field
            // arithmetic does not overflow on over-refined endpoints (mirrors the
            // grid lift's `root_to_value`). `None` ⇒ decline.
            Root::Algebraic(b) => Value::RealAlgebraic(coarsen_algebraic(b)?),
        };
        let mut point: BTreeMap<SymbolId, Value> = BTreeMap::new();
        point.insert(keep, alpha_val.clone());
        point.insert(elim, beta_val.clone());
        if cell_point_satisfies_all(comp, &point)? {
            return Some(CellOutcome::Sat(beta_val));
        }
    }

    // Every elim-cell (open interiors + all β 0-cells) at this fixed `α` is
    // definitively Unsat (an indeterminate sign would have declined via `?`). The
    // elim-axis is fully decomposed by `Res_keep(m, p)`'s roots (a SUPERSET of the
    // true boundaries ⇒ sign-invariant cells), and every sign was exact, so the
    // slice is Unsat — EXHAUSTIVELY for `keep = α`.
    Some(CellOutcome::Unsat)
}

/// Whether the component holds at the (mixed rational/algebraic) `point`, by exact
/// field-arithmetic sign of every atom poly. `Some(true)` = all atoms satisfied,
/// `Some(false)` = some atom definitely violated, `None` = an indeterminate /
/// overflowing sign ⇒ the caller DECLINES (never a wrong Unsat).
fn cell_point_satisfies_all(
    comp: &[&MultiAtom],
    point: &BTreeMap<SymbolId, Value>,
) -> Option<bool> {
    for atom in comp {
        let s = multipoly_sign_at(&atom.poly, point)?;
        if !sign_satisfies(atom.cmp, s) {
            return Some(false);
        }
    }
    Some(true)
}

/// The distinct constraint polynomials of a component (deduplicated by structure).
fn distinct_polys<'a>(comp: &[&'a MultiAtom]) -> Vec<&'a MultiPoly> {
    let mut polys: Vec<&MultiPoly> = Vec::new();
    for atom in comp {
        if !polys.iter().any(|p| p.terms == atom.poly.terms) {
            polys.push(&atom.poly);
        }
    }
    polys
}

/// Lift an LSB-first integer polynomial to a univariate [`MultiPoly`] in `var`.
/// `None` on a degree past [`MAX_DEGREE`] or a coefficient/exponent overflow.
fn univariate_multipoly(poly: &[i128], var: SymbolId) -> Option<MultiPoly> {
    if poly.len().checked_sub(1)? > MAX_DEGREE {
        return None;
    }
    let mut out = MultiPoly::zero();
    for (e, &c) in poly.iter().enumerate() {
        if c == 0 {
            continue;
        }
        let key: MonoKey = if e == 0 {
            Vec::new()
        } else {
            vec![(var, u32::try_from(e).ok()?)]
        };
        out.add_term(key, Rational::integer(c))?;
    }
    Some(out)
}

// ============================================================================
// Recursive N-variable strict CAD (all-strict components, any N ≥ 2)
// (the CAD/nlsat ladder, step 4 — recursive cylindrical decomposition).
// ============================================================================
//
// Scope: a connected component of N ≥ 2 variables in which EVERY atom is a STRICT
// inequality (`<`, `>`, or `≠`). The N = 2 case is owned by the (well-tested)
// `decide_strict_cad_two_var` above; this engine is routed only for N ≥ 3
// (`decide_strict_cad_nvar`), and reuses the SAME open-cell recursion internally,
// so the cell decomposition is one implementation, not divergent code.
//
// THE SOUNDNESS FACT (carries over to every dimension):
//
//   The solution set `S ⊆ ℝ^N` of a conjunction of STRICT inequalities is OPEN:
//   each atom `pᵢ ⋈ 0` (⋈ ∈ {<, >, ≠}) defines an open subset of ℝ^N, and a
//   finite intersection of open sets is open. So if `S ≠ ∅` it contains an open
//   box, hence a point with RATIONAL coordinates. More strongly, on each open
//   cell of the cylindrical arrangement the truth of the whole strict system is
//   constant, so ONE rational interior sample per open cell decides that cell
//   exactly — AT EVERY RECURSION LEVEL. The whole decomposition therefore stays
//   rational, with NO algebraic-coordinate substitution.
//
// `open_cell_samples(polys, vars)` returns a rational sample point (one per open
// cell of the arrangement of the zero sets of `polys`, covering ℝ^|vars| off the
// projection zeros), or `None` to DECLINE on any completeness doubt:
//
//   • N == 1: isolate the real roots of all (univariate-in the sole var) polys;
//     return one rational interior point per open interval (below least / between
//     consecutive / above greatest / `0` if none) — exactly the `cell_samples`
//     logic the 2-var path uses.
//
//   • N > 1: pick an elimination variable `e`; PROJECT it out — for each `p` with
//     positive degree in `e`: its leading coefficient in `e` (a delineability
//     boundary, where deg_e(p) drops), its discriminant in `e`
//     (`Res_e(p, ∂p/∂e)`, where p gains a repeated e-root), and for every pair
//     `p ≠ q` (both of positive e-degree) the resultant `Res_e(p, q)` (where p and
//     q share an e-root) — all multivariate polynomials in `vars \ {e}`. A `p`
//     CONSTANT in `e` contributes ITSELF to the projection (its e-independent zero
//     set is still a critical locus and keeps the cover complete). Recurse:
//     `base = open_cell_samples(projected, vars\{e})`. For EACH base rational
//     sample `P`: substitute `P` into the ORIGINAL `polys` → univariate in `e`;
//     isolate its real e-roots; take rational interior samples of the open
//     e-intervals; extend `P` with each e-sample. Collect all.
//
// PROJECTION gives per-cell sign-invariance (McCallum/Collins): over a cell where
// none of the projection polynomials vanish, lc_e ≠ 0 fixes deg_e(p), disc_e ≠ 0
// keeps p's e-roots simple, and Res_e(p,q) ≠ 0 keeps p and q from sharing an
// e-root — so the number and e-order of every p's real e-roots are CONSTANT across
// the cell, and the strict system's truth as a function of e is the same at every
// `P` in the cell. Hence sampling ONE rational interior P per projected cell, then
// recursing into e, loses no cell of ℝ^N.
//
// DECLINE (`None`) — never proceed past a gap — on:
//   • an identically-zero discriminant or pairwise resultant (NULLIFICATION /
//     non-isolated coincidence ⇒ sign-invariance not guaranteed),
//   • a poly NULLIFIED at a base point (all its e-coefficients vanish there ⇒ its
//     e-degree collapses ⇒ delineability fails ⇒ decline; we never sample its e),
//   • overflow in coefficient clearing / projection / substitution,
//   • any incomplete root isolation (`isolate_roots`/`sort_roots` return `None`),
//   • a global cell-count cap [`MAX_CAD_CELLS`] counted across the WHOLE recursion.
//
// VERDICTS (`decide_strict_cad_nvar`): build the poly set, run
// `open_cell_samples(polys, all_vars)`; for each full RATIONAL sample point
// evaluate EVERY atom's sign exactly (substitute all vars → constant → sign via
// the exact rational/algebraic evaluator). If all atoms hold at some point → Sat
// with that rational binding (the caller replay-checks against the original
// assertions). If every sample point fails → Unsat (COMPLETE by the open-set
// argument: a strict solution lies in an open box that meets some sampled open
// cell, contradicting that cell's failure). Any `None` from the decomposition ⇒
// decline (Unknown).
//
// This handles ALL-STRICT components ONLY; equalities / non-strict atoms still
// route elsewhere (the grid / resultant paths) or decline. No floating point;
// every sign test is exact over `Rational` / `RealAlgebraic`. Bounded — the
// cell-count cap guards against combinatorial blow-up in N (no OOM / hang).

/// A budget for the recursive cell enumeration: a single shared counter,
/// decremented as cells are produced anywhere in the recursion. Hitting zero ⇒
/// the whole decomposition declines (bounded — no OOM / hang in higher N). Held in
/// a [`Cell`] so the recursive call and its nested visitor closure can BOTH charge
/// it through a shared reference (no `&mut` aliasing, no `unsafe`).
struct CellBudget {
    remaining: core::cell::Cell<usize>,
}

impl CellBudget {
    fn new() -> Self {
        CellBudget {
            remaining: core::cell::Cell::new(MAX_CAD_CELLS),
        }
    }

    /// Charge one produced cell; `None` (decline) once the budget is exhausted.
    fn charge(&self) -> Option<()> {
        let next = self.remaining.get().checked_sub(1)?;
        self.remaining.set(next);
        Some(())
    }
}

/// One rational sample point: a binding of each (already-eliminated / sampled)
/// variable to an exact rational, interior to an open cell of the arrangement.
type SamplePoint = BTreeMap<SymbolId, Rational>;

/// The outcome of visiting one full sample point in the recursive decomposition.
enum Visit {
    /// Keep enumerating cells.
    Continue,
    /// Stop the whole enumeration early (a satisfying witness was found).
    Stop,
}

/// Recursive cylindrical decomposition for an ALL-STRICT system: invoke `visit`
/// once per open cell of the arrangement of the zero sets of `polys` over `vars`,
/// passing a RATIONAL interior sample point (covering ℝ^|vars| off the projection
/// zeros). Returns `Some(true)` if a visit asked to stop (witness found),
/// `Some(false)` if every cell was visited without stopping, or `None` to DECLINE
/// on any completeness doubt (see the module block above).
///
/// The visitor pattern lets the decision SHORT-CIRCUIT on the first satisfying
/// point (Sat) without materializing every cell, while still visiting EVERY cell
/// when none satisfies (the exhaustive Unsat). `vars` is the ordered set of
/// variables still to decompose (deterministic `BTreeSet` order ⇒ a fixed
/// elimination order); `partial` is the rational binding accumulated by outer
/// levels (the cells visited extend it); `budget` bounds the TOTAL cell count
/// across the whole recursion.
fn visit_open_cells(
    polys: &[MultiPoly],
    vars: &BTreeSet<SymbolId>,
    partial: &SamplePoint,
    budget: &CellBudget,
    visit: &mut dyn FnMut(&SamplePoint) -> Option<Visit>,
) -> Option<bool> {
    if vars.is_empty() {
        // No variables left: `partial` is a full cell point. Visit it.
        budget.charge()?;
        return Some(matches!(visit(partial)?, Visit::Stop));
    }
    if vars.len() == 1 {
        let var = *vars.iter().next().unwrap();
        // Each poly is univariate in `var` (or constant); isolate all real roots.
        let mut roots: Vec<Root> = Vec::new();
        for p in polys {
            if degree_in(p, var) == 0 {
                // Constant in `var`: contributes no critical value here (its sign
                // does not depend on `var`). A poly mentioning a FOREIGN variable
                // would have been rejected by `project_strict`'s subset check, so at
                // this leaf there are no foreign vars.
                continue;
            }
            let ipoly = p.to_single_var_integer_poly(var)?;
            if ipoly.len() <= 1 {
                continue;
            }
            roots.extend(isolate_roots(&ipoly)?);
        }
        let crit = dedup_sorted_roots(&roots)?;
        let samples = cell_samples(&crit)?;
        for s in samples {
            budget.charge()?;
            let mut pt = partial.clone();
            pt.insert(var, s);
            if matches!(visit(&pt)?, Visit::Stop) {
                return Some(true);
            }
        }
        return Some(false);
    }

    // N > 1: pick the (deterministic) first variable as the elimination var.
    let elim = *vars.iter().next().unwrap();
    let mut rest: BTreeSet<SymbolId> = vars.clone();
    rest.remove(&elim);

    // PROJECTION: build the projection polynomials in `rest`.
    let projected = project_strict(polys, elim, &rest)?;

    // Recurse to visit the open cells of the projection over `rest`. For each base
    // point, substitute it into the ORIGINAL polys (univariate in `elim`), isolate
    // the e-roots, sample the open e-intervals, and visit each extended point.
    visit_open_cells(&projected, &rest, partial, budget, &mut |base_pt| {
        let mut roots: Vec<Root> = Vec::new();
        for p in polys {
            // A poly constant in `elim` does not constrain the e-fiber; its critical
            // loci were captured in the projection as `p` itself.
            if degree_in(p, elim) == 0 {
                continue;
            }
            // Substitute the base rational point into `p` ⇒ univariate in `elim`.
            // NULLIFICATION guard: if every e-coefficient vanishes at `base_pt` (the
            // residual loses `elim` entirely) the e-degree of `p` collapsed here ⇒
            // delineability fails ⇒ decline (propagate `None`).
            let residual = substitute_rationals(p, base_pt)?;
            if degree_in(&residual, elim) == 0 {
                return None;
            }
            let ipoly = residual.to_single_var_integer_poly(elim)?;
            if ipoly.len() <= 1 {
                return None; // residual mentions `elim` yet collapsed ⇒ decline
            }
            roots.extend(isolate_roots(&ipoly)?);
        }
        let crit = dedup_sorted_roots(&roots)?;
        let samples = cell_samples(&crit)?;
        for s in samples {
            budget.charge()?;
            let mut pt = base_pt.clone();
            pt.insert(elim, s);
            if matches!(visit(&pt)?, Visit::Stop) {
                return Some(Visit::Stop);
            }
        }
        Some(Visit::Continue)
    })
}

/// Sort isolated `roots` ascending and deduplicate EQUAL critical values (a shared
/// root of two polys) so cell samples land in genuinely distinct open cells. `None`
/// if any pair cannot be ordered exactly (caller declines).
fn dedup_sorted_roots(roots: &[Root]) -> Option<Vec<Root>> {
    let ordered = sort_roots(roots, None)?;
    let mut crit: Vec<Root> = Vec::new();
    for r in ordered {
        match crit.last() {
            Some(prev) if compare_roots(prev, &r)? == Ordering::Equal => {}
            _ => crit.push(r),
        }
    }
    Some(crit)
}

/// Project the elimination variable `elim` out of `polys`, returning the
/// projection polynomials over the remaining variables `rest`: each `p`'s leading
/// coefficient in `elim`, discriminant in `elim` (`Res_elim(p, ∂p/∂elim)`), and
/// every pairwise resultant `Res_elim(p, q)` — plus any `p` CONSTANT in `elim`
/// contributed as itself (its e-independent critical locus). `None` declines on a
/// nullified discriminant / resultant (non-isolated coincidence) or any overflow.
fn project_strict(
    polys: &[MultiPoly],
    elim: SymbolId,
    rest: &BTreeSet<SymbolId>,
) -> Option<Vec<MultiPoly>> {
    // Coprime-split the projection INPUTS at every recursion level: a shared factor
    // between two of them (which arises freshly among the PROJECTED polynomials, not
    // only among the original atoms) makes their pairwise resultant vanish
    // (`Res ≡ 0`) and would force a decline. The split preserves the union of zero
    // sets — hence the whole cell arrangement — so projecting the split factors is a
    // valid (McCallum-style irreducible-factor) projection for the same arrangement,
    // never a wrong verdict. See [`coprime_split`].
    let split = coprime_split(polys);
    let polys: &[MultiPoly] = &split;
    let mut proj: Vec<MultiPoly> = Vec::new();
    for p in polys {
        if degree_in(p, elim) == 0 {
            // Constant in `elim`: its zero set is e-independent and IS a critical
            // locus in `rest` (the strict atom can flip across it). Keep it whole so
            // the projected cover is complete. Skip a constant-in-EVERYTHING poly.
            if !p.vars().is_empty() {
                push_proj(&mut proj, p.clone());
            }
            continue;
        }
        // Leading coefficient of `p` in `elim` (a MultiPoly in `rest`): its zeros
        // are where deg_elim(p) drops (a delineability boundary).
        let lead = leading_coeff_in(p, elim);
        if !lead.is_zero() && !lead.vars().is_empty() {
            push_proj(&mut proj, lead);
        }
        // Discriminant of `p` in `elim` = Res_elim(p, ∂p/∂elim).
        let dp = derivative_in(p, elim)?;
        if degree_in(&dp, elim) == 0 {
            // p linear in `elim`: its single e-root never collides ⇒ no discriminant
            // boundary. Nothing to add.
        } else {
            match multi_resultant(p, &dp, elim)? {
                ResultantOutcome::Poly(disc) => push_proj(&mut proj, disc),
                ResultantOutcome::Zero => return None, // repeated e-root for all rest
                ResultantOutcome::NonzeroConstant => {}
            }
        }
    }
    // Pairwise resultants Res_elim(p, q).
    for i in 0..polys.len() {
        for j in (i + 1)..polys.len() {
            if degree_in(&polys[i], elim) == 0 || degree_in(&polys[j], elim) == 0 {
                continue; // a constant-in-elim factor shares no e-root to track
            }
            match multi_resultant(&polys[i], &polys[j], elim)? {
                ResultantOutcome::Poly(res) => push_proj(&mut proj, res),
                ResultantOutcome::Zero => return None, // shared e-factor for all rest
                ResultantOutcome::NonzeroConstant => {}
            }
        }
    }
    // Every projection polynomial must live in `rest` (no `elim`, no foreign var):
    // verify so the recursion stays well-formed (defense-in-depth — the resultant
    // already eliminates `elim`, and the inputs are restricted to `vars`).
    for q in &proj {
        let qv = q.vars();
        if !qv.is_subset(rest) {
            return None;
        }
    }
    Some(proj)
}

/// Add `p` to the projection set, deduplicating by structure (avoid re-isolating
/// the same critical locus). A constant `p` (no variables) is dropped — it never
/// flips sign, so it contributes no critical value.
fn push_proj(proj: &mut Vec<MultiPoly>, p: MultiPoly) {
    if p.vars().is_empty() {
        return;
    }
    if !proj.iter().any(|q| q.terms == p.terms) {
        proj.push(p);
    }
}

/// The leading coefficient of `p` viewed as a univariate polynomial in `elim`: the
/// coefficient (a [`MultiPoly`] in the other variables) of `elim^d`, `d =
/// deg_elim(p)`. The zero poly maps to the zero poly.
fn leading_coeff_in(p: &MultiPoly, elim: SymbolId) -> MultiPoly {
    let d = degree_in(p, elim);
    let mut out = MultiPoly::zero();
    for (k, &c) in &p.terms {
        // Exponent of `elim` in this monomial.
        let mut e = 0u32;
        for &(v, ex) in k {
            if v == elim {
                e = ex;
            }
        }
        if e != d {
            continue;
        }
        // Strip the `elim^d` factor; keep the rest of the monomial. Each surviving
        // `rest` key is distinct (monomials are canonical), so a plain insert is
        // exact (no merge / overflow possible — we only copy an existing coeff).
        let rest: MonoKey = k.iter().copied().filter(|&(v, _)| v != elim).collect();
        out.terms.insert(rest, c);
    }
    out
}

/// The outcome of a multivariate resultant `Res_elim(p, q)` over the remaining
/// variables.
enum ResultantOutcome {
    /// A genuine variable-bearing resultant polynomial in the remaining variables.
    Poly(MultiPoly),
    /// The resultant is identically zero (a shared e-factor for ALL remaining-var
    /// values) — a non-isolated coincidence ⇒ the caller must decline.
    Zero,
    /// The resultant is a nonzero constant — no critical locus in the remaining
    /// variables (p and q never share an e-root). The caller adds nothing.
    NonzeroConstant,
}

/// Hard ceiling on the Sylvester dimension (= `deg_elim(p) + deg_elim(q)`) for the
/// MULTIVARIATE resultant. The determinant is taken by exact Leibniz expansion over
/// the [`MultiPoly`] ring (no division — `MultiPoly` is not a field), which is
/// `O(dim! · dim)` ring multiplications, so the dimension must stay small. Beyond
/// it we decline (bounded — no OOM / hang). For the degree-2 conic systems this
/// slice targets, `deg_elim ≤ 2` ⇒ `dim ≤ 4` (`4! = 24` permutations).
const MAX_MULTI_SYLVESTER_DIM: usize = 6;

/// `Res_elim(p, q)` as a [`MultiPoly`] in the remaining variables, by the Sylvester
/// determinant over the [`MultiPoly`] polynomial ring (each Sylvester entry is a
/// `MultiPoly` coefficient in the remaining variables, computed exactly with no
/// division). Returns the classified [`ResultantOutcome`], or `None` on overflow /
/// the dimension cap. Both `p` and `q` must have positive degree in `elim`.
fn multi_resultant(p: &MultiPoly, q: &MultiPoly, elim: SymbolId) -> Option<ResultantOutcome> {
    let pc = multipoly_in_elim(p, elim)?; // Vec<MultiPoly>, LSB-first in elim
    let qc = multipoly_in_elim(q, elim)?;
    let m = pc.len().checked_sub(1)?; // deg_elim(p)
    let n = qc.len().checked_sub(1)?; // deg_elim(q)
    if m == 0 || n == 0 {
        return None; // not genuinely of positive e-degree
    }
    let dim = m.checked_add(n)?;
    if dim > MAX_MULTI_SYLVESTER_DIM {
        return None;
    }
    // Build the (m+n) × (m+n) Sylvester matrix of `pc` (MSB-first rows) over `qc`.
    // Mirror the univariate layout: `n` shifted rows of `p`'s coefficients, then
    // `m` shifted rows of `q`'s coefficients (coefficients written MSB-first).
    let mut mat: Vec<Vec<MultiPoly>> = vec![vec![MultiPoly::zero(); dim]; dim];
    // p occupies the first `n` rows; q the next `m` rows.
    for (row, slot) in (0..n).zip(0..n) {
        for (i, c) in pc.iter().rev().enumerate() {
            mat[row][slot + i] = c.clone();
        }
    }
    for (row, slot) in (0..m).zip(0..m) {
        for (i, c) in qc.iter().rev().enumerate() {
            mat[n + row][slot + i] = c.clone();
        }
    }
    let det = multipoly_determinant(&mat)?;
    if det.is_zero() {
        return Some(ResultantOutcome::Zero);
    }
    if det.vars().is_empty() {
        return Some(ResultantOutcome::NonzeroConstant);
    }
    Some(ResultantOutcome::Poly(det))
}

/// View `p` as a univariate polynomial in `elim` with [`MultiPoly`] coefficients
/// (in the other variables), LSB-first by the exponent of `elim`. `None` on a
/// degree overflow.
fn multipoly_in_elim(p: &MultiPoly, elim: SymbolId) -> Option<Vec<MultiPoly>> {
    let de = usize::try_from(degree_in(p, elim)).ok()?;
    let mut out: Vec<MultiPoly> = vec![MultiPoly::zero(); de + 1];
    for (k, &c) in &p.terms {
        let mut e = 0u32;
        let mut rest: MonoKey = Vec::with_capacity(k.len());
        for &(v, ex) in k {
            if v == elim {
                e = ex;
            } else {
                rest.push((v, ex));
            }
        }
        let ie = usize::try_from(e).ok()?;
        out[ie].add_term(rest, c)?;
    }
    Some(out)
}

/// Hard ceiling on the coprime-split fixpoint iterations (a bounded guard; each
/// successful split strictly lowers a polynomial's total degree or removes one, so
/// the real bound is far smaller — this only defends against a surprise loop).
const MAX_COPRIME_SPLIT_ITERS: usize = 64;

/// The total degree of a monomial key (sum of exponents).
fn mono_key_total_degree(k: &MonoKey) -> u64 {
    k.iter().map(|&(_, e)| u64::from(e)).sum()
}

/// Compare two monomial keys under the graded-lexicographic (grlex) order — an
/// ADMISSIBLE monomial order (well-ordered and multiplicative), required for
/// polynomial division to terminate and to identify the true leading term. Higher
/// total degree is larger; on a tie, the monomial with the larger exponent at the
/// first differing variable (in increasing `SymbolId` order) is larger. The raw
/// `Vec` lex order is NOT admissible (it can rank `xy < y`), so we compare by
/// explicit per-variable exponent lookup.
fn mono_key_cmp_grlex(a: &MonoKey, b: &MonoKey) -> Ordering {
    let da = mono_key_total_degree(a);
    let db = mono_key_total_degree(b);
    if da != db {
        return da.cmp(&db);
    }
    // Equal total degree: lexicographic on the exponent vector over the merged
    // variable set in increasing SymbolId. A missing variable has exponent 0.
    let mut ia = a.iter().peekable();
    let mut ib = b.iter().peekable();
    loop {
        match (ia.peek(), ib.peek()) {
            (None, None) => return Ordering::Equal,
            (Some(&&(va, ea)), Some(&&(vb, eb))) => match va.cmp(&vb) {
                Ordering::Equal => {
                    if ea != eb {
                        return ea.cmp(&eb);
                    }
                    ia.next();
                    ib.next();
                }
                // `a` has variable `va` that `b` lacks (exp 0 in b) ⇒ a larger.
                Ordering::Less => return Ordering::Greater,
                Ordering::Greater => return Ordering::Less,
            },
            // One key exhausted its remaining variables (exponent 0 for the rest);
            // the one with a remaining positive exponent is larger. (Total degrees
            // are equal, so this branch only fires when the shared prefix matched.)
            (Some(_), None) => return Ordering::Greater,
            (None, Some(_)) => return Ordering::Less,
        }
    }
}

/// The leading `(monomial, coefficient)` of `p` under grlex, or `None` for the zero
/// polynomial. Deterministic.
fn multipoly_leading_term_grlex(p: &MultiPoly) -> Option<(MonoKey, Rational)> {
    p.terms
        .iter()
        .max_by(|(ka, _), (kb, _)| mono_key_cmp_grlex(ka, kb))
        .map(|(k, &c)| (k.clone(), c))
}

/// `Some(m_a / m_b)` iff the monomial `m_b` divides `m_a` (every variable's exponent
/// in `m_b` is ≤ that in `m_a`); otherwise `None`. The quotient key is canonical
/// (sorted by `SymbolId`, zero exponents dropped).
fn mono_key_exact_divide(m_a: &MonoKey, m_b: &MonoKey) -> Option<MonoKey> {
    let mut out: MonoKey = Vec::new();
    // Exponent of each variable in `m_a`, minus its exponent in `m_b`.
    let a_map: BTreeMap<SymbolId, u32> = m_a.iter().copied().collect();
    let b_map: BTreeMap<SymbolId, u32> = m_b.iter().copied().collect();
    // Every variable of `m_b` must appear in `m_a` with a ≥ exponent.
    for (&v, &eb) in &b_map {
        let ea = a_map.get(&v).copied().unwrap_or(0);
        if ea < eb {
            return None;
        }
    }
    for (&v, &ea) in &a_map {
        let eb = b_map.get(&v).copied().unwrap_or(0);
        let e = ea - eb; // ea ≥ eb guaranteed for shared vars; b-only vars ruled out
        if e > 0 {
            out.push((v, e));
        }
    }
    Some(out)
}

/// Exact multivariate division over the rational [`MultiPoly`] ring: `Some(quotient)`
/// iff `divisor` divides `dividend` with **zero remainder**; `None` otherwise (a
/// nonzero remainder — i.e. not an exact factor — or an overflow / degree-guard trip).
/// Uses the admissible grlex leading-term order, so it terminates and, when the
/// divisor is a genuine factor, produces the exact quotient regardless of order.
fn multipoly_exact_divide(dividend: &MultiPoly, divisor: &MultiPoly) -> Option<MultiPoly> {
    let (dlead_key, dlead_coeff) = multipoly_leading_term_grlex(divisor)?;
    if dlead_coeff.is_zero() {
        return None;
    }
    let mut remainder = dividend.clone();
    let mut quotient = MultiPoly::zero();
    // Each step cancels `remainder`'s leading term; when the divisor is a true factor
    // the leading monomial strictly decreases under grlex, so the loop terminates. The
    // cap is a bounded hard stop (a non-divisor bails on the first non-dividing lead).
    for _ in 0..(MAX_DEGREE + 2)
        .saturating_mul(dividend.terms.len().max(1))
        .saturating_add(1)
    {
        let Some((rlead_key, rlead_coeff)) = multipoly_leading_term_grlex(&remainder) else {
            // Remainder is zero ⇒ exact division succeeded.
            return Some(quotient);
        };
        // The divisor's leading monomial must divide the remainder's leading monomial.
        let factor_key = mono_key_exact_divide(&rlead_key, &dlead_key)?;
        let factor_coeff = rlead_coeff.checked_div(dlead_coeff)?;
        let mut term = MultiPoly::zero();
        term.add_term(factor_key, factor_coeff)?;
        quotient = quotient.add(&term)?;
        remainder = remainder.sub(&term.mul(divisor)?)?;
    }
    None
}

/// Refine a set of decomposition polynomials so no distinct pair shares a common
/// factor detectable by EXACT divisibility: whenever a non-constant `a` divides a
/// distinct non-constant `b` exactly, replace `b` by the cofactor `b / a` (of strictly
/// lower total degree), iterating to a fixpoint. Constants are dropped (a constant
/// never flips sign, so it contributes no CAD critical locus).
///
/// **Soundness.** The union of the zero sets is INVARIANT: `Z(b) = Z(a) ∪ Z(b/a)`, so
/// replacing `{a, b}` by `{a, b/a}` leaves the arrangement (and therefore every cell)
/// unchanged, while each original atom polynomial stays sign-invariant per cell
/// (`sign(b) = sign(a) · sign(b/a)`). The decision still evaluates the ORIGINAL atom
/// polynomials at each rational sample, so no verdict changes — this only lets the
/// projection proceed where a shared factor would otherwise make a pairwise resultant
/// vanish (`Res ≡ 0`) and force a decline.
fn coprime_split(polys: &[MultiPoly]) -> Vec<MultiPoly> {
    // Seed: deduplicate by structure, drop constants.
    let mut set: Vec<MultiPoly> = Vec::new();
    for p in polys {
        if p.vars().is_empty() {
            continue;
        }
        if !set.iter().any(|q| q.terms == p.terms) {
            set.push(p.clone());
        }
    }
    for _ in 0..MAX_COPRIME_SPLIT_ITERS {
        let mut split_at: Option<(usize, MultiPoly)> = None;
        'search: for i in 0..set.len() {
            for j in 0..set.len() {
                if i == j {
                    continue;
                }
                // Does `set[i]` divide `set[j]` exactly?
                if let Some(quot) = multipoly_exact_divide(&set[j], &set[i]) {
                    split_at = Some((j, quot));
                    break 'search;
                }
            }
        }
        let Some((j, quot)) = split_at else {
            break; // fixpoint: no pair couples by exact divisibility
        };
        if quot.vars().is_empty() {
            // `set[j]` was a constant multiple of `set[i]` (same zero set) ⇒ drop it.
            set.remove(j);
        } else {
            set[j] = quot;
        }
        // Re-normalize (dedup + drop constants) for the next round.
        let mut fresh: Vec<MultiPoly> = Vec::new();
        for p in &set {
            if p.vars().is_empty() {
                continue;
            }
            if !fresh.iter().any(|q| q.terms == p.terms) {
                fresh.push(p.clone());
            }
        }
        set = fresh;
    }
    set
}

/// Exact determinant of a square matrix over the [`MultiPoly`] ring by Leibniz
/// permutation expansion (no division — `MultiPoly` is not a field). Bounded by the
/// caller's dimension cap. `None` on overflow during the ring arithmetic.
fn multipoly_determinant(mat: &[Vec<MultiPoly>]) -> Option<MultiPoly> {
    let n = mat.len();
    if n == 0 {
        return Some(MultiPoly::constant(Rational::integer(1)));
    }
    // Heap's-style recursive permutation enumeration with sign tracking, summing
    // `sign · ∏ mat[i][perm[i]]`. Bounded by the dimension cap (≤ 6 ⇒ ≤ 720 perms).
    let mut col_used = vec![false; n];
    let mut perm = vec![0usize; n];
    let mut acc = MultiPoly::zero();
    multipoly_det_rec(mat, &mut col_used, &mut perm, 0, false, &mut acc)?;
    Some(acc)
}

/// Recursive Leibniz term accumulation for [`multipoly_determinant`]. `parity` is
/// the running permutation sign (false = even, true = odd); at depth `n` we add the
/// signed product of the chosen entries to `acc`. `None` on overflow.
fn multipoly_det_rec(
    mat: &[Vec<MultiPoly>],
    col_used: &mut [bool],
    perm: &mut [usize],
    row: usize,
    parity: bool,
    acc: &mut MultiPoly,
) -> Option<()> {
    let n = mat.len();
    if row == n {
        // Product of the chosen entries along the permutation.
        let mut prod = MultiPoly::constant(Rational::integer(1));
        for (r, &c) in perm.iter().enumerate() {
            // An early-zero product short-circuits (the zero MultiPoly absorbs).
            if prod.is_zero() {
                break;
            }
            prod = prod.mul(&mat[r][c])?;
        }
        if !prod.is_zero() {
            let signed = if parity { prod.neg()? } else { prod };
            *acc = acc.add(&signed)?;
        }
        return Some(());
    }
    // Count the inversions added by choosing column `col` at this row: the parity
    // flips once per already-used column with a LARGER index (standard transposition
    // parity for building a permutation left-to-right).
    for col in 0..n {
        if col_used[col] {
            continue;
        }
        // A zero entry contributes a zero product ⇒ skip (sound: it adds nothing).
        if mat[row][col].is_zero() {
            continue;
        }
        // Inversions added by appending `col`: already-chosen columns with a LARGER
        // index each contribute one transposition (standard left-to-right parity).
        let mut flips = 0usize;
        for (c, &used) in col_used.iter().enumerate() {
            if used && c > col {
                flips += 1;
            }
        }
        col_used[col] = true;
        perm[row] = col;
        let next_parity = parity ^ (flips % 2 == 1);
        multipoly_det_rec(mat, col_used, perm, row + 1, next_parity, acc)?;
        col_used[col] = false;
    }
    Some(())
}

/// Decide an ALL-STRICT-inequality N ≥ 3-variable component `comp` by the recursive
/// cylindrical decomposition [`open_cell_samples`]. Every atom is `<`, `>`, or `≠`.
///
/// Returns `Some(Sat(bindings))` / `Some(Unsat)` when the decomposition is provably
/// complete (Sat carries a fully-RATIONAL witness, replay-checked by the caller;
/// Unsat is exhaustive by the open-set argument), or `None` to DECLINE on ANY
/// completeness doubt (projection / isolation / sample / nullification / overflow /
/// the cell cap) — never a wrong verdict.
fn decide_strict_cad_nvar(comp: &[&MultiAtom], vars: &BTreeSet<SymbolId>) -> Option<TwoVarVerdict> {
    debug_assert!(vars.len() >= 3);
    debug_assert!(
        comp.iter()
            .all(|a| matches!(a.cmp, Cmp::Lt | Cmp::Gt | Cmp::Ne))
    );

    // The distinct constraint polynomials, coprime-split so a shared factor does not
    // make a pairwise projection resultant vanish (`Res ≡ 0`) and force a decline. The
    // split leaves the cell arrangement unchanged (`Z(a·h) = Z(a) ∪ Z(h)`) and every
    // atom is still evaluated on its ORIGINAL polynomial at each sample, so no verdict
    // shifts — see [`coprime_split`].
    let owned: Vec<MultiPoly> = comp.iter().map(|a| a.poly.clone()).collect();
    let polys = coprime_split(&owned);
    if polys.is_empty() {
        return None;
    }

    let budget = CellBudget::new();
    let mut witness: Option<Vec<(SymbolId, Value)>> = None;

    // Visit each open cell's rational interior sample, SHORT-CIRCUITING on the first
    // point that satisfies the whole strict system. A `None` from the visitor (an
    // indeterminate sign at a complete rational point — which should not occur, but
    // we never guess) propagates as a decline. The visitor binds `witness` and
    // returns `Stop` on the first satisfying point.
    let stopped = visit_open_cells(&polys, vars, &SamplePoint::new(), &budget, &mut |pt| {
        // Defensive completeness: the sample must bind EVERY component variable.
        if vars.iter().any(|v| !pt.contains_key(v)) {
            return None;
        }
        let mut value_pt: BTreeMap<SymbolId, Value> = BTreeMap::new();
        for (&v, &q) in pt {
            value_pt.insert(v, Value::Real(q));
        }
        let mut all_hold = true;
        for atom in comp {
            // Every variable of the atom is in `vars`, so the point is complete; an
            // indeterminate sign ⇒ decline (never a gap).
            let s = multipoly_sign_at(&atom.poly, &value_pt)?;
            if !sign_satisfies(atom.cmp, s) {
                all_hold = false;
                break;
            }
        }
        if all_hold {
            witness = Some(pt.iter().map(|(&v, &q)| (v, Value::Real(q))).collect());
            Some(Visit::Stop)
        } else {
            Some(Visit::Continue)
        }
    })?;

    if stopped {
        // The first satisfying interior sample of an open cell ⇒ a genuine solution.
        return Some(TwoVarVerdict::Sat(witness?));
    }

    // Every open cell's sample failed the strict system. By the open-set argument
    // (the solution set is open; if nonempty it contains an open box meeting some
    // sampled open cell), the component is Unsat — EXHAUSTIVELY. Reaching here means
    // every sign test resolved (an indeterminate one would have declined via `?`)
    // and the decomposition was complete (no decline anywhere).
    Some(TwoVarVerdict::Unsat)
}

// ============================================================================
// Recursive N-variable MIXED / NON-STRICT CAD (any N ≥ 3)
// (the CAD/nlsat ladder, step 5 — non-strict slice, RATIONAL critical points).
// ============================================================================
//
// Scope: a connected component of N ≥ 3 variables with AT LEAST ONE non-strict
// atom (`=`/`≤`/`≥`). (The N = 2 mixed case is owned by
// `decide_nonstrict_cad_two_var`; all-strict ≥3-var is owned by
// `decide_strict_cad_nvar`.)
//
// Mirrors the strict N-var recursion (`visit_open_cells` / `project_strict`)
// EXACTLY for the projection, but the cell sampler additionally emits each RATIONAL
// critical value (the 0-cells where a non-strict atom may hold on a boundary), at
// EVERY recursion level — because a non-strict system's solution set is a finite
// union of cells (open cells + the critical sections), not an open set. So a
// solution can live exactly on a critical section, which the strict (open-only)
// sampler would miss ⇒ a wrong `Unsat`.
//
// THE RESTRICTION (soundness + tractability, mirroring the 2-var mixed decider): if
// ANY critical value at ANY level is ALGEBRAIC, the WHOLE decomposition DECLINES
// (`None`) — sampling an algebraic critical coordinate, then substituting it into
// the polys, yields number-field coefficients (the deferred hard slice). Every
// sample coordinate is therefore RATIONAL, so each leaf point is a fully-rational
// binding whose atom signs are decided exactly by the rational evaluator. We never
// claim Unsat with a gap: any decline (algebraic critical value, nullification,
// overflow, incomplete isolation, the cell cap) propagates as `None` (Unknown).

/// Rational interior samples of the open intervals PLUS each rational critical
/// value of `crit`, for the MIXED/non-strict recursion. Returns the combined
/// rational sample set, or `None` to DECLINE — specifically if ANY critical value is
/// ALGEBRAIC (the non-strict slice's restriction) or `cell_samples` overflows.
fn nonstrict_axis_samples(crit: &[Root]) -> Option<Vec<Rational>> {
    let open = cell_samples(crit)?;
    let mut out = open;
    for r in crit {
        match r {
            Root::Rational(q) => out.push(*q),
            // An algebraic critical value ⇒ decline the whole non-strict
            // decomposition (we never sample an algebraic critical coordinate).
            Root::Algebraic(_) => return None,
        }
    }
    Some(out)
}

/// Recursive cylindrical decomposition for a MIXED / NON-STRICT system: invoke
/// `visit` once per cell (open interior AND rational critical 0-cell) of the
/// arrangement of the zero sets of `polys` over `vars`, passing a fully-RATIONAL
/// sample point. Mirrors [`visit_open_cells`] but the per-axis sampler adds the
/// rational critical values and DECLINES on any algebraic critical value.
///
/// Returns `Some(true)` if a visit asked to stop (a witness was found),
/// `Some(false)` if every cell was visited without stopping, or `None` to DECLINE
/// (an algebraic critical value, nullification, overflow, incomplete isolation, or
/// the cell-budget cap).
fn visit_all_cells(
    polys: &[MultiPoly],
    vars: &BTreeSet<SymbolId>,
    partial: &SamplePoint,
    budget: &CellBudget,
    visit: &mut dyn FnMut(&SamplePoint) -> Option<Visit>,
) -> Option<bool> {
    if vars.is_empty() {
        budget.charge()?;
        return Some(matches!(visit(partial)?, Visit::Stop));
    }
    if vars.len() == 1 {
        let var = *vars.iter().next().unwrap();
        let mut roots: Vec<Root> = Vec::new();
        for p in polys {
            if degree_in(p, var) == 0 {
                continue;
            }
            let ipoly = p.to_single_var_integer_poly(var)?;
            if ipoly.len() <= 1 {
                continue;
            }
            roots.extend(isolate_roots(&ipoly)?);
        }
        let crit = dedup_sorted_roots(&roots)?;
        // Open-interval interiors AND rational critical values (decline on algebraic).
        let samples = nonstrict_axis_samples(&crit)?;
        for s in samples {
            budget.charge()?;
            let mut pt = partial.clone();
            pt.insert(var, s);
            if matches!(visit(&pt)?, Visit::Stop) {
                return Some(true);
            }
        }
        return Some(false);
    }

    // N > 1: eliminate the deterministic first variable.
    let elim = *vars.iter().next().unwrap();
    let mut rest: BTreeSet<SymbolId> = vars.clone();
    rest.remove(&elim);

    // PROJECTION onto `rest` — IDENTICAL to the strict path.
    let projected = project_strict(polys, elim, &rest)?;

    // Recurse over ALL cells of the projection (open + rational critical), then for
    // each base point sample the e-fiber's open intervals AND rational critical
    // values, declining on any algebraic e-critical value.
    visit_all_cells(&projected, &rest, partial, budget, &mut |base_pt| {
        let mut roots: Vec<Root> = Vec::new();
        for p in polys {
            if degree_in(p, elim) == 0 {
                continue;
            }
            // NULLIFICATION guard: a base point that collapses `p`'s e-degree breaks
            // delineability ⇒ decline (sound: never proceed past a gap).
            let residual = substitute_rationals(p, base_pt)?;
            if degree_in(&residual, elim) == 0 {
                return None;
            }
            let ipoly = residual.to_single_var_integer_poly(elim)?;
            if ipoly.len() <= 1 {
                return None;
            }
            roots.extend(isolate_roots(&ipoly)?);
        }
        let crit = dedup_sorted_roots(&roots)?;
        let samples = nonstrict_axis_samples(&crit)?;
        for s in samples {
            budget.charge()?;
            let mut pt = base_pt.clone();
            pt.insert(elim, s);
            if matches!(visit(&pt)?, Visit::Stop) {
                return Some(Visit::Stop);
            }
        }
        Some(Visit::Continue)
    })
}

/// Decide a MIXED / NON-STRICT N ≥ 3-variable component `comp` (at least one
/// `=`/`≤`/`≥` atom) by the recursive cylindrical decomposition [`visit_all_cells`],
/// which samples both open-cell interiors and RATIONAL critical 0-cells at every
/// level.
///
/// Returns `Some(Sat(bindings))` (a fully-RATIONAL witness, replay-checked by the
/// caller) / `Some(Unsat)` (exhaustive by the cell argument: a solution lies in some
/// cell we sampled) when the decomposition is provably complete, or `None` to
/// DECLINE on ANY completeness doubt (an algebraic critical value, projection /
/// isolation / nullification / overflow / the cell cap) — never a wrong verdict.
fn decide_nonstrict_cad_nvar(
    comp: &[&MultiAtom],
    vars: &BTreeSet<SymbolId>,
) -> Option<TwoVarVerdict> {
    debug_assert!(vars.len() >= 3);
    debug_assert!(
        comp.iter()
            .any(|a| matches!(a.cmp, Cmp::Eq | Cmp::Le | Cmp::Ge))
    );

    // Coprime-split the decomposition polynomials (see [`coprime_split`]): a shared
    // factor would make a pairwise projection resultant vanish and force a decline,
    // while the split preserves the cell arrangement and every atom's per-cell sign.
    let owned: Vec<MultiPoly> = comp.iter().map(|a| a.poly.clone()).collect();
    let polys = coprime_split(&owned);
    if polys.is_empty() {
        return None;
    }

    let budget = CellBudget::new();
    let mut witness: Option<Vec<(SymbolId, Value)>> = None;

    let stopped = visit_all_cells(&polys, vars, &SamplePoint::new(), &budget, &mut |pt| {
        // Defensive completeness: the sample must bind EVERY component variable.
        if vars.iter().any(|v| !pt.contains_key(v)) {
            return None;
        }
        // Every sample coordinate is rational (the sampler declines on algebraic
        // critical values), so each atom's sign is decided exactly by the rational
        // evaluator. An indeterminate sign ⇒ decline (never a gap).
        let mut value_pt: BTreeMap<SymbolId, Value> = BTreeMap::new();
        for (&v, &q) in pt {
            value_pt.insert(v, Value::Real(q));
        }
        let mut all_hold = true;
        for atom in comp {
            let s = multipoly_sign_at(&atom.poly, &value_pt)?;
            if !sign_satisfies(atom.cmp, s) {
                all_hold = false;
                break;
            }
        }
        if all_hold {
            witness = Some(pt.iter().map(|(&v, &q)| (v, Value::Real(q))).collect());
            Some(Visit::Stop)
        } else {
            Some(Visit::Continue)
        }
    })?;

    if stopped {
        return Some(TwoVarVerdict::Sat(witness?));
    }

    // Every cell's sample (open interior AND rational critical 0-cell) failed. By the
    // cell argument (the solution set is a finite union of these cells), the
    // component is Unsat — EXHAUSTIVELY. Reaching here means every sign test resolved
    // and the decomposition was complete (no decline anywhere).
    Some(TwoVarVerdict::Unsat)
}

/// The recursive non-strict decomposition that DECIDES ALGEBRAIC critical values
/// (the slice's extension): it mirrors [`decide_nonstrict_cad_nvar`] but carries a
/// VALUE base point (each variable bound to a rational OR algebraic [`Value`]) and
/// derives every fiber's boundaries via the `Res(min-poly, p)` elimination
/// ([`fiber_boundary_poly`]) instead of declining on the first algebraic critical
/// value. It is tried ONLY as a fallback after the (faster) rational path
/// [`decide_nonstrict_cad_nvar`] declines — so it can only upgrade an Unknown to a
/// definite verdict, never flip an existing one.
///
/// SOUNDNESS — identical discipline to the 2-var algebraic decider and the strict
/// N-var recursion. At each level the fiber boundaries are the real roots of a
/// RATIONAL univariate in the fiber variable, obtained by eliminating every
/// algebraic-bound earlier coordinate against its integer min-poly (a SUPERSET of
/// the true boundaries — conjugate min-poly roots only REFINE the cells, never miss
/// one), plus the rational-bound coordinates substituted directly. Every open-cell
/// interior is sampled rationally and every critical 0-cell (rational or algebraic)
/// is sampled exactly; the base case evaluates every atom's sign at the
/// fully-bound (mixed rational/algebraic) point via exact field arithmetic
/// (`multipoly_sign_at`). Any decline — overflow, a nullified residual, an
/// identically-zero / over-large resultant, incomplete isolation, a field-arithmetic
/// indeterminacy, or the cell cap — propagates as `None` (Unknown). We never claim
/// Unsat with a gap, and every Sat carries a (rational/algebraic) witness the caller
/// replay-checks via the same field arithmetic.
fn decide_nonstrict_cad_nvar_algebraic(
    comp: &[&MultiAtom],
    vars: &BTreeSet<SymbolId>,
) -> Option<TwoVarVerdict> {
    debug_assert!(vars.len() >= 3);
    debug_assert!(
        comp.iter()
            .any(|a| matches!(a.cmp, Cmp::Eq | Cmp::Le | Cmp::Ge))
    );

    let mut polys: Vec<MultiPoly> = Vec::new();
    for atom in comp {
        if !polys.iter().any(|p| p.terms == atom.poly.terms) {
            polys.push(atom.poly.clone());
        }
    }
    if polys.is_empty() {
        return None;
    }

    let budget = CellBudget::new();
    let mut witness: Option<Vec<(SymbolId, Value)>> = None;

    let empty: BTreeMap<SymbolId, Value> = BTreeMap::new();
    let stopped = visit_all_cells_value(&polys, vars, &empty, &budget, &mut |pt| {
        // Defensive completeness: the sample must bind EVERY component variable.
        if vars.iter().any(|v| !pt.contains_key(v)) {
            return None;
        }
        // Each atom's sign at the (mixed rational/algebraic) point, decided exactly by
        // the field-arithmetic evaluator. An indeterminate sign ⇒ decline (never a gap).
        let mut all_hold = true;
        for atom in comp {
            let s = multipoly_sign_at(&atom.poly, pt)?;
            if !sign_satisfies(atom.cmp, s) {
                all_hold = false;
                break;
            }
        }
        if all_hold {
            witness = Some(pt.iter().map(|(&v, val)| (v, val.clone())).collect());
            Some(Visit::Stop)
        } else {
            Some(Visit::Continue)
        }
    })?;

    if stopped {
        return Some(TwoVarVerdict::Sat(witness?));
    }

    // Every cell's sample (open interior AND critical 0-cell, rational or algebraic)
    // failed, with NO decline anywhere — so the decomposition is COMPLETE and the
    // component is Unsat, EXHAUSTIVELY (the solution set is a finite union of these
    // cells; each fiber's boundary superset only refines, never drops, a cell).
    Some(TwoVarVerdict::Unsat)
}

/// One VALUE sample point: each (already-eliminated / sampled) variable bound to an
/// exact rational or algebraic [`Value`].
type ValuePoint = BTreeMap<SymbolId, Value>;

/// The result of deriving an atom's fiber-boundary polynomial in `elim` at a value
/// base point ([`fiber_boundary_poly`]).
enum FiberBoundary {
    /// A genuine univariate (LSB-first integer) boundary poly in `elim`, `len > 1`;
    /// its real roots are a superset of `{β : p(base, β) = 0}`.
    Poly(Vec<i128>),
    /// This atom imposes NO `elim`-boundary at the base point (a nonzero-constant
    /// resultant or a residual constant in `elim`).
    None,
}

/// Compute a RATIONAL univariate (LSB-first integer poly) in `elim` whose real roots
/// are a SUPERSET of `{β : p(base, β) = 0}`, where `base` binds the earlier variables
/// (other than `elim`) to rational or algebraic [`Value`]s.
///
/// METHOD: substitute the rational-bound variables directly, then eliminate each
/// algebraic-bound variable `xᵢ` (value `αᵢ`, integer min-poly `mᵢ`) by the
/// multivariate resultant `Res_{xᵢ}(mᵢ(xᵢ), cur)` (over the remaining variables) —
/// the same `Res(min-poly, p)` elimination the 2-var algebraic cell decider uses,
/// iterated. A common point with `mᵢ(αᵢ)=0` and `p(...)=0` forces the resultant to
/// vanish, so the final univariate vanishes at every true boundary β; conjugate
/// min-poly roots may add EXTRA β (a sound superset — it only refines the elim-cells,
/// never misses a boundary).
///
/// Returns `Some(FiberBoundary::Poly(ipoly))` (a genuine univariate boundary poly,
/// `len > 1`), `Some(FiberBoundary::None)` (no `elim`-boundary from this atom at
/// `base` — a nonzero constant resultant or a residual constant in `elim`), or `None`
/// to DECLINE (overflow, an identically-zero resultant, an algebraic coordinate whose
/// min-poly does not fit `i128`, or the Sylvester-dimension cap).
fn fiber_boundary_poly(p: &MultiPoly, base: &ValuePoint, elim: SymbolId) -> Option<FiberBoundary> {
    // Partition the bound earlier variables (those `p` mentions, other than `elim`)
    // into rational and algebraic. A variable `p` does not mention needs no binding.
    let pvars = p.vars();
    let mut rationals: BTreeMap<SymbolId, Rational> = BTreeMap::new();
    let mut algebraics: Vec<(SymbolId, RealAlgebraic)> = Vec::new();
    for v in &pvars {
        if *v == elim {
            continue;
        }
        match base.get(v)? {
            Value::Real(q) => {
                rationals.insert(*v, *q);
            }
            Value::RealAlgebraic(a) => algebraics.push((*v, a.clone())),
            _ => return None,
        }
    }

    // Substitute the rational coordinates first (exact, cheap). The result still
    // mentions `elim` and any algebraic-bound variables.
    let mut cur = substitute_rationals(p, &rationals)?;

    // Eliminate each algebraic-bound variable against its integer min-poly. After all
    // are eliminated, `cur` is univariate in `elim` with rational coefficients.
    for (v, a) in &algebraics {
        if degree_in(&cur, *v) == 0 {
            // `cur` no longer mentions `v` (an earlier elimination cleared it, or `p`
            // only ever had it through a now-substituted factor) ⇒ nothing to do.
            continue;
        }
        let m_i128 = a.defining_poly_i128()?; // i128-bound ⇒ decline (sound Unknown)
        let m_poly = univariate_multipoly(&m_i128, *v)?;
        if degree_in(&m_poly, *v) == 0 {
            return None; // algebraic value with a degree-0 min-poly view ⇒ defensive decline
        }
        match multi_resultant(&m_poly, &cur, *v)? {
            ResultantOutcome::Poly(res) => cur = res,
            // No common `v`-root with the min-poly for any remaining value ⇒ this atom
            // contributes NO `elim`-boundary at `base`.
            ResultantOutcome::NonzeroConstant => return Some(FiberBoundary::None),
            // A shared `v`-factor for all remaining values ⇒ a degeneracy we decline on.
            ResultantOutcome::Zero => return None,
        }
    }

    // `cur` must now be univariate in `elim` (every other variable was substituted or
    // eliminated). A residual that lost `elim` ⇒ no boundary from this atom.
    if degree_in(&cur, elim) == 0 {
        return Some(FiberBoundary::None);
    }
    // Any surviving foreign variable would make this not a valid univariate boundary
    // ⇒ decline (defensive: should not occur, the elimination cleared them all).
    if cur.vars().iter().any(|v| *v != elim) {
        return None;
    }
    let ipoly = cur.to_single_var_integer_poly(elim)?;
    if ipoly.len() <= 1 {
        return Some(FiberBoundary::None);
    }
    Some(FiberBoundary::Poly(ipoly))
}

/// Map an isolated [`Root`] to a [`Value`] for binding into a [`ValuePoint`],
/// coarsening an algebraic root to a small-denominator bracket so downstream field
/// arithmetic does not overflow on over-refined endpoints (mirrors
/// [`decide_nonstrict_cell_algebraic`]). `None` ⇒ decline.
fn root_to_point_value(r: &Root) -> Option<Value> {
    match r {
        Root::Rational(q) => Some(Value::Real(*q)),
        Root::Algebraic(a) => Some(Value::RealAlgebraic(coarsen_algebraic(a)?)),
    }
}

/// The VALUE analogue of [`visit_all_cells`]: invoke `visit` once per cell (open
/// interior AND critical 0-cell, rational OR algebraic) of the arrangement of the
/// zero sets of `polys` over `vars`, passing a mixed rational/algebraic
/// [`ValuePoint`]. Each fiber's boundaries are derived by [`fiber_boundary_poly`]
/// (the `Res(min-poly, p)` elimination), so an algebraic earlier coordinate is
/// DECIDED, not declined.
///
/// Returns `Some(true)` if a visit asked to stop (witness found), `Some(false)` if
/// every cell was visited without stopping, or `None` to DECLINE (overflow, a
/// nullified residual, an identically-zero / over-large resultant, incomplete
/// isolation, or the cell cap).
fn visit_all_cells_value(
    polys: &[MultiPoly],
    vars: &BTreeSet<SymbolId>,
    partial: &ValuePoint,
    budget: &CellBudget,
    visit: &mut dyn FnMut(&ValuePoint) -> Option<Visit>,
) -> Option<bool> {
    if vars.is_empty() {
        budget.charge()?;
        return Some(matches!(visit(partial)?, Visit::Stop));
    }
    if vars.len() == 1 {
        let var = *vars.iter().next().unwrap();
        // The deepest level: every poly is univariate in `var` (or constant). Its real
        // roots — rational OR algebraic — are the critical values; sample the open-cell
        // interiors (rational) and each critical value (as a Value).
        let mut roots: Vec<Root> = Vec::new();
        for p in polys {
            if degree_in(p, var) == 0 {
                continue;
            }
            let ipoly = p.to_single_var_integer_poly(var)?;
            if ipoly.len() <= 1 {
                continue;
            }
            roots.extend(isolate_roots(&ipoly)?);
        }
        let crit = dedup_sorted_roots(&roots)?;
        if crit.len() > MAX_CAD_CELLS {
            return None;
        }
        return visit_axis_values(&crit, var, partial, budget, visit);
    }

    // N > 1: eliminate the deterministic first variable. The projection is RATIONAL
    // (identical to the strict / rational paths); only the fiber sampling changes.
    let elim = *vars.iter().next().unwrap();
    let mut rest: BTreeSet<SymbolId> = vars.clone();
    rest.remove(&elim);
    let projected = project_strict(polys, elim, &rest)?;

    visit_all_cells_value(&projected, &rest, partial, budget, &mut |base_pt| {
        // Derive the `elim`-fiber boundaries at this (possibly algebraic) base point
        // via the `Res(min-poly, p)` elimination — a SUPERSET of the true boundaries.
        let mut roots: Vec<Root> = Vec::new();
        for p in polys {
            if degree_in(p, elim) == 0 {
                continue;
            }
            if let FiberBoundary::Poly(ipoly) = fiber_boundary_poly(p, base_pt, elim)? {
                roots.extend(isolate_roots(&ipoly)?);
            }
        }
        let crit = dedup_sorted_roots(&roots)?;
        if crit.len() > MAX_CAD_CELLS {
            return None;
        }
        if visit_axis_values(&crit, elim, base_pt, budget, &mut |pt| visit(pt))? {
            Some(Visit::Stop)
        } else {
            Some(Visit::Continue)
        }
    })
}

/// Sample one fiber axis given its (sorted, deduped) critical roots `crit` and the
/// base [`ValuePoint`]: visit each open-cell interior (a rational sample) and each
/// critical 0-cell (rational or algebraic, as a [`Value`]). Returns `Some(true)` if a
/// visit asked to stop, `Some(false)` if all were visited, or `None` to decline.
fn visit_axis_values(
    crit: &[Root],
    var: SymbolId,
    base: &ValuePoint,
    budget: &CellBudget,
    visit: &mut dyn FnMut(&ValuePoint) -> Option<Visit>,
) -> Option<bool> {
    // Open-cell interiors first (rational ⇒ a simpler witness), then the 0-cells.
    let open = cell_samples(crit)?;
    for q in open {
        budget.charge()?;
        let mut pt = base.clone();
        pt.insert(var, Value::Real(q));
        if matches!(visit(&pt)?, Visit::Stop) {
            return Some(true);
        }
    }
    for r in crit {
        budget.charge()?;
        let val = root_to_point_value(r)?;
        let mut pt = base.clone();
        pt.insert(var, val);
        if matches!(visit(&pt)?, Visit::Stop) {
            return Some(true);
        }
    }
    Some(false)
}

/// The partial derivative `∂p/∂v` of a [`MultiPoly`]: each monomial `c·v^e·rest`
/// maps to `(c·e)·v^(e−1)·rest` (terms with `e = 0` in `v` vanish). `None` on
/// overflow (coefficient multiply by the exponent).
fn derivative_in(p: &MultiPoly, v: SymbolId) -> Option<MultiPoly> {
    let mut out = MultiPoly::zero();
    for (k, &c) in &p.terms {
        // Find the exponent of `v` in this monomial.
        let mut exp = 0u32;
        for &(s, e) in k {
            if s == v {
                exp = e;
            }
        }
        if exp == 0 {
            continue; // ∂/∂v of a v-free term is 0
        }
        // New coefficient c·exp; new monomial has `v^(exp−1)`.
        let coeff = c.checked_mul(Rational::integer(i128::from(exp)))?;
        let mut nk: MonoKey = Vec::with_capacity(k.len());
        for &(s, e) in k {
            if s == v {
                if e > 1 {
                    nk.push((s, e - 1));
                }
            } else {
                nk.push((s, e));
            }
        }
        out.add_term(nk, coeff)?;
    }
    Some(out)
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
    // Both equalities collapsed to CONSTANTS in `elim` after fixing `keep = α`.
    // A NONZERO constant means that equality is false at α ⇒ no solution there.
    // But if BOTH are ZERO, the equalities are vacuously satisfied and the variety
    // is POSITIVE-DIMENSIONAL through α (e.g. `x*y + x = 0 ∧ x*y = 0` both become
    // `0 = 0` at `x = 0`, leaving `elim` free) — so a witness with ANY `elim` may
    // exist. Returning `None` here would let the caller wrongly conclude `Unsat`
    // (a real wrong-unsat: the system is Sat at `(0, anything)`). Decide the FULL
    // single-variable `elim`-system at `keep = α` (every atom of the component,
    // with its original comparator) completely instead.
    if p_poly.len() <= 1 && q_poly.len() <= 1 {
        return match (p_alpha.as_constant(), q_alpha.as_constant()) {
            (Some(a), Some(b)) if a.is_zero() && b.is_zero() => {
                match decide_nonstrict_cell(comp, keep, elim, alpha) {
                    Some(CellOutcome::Sat(beta)) => {
                        LiftOutcome::Found(vec![(keep, Value::Real(alpha)), (elim, beta)])
                    }
                    Some(CellOutcome::Unsat) => LiftOutcome::None, // no solution at α
                    None => LiftOutcome::Overflow,                 // indeterminate ⇒ decline
                }
            }
            // A nonzero-constant equality is false at α ⇒ no solution there.
            _ => LiftOutcome::None,
        };
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

// ============================================================================
// Algebraic (α, β) grid lift (the CAD/nlsat ladder, step 3 — coupled all-equality
// 2-variable component with ALGEBRAIC coordinates, decided by exact field
// arithmetic over `RealAlgebraic`).
// ============================================================================
//
// For two equalities `p(x,y)=0 ∧ q(x,y)=0` the common real solutions `(α,β)`
// satisfy, by the resultant elimination property:
//   • α is a real root of `Res_y(p,q)`  (eliminate y, univariate in x), AND
//   • β is a real root of `Res_x(p,q)`  (eliminate x, univariate in y).
// So the GRID `roots(Res_y) × roots(Res_x)` is an **exhaustive** finite candidate
// set: every common root's coordinates appear among the grid's first/second
// components (the grid is a *superset* of the solution set — it may contain
// spurious pairs whose coordinates each solve a resultant but which together do
// not solve the system). For each grid pair we test `p(α,β)=0 ∧ q(α,β)=0` EXACTLY
// via field arithmetic on `RealAlgebraic` (no float), so an algebraic α/β no longer
// forces a decline.
//
// Each axis's candidate set ([`axis_candidates`]) is a COMPLETE superset of that
// coordinate over the whole solution set — derived either from the roots of a
// univariate equality in that variable, or, when none exists, from the resultant
// eliminating the other variable. Both are complete by the same elimination
// property (a full solution also solves the chosen equality/-ies).
//
// Soundness invariant (the algebraic `Unsat`):
//   The grid PROVABLY contains every common solution of the equalities (each
//   coordinate appears in its axis's complete candidate set). When EVERY atom of
//   the component is an equality (region-free: no inequality can hide a solution
//   outside the discrete common-root set), if NO grid pair satisfies all the
//   equalities, the component is empty ⇒ `Unsat`, EXHAUSTIVELY — and this now holds
//   even when the roots are algebraic. The completeness rests on:
//     (a) each axis-candidate source being computed exactly (overflow/cap ⇒ decline),
//     (b) every root isolation being COMPLETE (`isolate_roots` is complete-or-None;
//         a None on either side ⇒ decline — the grid might miss a coordinate),
//     (c) the bounded grid size (cap ⇒ decline rather than risk OOM/hang),
//     (d) every per-pair test resolving to a definite zero/nonzero (a `None` field
//         evaluation on ANY pair ⇒ decline — that pair could be a real solution we
//         cannot rule out).
//   If any of (a)–(d) fails for a pair or a side, we DECLINE (`Unknown`) — a sound
//   Unknown beats a wrong Unsat. We never claim `Unsat` for a component that
//   contains an inequality from the grid (a region is not captured by point
//   candidates); the only inequality-tolerant Unsat is the existing exact
//   "no real resultant root ⇒ Unsat" rule, handled in `decide_two_var_component`.
//
// Every `Sat` returns a candidate model that the caller still replay-checks against
// every ORIGINAL assertion, so a spurious grid pair can never yield a wrong `Sat`.

/// Hard ceiling on the candidate grid size `|roots(Res_y)| × |roots(Res_x)|`.
/// Each pair test is bounded field arithmetic; the cap keeps the total work
/// bounded (no OOM / hang). Beyond it we decline.
const MAX_GRID: usize = 64;

/// The exhaustive candidate set for one coordinate `target` of the common
/// solutions of an all-equality system, with the OTHER variable `other`.
///
/// Soundness — each branch yields a COMPLETE superset of `target`'s coordinate
/// over the whole solution set:
///   • If some equality `g` is **univariate** in `target` (mentions only it),
///     every solution has `target` a real root of `g` ⇒ `roots(g)` is complete.
///   • Else if two equalities both have positive degree in `other`, every common
///     solution has `target` a real root of `Res_other(p,q)` (resultant
///     elimination completeness) ⇒ `roots(Res_other)` is complete.
/// Either source is a *superset* of the full system's `target`-coordinates (a
/// full solution also solves the chosen equality/-ies), so using it loses no
/// solution. Returns the complete root set, `Some(constant_nonzero=true)` packed
/// as an empty-vec + the flag — actually a dedicated enum keeps it explicit.
enum AxisRoots {
    /// The complete, finite real-root candidate set for this coordinate.
    Roots(Vec<Root>),
    /// A nonzero constant resultant: no common root anywhere ⇒ the system is Unsat.
    NoCommonRoot,
}

/// Compute [`AxisRoots`] for `target` from the equality set. `None` declines (no
/// usable source, overflow, incomplete isolation, a vanishing resultant).
fn axis_candidates(
    equalities: &[&MultiPoly],
    target: SymbolId,
    other: SymbolId,
) -> Option<AxisRoots> {
    // Prefer a univariate equality in `target` (its roots constrain `target`
    // completely with the fewest candidates). Pick the smallest-degree such one.
    let mut best_uni: Option<&MultiPoly> = None;
    for eq in equalities {
        if degree_in(eq, target) > 0 && degree_in(eq, other) == 0 {
            match best_uni {
                Some(b) if degree_in(b, target) <= degree_in(eq, target) => {}
                _ => best_uni = Some(eq),
            }
        }
    }
    if let Some(g) = best_uni {
        let ipoly = g.to_single_var_integer_poly(target)?;
        if ipoly.len() <= 1 {
            // Degenerate after view (a nonzero constant ⇒ no root; else decline).
            if ipoly.first().copied().unwrap_or(0) != 0 {
                return Some(AxisRoots::NoCommonRoot);
            }
            return None;
        }
        let roots = isolate_roots(&ipoly)?;
        return Some(AxisRoots::Roots(roots));
    }

    // Else eliminate `other` from a bivariate-in-`other` equality pair via the
    // resultant, giving a univariate polynomial in `target`.
    let mut pair: Option<(&MultiPoly, &MultiPoly)> = None;
    'outer: for i in 0..equalities.len() {
        if degree_in(equalities[i], other) == 0 {
            continue;
        }
        for &q in equalities.iter().skip(i + 1) {
            if degree_in(q, other) == 0 {
                continue;
            }
            pair = Some((equalities[i], q));
            break 'outer;
        }
    }
    let (p, q) = pair?;
    let res = resultant_univariate(p, q, other, target)?;
    if res.len() <= 1 {
        if res.first().copied().unwrap_or(0) != 0 {
            return Some(AxisRoots::NoCommonRoot);
        }
        // Vanishing resultant: a shared curve — not finitely enumerable ⇒ decline.
        return None;
    }
    let roots = isolate_roots(&res)?;
    Some(AxisRoots::Roots(roots))
}

/// Decide a 2-variable coupled all-equality component by the algebraic (α, β)
/// grid lift. Returns `Some(verdict)` when the grid is provably exhaustive (Sat
/// with a replay-pending witness, or an exhaustive Unsat); `None` to decline (a
/// candidate source unavailable, an incomplete isolation, the grid cap, or any
/// per-pair indeterminacy) — never a wrong verdict.
///
/// `equalities` are all the component's equality polynomials; `v0`, `v1` are the
/// two component variables. The full component `comp` is checked at any Sat
/// candidate.
fn decide_grid_two_var(
    comp: &[&MultiAtom],
    v0: SymbolId,
    v1: SymbolId,
    equalities: &[&MultiPoly],
    all_equalities: bool,
) -> Option<TwoVarVerdict> {
    // The grid Unsat is only exhaustive for a region-free (all-equality) component.
    // For a component with an inequality we may still find a Sat pair, but we must
    // NOT certify Unsat from the discrete grid. We therefore only run the grid when
    // the component is all-equalities (the in-scope shape); an inequality component
    // is left to the existing decline path.
    if !all_equalities {
        return None;
    }

    // The complete x-candidate and y-candidate sets (each a superset of the
    // respective coordinate over the whole solution set).
    let x_roots = match axis_candidates(equalities, v0, v1)? {
        AxisRoots::NoCommonRoot => return Some(TwoVarVerdict::Unsat),
        AxisRoots::Roots(r) => r,
    };
    let y_roots = match axis_candidates(equalities, v1, v0)? {
        AxisRoots::NoCommonRoot => return Some(TwoVarVerdict::Unsat),
        AxisRoots::Roots(r) => r,
    };

    // No real root on either side ⇒ the equality system has no common real
    // solution ⇒ Unsat (an empty equality variety stays empty).
    if x_roots.is_empty() || y_roots.is_empty() {
        return Some(TwoVarVerdict::Unsat);
    }

    // Bound the grid (no OOM / hang). Each pair test is bounded field arithmetic.
    let grid_size = x_roots.len().checked_mul(y_roots.len())?;
    if grid_size > MAX_GRID {
        return None;
    }

    // Test every (α, β) pair EXACTLY against EVERY atom of the component (all
    // equalities here). The first pair satisfying them all is a Sat witness
    // (replay-checked by the caller). A `None` on ANY pair (overflow / indeterminate
    // sign) means we cannot rule it in OR out ⇒ the grid is no longer provably
    // exhaustive ⇒ decline (never a wrong Unsat).
    for xr in &x_roots {
        let alpha = root_to_value(xr)?;
        for yr in &y_roots {
            let beta = root_to_value(yr)?;
            let mut point: BTreeMap<SymbolId, Value> = BTreeMap::new();
            point.insert(v0, alpha.clone());
            point.insert(v1, beta.clone());
            if grid_point_satisfies(comp, &point)? {
                return Some(TwoVarVerdict::Sat(vec![(v0, alpha), (v1, beta)]));
            }
        }
    }

    // No grid pair satisfies all the equalities. Because (a) each axis-candidate
    // source was exact and COMPLETE (a superset of that coordinate over the whole
    // solution set), (b) both isolations were complete, (c) the grid was within the
    // cap, and (d) every pair resolved to a definite sign, the grid is the COMPLETE
    // common-solution candidate set and it is empty of solutions ⇒ the all-equality
    // component is unsatisfiable, EXHAUSTIVELY.
    Some(TwoVarVerdict::Unsat)
}

/// Convert an isolated [`Root`] to a [`Value`] (rational or algebraic) usable in
/// exact field arithmetic. Algebraic roots are **coarsened** ([`coarsen_algebraic`])
/// to a small-denominator isolating interval first: root isolation over-refines the
/// bracket (huge power-of-two denominators), and the `RealAlgebraic` field-arithmetic
/// combine multiplies interval endpoints — large denominators there overflow even
/// bignum and spuriously decline. Coarsening keeps the SAME root with simpler
/// endpoints. `None` if coarsening cannot find a small isolating interval (decline).
fn root_to_value(r: &Root) -> Option<Value> {
    Some(match r {
        Root::Rational(q) => Value::Real(*q),
        Root::Algebraic(a) => Value::RealAlgebraic(coarsen_algebraic(a)?),
    })
}

/// Coarsen every algebraic value in `model` to a small-denominator isolating
/// interval (value-preserving). Root isolation over-refines the bracket (huge
/// dyadic denominators); the emitted model and any independent re-evaluation of the
/// original terms (the IR ground evaluator multiplies interval endpoints during
/// algebraic field arithmetic) overflow on those endpoints. Coarsening keeps the
/// verdict sound while making the witness replay-friendly. Best-effort: a value
/// whose coarsening declines is left unchanged (still a valid in-engine witness).
fn coarsen_model_algebraics(model: &mut Model) {
    let coarse: Vec<(SymbolId, Value)> = model
        .iter()
        .filter_map(|(v, val)| match &val {
            Value::RealAlgebraic(a) => coarsen_algebraic(a).map(|c| (v, Value::RealAlgebraic(c))),
            _ => None,
        })
        .collect();
    for (v, val) in coarse {
        model.set(v, val);
    }
}

/// The cap on the dyadic denominator `2^k` used to round an algebraic number's
/// isolating interval to small-denominator endpoints. Beyond it we keep the
/// original (and let field arithmetic decline if it must) — bounded, never a hang.
const COARSEN_MAX_EXP: u32 = 40;

/// Round `q` DOWN to the nearest multiple of `1/den` (`den > 0`).
fn floor_to_den(q: Rational, den: i128) -> Option<Rational> {
    let n = q.numerator().checked_mul(den)?; // q·den = (num·den)/qden
    let qden = q.denominator();
    // floor(n / qden) with Euclidean rounding toward −∞.
    let f = n.checked_div_euclid(qden)?;
    Rational::checked_new(f, den)
}

/// Round `q` UP to the nearest multiple of `1/den` (`den > 0`).
fn ceil_to_den(q: Rational, den: i128) -> Option<Rational> {
    let n = q.numerator().checked_mul(den)?;
    let qden = q.denominator();
    // ceil(n / qden) = −floor(−n / qden).
    let neg = n.checked_neg()?;
    let c = neg.checked_div_euclid(qden)?.checked_neg()?;
    Rational::checked_new(c, den)
}

/// Re-bracket the algebraic number `a` with a small-denominator isolating interval
/// `(nlo, nhi) ⊆ (lo, hi)` that still contains its (unique-in-`(lo,hi)`) root.
///
/// Soundness: any sub-interval of an isolating interval that still brackets the
/// root (strict sign change at its endpoints, both nonzero) isolates the SAME
/// single root — `(lo,hi)` holds exactly one root, so a sub-interval with a sign
/// change holds an odd count ≤ 1, i.e. exactly that root. We try increasing dyadic
/// denominators `2^k`; the smallest one whose rounded endpoints bracket the root
/// (and lie strictly inside `(lo,hi)`) wins. If none up to the cap works, return
/// `None` (decline) — never a wrong value.
fn coarsen_algebraic(a: &RealAlgebraic) -> Option<RealAlgebraic> {
    // This coarsening runs in `i128`: if the algebraic value's defining poly or
    // isolating interval do not fit `i128`, decline (the value is kept as-is by the
    // caller — still sound). The widening below preserves the exact real value.
    let (lo, hi) = a.interval()?;
    // Squarefree integer poly (same root SET, every root SIMPLE ⇒ sign-changing) and
    // its Sturm chain, so we can EXACTLY count distinct roots in a candidate widened
    // interval. The value is the same real number; replay still checks the ORIGINAL
    // atoms via `sign_at`.
    let rat = rat_from_int(&a.defining_poly_i128()?);
    let sqfree = squarefree_part(&rat)?;
    let sqf = rat_to_int_poly(&sqfree)?;
    if sqf.last().copied()? == 0 {
        return None;
    }
    let chain = sturm_chain(&sqfree)?;

    // Widen `(lo, hi)` OUTWARD to small-denominator dyadic endpoints, then verify by
    // an EXACT Sturm count that the widened interval still holds exactly ONE root,
    // and that it is `a` (root strictly between the endpoints). Widening can only be
    // accepted once the count is exactly 1 — so no other root is ever captured.
    let mut den: i128 = 1;
    for _ in 0..=COARSEN_MAX_EXP {
        let nlo = floor_to_den(lo, den)?;
        let nhi = ceil_to_den(hi, den)?;
        if nlo.checked_cmp(&nhi)? == core::cmp::Ordering::Less
            && !eval_rat(&sqf, nlo)?.is_zero()
            && !eval_rat(&sqf, nhi)?.is_zero()
            && count_roots_in(&chain, nlo, nhi)? == 1
        {
            // Exactly one distinct root in (nlo, nhi); confirm it is `a` (root
            // strictly between the endpoints) via `a`'s own exact comparison.
            let above = a.compare_rational(&nlo)?; // root vs nlo
            let below = a.compare_rational(&nhi)?; // root vs nhi
            if above == core::cmp::Ordering::Greater && below == core::cmp::Ordering::Less {
                return RealAlgebraic::new(sqf, nlo, nhi);
            }
        }
        den = den.checked_mul(2)?;
    }
    None
}

/// Whether the component is satisfied at the grid `point` (every atom). For the
/// all-equality grid this confirms each equality vanishes; an indeterminate atom
/// (`None`) declines. Returns `Some(true/false)` or `None` to decline.
fn grid_point_satisfies(comp: &[&MultiAtom], point: &BTreeMap<SymbolId, Value>) -> Option<bool> {
    for atom in comp {
        let s = multipoly_sign_at(&atom.poly, point)?;
        if !sign_satisfies(atom.cmp, s) {
            return Some(false);
        }
    }
    Some(true)
}

/// The exact sign of `p(point)` where `point` binds every variable of `p` to a
/// rational or algebraic [`Value`]. Computed by exact field arithmetic over
/// `RealAlgebraic` (no float). `None` on overflow, an unbound variable, or any
/// field-arithmetic decline.
fn multipoly_sign_at(p: &MultiPoly, point: &BTreeMap<SymbolId, Value>) -> Option<Sign> {
    let v = eval_multipoly_value(p, point)?;
    value_sign(&v)
}

/// Evaluate a [`MultiPoly`] at `point` (each variable bound to a rational or
/// algebraic [`Value`]) by exact field arithmetic. Returns the resulting
/// [`Value`]. `None` on overflow, an unbound variable, or a field-arithmetic
/// decline (e.g. a product of two distinct high-degree algebraic numbers whose
/// resultant overflows even bignum).
fn eval_multipoly_value(p: &MultiPoly, point: &BTreeMap<SymbolId, Value>) -> Option<Value> {
    let mut acc = Value::Real(Rational::zero());
    for (k, &c) in &p.terms {
        // term = c · ∏ vᵢ^eᵢ.
        let mut term = Value::Real(c);
        for &(v, e) in k {
            let base = point.get(&v)?;
            for _ in 0..e {
                term = value_mul(&term, base)?;
            }
        }
        acc = value_add(&acc, &term)?;
    }
    Some(acc)
}

/// Lift a real-sorted [`Value`] (rational or algebraic) to a [`RealAlgebraic`].
/// `None` on overflow or a non-real value.
fn value_as_algebraic(v: &Value) -> Option<RealAlgebraic> {
    match v {
        Value::RealAlgebraic(a) => Some(a.clone()),
        Value::Real(c) => RealAlgebraic::from_rational(*c),
        _ => None,
    }
}

/// Cap on the number of divisor candidates enumerated by [`try_rationalize`]'s
/// rational-root-theorem search (per endpoint). A composite constant/leading
/// coefficient with more divisors declines the rationality check (keeping the
/// value as an algebraic — still sound, just not collapsed). Bounded ⇒ no hang.
const RATIONALIZE_MAX_DIVISORS: usize = 256;

/// Map a [`RealAlgebraic`] result back to a [`Value`]. A degree-1 defining poly
/// `q·t + r` denotes the exact rational `−r/q`. A HIGHER-degree poly may still
/// denote a rational (e.g. `√2 · 1/√2 = 1` arrives as a root of `4t² − 4`): the
/// rational-root-theorem search [`try_rationalize`] recovers it. Collapsing to a
/// [`Value::Real`] keeps arithmetic exact and prevents an avoidable field-arithmetic
/// overflow downstream; failing the check just leaves an algebraic value (still
/// sound). Detection is exact (`compare_rational == Equal`), never a wrong collapse.
fn algebraic_result_to_value(a: RealAlgebraic) -> Value {
    if let Some(c) = try_rationalize(&a) {
        return Value::Real(c);
    }
    Value::RealAlgebraic(a)
}

/// The positive divisors of `|n|` (for `n ≠ 0`), bounded by
/// [`RATIONALIZE_MAX_DIVISORS`]. `None` if `n == 0` or the divisor set exceeds the
/// cap (decline — keep the value algebraic).
fn positive_divisors(n: i128) -> Option<Vec<i128>> {
    let m = n.checked_abs()?;
    if m == 0 {
        return None;
    }
    let mut out: Vec<i128> = Vec::new();
    let mut d: i128 = 1;
    while d.checked_mul(d)? <= m {
        if m % d == 0 {
            out.push(d);
            let other = m / d;
            if other != d {
                out.push(other);
            }
            if out.len() > RATIONALIZE_MAX_DIVISORS {
                return None;
            }
        }
        d = d.checked_add(1)?;
    }
    Some(out)
}

/// If the algebraic number `a` is in fact rational, return that exact rational.
///
/// By the rational-root theorem, a rational root `p/q` (lowest terms) of `a`'s
/// integer defining polynomial has `p | a₀` (constant) and `q | aₙ` (leading). We
/// enumerate those bounded candidates lying within `a`'s isolating interval and
/// confirm exactly via `a.compare_rational(&cand) == Equal` (which refines safely).
/// `None` if `a` is irrational or the candidate enumeration overflows / exceeds the
/// cap — never a wrong rationalization (the equality check is exact).
fn try_rationalize(a: &RealAlgebraic) -> Option<Rational> {
    // Rational-root enumeration runs in `i128`: a poly or interval that does not
    // fit `i128` declines (the value stays algebraic — still sound).
    let poly = a.defining_poly_i128()?;
    let poly = poly.as_slice();
    // Trimmed degree and the (nonzero) constant + leading coefficients.
    let mut deg_plus_one = poly.len();
    while deg_plus_one > 0 && poly[deg_plus_one - 1] == 0 {
        deg_plus_one -= 1;
    }
    if deg_plus_one < 2 {
        return None; // constant or empty ⇒ not a usable root poly
    }
    let lead = poly[deg_plus_one - 1];
    let a0 = poly[0];
    if a0 == 0 {
        // 0 is a root; but a `RealAlgebraic` is irrational by construction, so this
        // does not arise. Stay safe and decline.
        return None;
    }
    let (lo, hi) = a.interval()?;
    let p_divs = positive_divisors(a0)?;
    let q_divs = positive_divisors(lead)?;
    for &p in &p_divs {
        for &q in &q_divs {
            for signed in [p, p.checked_neg()?] {
                let Some(cand) = Rational::checked_new(signed, q) else {
                    continue;
                };
                // Must lie within the isolating interval (cheap reject).
                if cand.checked_cmp(&lo)? != Ordering::Greater
                    || cand.checked_cmp(&hi)? != Ordering::Less
                {
                    continue;
                }
                if a.compare_rational(&cand)? == Ordering::Equal {
                    return Some(cand);
                }
            }
        }
    }
    None
}

/// Exact `a + b` of two real-sorted [`Value`]s (rational or algebraic). A pure
/// rational sum stays rational (exact); any algebraic operand uses
/// [`RealAlgebraic::add`]. `None` on overflow / decline.
fn value_add(a: &Value, b: &Value) -> Option<Value> {
    if let (Value::Real(x), Value::Real(y)) = (a, b) {
        return Some(Value::Real(x.checked_add(*y)?));
    }
    // A rational operand `c` added to an algebraic `α` is the exact affine image
    // `α + c` (`affine_algebraic(α, 1, c)`) — an exact, resultant-free derived
    // algebraic number. This is more precise than lifting `c` to a degree-1
    // algebraic and running the sum resultant (whose wide rational bracket can
    // capture multiple roots of the result poly and decline). Only when BOTH are
    // genuinely algebraic do we use the resultant-based `RealAlgebraic::add`.
    match (a, b) {
        (Value::Real(c), Value::RealAlgebraic(alg))
        | (Value::RealAlgebraic(alg), Value::Real(c)) => {
            return Some(algebraic_result_to_value(affine_algebraic(
                alg,
                Rational::integer(1),
                *c,
            )?));
        }
        _ => {}
    }
    let alpha = value_as_algebraic(a)?;
    let beta = value_as_algebraic(b)?;
    Some(algebraic_result_to_value(alpha.add(&beta)?))
}

/// Exact `a · b` of two real-sorted [`Value`]s. A rational-`0` operand yields the
/// exact rational `0` (a [`RealAlgebraic`] is never `0`). A pure rational product
/// stays rational; any algebraic operand uses [`RealAlgebraic::mul`]. `None` on
/// overflow / decline.
fn value_mul(a: &Value, b: &Value) -> Option<Value> {
    if matches!(a, Value::Real(c) if c.is_zero()) || matches!(b, Value::Real(c) if c.is_zero()) {
        return Some(Value::Real(Rational::zero()));
    }
    if let (Value::Real(x), Value::Real(y)) = (a, b) {
        return Some(Value::Real(x.checked_mul(*y)?));
    }
    // A (nonzero) rational operand `c` times an algebraic `α` is the exact affine
    // image `c·α` (`affine_algebraic(α, c, 0)`) — exact, resultant-free, and avoids
    // the wide-bracket decline of lifting `c` to a degree-1 algebraic and running
    // the product resultant. Only genuinely algebraic × algebraic uses the
    // resultant-based `RealAlgebraic::mul`.
    match (a, b) {
        (Value::Real(c), Value::RealAlgebraic(alg))
        | (Value::RealAlgebraic(alg), Value::Real(c)) => {
            return Some(algebraic_result_to_value(affine_algebraic(
                alg,
                *c,
                Rational::zero(),
            )?));
        }
        _ => {}
    }
    let alpha = value_as_algebraic(a)?;
    let beta = value_as_algebraic(b)?;
    Some(algebraic_result_to_value(alpha.mul(&beta)?))
}

/// The exact sign of a real-sorted [`Value`]. A rational uses its numerator's
/// sign; an algebraic number (irrational by construction, so never zero) is
/// compared exactly against `0` via its isolating interval. `None` on overflow.
fn value_sign(v: &Value) -> Option<Sign> {
    match v {
        Value::Real(q) => Some(Sign::of_rational(*q)),
        Value::RealAlgebraic(a) => match a.compare_rational(&Rational::zero())? {
            Ordering::Less => Some(Sign::Neg),
            Ordering::Equal => Some(Sign::Zero),
            Ordering::Greater => Some(Sign::Pos),
        },
        _ => None,
    }
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

/// `Res_elim(p, q)` as a univariate **integer** polynomial in `keep`, by the
/// Sylvester determinant. Entries are univariate rational polynomials in `keep`;
/// the determinant is computed (in [`axeyum_ir::poly`]) by Leibniz permutation
/// expansion over that polynomial ring (exact, bounded by `MAX_SYLVESTER_DIM`).
/// Denominators are then cleared to integers (LSB-first). Returns `None` on a
/// foreign variable, a dimension over the cap, an identically-zero resultant, or
/// any overflow.
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
    if m + n > MAX_SYLVESTER_DIM {
        return None;
    }
    // Build the (m+n)×(m+n) Sylvester matrix (shared `axeyum-ir::poly` primitive),
    // then take its determinant by Leibniz expansion (dim ≤ MAX_SYLVESTER_DIM).
    let mat = axeyum_ir::poly::sylvester_matrix(&pc, &qc)?;
    let det = sylvester_determinant(&mat)?;
    // Clear denominators → integer poly. A genuinely-zero determinant declines.
    if det.iter().all(|c| c.is_zero()) {
        return None;
    }
    rat_coeffs_to_integer(&det)
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
    // The affine map runs in `i128`: an algebraic input whose defining poly or
    // interval does not fit `i128` declines (a sound `Unknown`).
    let p = alpha.defining_poly_i128()?;
    let p = p.as_slice();
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
    let (lo, hi) = alpha.interval()?;
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
/// vars are substituted; the residual is constant (→ rational sign), single-
/// variable in one algebraic var (→ `sign_at`), or — for a genuinely coupled
/// component whose model binds TWO algebraic coordinates — evaluated exactly by
/// `RealAlgebraic` field arithmetic at the algebraic point ([`multipoly_sign_at`],
/// the grid-lift evaluator). Returns `true` iff the comparison holds; `false` on
/// any overflow / unbound var / indeterminacy (the caller then declines — never a
/// wrong `Sat`).
fn replay_multi_atom(atom: &MultiAtom, model: &Model) -> bool {
    // Collect the rational bindings for this atom's variables; detect algebraic ones.
    let vars = atom.poly.vars();
    let mut rationals: BTreeMap<SymbolId, Rational> = BTreeMap::new();
    let mut algebraic_count = 0usize;
    let mut sole_algebraic: Option<SymbolId> = None;
    for v in &vars {
        match model.get(*v) {
            Some(Value::Real(q)) => {
                rationals.insert(*v, q);
            }
            Some(Value::RealAlgebraic(_)) => {
                algebraic_count += 1;
                sole_algebraic = Some(*v);
            }
            _ => return false,
        }
    }
    if algebraic_count >= 2 {
        // Two (or more) algebraic coordinates in one atom: evaluate the FULL
        // polynomial exactly at the algebraic point by field arithmetic. Every
        // variable of the atom is bound in the model (checked above), so the point
        // is complete. A `None` (overflow / decline) ⇒ `false` (the caller
        // declines — never a wrong Sat).
        let mut point: BTreeMap<SymbolId, Value> = BTreeMap::new();
        for v in &vars {
            match model.get(*v) {
                Some(val) => {
                    point.insert(*v, val);
                }
                None => return false,
            }
        }
        return match multipoly_sign_at(&atom.poly, &point) {
            Some(s) => sign_satisfies(atom.cmp, s),
            None => false,
        };
    }
    let Some(residual) = substitute_rationals(&atom.poly, &rationals) else {
        return false;
    };
    match sole_algebraic {
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

/// Collect every **Real-sorted** symbol that occurs in the term `t` (transitive),
/// into `out`. Used to bind any cancelled-but-still-present free variable before
/// the ground-evaluator replay (a symbol can vanish from a normalized polynomial
/// yet remain in the raw term the evaluator reads). Only Real symbols are gathered
/// so a non-Real symbol is never mis-bound to a Real value.
fn collect_term_symbols(arena: &TermArena, t: TermId, out: &mut BTreeSet<SymbolId>) {
    let mut stack = vec![t];
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    while let Some(cur) = stack.pop() {
        if !seen.insert(cur) {
            continue;
        }
        match arena.node(cur) {
            TermNode::Symbol(s) if arena.sort_of(cur) == Sort::Real => {
                out.insert(*s);
            }
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
}

/// The set of all Real-sorted symbols occurring across `assertions`.
fn real_symbols_of(arena: &TermArena, assertions: &[TermId]) -> BTreeSet<SymbolId> {
    let mut out = BTreeSet::new();
    for &a in assertions {
        collect_term_symbols(arena, a, &mut out);
    }
    out
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

/// Count the **distinct cross-product monomials** of the NORMALIZED polynomials
/// of `assertions`, for the deterministic OOM admission gate in
/// [`crate::nra::check_with_nra`].
///
/// A *cross-product monomial* is a nonzero-coefficient monomial mentioning **two
/// or more distinct variables** (e.g. `x·y`, `x·y·z`, `x²·y`). Pure powers of a
/// single variable (`x²`, `x³`) are squares/powers — cheap, never counted —
/// matching the raw gate's exclusion of `a == b`.
///
/// This counts over the canonical [`MultiPoly`] (like monomials collected,
/// zero-coefficient terms dropped, cancelling pairs removed), so it is **not
/// inflated** by `0·y·z` monomials or algebraically-cancelling products that the
/// raw term-tree walk over-counts. It is purely a *count* used by the gate; it
/// changes no verdict and only relaxes a conservative OOM refusal.
///
/// Returns `None` if any assertion is not a conjunction of multivariate
/// polynomial comparisons (so the caller falls back to the raw term-tree count,
/// preserving the original gate for shapes this normalizer cannot represent).
pub(crate) fn normalized_cross_product_count(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<usize> {
    let mut atoms: Vec<MultiAtom> = Vec::new();
    for &a in assertions {
        collect_multi_conjuncts(arena, a, &mut atoms)?;
    }
    let mut cross: BTreeSet<MonoKey> = BTreeSet::new();
    for atom in &atoms {
        for key in atom.poly.terms.keys() {
            // `terms` already excludes zero-coefficient monomials. A monomial with
            // ≥ 2 distinct variables is a cross-product (the `key` is a sorted list
            // of `(var, exp)` pairs, one entry per distinct variable).
            if key.len() >= 2 {
                cross.insert(key.clone());
            }
        }
    }
    Some(cross.len())
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
            op: inner_op,
            args: inner_args,
        } = arena.node(inner)
        else {
            return None;
        };
        // Dualize a negated real (in)equality to its complementary relation, so
        // refutation queries — which arrive as `¬goal` and are usually stated as
        // `≤`/`≥`/`=` — reach the decider (including the SOS/PSD certificate) rather
        // than falling through to the abstraction search. `lhs − rhs` is the same
        // polynomial as the un-negated comparison; only the relation flips.
        let cmp = match inner_op {
            Op::Eq => {
                if arena.sort_of(inner_args[0]) != Sort::Real {
                    return None;
                }
                Cmp::Ne // ¬(a = b)  ⇔  a ≠ b
            }
            Op::RealLt => Cmp::Ge, // ¬(a < b)  ⇔  a ≥ b
            Op::RealLe => Cmp::Gt, // ¬(a ≤ b)  ⇔  a > b
            Op::RealGt => Cmp::Le, // ¬(a > b)  ⇔  a ≤ b
            Op::RealGe => Cmp::Lt, // ¬(a ≥ b)  ⇔  a < b
            _ => return None,
        };
        let poly = collect_multi_diff(arena, inner_args[0], inner_args[1])?;
        return Some((cmp, poly));
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

// ============================================================================
// Degree-2 sum-of-squares / positive-semidefinite (PSD) refutation
// (sound, possibly incomplete).
// ============================================================================
//
// A real polynomial `p` of total degree ≤ 2 in variables x₁..xₙ is a quadratic
// form and can be written `p(x) = [x;1]ᵀ M [x;1]` with the symmetric rational
// (n+1)×(n+1) Gram matrix `M`:
//
//   M[i][i] = coeff(xᵢ²)
//   M[i][j] = M[j][i] = ½·coeff(xᵢxⱼ)         (i ≠ j, both real vars)
//   M[i][n] = M[n][i] = ½·coeff(xᵢ)           (linear term)
//   M[n][n] = constant term
//
// `[x;1]ᵀ M [x;1] = p(x)` identically (expanding the symmetric quadratic form
// reproduces every coefficient). Hence:
//   • `M` PSD  ⇒ `p(x) ≥ 0 ∀x` ⇒ a STRICT `p < 0` is UNSAT,
//   • `−M` PSD ⇒ `p(x) ≤ 0 ∀x` ⇒ a STRICT `p > 0` is UNSAT.
// These are SUFFICIENT (sound) conditions; failing them ⇒ decline (no verdict).
// We deliberately do NOT decide non-strict `≤`/`≥` atoms here: PSD yields `≥ 0`,
// not `> 0`, so `p ≤ 0` can be satisfied at a zero of `p`. We never emit Sat.
//
// Soundness rests on the exact rational LDLᵀ PSD test below; any `i128` overflow
// or unresolved sign during the factorization DECLINES (returns `false`), never
// a wrong Unsat. No floating point.

/// Attempt a degree-2 PSD refutation across all atoms of the conjunction. Any
/// single STRICT inequality atom that is globally one-signed (and so refuted
/// everywhere) makes the whole conjunction `Unsat`. Returns `None` to decline
/// (no atom certifies) — never `Sat`.
fn sos_refute_multivariate(atoms: &[MultiAtom]) -> Option<CheckResult> {
    for atom in atoms {
        if sos_certificate_for_strict_atom(atom.cmp, &atom.poly).is_some() {
            return Some(CheckResult::Unsat);
        }
    }
    None
}

/// Upper bound on an integer square weight `d` that [`SosCertificate::unit_squares`]
/// expands into `d` repeated squares (the reconstructed proof is linear in `d`, so a
/// large weight is declined as a later — denominator/scaling — slice).
const SOS_MAX_SQUARE_WEIGHT: i128 = 16;

/// A self-contained, independently re-checkable sum-of-squares refutation of a
/// STRICT quadratic inequality atom. [`SosCertificate::verify`] needs no arena or
/// solver state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SosCertificate {
    /// Monomials of `p` over canonical variable indices `0..n_vars` (the atom is
    /// `p < 0` when `strict_lt`, else `p > 0`). Each `(factors, coeff)` has total
    /// degree ≤ 2.
    terms: Vec<(Vec<(usize, u32)>, Rational)>,
    n_vars: usize,
    /// `true`: atom `p < 0`, certified by `M ⪰ 0` (⇒ `p ≥ 0`). `false`: atom
    /// `p > 0`, certified by `−M ⪰ 0` (⇒ `p ≤ 0`). Either contradicts the strict
    /// atom.
    strict_lt: bool,
    /// `LDLᵀ` factors of the certified matrix (`M` if `strict_lt`, else `−M`).
    l: Vec<Vec<Rational>>,
    d: Vec<Rational>,
}

impl SosCertificate {
    /// Independently re-validate this sum-of-squares refutation. **Fully
    /// independent of the producer**: it rebuilds the Gram matrix from
    /// `SosCertificate::terms`, never trusting any matrix the producer carried,
    /// then confirms the carried `LDLᵀ` factors reconstruct the certified target
    /// (`M` for `p < 0`, `−M` for `p > 0`) with `D ≥ 0`.
    ///
    /// `Some(true)`/`true` ⇒ `target ⪰ 0` ⇒ the certified quadratic form `p` is
    /// genuinely globally `≥ 0` (or `≤ 0`), so the STRICT atom is UNSAT. Returns
    /// `false` (never panics) on any malformed dimension, degree ≥ 3 monomial, or
    /// `i128`/`Rational` overflow — when in doubt, reject.
    #[must_use]
    pub fn verify(&self) -> bool {
        // 1. Rebuild the symmetric Gram matrix from the carried indexed terms,
        //    independent of any producer state. `None` ⇒ degree ≥ 3 / overflow.
        let Some(gram) = gram_from_indexed_terms(&self.terms, self.n_vars) else {
            return false;
        };
        let dim = self.n_vars + 1;
        // 2. The target the LDLᵀ factors must reconstruct.
        let target = if self.strict_lt {
            gram
        } else {
            match negate_matrix(&gram) {
                Some(neg) => neg,
                None => return false,
            }
        };
        // 3. Dimension sanity: `l` is dim×dim, `d` is dim.
        if target.len() != dim || self.d.len() != dim || self.l.len() != dim {
            return false;
        }
        if self.l.iter().any(|row| row.len() != dim) {
            return false;
        }
        // 4. Independently reconstruct L·D·Lᵀ and confirm it equals `target` with
        //    every D[k] ≥ 0 (the sum-of-squares nonnegativity condition).
        matches!(ldlt_reconstructs(&target, &self.l, &self.d), Some(true))
    }

    /// Number of real variables `n` (the matrix is `(n+1)×(n+1)`).
    #[must_use]
    pub(crate) fn n_vars(&self) -> usize {
        self.n_vars
    }

    /// The atom is `p < 0` (`true`) or `p > 0` (`false`).
    #[must_use]
    pub(crate) fn strict_lt(&self) -> bool {
        self.strict_lt
    }

    /// The certified polynomial `p`'s monomials over canonical variable indices
    /// `0..n_vars`, as `(factors, coeff)` with each `factors` a sorted list of
    /// `(var_index, exponent)` of total degree ≤ 2 (`[]` is the constant term).
    /// This is exactly the polynomial whose SOS the certificate refutes; the
    /// reconstructor reads it to build the faithful kernel encoding of `p`.
    #[must_use]
    pub(crate) fn poly_terms(&self) -> &[(Vec<(usize, u32)>, Rational)] {
        &self.terms
    }

    /// If this certificate is a **single perfect square of a ±1-coefficient linear
    /// form** — exactly ONE nonzero `D[k]` equal to `1`, all other `D` zero, and
    /// the square `ℓₖ(x) = Σⱼ L[j][k]·xⱼ + L[n][k]` having every variable
    /// coefficient `L[j][k] ∈ {−1, 0, +1}` and a **zero** affine entry `L[n][k]` —
    /// return that square's signed variable coefficients `[(var_index, ±1); …]`
    /// (ascending by index, zeros dropped). Otherwise `None` (decline): multiple
    /// nonzero `D`, `D[k] ≠ 1`, a coefficient needing scaling, or a nonzero affine
    /// row.
    ///
    /// The returned coefficients are over the SAME canonical indices as
    /// [`SosCertificate::poly_terms`], so `(Σ cⱼ·xⱼ)² = p` holds over ℚ (the
    /// reconstructor re-asserts this before trusting it).
    #[must_use]
    pub(crate) fn single_unit_square(&self) -> Option<Vec<(usize, i128)>> {
        let dim = self.n_vars + 1;
        if self.d.len() != dim || self.l.len() != dim {
            return None;
        }
        if self.l.iter().any(|row| row.len() != dim) {
            return None;
        }
        // Exactly one nonzero D[k], and it must equal 1.
        let one = Rational::integer(1);
        let mut sq_col: Option<usize> = None;
        for (k, &dk) in self.d.iter().enumerate() {
            if dk.is_zero() {
                continue;
            }
            if dk != one || sq_col.is_some() {
                return None; // ≠1, or a second nonzero square
            }
            sq_col = Some(k);
        }
        let k = sq_col?;
        // ℓₖ = column k of L, read over rows 0..dim. The affine entry (row n) must
        // be zero; each variable entry must be ∈ {−1, 0, +1}.
        let neg_one = Rational::integer(-1);
        let n = self.n_vars;
        if !self.l[n][k].is_zero() {
            return None; // nonzero affine row — outside this slice
        }
        let mut coeffs: Vec<(usize, i128)> = Vec::new();
        for j in 0..n {
            let c = self.l[j][k];
            if c.is_zero() {
                continue;
            }
            if c == one {
                coeffs.push((j, 1));
            } else if c == neg_one {
                coeffs.push((j, -1));
            } else {
                return None; // coefficient needs scaling — outside this slice
            }
        }
        if coeffs.is_empty() {
            return None; // the zero form squares to 0, never refutes p < 0
        }
        Some(coeffs)
    }

    /// If this certificate is a **sum of perfect squares of ±1-coefficient linear
    /// forms** — EVERY nonzero `D[k]` equals `1`, and each such square's column `k`
    /// of `L` has every variable coefficient `L[j][k] ∈ {−1, 0, +1}` and a **zero**
    /// affine entry `L[n][k]` — return the list of squares' signed unit coefficient
    /// vectors `[[(var_index, ±1); …]; …]`, one inner vector per nonzero `D[k]`
    /// (in ascending column order; within each square, ascending by index, zeros
    /// dropped). Otherwise `None` (decline): some nonzero `D[k] ≠ 1`, a coefficient
    /// needing scaling, a nonzero affine row, or a square whose form is identically
    /// zero.
    ///
    /// This is the multi-square generalization of [`SosCertificate::single_unit_square`]
    /// (which is the `m = 1` special case). The returned coefficients are over the
    /// SAME canonical indices as [`SosCertificate::poly_terms`], so
    /// `Σₖ (Σⱼ cₖⱼ·xⱼ)² = p` holds over ℚ (the reconstructor re-asserts this).
    #[must_use]
    pub(crate) fn unit_squares(&self) -> Option<Vec<Vec<(usize, i128)>>> {
        let dim = self.n_vars + 1;
        if self.d.len() != dim || self.l.len() != dim {
            return None;
        }
        if self.l.iter().any(|row| row.len() != dim) {
            return None;
        }
        let one = Rational::integer(1);
        let neg_one = Rational::integer(-1);
        let n = self.n_vars;
        let mut squares: Vec<Vec<(usize, i128)>> = Vec::new();
        for (k, &dk) in self.d.iter().enumerate() {
            if dk.is_zero() {
                continue;
            }
            // Accept a positive INTEGER weight `d` by emitting the square `d` times:
            // `d·ℓ²` is reconstructed as `ℓ² + … + ℓ²` (d copies), which the
            // nonnegativity fold and the ring normalizer already handle with no new
            // machinery. `d = 1` is the common case. A rational (non-integer) weight
            // needs denominator-clearing — a later slice — so it declines. The weight
            // is bounded to keep the (linear-in-d) proof size small.
            let weight = if dk == one {
                1
            } else if dk.denominator() == 1
                && dk.numerator() >= 1
                && dk.numerator() <= SOS_MAX_SQUARE_WEIGHT
            {
                dk.numerator()
            } else {
                return None; // rational or too-large weight — outside this slice
            };
            // Affine entry of column k must be zero.
            if !self.l[n][k].is_zero() {
                return None;
            }
            let mut coeffs: Vec<(usize, i128)> = Vec::new();
            for j in 0..n {
                let c = self.l[j][k];
                if c.is_zero() {
                    continue;
                }
                if c == one {
                    coeffs.push((j, 1));
                } else if c == neg_one {
                    coeffs.push((j, -1));
                } else {
                    return None; // coefficient needs scaling — outside this slice
                }
            }
            if coeffs.is_empty() {
                return None; // a zero form — would not refute p < 0 by itself
            }
            for _ in 0..weight {
                squares.push(coeffs.clone());
            }
        }
        if squares.is_empty() {
            return None; // no nonzero square ⇒ nothing to refute
        }
        Some(squares)
    }

    /// The **rational** sum-of-squares decomposition `p = Σₖ dₖ·ℓₖ²` carried by the
    /// `LDLᵀ` factors, with NO ±1 / integer-weight restriction: each returned entry
    /// is `(dₖ, [(var_index, cₖⱼ); …])` where `dₖ > 0` is the rational diagonal
    /// weight and `cₖⱼ = L[j][k]` are the rational variable coefficients of the
    /// `k`-th square's linear form `ℓₖ = Σⱼ cₖⱼ·xⱼ` (zeros dropped, ascending by
    /// index). Columns with `D[k] = 0` are dropped (they contribute nothing).
    ///
    /// The coefficients are over the SAME canonical indices as
    /// [`SosCertificate::poly_terms`], so `Σₖ dₖ·(Σⱼ cₖⱼ·xⱼ)² = p` holds over ℚ
    /// (the reconstructor re-asserts this over the kernel before trusting it).
    ///
    /// Returns `None` (decline) on a malformed dimension, a **nonzero affine row**
    /// `L[n][k] ≠ 0` (outside the homogeneous slice the denominator-clearing
    /// reconstructor handles), a negative `D[k]` (never produced by a PSD factor,
    /// but rejected defensively), or a square whose form is identically zero.
    #[must_use]
    #[allow(clippy::type_complexity)]
    pub(crate) fn rational_squares(&self) -> Option<Vec<(Rational, Vec<(usize, Rational)>)>> {
        let dim = self.n_vars + 1;
        if self.d.len() != dim || self.l.len() != dim {
            return None;
        }
        if self.l.iter().any(|row| row.len() != dim) {
            return None;
        }
        let n = self.n_vars;
        let zero = Rational::zero();
        let mut squares: Vec<(Rational, Vec<(usize, Rational)>)> = Vec::new();
        for (k, &dk) in self.d.iter().enumerate() {
            if dk.is_zero() {
                continue; // a zero-weight column contributes nothing
            }
            if dk.numerator() < 0 {
                return None; // negative weight — never PSD, reject defensively
            }
            // The affine entry of column k must be zero (homogeneous slice).
            if !self.l[n][k].is_zero() {
                return None;
            }
            let mut coeffs: Vec<(usize, Rational)> = Vec::new();
            for j in 0..n {
                let c = self.l[j][k];
                if c == zero {
                    continue;
                }
                coeffs.push((j, c));
            }
            if coeffs.is_empty() {
                return None; // a zero form would not refute p < 0 by itself
            }
            squares.push((dk, coeffs));
        }
        if squares.is_empty() {
            return None; // no nonzero square ⇒ nothing to refute
        }
        Some(squares)
    }
}

/// Rebuild the symmetric `(n_vars+1)×(n_vars+1)` rational Gram matrix `M` from
/// monomials over canonical variable indices `0..n_vars`, so that
/// `p(x) = [x;1]ᵀ M [x;1]`. Mirrors [`quadratic_gram_matrix`]'s classification
/// over integer indices instead of [`SymbolId`]s. Returns `None` (reject) on any
/// monomial of total degree ≥ 3, an out-of-range index, or any `Rational`
/// overflow while halving an odd cross/linear coefficient.
fn gram_from_indexed_terms(
    terms: &[(Vec<(usize, u32)>, Rational)],
    n_vars: usize,
) -> Option<Vec<Vec<Rational>>> {
    let n = n_vars;
    let dim = n + 1;
    let mut gram = vec![vec![Rational::zero(); dim]; dim];
    let half = Rational::checked_new(1, 2)?;

    for (key, coeff) in terms {
        match key.as_slice() {
            // Constant term → M[n][n].
            [] => {
                gram[n][n] = gram[n][n].checked_add(*coeff)?;
            }
            // Linear term `c·xᵢ` → split ½c onto M[i][n] and M[n][i].
            [(idx, 1)] => {
                let idx = *idx;
                if idx >= n {
                    return None;
                }
                let half_c = coeff.checked_mul(half)?;
                gram[idx][n] = gram[idx][n].checked_add(half_c)?;
                gram[n][idx] = gram[n][idx].checked_add(half_c)?;
            }
            // Square term `c·xᵢ²` → M[i][i].
            [(idx, 2)] => {
                let idx = *idx;
                if idx >= n {
                    return None;
                }
                gram[idx][idx] = gram[idx][idx].checked_add(*coeff)?;
            }
            // Cross term `c·xᵢxⱼ` (i ≠ j) → split ½c onto M[i][j] and M[j][i].
            [(row, 1), (col, 1)] => {
                let (row, col) = (*row, *col);
                if row >= n || col >= n {
                    return None;
                }
                let half_c = coeff.checked_mul(half)?;
                gram[row][col] = gram[row][col].checked_add(half_c)?;
                gram[col][row] = gram[col][row].checked_add(half_c)?;
            }
            // Any monomial of total degree ≥ 3 (or an unexpected shape) ⇒ reject.
            _ => return None,
        }
    }
    Some(gram)
}

/// If the STRICT inequality atom `p ⋈ 0` (`⋈ ∈ {<, >}`) is refuted globally by a
/// degree-2 PSD certificate, return a self-contained [`SosCertificate`]; else
/// `None` (decline). `p < 0` is certified by `M ⪰ 0` (⇒ `p ≥ 0 ∀x`); `p > 0` by
/// `−M ⪰ 0` (⇒ `p ≤ 0 ∀x`). Declines for any non-strict comparison, any
/// polynomial of total degree ≥ 3, or any overflow.
///
/// The verdict is unchanged from the old boolean predicate: a certificate is
/// returned **iff** the matrix (or its negation) is exact-PSD and that PSD claim
/// independently reconstructs — so `.is_some()` is the decision the decider uses.
fn sos_certificate_for_strict_atom(cmp: Cmp, poly: &MultiPoly) -> Option<SosCertificate> {
    // Only strict `<` / `>` admit a PSD refutation (see module note).
    let strict_lt = match cmp {
        Cmp::Lt => true,  // p < 0 refuted by p ≥ 0 everywhere (M PSD)
        Cmp::Gt => false, // p > 0 refuted by p ≤ 0 everywhere (−M PSD)
        Cmp::Eq | Cmp::Ne | Cmp::Le | Cmp::Ge => return None,
    };
    // Build M (degree ≥ 3 / overflow ⇒ decline).
    let matrix = quadratic_gram_matrix(poly)?;
    // The matrix the LDLᵀ certificate is over: M for `< 0`, −M for `> 0`.
    let target = if strict_lt {
        matrix
    } else {
        negate_matrix(&matrix)?
    };
    // Run the exact LDLᵀ; only a PSD factorization that independently reconstructs
    // the target certifies the atom.
    let Ldlt::Psd { l, d } = try_ldlt(&target) else {
        return None;
    };
    if ldlt_reconstructs(&target, &l, &d) != Some(true) {
        return None;
    }
    // Remap `poly`'s monomials from `SymbolId`s to the canonical `0..n` variable
    // indices used by `quadratic_gram_matrix` (the deterministic `vars()` order),
    // so the certificate is self-contained (no `SymbolId`s leak into it).
    let vars: Vec<SymbolId> = poly.vars().into_iter().collect();
    let n_vars = vars.len();
    let mut index: BTreeMap<SymbolId, usize> = BTreeMap::new();
    for (i, &v) in vars.iter().enumerate() {
        index.insert(v, i);
    }
    let mut terms: Vec<(Vec<(usize, u32)>, Rational)> = Vec::with_capacity(poly.terms.len());
    for (key, &coeff) in &poly.terms {
        let mut factors: Vec<(usize, u32)> = Vec::with_capacity(key.len());
        for &(sym, exp) in key {
            factors.push((*index.get(&sym)?, exp));
        }
        terms.push((factors, coeff));
    }
    Some(SosCertificate {
        terms,
        n_vars,
        strict_lt,
        l,
        d,
    })
}

/// Collect a conjunction's atoms (mirroring the multivariate decomposition path)
/// and return the [`SosCertificate`] of the **first** STRICT inequality atom a
/// degree-2 PSD certificate refutes, or `None` to decline. The verdict matches
/// [`sos_refute_multivariate`]: a returned certificate proves the conjunction
/// `Unsat`. Self-contained (no `SymbolId`s leak into the certificate).
pub(crate) fn sos_refute_with_certificate(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<SosCertificate> {
    let mut atoms: Vec<MultiAtom> = Vec::new();
    for &a in assertions {
        collect_multi_conjuncts(arena, a, &mut atoms)?;
    }
    if atoms.is_empty() {
        return None;
    }
    for atom in &atoms {
        if let Some(cert) = sos_certificate_for_strict_atom(atom.cmp, &atom.poly) {
            return Some(cert);
        }
    }
    None
}

/// Build the symmetric (n+1)×(n+1) rational Gram matrix `M` of a total-degree-≤2
/// polynomial `p`, so that `p(x) = [x;1]ᵀ M [x;1]`. Returns `None` (decline) if
/// any monomial has total degree ≥ 3, or on any `i128`/`Rational` overflow while
/// halving an odd cross / linear coefficient.
///
/// The variables are ordered by their (deterministic) `SymbolId` sort order; the
/// last index `n` is the affine ("1") coordinate. Every entry is exact.
fn quadratic_gram_matrix(poly: &MultiPoly) -> Option<Vec<Vec<Rational>>> {
    // Stable, deterministic variable ordering.
    let vars: Vec<SymbolId> = poly.vars().into_iter().collect();
    let n = vars.len();
    // Index of each variable in the matrix; the affine row/column is index `n`.
    let mut index: BTreeMap<SymbolId, usize> = BTreeMap::new();
    for (i, &v) in vars.iter().enumerate() {
        index.insert(v, i);
    }
    let dim = n + 1;
    let mut gram = vec![vec![Rational::zero(); dim]; dim];
    let half = Rational::checked_new(1, 2)?;

    for (key, &coeff) in &poly.terms {
        // Classify the monomial by its (variable, exponent) structure. Anything of
        // total degree ≥ 3 declines.
        match key.as_slice() {
            // Constant term → M[n][n].
            [] => {
                gram[n][n] = gram[n][n].checked_add(coeff)?;
            }
            // Linear term `c·xᵢ` → split ½c onto M[i][n] and M[n][i].
            [(var, 1)] => {
                let idx = *index.get(var)?;
                let half_c = coeff.checked_mul(half)?;
                gram[idx][n] = gram[idx][n].checked_add(half_c)?;
                gram[n][idx] = gram[n][idx].checked_add(half_c)?;
            }
            // Square term `c·xᵢ²` → M[i][i].
            [(var, 2)] => {
                let idx = *index.get(var)?;
                gram[idx][idx] = gram[idx][idx].checked_add(coeff)?;
            }
            // Cross term `c·xᵢxⱼ` (i ≠ j) → split ½c onto M[i][j] and M[j][i].
            [(left, 1), (right, 1)] => {
                let row = *index.get(left)?;
                let col = *index.get(right)?;
                let half_c = coeff.checked_mul(half)?;
                gram[row][col] = gram[row][col].checked_add(half_c)?;
                gram[col][row] = gram[col][row].checked_add(half_c)?;
            }
            // Any monomial of total degree ≥ 3 (or an unexpected shape) ⇒ decline:
            // this is a degree-2-only certificate.
            _ => return None,
        }
    }
    Some(gram)
}

/// Negate every entry of a rational matrix, declining (`None`) on overflow.
fn negate_matrix(matrix: &[Vec<Rational>]) -> Option<Vec<Vec<Rational>>> {
    let mut out = Vec::with_capacity(matrix.len());
    for row in matrix {
        let mut neg_row = Vec::with_capacity(row.len());
        for &entry in row {
            neg_row.push(entry.checked_neg()?);
        }
        out.push(neg_row);
    }
    Some(out)
}

/// The outcome of attempting an exact symmetric `LDLᵀ` factorization of a
/// rational matrix: a positive-semidefinite witness, a definite refutation, or a
/// graceful overflow decline.
enum Ldlt {
    /// `M = L·D·Lᵀ` with `L` unit lower-triangular and `D ≥ 0` (componentwise):
    /// an explicit certificate that the associated quadratic form is a sum of
    /// squares `p(x) = Σₖ D[k]·ℓₖ(x)²` (`ℓₖ` = the k-th coordinate of `Lᵀ[x;1]`),
    /// hence globally nonnegative.
    Psd {
        l: Vec<Vec<Rational>>,
        d: Vec<Rational>,
    },
    /// The matrix is provably NOT positive semidefinite.
    NotPsd,
    /// An `i128` overflow prevented an exact factorization ⇒ the caller declines.
    Overflow,
}

/// Exact symmetric `LDLᵀ` factorization of a SYMMETRIC rational matrix, recording
/// the `L`/`D` factors so the PSD claim carries an explicit, checkable
/// sum-of-squares certificate. Standard symmetric (Gaussian) elimination, exact
/// over ℚ; process pivots `k = 0..dim` on the running reduced matrix `a`:
///   • `a[k][k] > 0`: a positive pivot `D[k]`; record the multipliers
///     `L[i][k] = a[i][k]/a[k][k]` and apply the symmetric rank-1 update
///     `a[i][j] -= L[i][k]·a[k][j]`.
///   • `a[k][k] == 0`: PSD demands the entire remaining k-th row/column be zero (a
///     zero pivot with a nonzero off-diagonal ⇒ the form takes negative values ⇒
///     NOT PSD); when zero, `D[k] = 0`, `L[i][k] = 0`, nothing to eliminate.
///   • `a[k][k] < 0`: an immediate negative direction ⇒ NOT PSD.
#[allow(
    clippy::needless_range_loop,
    reason = "the symmetric rank-1 update reads a[i][j], a[i][k], a[k][j] by index together"
)]
fn try_ldlt(matrix: &[Vec<Rational>]) -> Ldlt {
    let dim = matrix.len();
    if matrix.iter().any(|r| r.len() != dim) {
        return Ldlt::NotPsd; // a non-square matrix is not something we certify
    }
    let mut a: Vec<Vec<Rational>> = matrix.to_vec();
    let mut l = vec![vec![Rational::zero(); dim]; dim];
    let mut d = vec![Rational::zero(); dim];
    for k in 0..dim {
        l[k][k] = Rational::integer(1); // unit lower triangular
    }

    for k in 0..dim {
        let pivot = a[k][k];
        d[k] = pivot;
        match Sign::of_rational(pivot) {
            Sign::Neg => return Ldlt::NotPsd,
            Sign::Zero => {
                for j in (k + 1)..dim {
                    if !a[k][j].is_zero() || !a[j][k].is_zero() {
                        return Ldlt::NotPsd;
                    }
                }
                // L[i][k] stays 0 (no elimination for a zero pivot).
            }
            Sign::Pos => {
                for i in (k + 1)..dim {
                    let Some(factor) = a[i][k].checked_div(pivot) else {
                        return Ldlt::Overflow;
                    };
                    l[i][k] = factor;
                    if factor.is_zero() {
                        continue;
                    }
                    for j in (k + 1)..dim {
                        let Some(term) = factor.checked_mul(a[k][j]) else {
                            return Ldlt::Overflow;
                        };
                        let Some(updated) = a[i][j].checked_sub(term) else {
                            return Ldlt::Overflow;
                        };
                        a[i][j] = updated;
                    }
                }
            }
        }
    }
    Ldlt::Psd { l, d }
}

/// Independently re-validate an `LDLᵀ` certificate: reconstruct `L·D·Lᵀ` and
/// confirm it equals `matrix` exactly, with every `D[k] ≥ 0`. This is the
/// self-checking step — the elimination is sound by construction, but an explicit
/// reconstruction catches any factorization bug before a `p ≥ 0` claim (hence an
/// `unsat`) is trusted. `None` on overflow during the reconstruction (⇒ decline).
#[allow(
    clippy::needless_range_loop,
    reason = "the triple sum L[i][k]·D[k]·L[j][k] indexes three arrays in lockstep"
)]
fn ldlt_reconstructs(
    matrix: &[Vec<Rational>],
    l: &[Vec<Rational>],
    d: &[Rational],
) -> Option<bool> {
    let dim = matrix.len();
    // D ≥ 0 is the sum-of-squares nonnegativity condition.
    if d.iter().any(|&dk| Sign::of_rational(dk) == Sign::Neg) {
        return Some(false);
    }
    for i in 0..dim {
        for j in 0..dim {
            let mut acc = Rational::zero();
            for k in 0..dim {
                let lik_dk = l[i][k].checked_mul(d[k])?;
                let term = lik_dk.checked_mul(l[j][k])?;
                acc = acc.checked_add(term)?;
            }
            if acc != matrix[i][j] {
                return Some(false); // factorization does not reconstruct ⇒ reject
            }
        }
    }
    Some(true)
}

/// Self-checked exact PSD test for a SYMMETRIC rational matrix. Returns
/// `Some(true)` only when an explicit `LDLᵀ` sum-of-squares certificate exists AND
/// independently reconstructs the matrix; `Some(false)` when provably not PSD (or
/// a certificate fails its own reconstruction — a conservative reject); `None` on
/// an `i128` overflow (⇒ the caller declines). Sound for global nonnegativity of
/// the associated quadratic form.
///
/// The certificate producer ([`sos_certificate_for_strict_atom`]) inlines the same
/// `try_ldlt` + `ldlt_reconstructs` so it can *retain* the `L`/`D` factors; this
/// boolean wrapper is exercised by the PSD unit tests.
#[cfg(test)]
fn is_psd_exact(matrix: &[Vec<Rational>]) -> Option<bool> {
    match try_ldlt(matrix) {
        Ldlt::Overflow => None,
        Ldlt::NotPsd => Some(false),
        Ldlt::Psd { l, d } => ldlt_reconstructs(matrix, &l, &d),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ipoly(coeffs: &[i128]) -> Vec<i128> {
        coeffs.to_vec()
    }

    #[test]
    fn grid_misses_two_close_roots_sturm_finds_them() {
        // p(x) = (10000x − 1)(10000x − 2) = 1e8 x² − 30000 x + 2. Its two roots
        // 1/10000 and 2/10000 fall inside ONE 2^14 grid cell — the grid scan sees
        // equal endpoint signs and reports it root-free, UNDER-counting (0 roots).
        // Sturm's exact count finds BOTH. This is the soundness-relevant gap: a
        // missed root could turn a real `sat` into a spurious `unsat` downstream.
        let poly = ipoly(&[2, -30000, 100_000_000]);
        let grid = isolate_roots_grid(&poly).unwrap();
        let sturm = isolate_roots_sturm(&poly).unwrap();
        assert_eq!(grid.len(), 0, "the coarse grid MISSES both close roots");
        assert_eq!(sturm.len(), 2, "Sturm's exact count finds both roots");
        // The dispatcher uses Sturm first ⇒ the complete set.
        assert_eq!(isolate_roots(&poly).unwrap().len(), 2);
    }

    #[test]
    fn sturm_distinct_count_nonsquarefree() {
        // (x² − 2)² has a double root at ±√2 ⇒ 2 DISTINCT roots. The squarefree
        // part (x² − 2) recovers them; the grid alone would see no sign change at
        // an even-multiplicity root and find NONE.
        let p = poly_mul_i(&[-2, 0, 1], &[-2, 0, 1]);
        let sturm = isolate_roots_sturm(&p).unwrap();
        assert_eq!(sturm.len(), 2, "(x²−2)² has 2 distinct real roots");
        for r in &sturm {
            // Each is a genuine root of the ORIGINAL (multiple-root) poly.
            match r {
                Root::Algebraic(a) => assert_eq!(a.sign_at(&p), Some(Sign::Zero)),
                Root::Rational(q) => assert!(eval_rat(&p, *q).unwrap().is_zero()),
            }
        }
    }

    fn poly_mul_i(a: &[i128], b: &[i128]) -> Vec<i128> {
        let mut out = vec![0i128; a.len() + b.len() - 1];
        for (i, &x) in a.iter().enumerate() {
            for (j, &y) in b.iter().enumerate() {
                out[i + j] += x * y;
            }
        }
        out
    }

    #[test]
    fn sturm_count_known_shapes() {
        // (chain count over the full Cauchy interval) must equal the known number
        // of distinct real roots.
        let known: &[(&[i128], usize)] = &[
            (&[-2, 0, 1], 2),    // x² − 2  → ±√2
            (&[1, 0, 1], 0),     // x² + 1  → none
            (&[0, -1, 0, 1], 3), // x³ − x  → −1, 0, 1
        ];
        for (poly, want) in known {
            let got = isolate_roots_sturm(poly).unwrap().len();
            assert_eq!(got, *want, "distinct-root count for {poly:?}");
        }
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

    // --- exact PSD / LDLᵀ unit tests ----------------------------------------

    fn rmat(rows: &[&[(i128, i128)]]) -> Vec<Vec<Rational>> {
        rows.iter()
            .map(|r| {
                r.iter()
                    .map(|&(n, d)| Rational::checked_new(n, d).unwrap())
                    .collect()
            })
            .collect()
    }

    #[test]
    fn psd_identity_is_psd() {
        let m = rmat(&[&[(1, 1), (0, 1)], &[(0, 1), (1, 1)]]);
        assert_eq!(is_psd_exact(&m), Some(true));
    }

    #[test]
    fn psd_rank_one_square_is_psd() {
        // (x − y)² ⇒ M = [[1,−1],[−1,1]], PSD (eigenvalues 0 and 2).
        let m = rmat(&[&[(1, 1), (-1, 1)], &[(-1, 1), (1, 1)]]);
        assert_eq!(is_psd_exact(&m), Some(true));
    }

    #[test]
    fn psd_negative_diagonal_is_not_psd() {
        let m = rmat(&[&[(-1, 1), (0, 1)], &[(0, 1), (1, 1)]]);
        assert_eq!(is_psd_exact(&m), Some(false));
    }

    #[test]
    fn psd_indefinite_is_not_psd() {
        // diag(1, −1): indefinite.
        let m = rmat(&[&[(1, 1), (0, 1)], &[(0, 1), (-1, 1)]]);
        assert_eq!(is_psd_exact(&m), Some(false));
    }

    #[test]
    fn psd_zero_pivot_with_offdiagonal_is_not_psd() {
        // [[0,1],[1,0]] = the form 2xy, indefinite ⇒ NOT PSD.
        let m = rmat(&[&[(0, 1), (1, 1)], &[(1, 1), (0, 1)]]);
        assert_eq!(is_psd_exact(&m), Some(false));
    }

    #[test]
    fn psd_zero_pivot_clean_is_psd() {
        // [[0,0],[0,1]] = the form y², PSD.
        let m = rmat(&[&[(0, 1), (0, 1)], &[(0, 1), (1, 1)]]);
        assert_eq!(is_psd_exact(&m), Some(true));
    }

    #[test]
    fn psd_three_var_am_gm_form_is_psd() {
        // a²+b²+c²−ab−bc−ca = ½[(a−b)²+(b−c)²+(c−a)²] ⇒ PSD Gram matrix
        // M = [[1,−½,−½],[−½,1,−½],[−½,−½,1]] (eigenvalues 0, 3/2, 3/2).
        let m = rmat(&[
            &[(1, 1), (-1, 2), (-1, 2)],
            &[(-1, 2), (1, 1), (-1, 2)],
            &[(-1, 2), (-1, 2), (1, 1)],
        ]);
        assert_eq!(is_psd_exact(&m), Some(true));
    }

    #[test]
    fn ldlt_certificate_reconstructs_the_am_gm_form() {
        // The 3-var AM–GM Gram matrix factors as L·D·Lᵀ, and that explicit
        // certificate must independently reconstruct M (the self-check that backs
        // every SOS `unsat`). D ≥ 0 throughout (the sum-of-squares condition).
        let m = rmat(&[
            &[(1, 1), (-1, 2), (-1, 2)],
            &[(-1, 2), (1, 1), (-1, 2)],
            &[(-1, 2), (-1, 2), (1, 1)],
        ]);
        let Ldlt::Psd { l, d } = try_ldlt(&m) else {
            panic!("AM–GM Gram matrix must factor as LDLᵀ");
        };
        assert!(
            d.iter().all(|&dk| Sign::of_rational(dk) != Sign::Neg),
            "every D[k] must be ≥ 0 (sum-of-squares)"
        );
        assert_eq!(
            ldlt_reconstructs(&m, &l, &d),
            Some(true),
            "L·D·Lᵀ must reconstruct M exactly"
        );
    }

    #[test]
    fn ldlt_rejects_a_tampered_certificate() {
        // A self-check must REJECT factors that do not reconstruct the matrix:
        // identity M, but a D scaled wrong ⇒ L·D·Lᵀ ≠ M ⇒ Some(false).
        let m = rmat(&[&[(1, 1), (0, 1)], &[(0, 1), (1, 1)]]);
        let ident = rmat(&[&[(1, 1), (0, 1)], &[(0, 1), (1, 1)]]);
        let bad_d = vec![Rational::integer(1), Rational::integer(2)]; // wrong
        assert_eq!(
            ldlt_reconstructs(&m, &ident, &bad_d),
            Some(false),
            "a certificate that does not reconstruct M must be rejected"
        );
    }

    #[test]
    fn sos_certificate_verify_rejects_tampered_factors() {
        // x² − 2xy + y² = (x − y)² < 0 is UNSAT (M ⪰ 0). Build a genuine,
        // self-contained certificate over canonical indices {0,1}, then tamper its
        // `d` so the carried factors no longer reconstruct the Gram matrix ⇒
        // `verify()` must return `false` (the self-check rejects bad factors), and
        // the untouched one must accept.
        let terms: Vec<(Vec<(usize, u32)>, Rational)> = vec![
            (vec![(0, 2)], Rational::integer(1)),          // x²
            (vec![(1, 2)], Rational::integer(1)),          // y²
            (vec![(0, 1), (1, 1)], Rational::integer(-2)), // −2xy
        ];
        let gram = gram_from_indexed_terms(&terms, 2).expect("Gram matrix builds");
        let Ldlt::Psd { l, d } = try_ldlt(&gram) else {
            panic!("(x − y)² Gram matrix must be PSD");
        };
        let cert = SosCertificate {
            terms,
            n_vars: 2,
            strict_lt: true,
            l,
            d,
        };
        assert!(cert.verify(), "an untampered certificate must verify");

        // Scale every D[k] by 2: L·D'·Lᵀ ≠ M ⇒ reconstruction fails ⇒ reject.
        let mut tampered = cert.clone();
        for dk in &mut tampered.d {
            *dk = dk.checked_mul(Rational::integer(2)).unwrap();
        }
        assert!(
            !tampered.verify(),
            "a tampered certificate (wrong D) must be rejected by verify()"
        );
    }

    #[test]
    fn cube_no_real_root_is_impossible_but_even_powers_are() {
        // x⁴ + 1: x⁴ ≥ 0 ⇒ no real root ⇒ Unsat for `= 0`.
        match decide_eq(&ipoly(&[1, 0, 0, 0, 1])).unwrap() {
            Verdict::Unsat => {}
            _ => panic!("x⁴ + 1 = 0 has no real root"),
        }
    }

    // === coprime-split / exact-division helpers (CAD-gate widening) ===============

    /// Three distinct fresh Real symbols `(x, y, z)` for the multivariate helpers.
    fn three_syms() -> (SymbolId, SymbolId, SymbolId) {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Real).unwrap();
        let y = arena.declare("y", Sort::Real).unwrap();
        let z = arena.declare("z", Sort::Real).unwrap();
        (x, y, z)
    }

    #[test]
    fn grlex_is_admissible_ranks_higher_degree_first() {
        let (x, y, _) = three_syms();
        // x·y (key over both) vs y (key over y alone): grlex ⇒ xy > y (deg 2 > 1).
        let xy: MonoKey = vec![(x, 1), (y, 1)];
        let just_y: MonoKey = vec![(y, 1)];
        assert_eq!(mono_key_cmp_grlex(&xy, &just_y), Ordering::Greater);
        // The raw Vec lex order gets this WRONG (it would rank xy < y); the explicit
        // per-variable comparison is why the division terminates.
        assert!(
            xy < just_y,
            "the raw Vec lex order is non-admissible (xy < y)"
        );
        // Same total degree, differing first variable: x² > xy under grlex.
        let x2: MonoKey = vec![(x, 2)];
        assert_eq!(mono_key_cmp_grlex(&x2, &xy), Ordering::Greater);
    }

    #[test]
    fn exact_divide_recovers_monotone_product_cofactor() {
        let (x, y, z) = three_syms();
        // xz − yz = z·(x − y): dividing by (x − y) yields exactly z.
        let xz_minus_yz = MultiPoly::var(x)
            .mul(&MultiPoly::var(z))
            .unwrap()
            .sub(&MultiPoly::var(y).mul(&MultiPoly::var(z)).unwrap())
            .unwrap();
        let x_minus_y = MultiPoly::var(x).sub(&MultiPoly::var(y)).unwrap();
        let quot = multipoly_exact_divide(&xz_minus_yz, &x_minus_y).unwrap();
        assert_eq!(quot.terms, MultiPoly::var(z).terms, "cofactor must be z");
        // Multiplying back reproduces the dividend exactly (a genuine factorization).
        assert_eq!(quot.mul(&x_minus_y).unwrap().terms, xz_minus_yz.terms);
    }

    #[test]
    fn exact_divide_rejects_non_factor() {
        let (x, y, z) = three_syms();
        // x + y does NOT divide x·z − y·z ⇒ no exact quotient.
        let xz_minus_yz = MultiPoly::var(x)
            .mul(&MultiPoly::var(z))
            .unwrap()
            .sub(&MultiPoly::var(y).mul(&MultiPoly::var(z)).unwrap())
            .unwrap();
        let x_plus_y = MultiPoly::var(x).add(&MultiPoly::var(y)).unwrap();
        assert!(multipoly_exact_divide(&xz_minus_yz, &x_plus_y).is_none());
    }

    #[test]
    fn exact_divide_handles_constant_scalar_multiple() {
        let (x, y, _) = three_syms();
        // 2·(x − y) ÷ (x − y) = 2 (a constant quotient).
        let x_minus_y = MultiPoly::var(x).sub(&MultiPoly::var(y)).unwrap();
        let doubled = x_minus_y
            .mul(&MultiPoly::constant(Rational::integer(2)))
            .unwrap();
        let quot = multipoly_exact_divide(&doubled, &x_minus_y).unwrap();
        assert_eq!(quot.as_constant(), Some(Rational::integer(2)));
    }

    #[test]
    fn coprime_split_breaks_shared_factor() {
        let (x, y, z) = three_syms();
        // {z, x−y, z·(x−y)} has a shared factor (x−y) between the 2nd and 3rd polys,
        // so their pairwise resultant vanishes. The split replaces the product by its
        // cofactor z ⇒ {z, x−y} (dedup), which is pairwise coprime.
        let z_poly = MultiPoly::var(z);
        let x_minus_y = MultiPoly::var(x).sub(&MultiPoly::var(y)).unwrap();
        let product = z_poly.mul(&x_minus_y).unwrap();
        let split = coprime_split(&[z_poly.clone(), x_minus_y.clone(), product]);
        assert_eq!(split.len(), 2, "product collapses to a duplicate of z");
        assert!(split.iter().any(|p| p.terms == z_poly.terms));
        assert!(split.iter().any(|p| p.terms == x_minus_y.terms));
    }

    #[test]
    fn coprime_split_drops_constants_and_is_idempotent() {
        let (x, y, _) = three_syms();
        let x_minus_y = MultiPoly::var(x).sub(&MultiPoly::var(y)).unwrap();
        let with_const = vec![x_minus_y.clone(), MultiPoly::constant(Rational::integer(7))];
        let once = coprime_split(&with_const);
        assert_eq!(once.len(), 1, "the constant is dropped");
        let twice = coprime_split(&once);
        assert_eq!(
            twice.len(),
            once.len(),
            "split is idempotent on a coprime set"
        );
    }

    #[test]
    fn simple_mono_style_all_strict_three_var_decides_unsat() {
        // z > 0 ∧ x − y > 0 ∧ xz − yz < 0. Since xz − yz = z·(x − y) > 0, the system
        // is unsat — but the shared factor makes the raw projection resultant vanish.
        // With coprime-split the strict CAD decides it. (The `simple-mono` shape.)
        let (x, y, z) = three_syms();
        let z_pos = MultiAtom {
            cmp: Cmp::Gt,
            poly: MultiPoly::var(z),
        };
        let x_gt_y = MultiAtom {
            cmp: Cmp::Gt,
            poly: MultiPoly::var(x).sub(&MultiPoly::var(y)).unwrap(),
        };
        let xz_lt_yz = MultiAtom {
            cmp: Cmp::Lt,
            poly: MultiPoly::var(x)
                .mul(&MultiPoly::var(z))
                .unwrap()
                .sub(&MultiPoly::var(y).mul(&MultiPoly::var(z)).unwrap())
                .unwrap(),
        };
        let comp: Vec<&MultiAtom> = vec![&z_pos, &x_gt_y, &xz_lt_yz];
        let vars: BTreeSet<SymbolId> = [x, y, z].into_iter().collect();
        match decide_strict_cad_nvar(&comp, &vars) {
            Some(TwoVarVerdict::Unsat) => {}
            other => panic!(
                "expected Unsat, got {:?}",
                matches!(other, Some(TwoVarVerdict::Sat(_)))
            ),
        }
    }
}
