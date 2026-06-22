//! Model-based projection (MBP) for linear real arithmetic (`P2.6-T2.6.6`).
//!
//! [`mbp_lra`] is the model-guided existential-elimination primitive that
//! Spacer/PDR-style engines need: given a **conjunction** of `LRA` literals
//! `F`, a **model** `M` that satisfies `F`, and a real variable `x` to
//! eliminate, it returns a finite conjunction of `LRA` literals `F'` over the
//! remaining variables such that
//!
//! 1. `M ⊨ F'` (every returned literal is true under `M`);
//! 2. `F' ⇒ ∃x. F` (`F'` is a sound *under-approximation* of the projection —
//!    re-adding `x`, the constraints of `F'` guarantee some value of `x`
//!    satisfies `F`);
//! 3. `x` does not occur in `F'`.
//!
//! **Method.** Model-guided Loos–Weispfenning / virtual substitution. Each
//! literal is normalized to `c·x + r ⋈ 0` (`r` linear over the other
//! variables, `c` a rational, `⋈ ∈ {<, ≤, =, ≠}`). Literals free of `x`
//! (`c = 0`) pass through unchanged. For `c ≠ 0` the literal becomes a bound
//! `x ⋈' e` with `e = -r/c`. Two cases are produced:
//!
//! - **Equality substitution.** If any equality `x = e` is present, substitute
//!   `x ↦ e` into every other literal and emit the (non-trivial) results. The
//!   projection is exactly the substitution.
//! - **Interval resolvent.** Otherwise, using `M`, pick the tightest lower
//!   bound `lb` (greatest `M`-value) and the tightest upper bound `ub` (least
//!   `M`-value); emit a domination literal placing every other same-direction
//!   bound on the correct side of the selected one at `M`, and the cross
//!   feasibility literal `e_lb ⋈ e_ub`. Disequalities `x ≠ e` are admitted by
//!   emitting the side literal that, true under `M`, places `e` strictly
//!   outside the `[lb, ub]` interval (so the interval witnesses `∃x`).
//!
//! **Trust — verify before return.** This module mirrors the crate's
//! self-checking discipline (the Farkas/`LRA` deciders). Before returning
//! `Some(F')`, [`verify_projection`] independently re-establishes all three
//! conditions: it replays every literal of `F'` under `M` through the ground
//! evaluator, structurally checks `x` is absent, and proves `F' ⇒ ∃x. F` by
//! computing the **exact** Fourier–Motzkin projection `∃x. F` and asking
//! [`check_with_lra`] whether `F' ∧ ¬(∃x. F)` is unsatisfiable. Any failure (or
//! any `i128`/rational overflow, any non-`LRA` input, any model mismatch)
//! yields `None`. An over-eager `None` is acceptable; an unsound projection is
//! never returned.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::{Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};

use crate::backend::CheckResult;
use crate::lra::check_with_lra;
use crate::model::Model;

/// A linear real expression `Σ coeff·sym + constant` over named symbols.
///
/// Keyed by [`SymbolId`] (sorted) so construction and emission are
/// deterministic. All arithmetic is exact and overflow-checked (`None` on
/// `i128` overflow → the caller declines).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct LinTerm {
    coeffs: BTreeMap<SymbolId, Rational>,
    constant: Rational,
}

impl LinTerm {
    fn constant(value: Rational) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: value,
        }
    }

    fn var(symbol: SymbolId) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(symbol, Rational::integer(1));
        Self {
            coeffs,
            constant: Rational::zero(),
        }
    }

    fn coeff(&self, symbol: SymbolId) -> Rational {
        self.coeffs
            .get(&symbol)
            .copied()
            .unwrap_or_else(Rational::zero)
    }

    /// Drops zero coefficients so two equal expressions compare equal.
    fn normalize(mut self) -> Self {
        self.coeffs.retain(|_, c| !c.is_zero());
        self
    }

    /// Exact scaling; `None` on `i128` overflow.
    fn scale(&self, factor: Rational) -> Option<Self> {
        if factor.is_zero() {
            return Some(Self::constant(Rational::zero()));
        }
        let mut coeffs = BTreeMap::new();
        for (&s, &c) in &self.coeffs {
            coeffs.insert(s, c.checked_mul(factor)?);
        }
        Some(
            Self {
                coeffs,
                constant: self.constant.checked_mul(factor)?,
            }
            .normalize(),
        )
    }

    /// Exact negation; `None` on overflow.
    fn neg(&self) -> Option<Self> {
        self.scale(Rational::integer(-1))
    }

    /// Exact addition; `None` on overflow.
    fn add(&self, other: &Self) -> Option<Self> {
        let mut coeffs = self.coeffs.clone();
        for (&s, &c) in &other.coeffs {
            let entry = coeffs.entry(s).or_insert_with(Rational::zero);
            *entry = (*entry).checked_add(c)?;
        }
        Some(
            Self {
                coeffs,
                constant: self.constant.checked_add(other.constant)?,
            }
            .normalize(),
        )
    }

    /// Exact subtraction; `None` on overflow.
    fn sub(&self, other: &Self) -> Option<Self> {
        self.add(&other.neg()?)
    }

    /// Substitutes `symbol ↦ replacement` (a `symbol`-free linear term);
    /// `None` on overflow.
    fn substitute(&self, symbol: SymbolId, replacement: &Self) -> Option<Self> {
        let c = self.coeff(symbol);
        if c.is_zero() {
            return Some(self.clone());
        }
        let mut base = self.clone();
        base.coeffs.remove(&symbol);
        let base = base.normalize();
        base.add(&replacement.scale(c)?)
    }

    /// Evaluates the expression under the symbol→[`Rational`] map; `None` on a
    /// missing symbol or overflow.
    fn eval(&self, point: &BTreeMap<SymbolId, Rational>) -> Option<Rational> {
        let mut acc = self.constant;
        for (&s, &c) in &self.coeffs {
            let value = *point.get(&s)?;
            acc = acc.checked_add(c.checked_mul(value)?)?;
        }
        Some(acc)
    }

    fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }
}

/// A relation between a normalized linear expression and `0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Rel {
    /// `expr < 0`.
    Lt,
    /// `expr ≤ 0`.
    Le,
    /// `expr = 0`.
    Eq,
    /// `expr ≠ 0`.
    Ne,
}

/// A parsed `LRA` literal `expr ⋈ 0`.
#[derive(Debug, Clone)]
struct Literal {
    expr: LinTerm,
    rel: Rel,
}

/// Model-based projection of `var` out of the `LRA` conjunction `formula`,
/// guided by the satisfying model `model`.
///
/// Returns `Some(F')` — a conjunction of `LRA` literals over the remaining
/// variables that is a sound under-approximation of `∃var. (⋀ formula)` and is
/// true under `model` — or `None` (declines) when `formula` is not a pure
/// conjunction of `LRA` literals over reals, when `model` does not satisfy
/// `formula`, on `i128`/rational overflow, or when the result fails its
/// independent verification. An unsound projection is **never** returned.
///
/// See the module docs for the method and the verify-before-return discipline.
#[must_use]
pub fn mbp_lra(
    arena: &mut TermArena,
    formula: &[TermId],
    model: &Model,
    var: SymbolId,
) -> Option<Vec<TermId>> {
    // Parse every literal into the `expr ⋈ 0` normal form. Any non-`LRA`
    // literal (or overflow) declines.
    let mut literals = Vec::with_capacity(formula.len());
    for &lit in formula {
        literals.push(parse_literal(arena, lit, false)?);
    }

    // Build the model point (symbol → rational) and verify M ⊨ formula. A model
    // that does not satisfy the conjunction is a precondition violation → decline.
    let point = model_point(model);
    for lit in &literals {
        if !literal_true(lit, &point)? {
            return None;
        }
    }

    // Split into var-free literals (pass through) and var-bound literals.
    let mut passthrough = Vec::new();
    let mut bounds = Vec::new();
    for lit in &literals {
        let c = lit.expr.coeff(var);
        if c.is_zero() {
            passthrough.push(lit.clone());
        } else {
            bounds.push(Bound::from_literal(lit, var, c)?);
        }
    }

    // Produce the projected literal set (still as `LinTerm`/`Rel`).
    let projected = if bounds.is_empty() {
        // `var` is unconstrained: the projection is just the var-free literals.
        passthrough
    } else if let Some(idx) = bounds.iter().position(|b| b.dir == Dir::Eq) {
        // Equality substitution: `var = e`. Substitute into every other literal.
        project_by_equality(&passthrough, &bounds, idx, var)?
    } else {
        // Interval / Loos–Weispfenning resolvent, guided by M.
        project_by_interval(&passthrough, &bounds, &point)?
    };

    // Emit terms, then VERIFY BEFORE RETURN. Any failure → decline.
    let mut result = Vec::with_capacity(projected.len());
    for lit in &projected {
        result.push(emit_literal(arena, lit)?);
    }
    if !verify_projection(arena, model, var, &result, &literals, &point) {
        return None;
    }
    Some(result)
}

/// A `var`-bearing literal rewritten as a bound `var ⋈ e`, with `e` a
/// `var`-free linear term and the bound's direction/strictness recorded.
#[derive(Debug, Clone)]
struct Bound {
    /// The bound term `e = -r/c` (free of `var`).
    e: LinTerm,
    dir: Dir,
    /// `true` for a strict `<`/`>` bound (irrelevant for `Eq`/`Ne`).
    strict: bool,
    /// The original normalized literal it came from (used by substitution).
    source: Literal,
}

/// Which side of `var` the bound constrains.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Dir {
    /// `var > e` or `var ≥ e`.
    Lower,
    /// `var < e` or `var ≤ e`.
    Upper,
    /// `var = e`.
    Eq,
    /// `var ≠ e`.
    Ne,
}

impl Bound {
    /// Rewrites the literal `c·var + r ⋈ 0` (`c ≠ 0`) as `var ⋈' (-r/c)`.
    /// `None` on overflow.
    fn from_literal(lit: &Literal, var: SymbolId, c: Rational) -> Option<Self> {
        // r = expr − c·var (drop var's term).
        let mut r = lit.expr.clone();
        r.coeffs.remove(&var);
        let r = r.normalize();
        // e = -r / c.
        let e = r.neg()?.scale(Rational::new(1, 1).checked_div(c)?)?;
        let c_negative = c.checked_cmp(&Rational::zero())? == core::cmp::Ordering::Less;
        let (dir, strict) = match lit.rel {
            Rel::Eq => (Dir::Eq, false),
            Rel::Ne => (Dir::Ne, false),
            // c·var + r < 0  ⟺  var < e (c>0) or var > e (c<0).
            Rel::Lt => {
                if c_negative {
                    (Dir::Lower, true)
                } else {
                    (Dir::Upper, true)
                }
            }
            Rel::Le => {
                if c_negative {
                    (Dir::Lower, false)
                } else {
                    (Dir::Upper, false)
                }
            }
        };
        Some(Bound {
            e,
            dir,
            strict,
            source: lit.clone(),
        })
    }
}

/// Equality-substitution projection: substitute `var ↦ e` (the equality's `e`)
/// into every passthrough literal and every other bound's source literal, drop
/// trivially-true results. `None` on overflow.
fn project_by_equality(
    passthrough: &[Literal],
    bounds: &[Bound],
    eq_index: usize,
    var: SymbolId,
) -> Option<Vec<Literal>> {
    let e = &bounds[eq_index].e;
    let mut out = Vec::new();
    // The equality itself becomes `e − e = 0` (vacuous); the *other* literals
    // carry the projected constraints. Passthroughs are already var-free.
    for lit in passthrough {
        out.push(lit.clone());
    }
    for (i, b) in bounds.iter().enumerate() {
        if i == eq_index {
            continue;
        }
        let substituted = substitute_into(&b.source, var, e)?;
        if !is_trivially_true(&substituted) {
            out.push(substituted);
        }
    }
    Some(out)
}

/// Substitutes `var ↦ replacement` into a literal, keeping its relation.
fn substitute_into(lit: &Literal, var: SymbolId, replacement: &LinTerm) -> Option<Literal> {
    Some(Literal {
        expr: lit.expr.substitute(var, replacement)?,
        rel: lit.rel,
    })
}

/// Interval projection (Loos–Weispfenning resolvent), guided by `M`. Selects
/// the `M`-tightest lower and upper bounds and emits the domination + cross
/// feasibility + disequality-side literals that `M` satisfies. `None` if any
/// case cannot be placed soundly (decline).
fn project_by_interval(
    passthrough: &[Literal],
    bounds: &[Bound],
    point: &BTreeMap<SymbolId, Rational>,
) -> Option<Vec<Literal>> {
    let mut lowers = Vec::new();
    let mut uppers = Vec::new();
    for b in bounds {
        match b.dir {
            Dir::Lower => lowers.push(b),
            Dir::Upper => uppers.push(b),
            // A `var` disequality makes the exact projection a disjunction (the
            // exact-FM verifier declines it, so a side literal here would only be
            // rejected); an `Eq` is routed through `project_by_equality` and
            // never reaches this case. Decline up front (sound — an over-eager
            // `None` is acceptable).
            Dir::Ne | Dir::Eq => return None,
        }
    }

    let mut out: Vec<Literal> = passthrough.to_vec();

    // Pick the M-tightest lower bound (greatest M-value) and M-tightest upper
    // bound (least M-value), deterministically (first index breaks ties). Empty
    // direction → no selection on that side.
    let lb = if lowers.is_empty() {
        None
    } else {
        Some(select_extreme(&lowers, point, Extreme::Greatest)?)
    };
    let ub = if uppers.is_empty() {
        None
    } else {
        Some(select_extreme(&uppers, point, Extreme::Least)?)
    };

    // Domination among lowers: each other lower `e' ≤ e_lb`. M satisfies it
    // (the chosen lb is the greatest at M); the non-strict (weaker) ordering is
    // always sound and M-satisfied.
    if let Some(lb) = lb {
        let e_lb = &lowers[lb].e;
        for (i, other) in lowers.iter().enumerate() {
            if i == lb {
                continue;
            }
            out.push(order_le(&other.e, e_lb)?);
        }
    }
    // Domination among uppers: each other upper `e_ub ≤ e'`.
    if let Some(ub) = ub {
        let e_ub = &uppers[ub].e;
        for (i, other) in uppers.iter().enumerate() {
            if i == ub {
                continue;
            }
            out.push(order_le(e_ub, &other.e)?);
        }
    }
    // Cross feasibility between the selected lower and upper. Strict if either
    // selected bound is strict.
    if let (Some(lb), Some(ub)) = (lb, ub) {
        let lower_e = &lowers[lb].e;
        let upper_e = &uppers[ub].e;
        let strict = lowers[lb].strict || uppers[ub].strict;
        out.push(order_cmp(lower_e, upper_e, strict)?);
    }

    Some(out)
}

/// `Extreme::Greatest` selects the bound with the largest `M`-value;
/// `Extreme::Least` the smallest. Deterministic first-index tie-break.
#[derive(Clone, Copy)]
enum Extreme {
    Greatest,
    Least,
}

/// Index of the extreme (greatest / least `M`-value) bound in a **non-empty**
/// slice; `None` on overflow during evaluation.
fn select_extreme(
    bounds: &[&Bound],
    point: &BTreeMap<SymbolId, Rational>,
    extreme: Extreme,
) -> Option<usize> {
    let mut best_index = 0usize;
    let mut best_value = bound_eval(&bounds[0].e, point)?;
    for (i, b) in bounds.iter().enumerate().skip(1) {
        let value = bound_eval(&b.e, point)?;
        let order = value.checked_cmp(&best_value)?;
        let take = match extreme {
            Extreme::Greatest => order == core::cmp::Ordering::Greater,
            Extreme::Least => order == core::cmp::Ordering::Less,
        };
        if take {
            best_index = i;
            best_value = value;
        }
    }
    Some(best_index)
}

/// Evaluates a bound term under `M`; `None` on overflow / missing symbol.
fn bound_eval(e: &LinTerm, point: &BTreeMap<SymbolId, Rational>) -> Option<Rational> {
    e.eval(point)
}

/// The literal `a ≤ b`, i.e. `a − b ≤ 0`. `None` on overflow.
fn order_le(a: &LinTerm, b: &LinTerm) -> Option<Literal> {
    Some(Literal {
        expr: a.sub(b)?,
        rel: Rel::Le,
    })
}

/// The literal `a < b` (strict) or `a ≤ b`, i.e. `a − b ⋈ 0`. `None` on
/// overflow.
fn order_cmp(a: &LinTerm, b: &LinTerm, strict: bool) -> Option<Literal> {
    Some(Literal {
        expr: a.sub(b)?,
        rel: if strict { Rel::Lt } else { Rel::Le },
    })
}

/// Whether a parsed literal `expr ⋈ 0` is constant-true (so it can be dropped).
fn is_trivially_true(lit: &Literal) -> bool {
    if !lit.expr.is_constant() {
        return false;
    }
    let zero = Rational::zero();
    let Some(order) = lit.expr.constant.checked_cmp(&zero) else {
        return false;
    };
    match lit.rel {
        Rel::Lt => order == core::cmp::Ordering::Less,
        Rel::Le => order != core::cmp::Ordering::Greater,
        Rel::Eq => order == core::cmp::Ordering::Equal,
        Rel::Ne => order != core::cmp::Ordering::Equal,
    }
}

/// Builds the symbol→rational map from `model`'s real entries. A symbol missing
/// where needed is caught lazily ([`LinTerm::eval`] returns `None`).
fn model_point(model: &Model) -> BTreeMap<SymbolId, Rational> {
    let mut point = BTreeMap::new();
    for (symbol, value) in model.iter() {
        if let Value::Real(r) = value {
            point.insert(symbol, r);
        }
    }
    point
}

/// Evaluates a parsed literal `expr ⋈ 0` under `M`. `None` on overflow / missing
/// symbol (treated as a decline upstream).
fn literal_true(lit: &Literal, point: &BTreeMap<SymbolId, Rational>) -> Option<bool> {
    let value = lit.expr.eval(point)?;
    let order = value.checked_cmp(&Rational::zero())?;
    Some(match lit.rel {
        Rel::Lt => order == core::cmp::Ordering::Less,
        Rel::Le => order != core::cmp::Ordering::Greater,
        Rel::Eq => order == core::cmp::Ordering::Equal,
        Rel::Ne => order != core::cmp::Ordering::Equal,
    })
}

/// Parses a Boolean term into an `LRA` literal `expr ⋈ 0`, pushing one level of
/// `BoolNot` via `negated`. `None` for any non-`LRA` literal or overflow.
fn parse_literal(arena: &TermArena, term: TermId, negated: bool) -> Option<Literal> {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolNot,
            args,
        } => parse_literal(arena, args[0], !negated),
        TermNode::App { op, args }
            if matches!(op, Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe) =>
        {
            let left = linearize(arena, args[0])?;
            let right = linearize(arena, args[1])?;
            // Resolve to `expr ⋈ 0` after negation.
            let effective = if negated { negate_op(*op) } else { *op };
            let (expr, rel) = match effective {
                Op::RealLt => (left.sub(&right)?, Rel::Lt),
                Op::RealLe => (left.sub(&right)?, Rel::Le),
                Op::RealGt => (right.sub(&left)?, Rel::Lt),
                Op::RealGe => (right.sub(&left)?, Rel::Le),
                _ => return None,
            };
            Some(Literal { expr, rel })
        }
        TermNode::App { op: Op::Eq, args } if is_real(arena, args[0]) => {
            let left = linearize(arena, args[0])?;
            let right = linearize(arena, args[1])?;
            let expr = left.sub(&right)?;
            Some(Literal {
                expr,
                rel: if negated { Rel::Ne } else { Rel::Eq },
            })
        }
        _ => None,
    }
}

/// Converts a real-sorted term into a [`LinTerm`]. `None` for non-linear /
/// non-real subterms or overflow.
fn linearize(arena: &TermArena, term: TermId) -> Option<LinTerm> {
    match arena.node(term) {
        TermNode::RealConst(value) => Some(LinTerm::constant(*value)),
        TermNode::Symbol(symbol) if is_real(arena, term) => Some(LinTerm::var(*symbol)),
        TermNode::App {
            op: Op::RealNeg,
            args,
        } => linearize(arena, args[0])?.neg(),
        TermNode::App {
            op: Op::RealAdd,
            args,
        } => {
            let a = linearize(arena, args[0])?;
            let b = linearize(arena, args[1])?;
            a.add(&b)
        }
        TermNode::App {
            op: Op::RealSub,
            args,
        } => {
            let a = linearize(arena, args[0])?;
            let b = linearize(arena, args[1])?;
            a.sub(&b)
        }
        TermNode::App {
            op: Op::RealMul,
            args,
        } => {
            let a = linearize(arena, args[0])?;
            let b = linearize(arena, args[1])?;
            if a.is_constant() {
                b.scale(a.constant)
            } else if b.is_constant() {
                a.scale(b.constant)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Builds the `TermId` for a parsed literal `expr ⋈ 0`. `None` on a builder
/// error (which cannot happen for a real expression, but is forwarded as a
/// decline rather than panicking).
fn emit_literal(arena: &mut TermArena, lit: &Literal) -> Option<TermId> {
    let lhs = emit_linterm(arena, &lit.expr)?;
    let zero = arena.real_const(Rational::zero());
    match lit.rel {
        Rel::Lt => arena.real_lt(lhs, zero).ok(),
        Rel::Le => arena.real_le(lhs, zero).ok(),
        Rel::Eq => arena.eq(lhs, zero).ok(),
        Rel::Ne => {
            let eq = arena.eq(lhs, zero).ok()?;
            arena.not(eq).ok()
        }
    }
}

/// Builds the `TermId` for a linear expression `Σ coeff·sym + constant`.
fn emit_linterm(arena: &mut TermArena, e: &LinTerm) -> Option<TermId> {
    let mut acc: Option<TermId> = None;
    for (&sym, &coeff) in &e.coeffs {
        if coeff.is_zero() {
            continue;
        }
        let var = arena.var(sym);
        let term = if coeff == Rational::integer(1) {
            var
        } else {
            let c = arena.real_const(coeff);
            arena.real_mul(c, var).ok()?
        };
        acc = Some(match acc {
            None => term,
            Some(prev) => arena.real_add(prev, term).ok()?,
        });
    }
    if !e.constant.is_zero() || acc.is_none() {
        let c = arena.real_const(e.constant);
        acc = Some(match acc {
            None => c,
            Some(prev) => arena.real_add(prev, c).ok()?,
        });
    }
    acc
}

fn negate_op(op: Op) -> Op {
    match op {
        Op::RealLt => Op::RealGe,
        Op::RealLe => Op::RealGt,
        Op::RealGt => Op::RealLe,
        Op::RealGe => Op::RealLt,
        other => other,
    }
}

fn is_real(arena: &TermArena, term: TermId) -> bool {
    arena.sort_of(term) == Sort::Real
}

// ---------------------------------------------------------------------------
// VERIFY BEFORE RETURN — the soundness anchor.
// ---------------------------------------------------------------------------

/// Independently re-establishes the three soundness conditions of `mbp_lra`
/// before `Some(F')` is returned. Returns `true` only if **all** hold; any
/// failure (including any overflow or `unknown` from the implication check)
/// returns `false`, so the caller declines.
///
/// 1. **`M ⊨ F'`** — every literal of `result` evaluates to `Bool(true)` under
///    the model via the ground evaluator.
/// 2. **`var` absent** — `var` occurs in no literal of `result` (structural).
/// 3. **`F' ⇒ ∃var. F`** — the *exact* projection `∃var. (⋀ formula)` is
///    computed by Fourier–Motzkin elimination of `var` (built from the parsed
///    `literals`), and `F' ∧ ¬(∃var. F)` is checked unsatisfiable by
///    [`check_with_lra`]. `¬(∃var. F)` is the negation of a conjunction (a
///    disjunction); the entailment is established by checking, for each
///    projection literal `p`, that `F' ∧ ¬p` is unsat (so `F' ⇒ p` for every
///    `p`, hence `F' ⇒ ⋀ p = ∃var. F`).
fn verify_projection(
    arena: &mut TermArena,
    model: &Model,
    var: SymbolId,
    result: &[TermId],
    literals: &[Literal],
    point: &BTreeMap<SymbolId, Rational>,
) -> bool {
    // (1) M ⊨ F'.
    let assignment = model.to_assignment();
    for &lit in result {
        match eval(arena, lit, &assignment) {
            Ok(Value::Bool(true)) => {}
            _ => return false,
        }
    }

    // (2) var absent (structural).
    let mut seen = BTreeSet::new();
    for &lit in result {
        if term_mentions(arena, lit, var, &mut seen) {
            return false;
        }
    }

    // (3) F' ⇒ ∃var. F. Compute the exact projection literals, then check that
    // F' entails each one (F' ∧ ¬p UNSAT). An empty projection means ∃var.F is
    // trivially true; then F' (true under M, var-free) trivially entails it.
    // Could not build the exact projection (overflow / unsupported) → cannot
    // certify the implication → decline.
    let Some(projection) = fourier_motzkin_eliminate(literals, var, point) else {
        return false;
    };
    for plit in &projection {
        // Skip trivially-true projection literals (entailed by anything).
        if is_trivially_true(plit) {
            continue;
        }
        let Some(not_p) = negate_literal_term(arena, plit) else {
            return false;
        };
        // F' ∧ ¬p must be UNSAT.
        let mut asserts: Vec<TermId> = result.to_vec();
        asserts.push(not_p);
        match check_with_lra(arena, &asserts) {
            Ok(CheckResult::Unsat) => {}
            // Sat, Unknown, or any error: cannot certify F' ⇒ p → decline.
            _ => return false,
        }
    }
    true
}

/// Whether `term` structurally mentions `var`. Memoizes visited terms.
fn term_mentions(
    arena: &TermArena,
    term: TermId,
    var: SymbolId,
    seen: &mut BTreeSet<TermId>,
) -> bool {
    if !seen.insert(term) {
        return false;
    }
    match arena.node(term) {
        TermNode::Symbol(s) => *s == var,
        TermNode::App { args, .. } => {
            let args = args.clone();
            args.iter().any(|&a| term_mentions(arena, a, var, seen))
        }
        _ => false,
    }
}

/// Emits the term for `¬p` where `p` is a parsed literal `expr ⋈ 0`. The
/// negation is a single `LRA` literal (`<`↔`≥`, `≤`↔`>`, `=`↔`≠`), kept
/// conjunction-friendly so [`check_with_lra`] can decide `F' ∧ ¬p`.
fn negate_literal_term(arena: &mut TermArena, lit: &Literal) -> Option<TermId> {
    let negated = Literal {
        expr: lit.expr.clone(),
        rel: match lit.rel {
            // ¬(expr < 0) = expr ≥ 0 = (−expr) ≤ 0.
            Rel::Lt => Rel::Le,
            // ¬(expr ≤ 0) = expr > 0 = (−expr) < 0.
            Rel::Le => Rel::Lt,
            Rel::Eq => Rel::Ne,
            Rel::Ne => Rel::Eq,
        },
    };
    // For Lt/Le the relation flips *and* the expression negates (≥0 / >0 → ≤0 / <0).
    let negated = match lit.rel {
        Rel::Lt | Rel::Le => Literal {
            expr: negated.expr.neg()?,
            rel: negated.rel,
        },
        Rel::Eq | Rel::Ne => negated,
    };
    emit_literal(arena, &negated)
}

/// The exact projection `∃var. (⋀ literals)` by Fourier–Motzkin elimination of
/// `var`: pass var-free literals through; substitute through an equality if one
/// is present; otherwise pair every lower bound with every upper bound (and
/// keep var-free residue). Disequalities make exact FM a disjunction, so when a
/// disequality on `var` is present this returns the **sound over-approximation**
/// that drops it — which still yields a *valid* implication target only if it is
/// genuinely implied. To stay sound we instead DECLINE (return `None`) when a
/// `var` disequality is present, forcing `mbp_lra` to not certify (and thus not
/// return) in that sub-case via verification. `None` on overflow.
fn fourier_motzkin_eliminate(
    literals: &[Literal],
    var: SymbolId,
    point: &BTreeMap<SymbolId, Rational>,
) -> Option<Vec<Literal>> {
    let mut passthrough = Vec::new();
    let mut lowers = Vec::new();
    let mut uppers = Vec::new();
    let mut has_diseq = false;
    let mut equality: Option<Bound> = None;
    for lit in literals {
        let c = lit.expr.coeff(var);
        if c.is_zero() {
            passthrough.push(lit.clone());
            continue;
        }
        let b = Bound::from_literal(lit, var, c)?;
        match b.dir {
            Dir::Lower => lowers.push(b),
            Dir::Upper => uppers.push(b),
            Dir::Eq => equality = Some(b),
            Dir::Ne => has_diseq = true,
        }
    }

    // Equality: substitute and we are done (exact). The first equality is the
    // pivot; substituting `var ↦ e` into it yields a vacuous `0 = 0`, dropped as
    // trivially true. Every other var-bearing literal is substituted through.
    if let Some(eq) = &equality {
        let mut out = passthrough;
        for lit in literals {
            let c = lit.expr.coeff(var);
            if c.is_zero() {
                continue;
            }
            let substituted = substitute_into(lit, var, &eq.e)?;
            if !is_trivially_true(&substituted) {
                out.push(substituted);
            }
        }
        return Some(out);
    }

    // A disequality on var makes the exact projection a disjunction: decline the
    // exact-FM certificate (verification then fails → mbp_lra declines, sound).
    if has_diseq {
        return None;
    }

    // Pure lower×upper resolvents.
    let mut out = passthrough;
    for lo in &lowers {
        for up in &uppers {
            // lower: var > e_lo (or ≥); upper: var < e_up (or ≤). Resolvent:
            // e_lo < e_up (or ≤), strict iff either is strict.
            let strict = lo.strict || up.strict;
            let resolvent = order_cmp(&lo.e, &up.e, strict)?;
            if !is_trivially_true(&resolvent) {
                out.push(resolvent);
            }
        }
    }
    let _ = point;
    Some(out)
}
