//! Model-based projection (MBP) for linear real and integer arithmetic
//! (`P2.6-T2.6.6`).
//!
//! This module hosts two model-guided existential-elimination primitives:
//! [`mbp_lra`] over the reals (Loos–Weispfenning / virtual substitution) and
//! [`mbp_lia`] over the integers (model-guided Cooper / Omega). Both share the
//! same three-condition soundness contract and the same verify-before-return
//! discipline; see [`mbp_lia`]'s own docs for the integer method, the
//! unit-coefficient *exact* slice, and the divisibility *decline* boundary.
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

use crate::backend::{CheckResult, SolverConfig};
use crate::dpll_lia::check_with_lia_dpll;
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

// ===========================================================================
// Integer model-based projection — `mbp_lia` (model-guided Cooper / Omega).
// ===========================================================================

/// Model-based projection of the **integer** variable `var` out of the `LIA`
/// conjunction `formula`, guided by the satisfying integer model `model`.
///
/// This is the linear-integer-arithmetic mirror of [`mbp_lra`]: the
/// existential-elimination primitive an integer PDR / quantifier-elimination
/// loop needs. Given a conjunction `F` of linear integer literals, a model `M`
/// with `M ⊨ F`, and an integer variable `x`, it returns a finite conjunction
/// `F'` over the remaining (integer) variables such that
///
/// 1. `M ⊨ F'`;
/// 2. `F' ⇒ ∃x∈ℤ. F` (sound integer *under-approximation*);
/// 3. `x` does not occur in `F'`.
///
/// **Method — model-guided Cooper / Omega.** Each literal is normalized to
/// `c·x + r ⋈ 0`. The cases, in order of increasing difficulty:
///
/// 1. **`x`-free literals** (`c = 0`): pass through.
/// 2. **Unit-coefficient equality.** An equality `c·x = e` with `c = ±1` forces
///    `x = ±e` exactly over ℤ; substitute and emit the residue. `|c| ≠ 1`
///    DECLINES (see the boundary below).
/// 3. **Unit-coefficient interval resolvent.** When every `x`-bound has
///    coefficient `±1`, rewrite each to `x ≥ e` / `x ≤ e` with **integer**
///    bounds (a strict integer bound `x > e` becomes `x ≥ e + 1`, `x < e`
///    becomes `x ≤ e − 1`). With unit coefficients the integer interval
///    `[e_lb, e_ub]` is non-empty *iff* `e_lb ≤ e_ub` (the bounds are
///    integer-valued), so the cross-feasibility literal `e_lb ≤ e_ub` is exact
///    and **no divisibility predicate is needed** — this is the clean integer
///    slice. The `M`-tightest lower/upper bounds are selected and the dominated
///    same-direction bounds emitted, exactly as in [`mbp_lra`]. A disequality
///    `x ≠ e` makes the exact projection disjunctive and is DECLINED.
/// 4. **Non-unit coefficients (Cooper divisibility).** A general `a·x ≤ b`
///    with `|a| > 1` needs a divisibility constraint `δ | (…)` plus a
///    model-selected residue to project exactly. Axeyum's integer deciders do
///    not (yet) interpret the `mod`/`divisible` operator, so a divisibility
///    output could never be *verified* (condition 2) — emitting it would be
///    unsound-by-omission. We therefore **DECLINE (`None`)**, a sound
///    under-approximation that defers the hard case. This is the divisibility
///    boundary.
///
/// **Trust — verify before return.** An independent verifier re-establishes
/// all three conditions before `Some(F')` is returned: `M ⊨ F'`
/// by the ground evaluator, `x`-absence structurally, and `F' ⇒ ∃x∈ℤ. F` by an
/// **exact integer decision** — it computes the exact integer projection
/// `∃x∈ℤ. F` (unit-coefficient Omega elimination of `x`) and asks
/// [`check_with_lia_dpll`] whether `F' ∧ ¬p` is unsatisfiable for every
/// projection literal `p`. Any failure (or any `i128` overflow, any non-`LIA`
/// input, any model mismatch, any non-unit coefficient) yields `None`. An
/// over-eager `None` is acceptable; an unsound projection is never returned.
///
/// Returns `None` (declines) when `formula` is not a pure conjunction of `LIA`
/// literals over integers, when `model` does not satisfy `formula`, on
/// `i128`/rational overflow, when a case is outside the unit-coefficient slice,
/// or when the result fails its independent verification.
///
/// # References
///
/// D. C. Cooper, *Theorem Proving in Arithmetic without Multiplication* (1972);
/// W. Pugh, *The Omega Test* (1991).
#[must_use]
pub fn mbp_lia(
    arena: &mut TermArena,
    formula: &[TermId],
    model: &Model,
    var: SymbolId,
) -> Option<Vec<TermId>> {
    // Parse every literal into the integer `expr ⋈ 0` normal form. Any
    // non-`LIA` literal (or overflow) declines.
    let mut literals = Vec::with_capacity(formula.len());
    for &lit in formula {
        literals.push(parse_literal_int(arena, lit, false)?);
    }

    // Build the integer model point and verify M ⊨ formula (precondition).
    let point = model_point_int(model);
    for lit in &literals {
        if !literal_true(lit, &point)? {
            return None;
        }
    }

    // Split into var-free (pass through) and var-bound literals.
    let mut passthrough = Vec::new();
    let mut bounds = Vec::new();
    for lit in &literals {
        let c = lit.expr.coeff(var);
        if c.is_zero() {
            passthrough.push(lit.clone());
        } else {
            // Outside the unit-coefficient slice → decline (the divisibility
            // boundary: a non-unit coefficient needs a Cooper `δ | …` output
            // we cannot verify, see the module docs).
            if !is_unit_coeff(c) {
                return None;
            }
            bounds.push(IntBound::from_literal(lit, var, c)?);
        }
    }

    let projected = if bounds.is_empty() {
        passthrough
    } else if let Some(idx) = bounds.iter().position(|b| b.dir == Dir::Eq) {
        project_by_equality_int(&passthrough, &bounds, idx, var)?
    } else {
        project_by_interval_int(&passthrough, &bounds, &point)?
    };

    // Emit integer terms, then VERIFY BEFORE RETURN. Any failure → decline.
    let mut result = Vec::with_capacity(projected.len());
    for lit in &projected {
        result.push(emit_literal_int(arena, lit)?);
    }
    if !verify_projection_lia(arena, model, var, &result, &literals, &point) {
        return None;
    }
    Some(result)
}

/// Whether `c` is the unit coefficient `+1` or `−1` (the exact-substitution /
/// exact-interval slice). A non-integer coefficient is never a unit.
fn is_unit_coeff(c: Rational) -> bool {
    if !c.is_integer() {
        return false;
    }
    let n = c.numerator();
    n == 1 || n == -1
}

/// A `var`-bearing **integer** literal rewritten as a *non-strict* integer
/// bound `var ≥ e` / `var ≤ e` / `var = e` / `var ≠ e`, with `e` an integer
/// `var`-free linear term. Strictness is folded into `e` (`x > e ⟹ x ≥ e + 1`,
/// `x < e ⟹ x ≤ e − 1`), which is exact over ℤ.
#[derive(Debug, Clone)]
struct IntBound {
    /// The (already strictness-folded) integer bound term, free of `var`.
    e: LinTerm,
    dir: Dir,
    source: Literal,
}

impl IntBound {
    /// Rewrites `c·var + r ⋈ 0` (`c = ±1`) as a non-strict integer bound. The
    /// `±1` precondition is enforced by the caller. `None` on overflow.
    fn from_literal(lit: &Literal, var: SymbolId, c: Rational) -> Option<Self> {
        // r = expr − c·var (drop var's term); e = -r/c.
        let mut r = lit.expr.clone();
        r.coeffs.remove(&var);
        let r = r.normalize();
        let e = r.neg()?.scale(Rational::integer(1).checked_div(c)?)?;
        let c_negative = c.checked_cmp(&Rational::zero())? == core::cmp::Ordering::Less;
        let one = LinTerm::constant(Rational::integer(1));
        let (dir, e) = match lit.rel {
            Rel::Eq => (Dir::Eq, e),
            Rel::Ne => (Dir::Ne, e),
            // c·var + r < 0  ⟺  var < e (c>0) or var > e (c<0). Fold the
            // strict integer bound into a non-strict one: x > e ⟹ x ≥ e+1,
            // x < e ⟹ x ≤ e-1.
            Rel::Lt => {
                if c_negative {
                    (Dir::Lower, e.add(&one)?)
                } else {
                    (Dir::Upper, e.sub(&one)?)
                }
            }
            // c·var + r ≤ 0  ⟺  var ≤ e (c>0) or var ≥ e (c<0); already
            // non-strict integer bounds.
            Rel::Le => {
                if c_negative {
                    (Dir::Lower, e)
                } else {
                    (Dir::Upper, e)
                }
            }
        };
        Some(IntBound {
            e,
            dir,
            source: lit.clone(),
        })
    }
}

/// Integer equality-substitution projection: with `c = ±1` the equality
/// `var = e` (where `e` is already `±(original e)`) determines `var` exactly
/// over ℤ; substitute `var ↦ e` into every other literal. `None` on overflow.
fn project_by_equality_int(
    passthrough: &[Literal],
    bounds: &[IntBound],
    eq_index: usize,
    var: SymbolId,
) -> Option<Vec<Literal>> {
    let e = &bounds[eq_index].e;
    let mut out: Vec<Literal> = passthrough.to_vec();
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

/// Integer interval projection, guided by `M`. With unit coefficients every
/// bound is already a non-strict integer bound; the integer interval
/// `[e_lb, e_ub]` is non-empty iff `e_lb ≤ e_ub`, so the cross-feasibility
/// literal is the exact `e_lb ≤ e_ub` (no divisibility predicate). Mirrors
/// [`project_by_interval`]. `None` on a case that cannot be placed soundly.
fn project_by_interval_int(
    passthrough: &[Literal],
    bounds: &[IntBound],
    point: &BTreeMap<SymbolId, Rational>,
) -> Option<Vec<Literal>> {
    let mut lowers = Vec::new();
    let mut uppers = Vec::new();
    for b in bounds {
        match b.dir {
            Dir::Lower => lowers.push(b),
            Dir::Upper => uppers.push(b),
            // A disequality makes the exact projection disjunctive (the
            // exact-Omega verifier declines it); an `Eq` is routed through
            // `project_by_equality_int`. Decline up front (sound).
            Dir::Ne | Dir::Eq => return None,
        }
    }

    let mut out: Vec<Literal> = passthrough.to_vec();

    let lb = if lowers.is_empty() {
        None
    } else {
        Some(select_extreme_int(&lowers, point, Extreme::Greatest)?)
    };
    let ub = if uppers.is_empty() {
        None
    } else {
        Some(select_extreme_int(&uppers, point, Extreme::Least)?)
    };

    // Domination among lowers: each other lower `e' ≤ e_lb` (M-satisfied: the
    // chosen lb has the greatest M-value).
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
    // Cross feasibility: `e_lb ≤ e_ub` (non-strict — bounds are integer-folded).
    if let (Some(lb), Some(ub)) = (lb, ub) {
        out.push(order_le(&lowers[lb].e, &uppers[ub].e)?);
    }

    Some(out)
}

/// Index of the extreme (greatest / least `M`-value) integer bound in a
/// **non-empty** slice; `None` on overflow.
fn select_extreme_int(
    bounds: &[&IntBound],
    point: &BTreeMap<SymbolId, Rational>,
    extreme: Extreme,
) -> Option<usize> {
    let mut best_index = 0usize;
    let mut best_value = bounds[0].e.eval(point)?;
    for (i, b) in bounds.iter().enumerate().skip(1) {
        let value = b.e.eval(point)?;
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

/// Builds the symbol→rational map from `model`'s **integer** entries.
fn model_point_int(model: &Model) -> BTreeMap<SymbolId, Rational> {
    let mut point = BTreeMap::new();
    for (symbol, value) in model.iter() {
        if let Value::Int(n) = value {
            point.insert(symbol, Rational::integer(n));
        }
    }
    point
}

/// Parses a Boolean term into an integer `LIA` literal `expr ⋈ 0`, pushing one
/// level of `BoolNot` via `negated`. `None` for any non-`LIA` literal or
/// overflow.
fn parse_literal_int(arena: &TermArena, term: TermId, negated: bool) -> Option<Literal> {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolNot,
            args,
        } => parse_literal_int(arena, args[0], !negated),
        TermNode::App { op, args }
            if matches!(op, Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe) =>
        {
            let left = linearize_int(arena, args[0])?;
            let right = linearize_int(arena, args[1])?;
            let effective = if negated { negate_int_op(*op) } else { *op };
            let (expr, rel) = match effective {
                Op::IntLt => (left.sub(&right)?, Rel::Lt),
                Op::IntLe => (left.sub(&right)?, Rel::Le),
                Op::IntGt => (right.sub(&left)?, Rel::Lt),
                Op::IntGe => (right.sub(&left)?, Rel::Le),
                _ => return None,
            };
            Some(Literal { expr, rel })
        }
        TermNode::App { op: Op::Eq, args } if is_int(arena, args[0]) => {
            let left = linearize_int(arena, args[0])?;
            let right = linearize_int(arena, args[1])?;
            let expr = left.sub(&right)?;
            Some(Literal {
                expr,
                rel: if negated { Rel::Ne } else { Rel::Eq },
            })
        }
        _ => None,
    }
}

/// Converts an integer-sorted term into a [`LinTerm`]. `None` for non-linear /
/// non-integer subterms or overflow. Mirrors the integer linearizer accepted by
/// the `LIA` deciders (`IntConst`, `Symbol`, `IntNeg`, `IntAdd`, `IntSub`,
/// `IntMul`-by-const), so every emitted term round-trips through the verifier.
fn linearize_int(arena: &TermArena, term: TermId) -> Option<LinTerm> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(LinTerm::constant(Rational::integer(*value))),
        TermNode::Symbol(symbol) if is_int(arena, term) => Some(LinTerm::var(*symbol)),
        TermNode::App {
            op: Op::IntNeg,
            args,
        } => linearize_int(arena, args[0])?.neg(),
        TermNode::App {
            op: Op::IntAdd,
            args,
        } => {
            let a = linearize_int(arena, args[0])?;
            let b = linearize_int(arena, args[1])?;
            a.add(&b)
        }
        TermNode::App {
            op: Op::IntSub,
            args,
        } => {
            let a = linearize_int(arena, args[0])?;
            let b = linearize_int(arena, args[1])?;
            a.sub(&b)
        }
        TermNode::App {
            op: Op::IntMul,
            args,
        } => {
            let a = linearize_int(arena, args[0])?;
            let b = linearize_int(arena, args[1])?;
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

/// Builds the `TermId` for an integer literal `expr ⋈ 0`. `None` on a builder
/// error (forwarded as a decline rather than panicking).
fn emit_literal_int(arena: &mut TermArena, lit: &Literal) -> Option<TermId> {
    let lhs = emit_linterm_int(arena, &lit.expr)?;
    let zero = arena.int_const(0);
    match lit.rel {
        Rel::Lt => arena.int_lt(lhs, zero).ok(),
        Rel::Le => arena.int_le(lhs, zero).ok(),
        Rel::Eq => arena.eq(lhs, zero).ok(),
        Rel::Ne => {
            let eq = arena.eq(lhs, zero).ok()?;
            arena.not(eq).ok()
        }
    }
}

/// Builds the `TermId` for an integer linear expression `Σ coeff·sym + const`.
/// Every coefficient is integer-valued (`LIA` constraints, unit-coefficient
/// substitution); a non-integer coefficient declines (`None`).
fn emit_linterm_int(arena: &mut TermArena, e: &LinTerm) -> Option<TermId> {
    let mut acc: Option<TermId> = None;
    for (&sym, &coeff) in &e.coeffs {
        if coeff.is_zero() {
            continue;
        }
        if !coeff.is_integer() {
            return None;
        }
        let var = arena.var(sym);
        let term = if coeff == Rational::integer(1) {
            var
        } else {
            let c = arena.int_const(coeff.numerator());
            arena.int_mul(c, var).ok()?
        };
        acc = Some(match acc {
            None => term,
            Some(prev) => arena.int_add(prev, term).ok()?,
        });
    }
    if !e.constant.is_zero() || acc.is_none() {
        if !e.constant.is_integer() {
            return None;
        }
        let c = arena.int_const(e.constant.numerator());
        acc = Some(match acc {
            None => c,
            Some(prev) => arena.int_add(prev, c).ok()?,
        });
    }
    acc
}

fn negate_int_op(op: Op) -> Op {
    match op {
        Op::IntLt => Op::IntGe,
        Op::IntLe => Op::IntGt,
        Op::IntGt => Op::IntLe,
        Op::IntGe => Op::IntLt,
        other => other,
    }
}

fn is_int(arena: &TermArena, term: TermId) -> bool {
    arena.sort_of(term) == Sort::Int
}

// ---------------------------------------------------------------------------
// VERIFY BEFORE RETURN — the integer soundness anchor.
// ---------------------------------------------------------------------------

/// Independently re-establishes the three soundness conditions of [`mbp_lia`]
/// before `Some(F')` is returned. Returns `true` only if **all** hold; any
/// failure (overflow, `unknown`, or a verifier error) returns `false`, so the
/// caller declines.
///
/// 1. **`M ⊨ F'`** — every literal of `result` evaluates to `Bool(true)` under
///    `model` via the ground evaluator.
/// 2. **`var` absent** — `var` occurs in no literal of `result` (structural).
/// 3. **`F' ⇒ ∃var∈ℤ. F`** — the exact integer projection `∃var∈ℤ. F` is
///    computed by unit-coefficient Omega elimination of `var`, and
///    `F' ∧ ¬p` is checked unsatisfiable over ℤ by [`check_with_lia_dpll`] for
///    every projection literal `p` (so `F' ⇒ ⋀ p = ∃var∈ℤ. F`).
fn verify_projection_lia(
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

    // (3) F' ⇒ ∃var∈ℤ. F. Could not build the exact integer projection
    // (overflow / non-unit / unsupported) → cannot certify → decline.
    let Some(projection) = omega_eliminate_int(literals, var, point) else {
        return false;
    };
    let config = SolverConfig::default();
    for plit in &projection {
        if is_trivially_true(plit) {
            continue;
        }
        let Some(not_p) = negate_literal_term_int(arena, plit) else {
            return false;
        };
        let mut asserts: Vec<TermId> = result.to_vec();
        asserts.push(not_p);
        // F' ∧ ¬p must be UNSAT over ℤ. A disequality in ¬p (from an equality
        // projection literal) is handled by the DPLL(T) integer decider.
        match check_with_lia_dpll(arena, &asserts, &config) {
            Ok(CheckResult::Unsat) => {}
            _ => return false,
        }
    }
    true
}

/// Emits the term for `¬p` where `p` is a parsed integer literal `expr ⋈ 0`.
/// The negation is a single literal (`<`↔`≥`, `≤`↔`>`, `=`↔`≠`), kept
/// conjunction/DPLL-friendly. `None` on overflow.
fn negate_literal_term_int(arena: &mut TermArena, lit: &Literal) -> Option<TermId> {
    let negated = match lit.rel {
        // ¬(expr < 0) = expr ≥ 0 = (−expr) ≤ 0.
        Rel::Lt => Literal {
            expr: lit.expr.neg()?,
            rel: Rel::Le,
        },
        // ¬(expr ≤ 0) = expr > 0 = (−expr) < 0.
        Rel::Le => Literal {
            expr: lit.expr.neg()?,
            rel: Rel::Lt,
        },
        Rel::Eq => Literal {
            expr: lit.expr.clone(),
            rel: Rel::Ne,
        },
        Rel::Ne => Literal {
            expr: lit.expr.clone(),
            rel: Rel::Eq,
        },
    };
    emit_literal_int(arena, &negated)
}

/// The exact integer projection `∃var∈ℤ. (⋀ literals)` by unit-coefficient
/// Omega elimination of `var`. Equality (`c = ±1`) substitutes; otherwise every
/// strict integer bound is folded to non-strict (`x > e ⟹ x ≥ e+1`,
/// `x < e ⟹ x ≤ e-1`) and every lower×upper pair yields the exact resolvent
/// `e_lo ≤ e_up`. With unit coefficients this is *exact* over ℤ (no
/// divisibility predicate). Declines (`None`) on a non-unit coefficient, a
/// `var` disequality (disjunctive), or overflow — forcing [`mbp_lia`] to not
/// certify (and thus not return) those sub-cases.
fn omega_eliminate_int(
    literals: &[Literal],
    var: SymbolId,
    point: &BTreeMap<SymbolId, Rational>,
) -> Option<Vec<Literal>> {
    let mut passthrough = Vec::new();
    let mut lowers = Vec::new();
    let mut uppers = Vec::new();
    let mut has_diseq = false;
    let mut equality: Option<IntBound> = None;
    for lit in literals {
        let c = lit.expr.coeff(var);
        if c.is_zero() {
            passthrough.push(lit.clone());
            continue;
        }
        if !is_unit_coeff(c) {
            return None;
        }
        let b = IntBound::from_literal(lit, var, c)?;
        match b.dir {
            Dir::Lower => lowers.push(b),
            Dir::Upper => uppers.push(b),
            Dir::Eq => equality = Some(b),
            Dir::Ne => has_diseq = true,
        }
    }

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

    if has_diseq {
        return None;
    }

    // Pure lower×upper resolvents: `e_lo ≤ e_up` (bounds already integer-folded,
    // so the integer interval is non-empty iff `e_lo ≤ e_up`).
    let mut out = passthrough;
    for lo in &lowers {
        for up in &uppers {
            let resolvent = order_le(&lo.e, &up.e)?;
            if !is_trivially_true(&resolvent) {
                out.push(resolvent);
            }
        }
    }
    let _ = point;
    Some(out)
}
