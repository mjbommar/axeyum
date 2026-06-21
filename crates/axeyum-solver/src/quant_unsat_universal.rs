//! Unsatisfiable-universal detection (an always-false linear universal).
//!
//! The *vacuous*-universal pass ([`crate::quant_vacuous_universal`]) owns the
//! case where the bound variable's net coefficient cancels to **zero** (`x`
//! does not affect the body's truth). This pass owns the complementary,
//! non-vacuous case: a top-level `∀x. body` whose body is a **single linear
//! arithmetic atom** in which `x` *genuinely* appears (net coefficient `c ≠ 0`)
//! and the rest of the atom is `x`-free, i.e. after linear normalization
//!
//! ```text
//! c·x ⋈ t      with c ≠ 0, t free of x, ⋈ ∈ {<, ≤, >, ≥, =}.
//! ```
//!
//! Such a universal is **unsatisfiable** — and asserting it makes the whole
//! query `unsat`. A linear function `c·x` of an *unbounded* `x` (both `Int` and
//! `Real` are unbounded below and above) ranges over arbitrarily large positive
//! and negative values, so:
//!
//! - For a one-sided inequality (`<`/`≤`/`>`/`≥`) the function `c·x` exceeds
//!   (or falls below) the fixed bound `t` for some `x`, falsifying the atom; no
//!   single bound holds for *every* `x`.
//! - For an equality `c·x = t` with `c ≠ 0` there is at most one `x` that
//!   satisfies it (`x = t/c`), so it cannot hold for *all* `x`.
//!
//! In every case `∀x. (c·x ⋈ t)` is false in every model, hence the assertion —
//! and the conjoined query — is `unsat`. Concrete instances this decides that
//! the engine previously left `unknown`:
//!
//! ```text
//! ∀x:Int.  x > 0           (false at x = 0)
//! ∀x:Int.  2·x = 5         (no integer, indeed no real, solution for all x)
//! ∀x:Real. x ≤ y           (y free; false at x = y + 1)
//! ∃y:Int. ∀x:Int. x ≤ y    (skolemize y → c; residual ∀x. x ≤ c is this shape)
//! ```
//!
//! ## Soundness — what is deliberately **excluded**
//!
//! The verdict is `unsat`, so every exclusion below is soundness-critical; any
//! doubt declines (returns `false`/passes the assertion through unchanged) and
//! leaves the universal to the other passes.
//!
//! - **`≠` / `distinct`.** `∀x:Int. 2·x ≠ 5` is *true* (no integer halves an odd
//!   number), so it is `sat`, **not** `unsat`. A disequality is built as
//!   `not(eq)`, whose top operator is [`Op::BoolNot`], not a bare atom — so the
//!   single-atom shape never matches it, and it is excluded structurally.
//! - **`c = 0`.** When the net coefficient cancels, `x` is vacuous and the
//!   universal is equivalent to a `x`-free atom (decided by the *vacuous* pass).
//!   This pass requires `c ≠ 0` and otherwise declines, so the two compose with
//!   no overlap.
//! - **Non-atomic body.** A conjunction/disjunction/implication/`ite` (e.g. the
//!   *valid* `∀x. (x > 0 ∨ x ≤ 0)`, or a guarded `∀x. (lo ≤ x ≤ hi) ⇒ …`) is
//!   left for the valid-/guarded-universal passes.
//! - **Non-linear / non-`x`-free.** If `x` appears inside a UF, array, `div`,
//!   `mod`, `abs`, a product of two non-constants, or `t` is not `x`-free, the
//!   affine normalization fails and the pass declines.
//! - **Nested quantifiers** under the `∀x` — declined.
//!
//! The pass is **strictly additive**: it can only turn an otherwise-`unknown`
//! verdict into `unsat` for the proven-always-false shape, and a universal that
//! fails *any* check is passed through unchanged.

use std::collections::BTreeMap;

use axeyum_ir::{Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode};

/// Scans the top-level assertions for a universal of the always-false linear
/// shape `∀x. (c·x ⋈ t)` (with `c ≠ 0`, `t` free of `x`, and `⋈` a one-sided
/// comparison or equality — never `≠`). Returns `true` if any assertion
/// matches, meaning the whole query is **unsatisfiable**.
///
/// A `true` verdict is sound: such a universal is false in every model, so its
/// conjunction with the remaining assertions is `unsat`. A `false` verdict
/// means *no* assertion was proven to have this shape — the query is left for
/// the other passes (it is *not* a claim of satisfiability).
pub fn detect_unsatisfiable_universal(arena: &TermArena, assertions: &[TermId]) -> bool {
    assertions
        .iter()
        .any(|&assertion| is_unsatisfiable_universal(arena, assertion))
}

/// Whether a single top-level assertion is an always-false linear universal
/// `∀x. (c·x ⋈ t)` (see [`detect_unsatisfiable_universal`]).
fn is_unsatisfiable_universal(arena: &TermArena, assertion: TermId) -> bool {
    // Must be a top-level `∀x. body`.
    let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(assertion)
    else {
        return false;
    };
    let var = *var;
    let body = args[0];

    // Only `Int`/`Real` bound variables: the unboundedness argument relies on
    // an unbounded domain, and the affine analysis is defined for them. (A
    // finite `Bool`/`BitVec` universal is decided by finite expansion.)
    if !matches!(arena.symbol(var).1, Sort::Int | Sort::Real) {
        return false;
    }

    // A nested quantifier under the `∀x` is out of scope — decline.
    if contains_quantifier(arena, body) {
        return false;
    }

    // The body must be a *single* arithmetic atom whose top operator is a
    // one-sided comparison or an equality over an arithmetic sort. A `not`,
    // `and`, `or`, `implies`, `ite`, … is *not* this shape (which excludes the
    // `≠`-as-`not(eq)` case structurally).
    let TermNode::App { op, args } = arena.node(body) else {
        return false;
    };
    if !matches!(
        op,
        Op::Eq
            | Op::IntLt
            | Op::IntLe
            | Op::IntGt
            | Op::IntGe
            | Op::RealLt
            | Op::RealLe
            | Op::RealGt
            | Op::RealGe
    ) {
        return false;
    }
    if args.len() != 2 {
        return false;
    }
    let (lhs, rhs) = (args[0], args[1]);

    // Restrict to arithmetic operands; an `Eq` over Bool/BV/array/etc. is not a
    // linear arithmetic atom and the unboundedness argument does not apply.
    if !matches!(arena.sort_of(lhs), Sort::Int | Sort::Real) {
        return false;
    }

    // Both sides must fully linearize. `affine` returns `None` whenever `x`
    // could hide unaccounted (a non-constant product, `div`/`mod`/`abs`, a UF
    // argument, an array index, …), which is exactly the non-linear /
    // non-`x`-free exclusion: in that case we decline.
    let Some(left) = affine(arena, lhs, var) else {
        return false;
    };
    let Some(right) = affine(arena, rhs, var) else {
        return false;
    };

    // Net `x` coefficient of `lhs - rhs`. Require `c ≠ 0` — `x` genuinely
    // appears (the `c = 0` vacuous case belongs to the sibling pass). Because
    // both sides fully linearized, the residual `lhs - rhs` is exactly
    // `c·x + (x-free terms)`, so `c ≠ 0` already guarantees `t` is `x`-free.
    // An `i128` overflow subtracting the two coefficients ⇒ not provably this
    // shape (decline; a `false` verdict is never an unsoundness, only a missed
    // `unsat`).
    let Some(c) = left.coeff(var).checked_sub(right.coeff(var)) else {
        return false;
    };
    !c.is_zero()
}

/// An affine expression `sum coeff_i * symbol_i + constant` over the arena's
/// symbols, used solely to read off the bound variable's net coefficient.
#[derive(Clone)]
struct Affine {
    coeffs: BTreeMap<SymbolId, Rational>,
    constant: Rational,
}

impl Affine {
    fn constant(value: Rational) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            constant: value,
        }
    }

    fn symbol(sym: SymbolId) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(sym, Rational::integer(1));
        Self {
            coeffs,
            constant: Rational::zero(),
        }
    }

    fn coeff(&self, sym: SymbolId) -> Rational {
        self.coeffs
            .get(&sym)
            .copied()
            .unwrap_or_else(Rational::zero)
    }

    /// Negate, declining (`None`) on any `i128` overflow during normalization.
    fn neg(&self) -> Option<Self> {
        let mut coeffs = BTreeMap::new();
        for (&s, &c) in &self.coeffs {
            coeffs.insert(s, c.checked_neg()?);
        }
        Some(Self {
            coeffs,
            constant: self.constant.checked_neg()?,
        })
    }

    /// Add, declining (`None`) on any `i128` overflow.
    fn add(&self, other: &Self) -> Option<Self> {
        let mut coeffs = self.coeffs.clone();
        for (&s, &c) in &other.coeffs {
            let entry = coeffs.entry(s).or_insert_with(Rational::zero);
            *entry = entry.checked_add(c)?;
        }
        Some(Self {
            coeffs,
            constant: self.constant.checked_add(other.constant)?,
        })
    }

    fn sub(&self, other: &Self) -> Option<Self> {
        self.add(&other.neg()?)
    }

    /// Scale by `factor`, declining (`None`) on any `i128` overflow.
    fn scale(&self, factor: Rational) -> Option<Self> {
        let mut coeffs = BTreeMap::new();
        for (&s, &c) in &self.coeffs {
            coeffs.insert(s, c.checked_mul(factor)?);
        }
        Some(Self {
            coeffs,
            constant: self.constant.checked_mul(factor)?,
        })
    }
}

/// Linearizes `term` (`Int`/`Real`-sorted) into an [`Affine`] form, or `None`
/// if it is not a purely affine expression in which the bound variable `var` is
/// fully accounted for.
///
/// Handled: integer/real constants, the bound variable and other symbols
/// (opaque leaves with coefficient `1`), `+`, `-` (binary and unary negation),
/// `*` **only** when one operand is a constant (linear scaling), and the
/// transparent `Int → Real` embedding ([`Op::IntToReal`]).
///
/// Returns `None` for any construct under which `var` could hide unaccounted —
/// a product of two non-constants, `div`/`mod`/`abs`, a uninterpreted-function
/// application, a `select`, … — conservatively forcing the caller to decline
/// (sound: the always-false argument applies only to the genuine linear shape).
fn affine(arena: &TermArena, term: TermId, var: SymbolId) -> Option<Affine> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(Affine::constant(Rational::integer(*value))),
        TermNode::RealConst(value) => Some(Affine::constant(*value)),
        TermNode::Symbol(sym) => Some(Affine::symbol(*sym)),
        TermNode::App { op, args } => match op {
            Op::IntAdd | Op::RealAdd => {
                let a = affine(arena, args[0], var)?;
                let b = affine(arena, args[1], var)?;
                a.add(&b)
            }
            Op::IntSub | Op::RealSub => {
                let a = affine(arena, args[0], var)?;
                let b = affine(arena, args[1], var)?;
                a.sub(&b)
            }
            Op::IntNeg | Op::RealNeg => {
                let a = affine(arena, args[0], var)?;
                a.neg()
            }
            Op::IntMul | Op::RealMul => {
                let a = affine(arena, args[0], var)?;
                let b = affine(arena, args[1], var)?;
                // Linear only when one factor is a (var-free) constant; a
                // product of two non-constants is non-linear, so `var` could
                // appear in a way the affine form cannot represent — bail.
                if a.coeffs.is_empty() {
                    b.scale(a.constant)
                } else if b.coeffs.is_empty() {
                    a.scale(b.constant)
                } else {
                    None
                }
            }
            // `to_real` is the identity numeric embedding; the affine form
            // carries over unchanged.
            Op::IntToReal => affine(arena, args[0], var),
            // Anything else (`div`/`mod`/`abs`/`/`, UF apply, select, bv ops, …)
            // is opaque. If `var` hides inside, we must not claim a linear form —
            // bail. A var-free opaque term is a coefficient-free leaf.
            _ => {
                if occurs(arena, term, var) {
                    None
                } else {
                    Some(Affine::constant(Rational::zero()))
                }
            }
        },
        // Wide BV / Bool constants etc. cannot appear in an Int/Real affine
        // position for a well-sorted body; treat as var-free opaque.
        _ => {
            if occurs(arena, term, var) {
                None
            } else {
                Some(Affine::constant(Rational::zero()))
            }
        }
    }
}

/// Whether `var` occurs syntactically anywhere in `term`.
fn occurs(arena: &TermArena, term: TermId, var: SymbolId) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(s) if *s == var => return true,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

/// Whether `term` contains any quantifier operator.
fn contains_quantifier(arena: &TermArena, term: TermId) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}
