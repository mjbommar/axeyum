//! Vacuous-universal elimination (bound variable that does not affect the body).
//!
//! The finite-domain quantifier path ([`crate::check_with_quantifiers`]) is
//! complete for `Bool`/`BitVec` bound variables; the infinite-domain fallback
//! ([`crate::prove_unsat_by_instantiation`] / MBQI) can only ever conclude
//! `unsat`/`unknown`; and the *valid*-universal pass
//! ([`crate::quant_valid_universal`]) decides only universals that are true in
//! *every* model. None of them handles a universal whose bound variable simply
//! **does not affect the body's truth**, e.g.
//!
//! ```text
//! ∀x:Int. x + c >= x
//! ```
//!
//! The atom `x + c >= x` is `c >= 0` after linear normalization — its truth does
//! not depend on `x` (the net coefficient of `x` is `0`). So the universal is
//! logically equivalent to the quantifier-free `c >= 0`, which is *not* valid (it
//! fails when `c < 0`), so the valid-universal pass leaves it `unknown`. This is
//! the residual that `∃y.∀x. x + y >= x` reduces to once the top-level `∃y` is
//! skolemized to a fresh constant `c` — the witness `y = 0` makes it `sat`, but
//! the engine returned `unknown`.
//!
//! ## The rewrite
//!
//! For a top-level `∀x. body` with a quantifier-free body, this pass proves that
//! `x` is **vacuous** — its value cannot change the truth of `body` — and then
//! replaces the universal with `body[x := 0]` (an arbitrary fixed value of `x`'s
//! sort), a quantifier-free formula the ordinary dispatch decides.
//!
//! *Soundness.* The substitution `body[x := 0]` is equivalent to `∀x. body`
//! **only** once vacuousness is proven, so the proof is the whole game:
//!
//! - Every Boolean *atom* of `body` (descending through the Boolean connectives)
//!   that mentions `x` must be a **linear arithmetic comparison or equality**
//!   whose two sides fully linearize into affine expressions over the symbols,
//!   and whose **net `x` coefficient is `0`**. Such an atom's truth is the same
//!   for every value of `x` (the `x` terms cancel), so substituting any concrete
//!   value preserves it.
//! - `x` must not occur in **any** other position — a uninterpreted-function
//!   argument, an array index, a bit-vector term, a non-linear product, a
//!   division/modulo, an `ite`, etc. — because the affine analysis cannot account
//!   for it there, so its value *might* matter. Any such occurrence aborts the
//!   rewrite (the universal is left untouched).
//!
//! When every `x` occurrence sits inside a proven-coefficient-`0` arithmetic
//! atom, `body`'s truth is genuinely `x`-independent, so `∀x. body ⟺ body[x := 0]`
//! is **exact** (it changes no model). A universal that fails *any* check is
//! passed through unchanged, so the pass is **strictly additive**: it can only
//! turn an otherwise-`unknown` verdict into a decided one, never alter an
//! already-decided result, and it never risks an unsound `sat`/`unsat`.
//!
//! *Termination.* The pass is a single bottom-up structural pass per assertion
//! with no solver call and no recursion into the quantifier front door.

use std::collections::{BTreeMap, HashMap};

use axeyum_ir::{Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::backend::SolverError;

/// Rewrites every top-level vacuous universal `∀x. body` (quantifier-free body in
/// which `x` is provably truth-irrelevant) to the equivalent `body[x := 0]`,
/// leaving every other assertion unchanged.
///
/// Returns the (possibly) rewritten assertions and whether any rewrite fired. The
/// rewrite is equivalence-preserving — a vacuous `∀x. body` is true in exactly the
/// models in which `body[x := 0]` is — so the caller may decide the result with
/// the ordinary dispatch and trust both `sat` and `unsat`.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] only on an internal IR builder failure (which
/// cannot occur for well-sorted input); a universal that fails the vacuousness
/// proof is *not* an error — it is simply passed through unchanged.
pub fn eliminate_vacuous_universals(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<(Vec<TermId>, bool), SolverError> {
    let mut out = Vec::with_capacity(assertions.len());
    let mut rewrote = false;
    for &assertion in assertions {
        match try_eliminate(arena, assertion)? {
            Some(simplified) => {
                rewrote = true;
                out.push(simplified);
            }
            None => out.push(assertion),
        }
    }
    Ok((out, rewrote))
}

/// Attempts the vacuous-universal rewrite on a single top-level assertion.
///
/// Returns `Ok(Some(body[x := 0]))` when the assertion is a top-level `∀x. body`
/// with a quantifier-free body in which the bound variable `x` is **proven
/// vacuous** (truth-irrelevant); `Ok(None)` otherwise (not a universal, a nested
/// quantifier in the body, an arithmetic atom whose `x`-coefficient is non-zero or
/// does not fully linearize, or an `x` occurrence outside an analyzable arithmetic
/// atom), in which case the caller leaves the assertion unchanged.
fn try_eliminate(arena: &mut TermArena, assertion: TermId) -> Result<Option<TermId>, SolverError> {
    // Must be a top-level `∀x. body`.
    let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(assertion)
    else {
        return Ok(None);
    };
    let var = *var;
    let body = args[0];

    // Only `Int`/`Real` bound variables: the affine analysis is defined for them,
    // and the finite-domain expansion already handles `Bool`/`BitVec`. (A vacuous
    // `Bool`/`BitVec` universal is decided elsewhere; we need not duplicate it.)
    let sort = arena.symbol(var).1;
    if !matches!(sort, Sort::Int | Sort::Real) {
        return Ok(None);
    }

    // A nested quantifier could re-bind/shadow `x`; the substitution would be
    // unsound, so leave it for the existing quantifier path.
    if contains_quantifier(arena, body) {
        return Ok(None);
    }

    // Prove `x` is truth-irrelevant in `body`. Any failure leaves the universal
    // untouched (a sound pass-through).
    if !body_is_x_vacuous(arena, body, var) {
        return Ok(None);
    }

    // `x` is vacuous ⇒ `∀x. body ⟺ body[x := 0]`. Substitute an arbitrary fixed
    // value of `x`'s sort; the body is quantifier-free, so this is capture-free.
    let value = match sort {
        Sort::Int => arena.int_const(0),
        Sort::Real => arena.real_const(Rational::zero()),
        // Guarded above; unreachable, but stay total rather than panic.
        _ => return Ok(None),
    };
    let var_term = arena.var(var);
    let mut replacements: HashMap<TermId, TermId> = HashMap::new();
    replacements.insert(var_term, value);
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let rewritten = replace_subterms(arena, body, &replacements, &mut memo).map_err(err)?;
    Ok(Some(rewritten))
}

/// Whether `var` is **provably truth-irrelevant** in the quantifier-free `body`.
///
/// Descends the Boolean structure (the connectives `not`, `and`, `or`, `implies`,
/// `xor`, and `ite`/`eq` over `Bool`) to the atoms. An atom that does not mention
/// `var` is fine. An atom that mentions `var` is acceptable **only** if it is a
/// linear arithmetic comparison or equality whose two sides fully linearize and
/// whose net `var` coefficient is `0`. Any other `var` occurrence (a UF argument,
/// an array/BV/`ite` context, a non-linear product, a `div`/`mod`, …) is *not*
/// provably irrelevant, so the whole check fails.
fn body_is_x_vacuous(arena: &TermArena, body: TermId, var: SymbolId) -> bool {
    // Fast path: `var` absent everywhere ⇒ trivially vacuous.
    if !occurs(arena, body, var) {
        return true;
    }
    check_node(arena, body, var)
}

/// Recursive vacuousness check at one node (see [`body_is_x_vacuous`]).
fn check_node(arena: &TermArena, term: TermId, var: SymbolId) -> bool {
    // A subtree free of `var` is always fine, whatever it is.
    if !occurs(arena, term, var) {
        return true;
    }
    let TermNode::App { op, args } = arena.node(term) else {
        // A bare `Symbol(var)` reached here is `var` in a Boolean position, which
        // cannot happen (var is Int/Real). Any other leaf does not contain var.
        return false;
    };
    match op {
        // Boolean connectives: `var` (Int/Real) can only reach an atom *through*
        // these, so recurse into the operands.
        Op::BoolNot | Op::BoolAnd | Op::BoolOr | Op::BoolImplies | Op::BoolXor => {
            args.iter().all(|&a| check_node(arena, a, var))
        }
        // `ite`/`eq` may join Bool operands (then recurse) or be the atom itself.
        // For `eq` over an arithmetic sort, treat it as an arithmetic atom.
        Op::Ite => args.iter().all(|&a| {
            // The condition is Bool; the branches share the result sort. Recursing
            // into every operand is sound: a `var`-bearing Int/Real branch is not a
            // Boolean connective, so it cannot itself be vacuous unless `var` is
            // absent — which `occurs` already short-circuits. An `ite` whose branch
            // genuinely carries `var` therefore fails (correctly: the value flows
            // out and may matter).
            check_node(arena, a, var)
        }),
        // `eq` over an arithmetic sort, and the arithmetic comparisons, are the
        // only atoms in which `var` may legitimately appear — provided its net
        // coefficient cancels to zero (`arith_atom_x_free` also rejects a non-arith
        // `eq` that still carries `var`).
        Op::Eq
        | Op::IntLt
        | Op::IntLe
        | Op::IntGt
        | Op::IntGe
        | Op::RealLt
        | Op::RealLe
        | Op::RealGt
        | Op::RealGe => arith_atom_x_free(arena, args, var),
        // Any other operator carrying `var` (UF apply, array, BV, datatype test,
        // non-linear arithmetic, …) is not provably irrelevant.
        _ => false,
    }
}

/// Whether a binary arithmetic atom `args = [lhs, rhs]` has a net `var`
/// coefficient of zero, with both sides fully linearizing into affine
/// expressions.
///
/// `var` is truth-irrelevant in such an atom: with coefficient `0` the `var`
/// terms cancel in `lhs - rhs`, so the comparison/equality holds for the same
/// values regardless of `var`. Returns `false` (not provably irrelevant) if
/// either side fails to fully linearize, or the net coefficient is non-zero, or
/// the operands are not both `Int`/`Real`.
fn arith_atom_x_free(arena: &TermArena, args: &[TermId], var: SymbolId) -> bool {
    if args.len() != 2 {
        return false;
    }
    let (lhs, rhs) = (args[0], args[1]);
    // Restrict to arithmetic operands; an `Eq` over Bool/BV/array/etc. is handled
    // by the generic branch only when `var`-free (already short-circuited).
    if !matches!(arena.sort_of(lhs), Sort::Int | Sort::Real) {
        return false;
    }
    let Some(left) = affine(arena, lhs, var) else {
        return false;
    };
    let Some(right) = affine(arena, rhs, var) else {
        return false;
    };
    // Net `var` coefficient of `lhs - rhs`. Subtracting two coefficients cannot
    // overflow for a coefficient `1` (the only coefficients `affine` produces here
    // are `±1`), but stay checked; an overflow ⇒ not provably vacuous (decline).
    let Some(net) = left.coeff(var).checked_sub(right.coeff(var)) else {
        return false;
    };
    net.is_zero()
}

/// An affine expression `sum coeff_i * symbol_i + constant` over the arena's
/// symbols, used solely to read off a bound variable's net coefficient.
///
/// Only the `coeffs` map matters for the vacuousness test; the constant is
/// tracked for completeness of the affine algebra (so `affine` can compose
/// add/sub/neg/mul-by-constant faithfully).
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

/// Linearizes `term` (`Int`/`Real`-sorted) into an [`Affine`] form, or `None` if
/// it is not a purely affine expression in which **the bound variable `var` is
/// fully accounted for**.
///
/// Handled: integer/real constants, the bound variable and other symbols (opaque
/// leaves with coefficient `1`), `+`, `-` (binary and unary negation), and `*`
/// **only** when one operand is a constant (linear scaling). The `Int → Real`
/// embedding ([`Op::IntToReal`]) is transparent for the affine algebra.
///
/// Returns `None` for any construct under which `var` could hide unaccounted —
/// a product of two non-constants, `div`/`mod`/`abs`, a uninterpreted-function
/// application, a `select`, etc. Conservatively returning `None` there forces the
/// caller to leave the universal untouched (sound).
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
                // Linear only when one factor is a (var-free) constant; otherwise
                // the product is non-linear and `var` might appear in a way the
                // affine form cannot represent.
                if a.coeffs.is_empty() {
                    b.scale(a.constant)
                } else if b.coeffs.is_empty() {
                    a.scale(b.constant)
                } else {
                    None
                }
            }
            // `to_real` is the identity numeric embedding; the affine form carries
            // over unchanged (coefficients/constants are the same rationals).
            Op::IntToReal => affine(arena, args[0], var),
            // Anything else (`div`/`mod`/`abs`/`/`, UF apply, select, bv ops, …)
            // is opaque. If `var` hides inside, we must not claim it cancels —
            // bail. (A var-free opaque term is fine, but `affine` is only invoked
            // on atoms already known to contain `var`, so we simply refuse here.)
            _ => {
                if occurs(arena, term, var) {
                    None
                } else {
                    // A `var`-free opaque subterm: model it as a single opaque
                    // leaf so the surrounding affine algebra stays faithful. It
                    // never contributes a `var` coefficient.
                    Some(opaque_leaf(term))
                }
            }
        },
        // Wide BV / Bool constants etc. cannot appear in an Int/Real affine
        // position for a well-sorted body; treat as var-free opaque.
        _ => {
            if occurs(arena, term, var) {
                None
            } else {
                Some(opaque_leaf(term))
            }
        }
    }
}

/// A var-free opaque subterm modeled as a fresh "pseudo-symbol" so the affine
/// algebra composes faithfully without ever attributing a coefficient to `var`.
///
/// The exact key is irrelevant to the vacuousness test (only `var`'s coefficient
/// is read), so a constant-zero affine with a sentinel constant suffices: the
/// opaque value never carries a `var` coefficient, which is all that matters.
fn opaque_leaf(_term: TermId) -> Affine {
    // The opaque value contributes no `var` coefficient. Representing it as the
    // zero affine is sufficient because the test only inspects `coeff(var)`, and
    // a var-free term contributes nothing to it.
    Affine::constant(Rational::zero())
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
