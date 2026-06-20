//! Single-variable real **Fourier-Motzkin** elimination for a top-level
//! universal (a conservative, *exact* quantifier-elimination keystone).
//!
//! The sibling passes decide narrow shapes: [`crate::quant_vacuous_universal`]
//! owns the case where the bound variable cancels (net coefficient `0`), and
//! [`crate::quant_unsat_universal`] owns a `∀x. (c·x ⋈ t)` whose body is a
//! **single** linear atom with `c ≠ 0`. Neither decides a *multi-atom* real
//! universal such as
//!
//! ```text
//! ∀x:Real. (x ≥ 0 ∧ x ≤ 10)        — false (x = -1 falsifies it) ⇒ unsat
//! ∀x:Real. (x ≤ 0 ∨ x > 0)         — valid (real trichotomy)      ⇒ sat
//! ```
//!
//! This pass closes that gap by **eliminating `x` exactly** over the reals.
//!
//! ## The reduction
//!
//! For a top-level `∀x:Real. φ` with `φ` quantifier-free over **linear real
//! atoms**, universal quantification is the dual of existential:
//!
//! ```text
//! ∀x. φ  ⟺  ¬ ∃x. ¬φ.
//! ```
//!
//! We put `¬φ` in **disjunctive normal form** `⋁_k (⋀_i ℓ_{k,i})` over the
//! atoms (each `ℓ` a linear-real literal in `x`). Existential quantification
//! distributes over `∨`, so
//!
//! ```text
//! ∃x. ¬φ  =  ⋁_k ( ∃x. ⋀_i ℓ_{k,i} ).
//! ```
//!
//! Each conjunctive clause `∃x. ⋀_i ℓ_{k,i}` is eliminated by Fourier-Motzkin:
//! normalize every literal to `a·x + r ⋈ 0` (`r` free of `x`, `⋈ ∈ {<, ≤, =}`),
//! split into **lower bounds** `x ≳ Lᵢ` (from `a < 0`) and **upper bounds**
//! `x ≲ Uⱼ` (from `a > 0`); an equality contributes *both* a non-strict lower
//! and a non-strict upper bound. Over the **reals** (an unbounded, dense, gap-
//! free domain) an `x` satisfying the clause exists iff **every** lower bound
//! lies below **every** upper bound — `Lᵢ < Uⱼ` when either side is strict, else
//! `Lᵢ ≤ Uⱼ` — *and* every `x`-free atom of the clause holds. (With no lower or
//! no upper bound, `x` is unbounded on that side and the bound-pair conjunction
//! is empty — vacuously true.) Real FM is **exact**: no integer rounding
//! subtleties arise, which is exactly why the pass is scoped to `Sort::Real`.
//!
//! The eliminated `∃x. ¬φ` is an `x`-free formula `ψ(y…)`; then
//! `χ := ¬ψ` is an `x`-free formula equivalent to `∀x. φ`. The pass:
//!
//! - if `χ` is identically `false` (i.e. `∃x. ¬φ` is valid), reports the
//!   assertion — and the whole query — **`unsat`**;
//! - otherwise **rewrites** the assertion `∀x. φ` to `χ` and lets the ordinary
//!   dispatch decide the residual (for a closed `φ`, `χ` is `true`/`false`
//!   directly).
//!
//! ## Soundness — the deliberate scope
//!
//! The verdict can be `unsat` or a logically-equivalent rewrite, so every
//! restriction below is soundness-critical; **any** shape outside the precise
//! fragment declines (returns [`FmOutcome`]-`None`, leaving the assertion
//! untouched).
//!
//! - **`Sort::Real` only.** Integer universals are *out of scope* — real FM is
//!   only an over-approximation over `ℤ` (it ignores integrality). An
//!   `∀x:Int. …` declines and is left to the other passes.
//! - **Linear real atoms only.** Every atom must be `RealLt/Le/Gt/Ge` or an
//!   `Eq` over reals, and both sides must fully linearize via the affine
//!   collector. Any non-linear `x` (a product `x·x`, `x` inside a UF / `div` /
//!   `abs` / array), any bit-vector/array/datatype/`Int` atom, or any nested
//!   quantifier ⇒ decline.
//! - **No `x`-disequality clause.** A clause whose negated literal puts a
//!   *strict disequality* `x ≠ c` on `x` (a single-point hole) is not a simple
//!   FM bound pair, so any clause carrying such a literal declines.
//! - **Bounded DNF.** The negation's DNF is capped ([`MAX_DNF_CLAUSES`],
//!   [`MAX_CLAUSE_LITERALS`]); a wider formula declines rather than risk blow-up
//!   or a subtle normalization error.
//!
//! The pass is **strictly additive**: it can only turn an otherwise-`unknown`
//! verdict into a *provably-correct* `unsat` or an equivalent rewrite; every
//! universal that fails any check passes through byte-identical.

use std::collections::BTreeMap;

use axeyum_ir::{Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode};

/// Maximum number of conjunctive clauses in the DNF of `¬φ`. A wider boolean
/// structure declines (conservative — avoids blow-up and keeps the exactness
/// argument tractable).
const MAX_DNF_CLAUSES: usize = 64;

/// Maximum number of literals in any one DNF clause. A wider clause declines.
const MAX_CLAUSE_LITERALS: usize = 64;

/// The outcome of attempting real Fourier-Motzkin elimination on one assertion.
#[derive(Debug, Clone, Copy)]
pub enum FmOutcome {
    /// `∀x. φ` reduces to `false` — the assertion (and whole query) is `unsat`.
    Unsat,
    /// `∀x. φ` reduces to the `x`-free, logically-equivalent term `χ`; the
    /// caller should replace the assertion with it and re-dispatch.
    Rewrite(TermId),
}

/// Attempts single-variable real FM elimination on a top-level `∀x:Real. φ`.
///
/// Returns [`FmOutcome::Unsat`] when `∀x. φ` is identically false, or
/// [`FmOutcome::Rewrite`] with an `x`-free term logically equivalent to the
/// universal; returns `None` (decline) for any assertion outside the exactly-
/// eliminable real fragment — see the module docs for the precise scope. A
/// decline leaves the assertion untouched, so the pass never weakens the
/// problem nor risks a wrong verdict.
pub fn eliminate_real_universal(arena: &mut TermArena, assertion: TermId) -> Option<FmOutcome> {
    // Must be a top-level `∀x. body`.
    let (var, body) = match arena.node(assertion) {
        TermNode::App {
            op: Op::Forall(var),
            args,
        } => (*var, args[0]),
        _ => return None,
    };

    // `Sort::Real` only — integer FM is not exact (decline `Int` universals).
    if arena.symbol(var).1 != Sort::Real {
        return None;
    }

    // A nested quantifier under `∀x` is out of scope.
    if contains_quantifier(arena, body) {
        return None;
    }

    // Build the DNF of `¬φ` as conjunctive clauses of linear-real literals in
    // `x`. Any non-linear `x`, non-real atom, or unsupported connective makes
    // this `None` (decline).
    let dnf = dnf_of_negation(arena, body)?;
    if dnf.is_empty() {
        // `¬φ` is identically false ⇒ `∃x. ¬φ` is false ⇒ `∀x. φ` is `true`.
        let t = arena.bool_const(true);
        return Some(FmOutcome::Rewrite(t));
    }
    if dnf.len() > MAX_DNF_CLAUSES {
        return None;
    }

    // `∃x. ¬φ = ⋁_k (∃x. clause_k)`. Eliminate `x` from each clause exactly.
    // The disjuncts are `x`-free terms; collect them. A clause may eliminate to
    // a definite `true`/`false` (tracked structurally) or to a residual term.
    let mut disjuncts: Vec<ClauseElim> = Vec::with_capacity(dnf.len());
    for clause in &dnf {
        if clause.len() > MAX_CLAUSE_LITERALS {
            return None;
        }
        disjuncts.push(eliminate_clause(arena, var, clause)?);
    }

    // `∃x. ¬φ = ⋁ disjuncts`. If any disjunct is definitely `true`, the whole
    // existential is valid ⇒ `∀x. φ` is `false` ⇒ **unsat**.
    if disjuncts.iter().any(|d| matches!(d, ClauseElim::True)) {
        return Some(FmOutcome::Unsat);
    }
    // Drop the definitely-`false` disjuncts (they contribute nothing to the ∨).
    let residuals: Vec<TermId> = disjuncts
        .into_iter()
        .filter_map(|d| match d {
            ClauseElim::Term(t) => Some(t),
            ClauseElim::False => None,
            ClauseElim::True => unreachable!("handled above"),
        })
        .collect();

    if residuals.is_empty() {
        // `∃x. ¬φ` is identically `false` ⇒ `∀x. φ` is identically `true`.
        // (This is the *valid* universal, e.g. `∀x. (x ≤ 0 ∨ x > 0)`.)
        let t = arena.bool_const(true);
        return Some(FmOutcome::Rewrite(t));
    }

    // `∃x. ¬φ` = OR(residuals); `χ = ∀x. φ = ¬(∃x. ¬φ)`.
    let exists_not_phi = fold_or(arena, &residuals)?;
    let chi = arena.not(exists_not_phi).ok()?;
    Some(FmOutcome::Rewrite(chi))
}

/// The result of FM-eliminating `x` from one conjunctive clause `∃x. ⋀ ℓᵢ`.
enum ClauseElim {
    /// The clause's existential is identically `true`.
    True,
    /// The clause's existential is identically `false`.
    False,
    /// An `x`-free residual term (the conjunction of bound-pair atoms and the
    /// clause's `x`-free atoms).
    Term(TermId),
}

/// A linear-real atom normalized to `affine ⋈ 0`, where `affine` is over the
/// arena symbols and `⋈` is one of `<`, `≤`, `=` (a `≠` is tracked separately).
#[derive(Clone, Copy)]
enum Rel {
    /// `affine < 0`.
    Lt,
    /// `affine ≤ 0`.
    Le,
    /// `affine = 0`.
    Eq,
    /// `affine ≠ 0` — a disequality; a clause with this literal *on `x`*
    /// declines.
    Ne,
}

/// One normalized literal: `expr ⋈ 0` with `expr` an affine over symbols.
struct Literal {
    expr: Affine,
    rel: Rel,
}

/// A conjunctive clause is a list of normalized literals.
type Clause = Vec<Literal>;

/// Eliminates `x` from a single conjunctive clause `∃x. ⋀ literals` by real
/// Fourier-Motzkin. Returns the `x`-free [`ClauseElim`], or `None` to decline
/// (a non-FM-eliminable literal — e.g. an `x`-disequality, or an `x`-free
/// disequality the residual builder cannot represent exactly).
fn eliminate_clause(arena: &mut TermArena, var: SymbolId, clause: &Clause) -> Option<ClauseElim> {
    // Lower bounds (x ≳ L) and upper bounds (x ≲ U); `strict` tracks `>`/`<`.
    let mut lowers: Vec<(Affine, bool)> = Vec::new();
    let mut uppers: Vec<(Affine, bool)> = Vec::new();
    // The clause's `x`-free atoms, accumulated as residual comparison terms.
    let mut xfree: Vec<TermId> = Vec::new();

    for lit in clause {
        let a = lit.expr.coeff(var);
        if a.is_zero() {
            // `x`-free atom: it passes through `∃x` unchanged. Rebuild it as a
            // term `expr ⋈ 0`. A residual disequality cannot be built exactly
            // here, so decline if it appears `x`-free too.
            match build_xfree_atom(arena, &lit.expr, lit.rel)? {
                AtomValue::True => {} // a ∧ true = a
                AtomValue::False => return Some(ClauseElim::False),
                AtomValue::Term(t) => xfree.push(t),
            }
            continue;
        }

        // `x` genuinely appears. Isolate `x`: from `a·x + r ⋈ 0`, the bound is
        // `x = -r/a` (so `bound = expr_without_x scaled by -1/a`).
        let r = without_var(&lit.expr, var); // the `x`-free part `r`
        // bound = -r / a
        let neg_inv_a = Rational::zero() - Rational::integer(1) / a;
        let bound = r.scale(neg_inv_a);
        let a_pos = a > Rational::zero();

        match lit.rel {
            Rel::Lt => {
                // a·x + r < 0  ⇒  a·x < -r.
                if a_pos {
                    uppers.push((bound, true)); // x < -r/a
                } else {
                    lowers.push((bound, true)); // x > -r/a (divide flips)
                }
            }
            Rel::Le => {
                if a_pos {
                    uppers.push((bound, false)); // x ≤ -r/a
                } else {
                    lowers.push((bound, false)); // x ≥ -r/a
                }
            }
            Rel::Eq => {
                // a·x + r = 0  ⇒  x = -r/a: a non-strict lower *and* upper.
                lowers.push((bound.clone(), false));
                uppers.push((bound, false));
            }
            // `x ≠ c`: a single-point hole, not a simple FM bound — decline.
            Rel::Ne => return None,
        }
    }

    // FM join: `∃x` exists iff every lower bound is below every upper bound
    // (strictly if either is strict), AND every `x`-free atom holds. With no
    // lowers or no uppers, the pair-conjunction is empty (vacuously satisfied),
    // so `x` is unbounded on that side and the clause reduces to its `x`-free
    // atoms.
    let mut conjuncts: Vec<TermId> = xfree;
    for (lo, lo_strict) in &lowers {
        for (up, up_strict) in &uppers {
            // `lo ⋈ up` with `⋈` strict iff either bound is strict.
            let strict = *lo_strict || *up_strict;
            match build_pair_atom(arena, lo, up, strict)? {
                AtomValue::True => {} // contributes nothing
                AtomValue::False => return Some(ClauseElim::False),
                AtomValue::Term(t) => conjuncts.push(t),
            }
        }
    }

    if conjuncts.is_empty() {
        // No residual constraint ⇒ the clause's existential is `true`.
        return Some(ClauseElim::True);
    }
    Some(ClauseElim::Term(fold_and(arena, &conjuncts)?))
}

/// The (possibly constant-folded) value of an `x`-free atom.
enum AtomValue {
    /// The atom is a tautology.
    True,
    /// The atom is a contradiction.
    False,
    /// A residual `Bool` term.
    Term(TermId),
}

/// Builds the `x`-free comparison `expr ⋈ 0` from an affine `expr` over real
/// symbols and a relation. A fully-constant `expr` folds to `True`/`False`.
/// A disequality (`Rel::Ne`) over a non-constant residual declines (`None`) —
/// the pass does not emit `x`-free disequalities (they are not needed by the
/// supported scope and keep the residual builder exact).
fn build_xfree_atom(arena: &mut TermArena, expr: &Affine, rel: Rel) -> Option<AtomValue> {
    // Constant fold when `expr` has no symbol terms.
    if expr.coeffs.values().all(|c| c.is_zero()) {
        let c = expr.constant;
        let z = Rational::zero();
        let holds = match rel {
            Rel::Lt => c < z,
            Rel::Le => c <= z,
            Rel::Eq => c == z,
            Rel::Ne => c != z,
        };
        return Some(if holds {
            AtomValue::True
        } else {
            AtomValue::False
        });
    }
    let lhs = build_affine_term(arena, expr)?;
    let zero = arena.real_const(Rational::zero());
    let term = match rel {
        Rel::Lt => arena.real_lt(lhs, zero).ok()?,
        Rel::Le => arena.real_le(lhs, zero).ok()?,
        Rel::Eq => arena.eq(lhs, zero).ok()?,
        // We deliberately do not emit a residual disequality (out of scope).
        Rel::Ne => return None,
    };
    Some(AtomValue::Term(term))
}

/// Builds the bound-pair atom `lo ⋈ up` (`<` if `strict`, else `≤`) as an
/// `x`-free `Bool` term. Equivalent to `lo - up ⋈ 0`; folds to `True`/`False`
/// when `lo - up` is constant.
fn build_pair_atom(
    arena: &mut TermArena,
    lo: &Affine,
    up: &Affine,
    strict: bool,
) -> Option<AtomValue> {
    let diff = lo.sub(up); // lo - up ⋈ 0
    build_xfree_atom(arena, &diff, if strict { Rel::Lt } else { Rel::Le })
}

/// Folds a non-empty list into a left-nested `and`; a singleton passes through.
fn fold_and(arena: &mut TermArena, terms: &[TermId]) -> Option<TermId> {
    let mut iter = terms.iter().copied();
    let mut acc = iter.next()?;
    for t in iter {
        acc = arena.and(acc, t).ok()?;
    }
    Some(acc)
}

/// Folds a non-empty list into a left-nested `or`; a singleton passes through.
fn fold_or(arena: &mut TermArena, terms: &[TermId]) -> Option<TermId> {
    let mut iter = terms.iter().copied();
    let mut acc = iter.next()?;
    for t in iter {
        acc = arena.or(acc, t).ok()?;
    }
    Some(acc)
}

// ---------------------------------------------------------------------------
// DNF of `¬φ` over linear-real literals.
// ---------------------------------------------------------------------------

/// Builds the disjunctive normal form of `¬φ` as a list of conjunctive clauses
/// (each a list of normalized [`Literal`]s). Returns `None` to decline whenever
/// any atom is not a linear-real comparison/equality, any side fails to
/// linearize over `x`, or an unsupported connective appears.
///
/// Works by computing the DNF of `body` under a sign (`negate = true` ⇒ we want
/// `¬body`). `not` flips the sign; `and`/`or` combine per the sign (an `and`
/// under negation is an `or` of negations, etc.). Each leaf atom yields a
/// single literal (or its negation), normalized to `expr ⋈ 0`.
fn dnf_of_negation(arena: &TermArena, body: TermId) -> Option<Vec<Clause>> {
    dnf(arena, body, true)
}

/// DNF of `body` (or `¬body` when `negate`), as `⋁ (⋀ literals)`. The empty
/// `Vec` (no clauses) denotes **false**; a clause with no literals denotes a
/// **true** conjunct.
fn dnf(arena: &TermArena, body: TermId, negate: bool) -> Option<Vec<Clause>> {
    if let TermNode::App { op, args } = arena.node(body) {
        match op {
            Op::BoolNot => return dnf(arena, args[0], !negate),
            // Constant `true`/`false` short-circuits.
            Op::BoolAnd if !negate => return dnf_conjunction(arena, args, false),
            Op::BoolAnd if negate => return dnf_disjunction(arena, args, true),
            Op::BoolOr if !negate => return dnf_disjunction(arena, args, false),
            Op::BoolOr if negate => return dnf_conjunction(arena, args, true),
            // `implies(a, b) ≡ ¬a ∨ b`; the helper desugars under `negate`.
            Op::BoolImplies if args.len() == 2 => {
                return dnf_implies(arena, args[0], args[1], negate);
            }
            _ => {}
        }
    }
    // A leaf: try to read a `Bool` constant, else a linear-real atom literal.
    if let TermNode::BoolConst(b) = arena.node(body) {
        let truth = b ^ negate;
        return Some(if truth {
            vec![Vec::new()] // a single empty clause = true
        } else {
            Vec::new() // no clauses = false
        });
    }
    let lit = atom_literal(arena, body, negate)?;
    Some(vec![vec![lit]])
}

/// DNF of `implies(a, b)` (or its negation). `implies(a,b) ≡ ¬a ∨ b`; under
/// `negate` we want `a ∧ ¬b`.
fn dnf_implies(arena: &TermArena, a: TermId, b: TermId, negate: bool) -> Option<Vec<Clause>> {
    if negate {
        // a ∧ ¬b
        let da = dnf(arena, a, false)?;
        let dnb = dnf(arena, b, true)?;
        cross_and(&da, &dnb)
    } else {
        // ¬a ∨ b
        let dna = dnf(arena, a, true)?;
        let db = dnf(arena, b, false)?;
        Some(union_clauses(dna, db))
    }
}

/// DNF of `⋀ args` (or, with `negate`, the *conjunction* arising from a negated
/// `or`): cross-product (AND) of the per-argument DNFs.
fn dnf_conjunction(arena: &TermArena, args: &[TermId], negate: bool) -> Option<Vec<Clause>> {
    // Start from `true` (single empty clause) and AND each argument in.
    let mut acc: Vec<Clause> = vec![Vec::new()];
    for &arg in args {
        let d = dnf(arena, arg, negate)?;
        acc = cross_and(&acc, &d)?;
    }
    Some(acc)
}

/// DNF of `⋁ args` (or, with `negate`, the *disjunction* arising from a negated
/// `and`): union of the per-argument DNFs.
fn dnf_disjunction(arena: &TermArena, args: &[TermId], negate: bool) -> Option<Vec<Clause>> {
    let mut acc: Vec<Clause> = Vec::new();
    for &arg in args {
        let d = dnf(arena, arg, negate)?;
        acc = union_clauses(acc, d);
        if acc.len() > MAX_DNF_CLAUSES {
            return None;
        }
    }
    Some(acc)
}

/// Cross-product AND of two DNFs: `(⋁ cᵢ) ∧ (⋁ dⱼ) = ⋁_{i,j} (cᵢ ∧ dⱼ)`.
fn cross_and(left: &[Clause], right: &[Clause]) -> Option<Vec<Clause>> {
    if left.is_empty() || right.is_empty() {
        // Either side is `false` ⇒ the conjunction is `false`.
        return Some(Vec::new());
    }
    if left.len().saturating_mul(right.len()) > MAX_DNF_CLAUSES {
        return None;
    }
    let mut out = Vec::with_capacity(left.len() * right.len());
    for c in left {
        for d in right {
            let mut merged = Vec::with_capacity(c.len() + d.len());
            for lit in c {
                merged.push(Literal {
                    expr: lit.expr.clone(),
                    rel: lit.rel,
                });
            }
            for lit in d {
                merged.push(Literal {
                    expr: lit.expr.clone(),
                    rel: lit.rel,
                });
            }
            out.push(merged);
        }
    }
    Some(out)
}

/// Union (OR) of two DNFs.
fn union_clauses(mut left: Vec<Clause>, mut right: Vec<Clause>) -> Vec<Clause> {
    left.append(&mut right);
    left
}

/// Normalizes a leaf linear-real atom (or its negation, when `negate`) to a
/// single [`Literal`] `expr ⋈ 0`. Returns `None` to decline if the atom is not
/// a real comparison/equality, or either side fails to linearize over `x`.
///
/// The relation is normalized to `<`, `≤`, `=`, or `≠`:
/// `a < b ⇒ a-b < 0`; `a ≤ b ⇒ a-b ≤ 0`; `a > b ⇒ b-a < 0`; `a ≥ b ⇒ b-a ≤ 0`;
/// `a = b ⇒ a-b = 0`. Negation flips: `¬(<) = (≥)`, `¬(≤) = (>)`, `¬(=) = (≠)`.
fn atom_literal(arena: &TermArena, atom: TermId, negate: bool) -> Option<Literal> {
    let TermNode::App { op, args } = arena.node(atom) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (lhs, rhs) = (args[0], args[1]);
    // Only real comparisons / real equalities are in scope. An `Eq` must be
    // over reals (a Bool/BV/Int `Eq` is not a linear-real atom).
    let is_real_cmp = matches!(op, Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe);
    let is_real_eq = matches!(op, Op::Eq) && arena.sort_of(lhs) == Sort::Real;
    if !is_real_cmp && !is_real_eq {
        return None;
    }
    let left = affine(arena, lhs)?;
    let right = affine(arena, rhs)?;

    // Build `expr` and base relation so the atom is `expr ⋈ 0` (pre-negation).
    let (expr, rel) = match op {
        Op::RealLt => (left.sub(&right), Rel::Lt), // a - b < 0
        Op::RealLe => (left.sub(&right), Rel::Le), // a - b ≤ 0
        Op::RealGt => (right.sub(&left), Rel::Lt), // b - a < 0
        Op::RealGe => (right.sub(&left), Rel::Le), // b - a ≤ 0
        Op::Eq => (left.sub(&right), Rel::Eq),     // a - b = 0
        _ => return None,
    };
    if !negate {
        return Some(Literal { expr, rel });
    }
    // Negate: flip the relation, flipping the expression where needed so the
    // result stays in the `expr ⋈ 0` normal form with `⋈ ∈ {<, ≤, =, ≠}`.
    //   ¬(e < 0)  =  e ≥ 0   =  (-e) ≤ 0
    //   ¬(e ≤ 0)  =  e > 0   =  (-e) < 0
    //   ¬(e = 0)  =  e ≠ 0
    let (expr, rel) = match rel {
        Rel::Lt => (expr.neg(), Rel::Le),
        Rel::Le => (expr.neg(), Rel::Lt),
        Rel::Eq => (expr, Rel::Ne),
        Rel::Ne => (expr, Rel::Eq), // unreachable for a freshly-built atom
    };
    Some(Literal { expr, rel })
}

// ---------------------------------------------------------------------------
// Affine algebra (mirrors the sibling passes, extended to rebuild terms).
// ---------------------------------------------------------------------------

/// An affine expression `Σ coeff_i · symbol_i + constant` over arena symbols.
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

    fn neg(&self) -> Self {
        Self {
            coeffs: self
                .coeffs
                .iter()
                .map(|(&s, &c)| (s, Rational::zero() - c))
                .collect(),
            constant: Rational::zero() - self.constant,
        }
    }

    fn add(&self, other: &Self) -> Self {
        let mut coeffs = self.coeffs.clone();
        for (&s, &c) in &other.coeffs {
            let entry = coeffs.entry(s).or_insert_with(Rational::zero);
            *entry = *entry + c;
        }
        Self {
            coeffs,
            constant: self.constant + other.constant,
        }
    }

    fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    fn scale(&self, factor: Rational) -> Self {
        Self {
            coeffs: self.coeffs.iter().map(|(&s, &c)| (s, c * factor)).collect(),
            constant: self.constant * factor,
        }
    }
}

/// The `x`-free part of an affine: drop `var`'s term, keep all other symbols
/// and the constant.
fn without_var(expr: &Affine, var: SymbolId) -> Affine {
    let mut coeffs = expr.coeffs.clone();
    coeffs.remove(&var);
    Affine {
        coeffs,
        constant: expr.constant,
    }
}

/// Rebuilds an affine `Σ cᵢ·sᵢ + k` (over **real** symbols only) into a real
/// `TermId`. Returns `None` if any contributing symbol is not real (defensive —
/// a well-sorted real atom only carries real symbols here).
fn build_affine_term(arena: &mut TermArena, expr: &Affine) -> Option<TermId> {
    let mut acc: Option<TermId> = None;
    for (&sym, &c) in &expr.coeffs {
        if c.is_zero() {
            continue;
        }
        // Only real symbols may appear in a real affine residual.
        if arena.symbol(sym).1 != Sort::Real {
            return None;
        }
        let var_term = arena.var(sym);
        let term = if c == Rational::integer(1) {
            var_term
        } else {
            let coeff = arena.real_const(c);
            arena.real_mul(coeff, var_term).ok()?
        };
        acc = Some(match acc {
            None => term,
            Some(prev) => arena.real_add(prev, term).ok()?,
        });
    }
    if !expr.constant.is_zero() || acc.is_none() {
        let k = arena.real_const(expr.constant);
        acc = Some(match acc {
            None => k,
            Some(prev) => arena.real_add(prev, k).ok()?,
        });
    }
    acc
}

/// Linearizes `term` (`Real`/`Int`-sorted) into an [`Affine`], or `None` if it
/// is not a purely affine expression over the arena symbols.
///
/// Handled: real/int constants, symbols (opaque leaves, coefficient `1`), `+`,
/// `-`, unary negation, `*` only when one operand is a constant, and the
/// transparent `Int → Real` embedding. Anything else (a non-constant product,
/// `div`, `abs`, a UF application, a `select`, …) returns `None` —
/// conservatively forcing a decline (sound: FM applies only to the genuine
/// linear shape). An opaque subterm cannot be represented faithfully for term
/// rebuilding either, so it likewise returns `None` whether or not the bound
/// variable occurs inside it.
fn affine(arena: &TermArena, term: TermId) -> Option<Affine> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(Affine::constant(Rational::integer(*value))),
        TermNode::RealConst(value) => Some(Affine::constant(*value)),
        TermNode::Symbol(sym) => Some(Affine::symbol(*sym)),
        TermNode::App { op, args } => match op {
            Op::IntAdd | Op::RealAdd => {
                let a = affine(arena, args[0])?;
                let b = affine(arena, args[1])?;
                Some(a.add(&b))
            }
            Op::IntSub | Op::RealSub => {
                let a = affine(arena, args[0])?;
                let b = affine(arena, args[1])?;
                Some(a.sub(&b))
            }
            Op::IntNeg | Op::RealNeg => {
                let a = affine(arena, args[0])?;
                Some(a.neg())
            }
            Op::IntMul | Op::RealMul => {
                let a = affine(arena, args[0])?;
                let b = affine(arena, args[1])?;
                // Linear only when one factor is a (var-free) constant.
                if a.coeffs.is_empty() {
                    Some(b.scale(a.constant))
                } else if b.coeffs.is_empty() {
                    Some(a.scale(b.constant))
                } else {
                    None
                }
            }
            Op::IntToReal => affine(arena, args[0]),
            // Any other operator is opaque. Because the residual builder must
            // reconstruct a faithful term, we cannot represent an opaque
            // subterm as a sum of symbols — decline. (A `div`/`abs`/UF carrying
            // the bound variable is non-linear anyway.)
            _ => None,
        },
        // Non-arithmetic leaves cannot appear in a well-sorted real affine.
        _ => None,
    }
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
