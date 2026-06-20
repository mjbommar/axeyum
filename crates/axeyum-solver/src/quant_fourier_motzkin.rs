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

/// The internal, sign-precise verdict of running the FM elimination core on a
/// single `∀x. φ`. Distinguishes the three structurally-distinct outcomes the
/// core can reach so each caller can act on exactly the ones it is allowed to:
///
/// - [`Verdict::Valid`] — `∃x. ¬φ` is *identically false*, so `∀x. φ` is
///   identically **true** over the relaxation domain (the reals). This is the
///   *only* verdict the integer-relaxation entry point may act on.
/// - [`Verdict::Unsat`] — `∃x. ¬φ` is *identically true*, so the real universal
///   is **false** in every model.
/// - [`Verdict::Rewrite`] — a non-trivial `x`-free residual `χ` equivalent to
///   the *real* universal.
enum Verdict {
    /// The real universal is valid (`∀x:Real. φ` is identically `true`).
    Valid,
    /// The real universal is false in every model.
    Unsat,
    /// A non-trivial `x`-free term `χ` equivalent to the *real* universal.
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
    // (The integer-relaxation entry point [`eliminate_int_universal_valid`]
    // owns the `Sort::Int` case and acts on the `Valid` verdict only.)
    if arena.symbol(var).1 != Sort::Real {
        return None;
    }

    // Run the shared elimination core over the reals (no Int-atom relaxation).
    match eliminate_core(arena, var, body, /* relax_int = */ false)? {
        // The real universal is valid ⇒ rewrite the assertion to `true`.
        Verdict::Valid => {
            let t = arena.bool_const(true);
            Some(FmOutcome::Rewrite(t))
        }
        // The real universal is false in every model ⇒ the query is `unsat`.
        Verdict::Unsat => Some(FmOutcome::Unsat),
        // A non-trivial `x`-free residual equivalent to the real universal.
        Verdict::Rewrite(chi) => Some(FmOutcome::Rewrite(chi)),
    }
}

/// Attempts the **sound, one-directional real relaxation** of a top-level
/// `∀x:Int. φ`.
///
/// Integers are a subset of the reals, so `∀x:Real. φ` *valid* ⇒ `∀x:Int. φ`
/// *valid* — but **not** the converse (an integer universal can hold where the
/// real universal fails, the real counterexample landing in a gap between
/// integers, e.g. `∀x:Int. (x ≤ 0 ∨ x ≥ 1)`). So this entry point runs the
/// same FM elimination core, **treating `x` as a real**, and returns a
/// rewrite-to-`true` **iff and only iff** the core's verdict is
/// [`Verdict::Valid`]. Every other outcome — [`Verdict::Unsat`] (the real
/// universal is false, but the integer one might still hold in the gaps) and
/// [`Verdict::Rewrite`] (a residual equivalent to the *stronger* real
/// universal, which would *under-approximate* the integer one) — **declines**
/// (`None`), leaving the assertion byte-identical for the other passes / the
/// quantifier front door.
///
/// Soundness: this path can only ever turn an otherwise-`unknown` integer
/// universal into a *provably-true* `true`-rewrite. It **never** returns
/// `Unsat` and **never** rewrites to a non-`true` term, so it cannot weaken
/// the problem nor risk a wrong sat/unsat. All the real path's structural
/// declines (non-linear `x`, nested quantifier, `x` in a UF, `x`-disequality,
/// DNF caps, unsupported atoms) apply unchanged.
pub fn eliminate_int_universal_valid(
    arena: &mut TermArena,
    assertion: TermId,
) -> Option<FmOutcome> {
    // Must be a top-level `∀x. body`.
    let (var, body) = match arena.node(assertion) {
        TermNode::App {
            op: Op::Forall(var),
            args,
        } => (*var, args[0]),
        _ => return None,
    };

    // `Sort::Int` only — the real path owns `Sort::Real`.
    if arena.symbol(var).1 != Sort::Int {
        return None;
    }

    // Run the shared elimination core, relaxing `x` to the reals (admitting Int
    // comparison/equality atoms). Accept ONLY the `Valid` verdict.
    match eliminate_core(arena, var, body, /* relax_int = */ true)? {
        Verdict::Valid => {
            // `∀x:Real. φ` is valid ⇒ `∀x:Int. φ` is valid ⇒ rewrite to `true`.
            let t = arena.bool_const(true);
            Some(FmOutcome::Rewrite(t))
        }
        // `Unsat` (real-false) and any non-trivial `Rewrite` would be unsound on
        // `ℤ` (the real verdict is strictly stronger than the integer one), so
        // decline and leave the integer universal to the other passes.
        Verdict::Unsat | Verdict::Rewrite(_) => None,
    }
}

/// Attempts the **exact** decision of a **closed** top-level `∀x:Int. φ` —
/// a universal whose body mentions *only* the bound variable `x` (no other
/// symbol, no free variable), so every Fourier-Motzkin bound on `x` is a
/// concrete [`Rational`] constant.
///
/// ## Why closed integer universals can be decided exactly
///
/// `∀x:Int. φ ⟺ ¬∃x:Int. ¬φ`. We DNF `¬φ` exactly as the real path does; each
/// clause of `¬φ` reduces to a concrete real interval `(Lmax, Umin)` (per-
/// endpoint strict/non-strict, or unbounded on a side). The integer
/// existential `∃x:Int` of that clause holds **iff the interval contains an
/// integer** — a question decided *exactly* by integer ceil/floor of the
/// rational endpoints (see [`clause_has_integer`]). Then:
///
/// - if **any** clause contains an integer, `∃x:Int. ¬φ` is true ⇒
///   `∀x:Int. φ` is false ⇒ [`FmOutcome::Unsat`];
/// - if **no** clause contains an integer, `∃x:Int. ¬φ` is false ⇒
///   `∀x:Int. φ` is valid ⇒ rewrite to `true`.
///
/// This *closes the inter-integer-gap* cases the real-validity relaxation
/// declines: `∀x:Int. (x ≤ 0 ∨ x ≥ 1)` is real-invalid (the real hole `(0,1)`)
/// yet integer-valid (no integer in `(0,1)`), so this path returns the
/// `true`-rewrite the relaxation could not.
///
/// ## The closedness requirement (soundness-critical)
///
/// The integer-emptiness test is exact **only** when both interval endpoints
/// are concrete rationals. If any FM bound or any `x`-free atom carries a
/// *symbolic* residual (another symbol survives the affine), the clause is an
/// *open* universal: its truth depends on the free variable, and the integer
/// ceil/floor test does not apply. Such a universal **declines** (`None`) and
/// is left to [`eliminate_int_universal_valid`] / the other passes. Closedness
/// is enforced structurally — [`clause_has_integer`] returns `None` the moment
/// a non-constant residual appears, so an open universal can never reach a
/// verdict here.
///
/// Soundness: every verdict is exact for the closed single-variable integer
/// fragment, and every shape outside it declines byte-identically. Strictly
/// additive — only ever turns an `unknown` integer universal into a
/// provably-correct `unsat` or a `true`-rewrite.
pub fn eliminate_int_universal_closed(
    arena: &mut TermArena,
    assertion: TermId,
) -> Option<FmOutcome> {
    // Must be a top-level `∀x. body`.
    let (var, body) = match arena.node(assertion) {
        TermNode::App {
            op: Op::Forall(var),
            args,
        } => (*var, args[0]),
        _ => return None,
    };

    // `Sort::Int` only — the real path owns `Sort::Real`.
    if arena.symbol(var).1 != Sort::Int {
        return None;
    }

    // A nested quantifier under `∀x` is out of scope.
    if contains_quantifier(arena, body) {
        return None;
    }

    // Build the DNF of `¬φ`, relaxing Int atoms (treated as linear over the
    // arena symbols). Any non-linear `x`, unsupported atom, or wide DNF declines.
    let dnf = dnf_of_negation(arena, body, /* relax_int = */ true)?;
    if dnf.is_empty() {
        // `¬φ` is identically false ⇒ `∃x:Int. ¬φ` is false ⇒ `∀x:Int. φ` valid.
        let t = arena.bool_const(true);
        return Some(FmOutcome::Rewrite(t));
    }
    if dnf.len() > MAX_DNF_CLAUSES {
        return None;
    }

    // `∃x:Int. ¬φ = ⋁_k (∃x:Int. clause_k)`. Each clause's integer existential
    // is decided exactly by integer-emptiness of its concrete real interval. If
    // ANY clause carries a non-constant (symbolic) residual the universal is
    // *open* — decline the whole assertion (no partial verdict).
    let mut any_clause_has_integer = false;
    for clause in &dnf {
        if clause.len() > MAX_CLAUSE_LITERALS {
            return None;
        }
        // `None` ⇒ non-constant residual (open universal) ⇒ decline exactly.
        if clause_has_integer(var, clause)? {
            any_clause_has_integer = true;
        }
    }

    if any_clause_has_integer {
        // `∃x:Int. ¬φ` is true ⇒ `∀x:Int. φ` is false in every model ⇒ unsat.
        Some(FmOutcome::Unsat)
    } else {
        // No clause of `¬φ` contains an integer ⇒ `∀x:Int. φ` is valid ⇒ `true`.
        let t = arena.bool_const(true);
        Some(FmOutcome::Rewrite(t))
    }
}

/// Attempts the **exact** decision of an **open, constant-width-gap** top-level
/// `∀x:Int. φ` — a universal whose Fourier-Motzkin bounds on `x` are *symbolic*
/// (mention free parameters), but where every clause of `¬φ` carves out an
/// integer interval `[L, U]` whose **width `U − L` is a constant** and whose
/// endpoints are **integer-valued** linear expressions in the parameters.
///
/// ## Why a constant-width symbolic gap can still be decided exactly
///
/// `∀x:Int. φ ⟺ ¬∃x:Int. ¬φ`. We DNF `¬φ` exactly as the closed path does; each
/// clause reduces to an interval `[L, U]` over `x`, where `L`/`U` are now affine
/// expressions over the free parameters (`+ strictness`). The integer
/// *content* of `[L, U]` — the number of integers it admits — is governed by the
/// **width** `w = U − L` and the strictness alone, **provided** both endpoints
/// are integer-valued: integer content of an interval is *translation-invariant*,
/// so sliding `[L, U]` by an integer offset (which an integer parameter
/// assignment does, when `L` is integer-valued) preserves the count. Concretely,
/// for an integer-valued `L` (so `L` is some integer `n` at every assignment) and
/// `U = L + w` with `w` a constant integer, the admissible integers run from
/// `n + [lo strict]` to `n + w − [hi strict]`, a count of
/// `w − [lo strict] − [hi strict] + 1` that does **not** depend on `n`. So:
///
/// - if **any** clause's interval **always** admits an integer (count ≥ 1 for
///   every parameter assignment) ⇒ `∃x:Int. ¬φ` is true for all parameters ⇒
///   `∀x:Int. φ` is false in every model ⇒ [`FmOutcome::Unsat`];
/// - else if **every** clause's interval **never** admits an integer (count ≤ 0
///   for all parameters) ⇒ `∃x:Int. ¬φ` is false for all parameters ⇒
///   `∀x:Int. φ` is valid ⇒ rewrite to `true`.
///
/// This decides the open gap the closed and real-relaxation paths both decline,
/// e.g. `∀x:Int. (x ≤ y ∨ x ≥ y + 2)`: `¬φ = (x > y ∧ x < y + 2)`, the **open**
/// interval `(y, y + 2)` of constant width `2`, which contains `y + 1` for every
/// integer `y` ⇒ `unsat`. The `k = 1` sibling `∀x:Int. (x ≤ y ∨ x ≥ y + 1)`
/// (open `(y, y + 1)`, width `1`, no integer) is valid ⇒ rewrites to `true`.
///
/// ## Soundness-critical restrictions
///
/// Each restriction below keeps the constant-width / translation-invariance
/// argument *airtight*; any clause that fails a check makes the clause
/// **indeterminate**, and an indeterminate clause that is not overridden by an
/// always-contains clause declines the whole assertion (`None`):
///
/// - **One lower and one upper bound per clause.** With two symbolic lowers (or
///   uppers) the tightest is parameter-dependent (no `max`/`min` of symbolic
///   affines), so the interval is not a single `[L, U]` — indeterminate.
/// - **Both sides bounded.** A clause with only a lower (or only an upper) is an
///   unbounded interval; that is the single-bound shape owned by other passes —
///   indeterminate here (declined, never decided).
/// - **Constant width.** `U − L` must have *all* symbolic coefficients cancel to
///   a constant; otherwise the count is parameter-dependent — indeterminate.
/// - **Integer-valued endpoints.** Every coefficient *and* the constant of `L`
///   (equivalently `U`) must be an integer, so `L` lands on an integer at every
///   integer parameter assignment (translation-invariance) — otherwise
///   indeterminate.
/// - **No `x`-disequality, no symbolic `x`-free atom.** A clause carrying an
///   `x`-disequality (single-point hole) or a non-constant `x`-free atom (whose
///   truth depends on the parameters) is indeterminate.
/// - **No nested quantifier, non-linear `x`, or unsupported atom.** Inherited
///   from the shared DNF machinery (decline the whole assertion).
///
/// Soundness: every verdict is exact for the open constant-width-gap fragment,
/// and every shape outside it declines. Strictly additive — only ever turns an
/// `unknown` integer universal into a provably-correct `unsat` or `true`-rewrite.
pub fn eliminate_int_universal_open_gap(
    arena: &mut TermArena,
    assertion: TermId,
) -> Option<FmOutcome> {
    // Must be a top-level `∀x. body`.
    let (var, body) = match arena.node(assertion) {
        TermNode::App {
            op: Op::Forall(var),
            args,
        } => (*var, args[0]),
        _ => return None,
    };

    // `Sort::Int` only — the real path owns `Sort::Real`.
    if arena.symbol(var).1 != Sort::Int {
        return None;
    }

    // A nested quantifier under `∀x` is out of scope.
    if contains_quantifier(arena, body) {
        return None;
    }

    // Build the DNF of `¬φ`, relaxing Int atoms. Any non-linear `x`, unsupported
    // atom, or wide DNF declines the whole assertion.
    let dnf = dnf_of_negation(arena, body, /* relax_int = */ true)?;
    if dnf.is_empty() {
        // `¬φ` identically false ⇒ `∃x:Int. ¬φ` false ⇒ `∀x:Int. φ` valid.
        let t = arena.bool_const(true);
        return Some(FmOutcome::Rewrite(t));
    }
    if dnf.len() > MAX_DNF_CLAUSES {
        return None;
    }

    // Classify every clause's interval. `∃x:Int. ¬φ = ⋁_k (∃x:Int. clause_k)`:
    // - if ANY clause always contains an integer ⇒ the existential is true for
    //   all parameters ⇒ `∀x:Int. φ` false in every model ⇒ unsat;
    // - else if EVERY clause never contains an integer ⇒ the existential is false
    //   for all parameters ⇒ `∀x:Int. φ` valid ⇒ rewrite to `true`;
    // - else (some indeterminate clause, no always-contains) ⇒ decline.
    let mut all_never = true;
    for clause in &dnf {
        if clause.len() > MAX_CLAUSE_LITERALS {
            return None;
        }
        match clause_gap_content(var, clause) {
            GapContent::AlwaysContains => {
                // One clause always-contains is enough to force `unsat`.
                return Some(FmOutcome::Unsat);
            }
            GapContent::NeverContains => {}
            GapContent::Indeterminate => all_never = false,
        }
    }

    if all_never {
        // Every clause's interval never admits an integer ⇒ `∀x:Int. φ` valid.
        let t = arena.bool_const(true);
        Some(FmOutcome::Rewrite(t))
    } else {
        // Some clause could not be classified and none always-contained ⇒ decline.
        None
    }
}

/// The classification of one DNF clause's interval for the open constant-width
/// gap decision: whether its integer content is provably ≥ 1 for *every*
/// parameter assignment, provably 0 for every assignment, or indeterminate
/// (a shape outside the constant-width / integer-valued / single-bound-pair
/// fragment).
enum GapContent {
    /// The clause's interval admits an integer for every parameter assignment.
    AlwaysContains,
    /// The clause's interval admits no integer for any parameter assignment.
    NeverContains,
    /// Outside the decidable fragment — the whole assertion declines unless an
    /// always-contains clause overrides.
    Indeterminate,
}

/// Classifies one DNF clause's interval `[L, U]` over `x` (see [`GapContent`]).
///
/// Extracts the clause's lower/upper bounds (mirroring [`eliminate_clause`]) but
/// keeps the bounds as *symbolic* [`Affine`]s. It then requires the
/// constant-width-gap shape: exactly one lower and one upper bound, an
/// integer-valued lower endpoint, and a constant width `w = U − L`. From `w` and
/// the strictness it computes the (translation-invariant) integer content and
/// reports `AlwaysContains` (content ≥ 1) or `NeverContains` (content ≤ 0); any
/// shape outside the fragment is `Indeterminate`.
fn clause_gap_content(var: SymbolId, clause: &Clause) -> GapContent {
    // Symbolic lower/upper bounds (`x = bound` form) with strictness.
    let mut lowers: Vec<(Affine, bool)> = Vec::new();
    let mut uppers: Vec<(Affine, bool)> = Vec::new();

    for lit in clause {
        let a = lit.expr.coeff(var);
        if a.is_zero() {
            // `x`-free atom. Must be a concrete constant (its truth is otherwise
            // parameter-dependent). A non-constant residual ⇒ indeterminate.
            if !lit.expr.coeffs.values().all(|c| c.is_zero()) {
                return GapContent::Indeterminate;
            }
            let c = lit.expr.constant;
            let z = Rational::zero();
            let holds = match lit.rel {
                Rel::Lt => c < z,
                Rel::Le => c <= z,
                Rel::Eq => c == z,
                Rel::Ne => c != z,
            };
            if !holds {
                // `x`-free contradiction ⇒ the clause is empty ⇒ no integer.
                return GapContent::NeverContains;
            }
            continue;
        }

        // `x` appears: bound `x = -r/a`, keeping `r`'s symbolic part.
        let r = without_var(&lit.expr, var);
        let neg_inv_a = Rational::zero() - Rational::integer(1) / a;
        let bound = r.scale(neg_inv_a);
        let a_pos = a > Rational::zero();

        match lit.rel {
            Rel::Lt => {
                if a_pos {
                    uppers.push((bound, true));
                } else {
                    lowers.push((bound, true));
                }
            }
            Rel::Le => {
                if a_pos {
                    uppers.push((bound, false));
                } else {
                    lowers.push((bound, false));
                }
            }
            Rel::Eq => {
                // x = bound: a non-strict lower *and* upper.
                lowers.push((bound.clone(), false));
                uppers.push((bound, false));
            }
            // `x ≠ c`: a single-point hole, not a simple FM bound ⇒ indeterminate.
            Rel::Ne => return GapContent::Indeterminate,
        }
    }

    // The constant-width-gap shape needs exactly one lower and one upper bound:
    // with two symbolic lowers (or uppers) the tightest is parameter-dependent,
    // and an unbounded side is the single-bound shape owned by the other passes.
    if lowers.len() != 1 || uppers.len() != 1 {
        return GapContent::Indeterminate;
    }
    let (lo, lo_strict) = &lowers[0];
    let (up, up_strict) = &uppers[0];

    // The lower endpoint must be integer-valued for translation-invariance: every
    // coefficient *and* the constant of `lo` must be an integer.
    if !affine_is_integer_valued(lo) {
        return GapContent::Indeterminate;
    }

    // The width `w = U − L` must be a constant (all symbolic coefficients cancel).
    let width = up.sub(lo);
    if !width.coeffs.values().all(|c| c.is_zero()) {
        return GapContent::Indeterminate;
    }
    // With `lo` integer-valued and `up = lo + w`, `up` is integer-valued iff `w`
    // is an integer; a non-integer width admits no integer-valued translation
    // argument here ⇒ indeterminate (declined, never guessed).
    let w = width.constant;
    if !w.is_integer() {
        return GapContent::Indeterminate;
    }
    let w = w.numerator();

    // Translation-invariant integer content of `[L, U]` (`U − L = w` constant,
    // `L` integer-valued): admissible integers run from `L + [lo strict]` to
    // `L + w − [hi strict]`, a count of `w − [lo strict] − [hi strict] + 1`.
    let lo_adj = i128::from(*lo_strict);
    let hi_adj = i128::from(*up_strict);
    let content = w - lo_adj - hi_adj + 1;

    if content >= 1 {
        GapContent::AlwaysContains
    } else {
        GapContent::NeverContains
    }
}

/// Whether an affine `Σ cᵢ·sᵢ + k` is **integer-valued** at every integer
/// assignment of its symbols — i.e. every coefficient `cᵢ` and the constant `k`
/// is an integer. (Conversely, a non-integer coefficient `c` is witnessed by
/// setting its symbol to `1` and the rest to `0`, giving a non-integer value, so
/// this is exactly the integer-valued condition for integer parameters.)
fn affine_is_integer_valued(expr: &Affine) -> bool {
    expr.constant.is_integer() && expr.coeffs.values().all(|c| c.is_integer())
}

/// Decides, **exactly**, whether the integer existential `∃x:Int. ⋀ literals`
/// of one DNF clause holds — i.e. whether the clause's concrete real interval
/// `(Lmax, Umin)` contains an integer.
///
/// Returns:
/// - `Some(true)`  — the clause admits an integer `x`;
/// - `Some(false)` — the clause admits no integer (empty over `ℤ`, e.g. the
///   open hole `(0,1)` or a constant `x`-free contradiction);
/// - `None`        — **decline**: a bound or `x`-free atom has a *non-constant*
///   residual (another symbol survives), so the universal is *open* and the
///   integer-emptiness test does not apply.
///
/// The bound extraction mirrors [`eliminate_clause`], but instead of building
/// residual terms it requires every residual to be a concrete [`Rational`] and
/// runs the **integer** ceil/floor emptiness test:
///
/// - a lower bound `L` (rational) admits integers `x ≥ ceil(L)` (non-strict) or
///   `x ≥ floor(L)+1` (strict). The tightest lower over all lower bounds is the
///   max of these `lo_int`s; with no lower bound, `x` is unbounded below (`-∞`).
/// - an upper bound `U` admits integers `x ≤ floor(U)` (non-strict) or
///   `x ≤ ceil(U)−1` (strict). The tightest upper is the min of these
///   `hi_int`s; with no upper bound, `x` is unbounded above (`+∞`).
/// - the clause admits an integer iff `lo_int ≤ hi_int` (an unbounded side never
///   binds: `ℤ` is unbounded both ways, so a one-sided clause always has an
///   integer once its `x`-free atoms hold).
fn clause_has_integer(var: SymbolId, clause: &Clause) -> Option<bool> {
    // The tightest admissible integer lower (`None` ⇒ unbounded below) and upper
    // (`None` ⇒ unbounded above). Tracked as concrete `i128` integers.
    let mut lo_int: Option<i128> = None;
    let mut hi_int: Option<i128> = None;

    for lit in clause {
        let a = lit.expr.coeff(var);
        if a.is_zero() {
            // `x`-free atom: must be a concrete constant (closedness). A
            // non-constant residual ⇒ open universal ⇒ decline.
            if !lit.expr.coeffs.values().all(|c| c.is_zero()) {
                return None;
            }
            let c = lit.expr.constant;
            let z = Rational::zero();
            let holds = match lit.rel {
                Rel::Lt => c < z,
                Rel::Le => c <= z,
                Rel::Eq => c == z,
                Rel::Ne => c != z,
            };
            if !holds {
                // `x`-free contradiction ⇒ the clause is empty ⇒ no integer.
                return Some(false);
            }
            continue;
        }

        // `x` appears. Bound `x = -r/a`; `r` is the `x`-free part, which must be
        // a concrete constant for a closed universal.
        let r = without_var(&lit.expr, var);
        if !r.coeffs.values().all(|c| c.is_zero()) {
            // A symbolic residual on the bound ⇒ open universal ⇒ decline.
            return None;
        }
        let neg_inv_a = Rational::zero() - Rational::integer(1) / a;
        let bound = r.constant * neg_inv_a; // -r/a, a concrete rational
        let a_pos = a > Rational::zero();

        match lit.rel {
            Rel::Lt => {
                if a_pos {
                    tighten_upper(&mut hi_int, int_upper(bound, /* strict = */ true));
                } else {
                    tighten_lower(&mut lo_int, int_lower(bound, /* strict = */ true));
                }
            }
            Rel::Le => {
                if a_pos {
                    tighten_upper(&mut hi_int, int_upper(bound, /* strict = */ false));
                } else {
                    tighten_lower(&mut lo_int, int_lower(bound, /* strict = */ false));
                }
            }
            Rel::Eq => {
                // x = bound: a non-strict lower *and* upper.
                tighten_lower(&mut lo_int, int_lower(bound, false));
                tighten_upper(&mut hi_int, int_upper(bound, false));
            }
            // `x ≠ c`: a single-point hole, not a simple FM bound — decline.
            Rel::Ne => return None,
        }
    }

    // The clause admits an integer iff the tightest integer lower ≤ the tightest
    // integer upper. An unbounded side never binds (`ℤ` is unbounded both ways).
    Some(match (lo_int, hi_int) {
        (Some(lo), Some(hi)) => lo <= hi,
        // Unbounded below or above (or both) ⇒ an integer always exists.
        _ => true,
    })
}

/// The smallest integer admitted by a lower bound `x ⋈ bound` (`>` if `strict`,
/// else `≥`): `ceil(bound)` when non-strict, `floor(bound)+1` when strict.
fn int_lower(bound: Rational, strict: bool) -> i128 {
    if strict {
        // `x > bound` ⇒ smallest integer is `floor(bound) + 1`.
        rational_floor(bound).saturating_add(1)
    } else {
        // `x ≥ bound` ⇒ smallest integer is `ceil(bound)`.
        rational_ceil(bound)
    }
}

/// The largest integer admitted by an upper bound `x ⋈ bound` (`<` if `strict`,
/// else `≤`): `floor(bound)` when non-strict, `ceil(bound)−1` when strict.
fn int_upper(bound: Rational, strict: bool) -> i128 {
    if strict {
        // `x < bound` ⇒ largest integer is `ceil(bound) − 1`.
        rational_ceil(bound).saturating_sub(1)
    } else {
        // `x ≤ bound` ⇒ largest integer is `floor(bound)`.
        rational_floor(bound)
    }
}

/// Tightens the running integer lower bound (the **max** of admissible lowers).
fn tighten_lower(lo: &mut Option<i128>, candidate: i128) {
    *lo = Some(match *lo {
        None => candidate,
        Some(prev) => prev.max(candidate),
    });
}

/// Tightens the running integer upper bound (the **min** of admissible uppers).
fn tighten_upper(hi: &mut Option<i128>, candidate: i128) {
    *hi = Some(match *hi {
        None => candidate,
        Some(prev) => prev.min(candidate),
    });
}

/// `floor(r)` for a rational `r = num/den` with `den > 0`. Euclidean division
/// by the positive denominator yields the floor exactly.
fn rational_floor(r: Rational) -> i128 {
    r.numerator().div_euclid(r.denominator())
}

/// `ceil(r)` for a rational `r`. An integer is its own ceiling; otherwise
/// `ceil(r) = floor(r) + 1`.
fn rational_ceil(r: Rational) -> i128 {
    if r.is_integer() {
        r.numerator()
    } else {
        rational_floor(r).saturating_add(1)
    }
}

/// The shared FM elimination core for a top-level `∀x. body`. Computes the DNF
/// of `¬φ`, eliminates `x` from each clause over the reals, and returns the
/// sign-precise [`Verdict`]. With `relax_int`, the bound variable is treated as
/// a real and Int comparison/equality atoms are admitted (the integer
/// relaxation); otherwise only real atoms are in scope (the exact real path).
/// Returns `None` to decline for any shape outside the eliminable fragment.
fn eliminate_core(
    arena: &mut TermArena,
    var: SymbolId,
    body: TermId,
    relax_int: bool,
) -> Option<Verdict> {
    // A nested quantifier under `∀x` is out of scope.
    if contains_quantifier(arena, body) {
        return None;
    }

    // Build the DNF of `¬φ` as conjunctive clauses of linear literals in `x`.
    // Any non-linear `x`, out-of-scope atom, or unsupported connective makes
    // this `None` (decline).
    let dnf = dnf_of_negation(arena, body, relax_int)?;
    if dnf.is_empty() {
        // `¬φ` is identically false ⇒ `∃x. ¬φ` is false ⇒ `∀x. φ` is valid.
        return Some(Verdict::Valid);
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
        return Some(Verdict::Unsat);
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
        return Some(Verdict::Valid);
    }

    // `∃x. ¬φ` = OR(residuals); `χ = ∀x. φ = ¬(∃x. ¬φ)`.
    let exists_not_phi = fold_or(arena, &residuals)?;
    let chi = arena.not(exists_not_phi).ok()?;
    Some(Verdict::Rewrite(chi))
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
fn dnf_of_negation(arena: &TermArena, body: TermId, relax_int: bool) -> Option<Vec<Clause>> {
    dnf(arena, body, true, relax_int)
}

/// DNF of `body` (or `¬body` when `negate`), as `⋁ (⋀ literals)`. The empty
/// `Vec` (no clauses) denotes **false**; a clause with no literals denotes a
/// **true** conjunct. `relax_int` admits Int comparison/equality atoms (the
/// integer-relaxation path); see [`atom_literal`].
fn dnf(arena: &TermArena, body: TermId, negate: bool, relax_int: bool) -> Option<Vec<Clause>> {
    if let TermNode::App { op, args } = arena.node(body) {
        match op {
            Op::BoolNot => return dnf(arena, args[0], !negate, relax_int),
            // Constant `true`/`false` short-circuits.
            Op::BoolAnd if !negate => return dnf_conjunction(arena, args, false, relax_int),
            Op::BoolAnd if negate => return dnf_disjunction(arena, args, true, relax_int),
            Op::BoolOr if !negate => return dnf_disjunction(arena, args, false, relax_int),
            Op::BoolOr if negate => return dnf_conjunction(arena, args, true, relax_int),
            // `implies(a, b) ≡ ¬a ∨ b`; the helper desugars under `negate`.
            Op::BoolImplies if args.len() == 2 => {
                return dnf_implies(arena, args[0], args[1], negate, relax_int);
            }
            _ => {}
        }
    }
    // A leaf: try to read a `Bool` constant, else a linear atom literal.
    if let TermNode::BoolConst(b) = arena.node(body) {
        let truth = b ^ negate;
        return Some(if truth {
            vec![Vec::new()] // a single empty clause = true
        } else {
            Vec::new() // no clauses = false
        });
    }
    let lit = atom_literal(arena, body, negate, relax_int)?;
    Some(vec![vec![lit]])
}

/// DNF of `implies(a, b)` (or its negation). `implies(a,b) ≡ ¬a ∨ b`; under
/// `negate` we want `a ∧ ¬b`.
fn dnf_implies(
    arena: &TermArena,
    a: TermId,
    b: TermId,
    negate: bool,
    relax_int: bool,
) -> Option<Vec<Clause>> {
    if negate {
        // a ∧ ¬b
        let da = dnf(arena, a, false, relax_int)?;
        let dnb = dnf(arena, b, true, relax_int)?;
        cross_and(&da, &dnb)
    } else {
        // ¬a ∨ b
        let dna = dnf(arena, a, true, relax_int)?;
        let db = dnf(arena, b, false, relax_int)?;
        Some(union_clauses(dna, db))
    }
}

/// DNF of `⋀ args` (or, with `negate`, the *conjunction* arising from a negated
/// `or`): cross-product (AND) of the per-argument DNFs.
fn dnf_conjunction(
    arena: &TermArena,
    args: &[TermId],
    negate: bool,
    relax_int: bool,
) -> Option<Vec<Clause>> {
    // Start from `true` (single empty clause) and AND each argument in.
    let mut acc: Vec<Clause> = vec![Vec::new()];
    for &arg in args {
        let d = dnf(arena, arg, negate, relax_int)?;
        acc = cross_and(&acc, &d)?;
    }
    Some(acc)
}

/// DNF of `⋁ args` (or, with `negate`, the *disjunction* arising from a negated
/// `and`): union of the per-argument DNFs.
fn dnf_disjunction(
    arena: &TermArena,
    args: &[TermId],
    negate: bool,
    relax_int: bool,
) -> Option<Vec<Clause>> {
    let mut acc: Vec<Clause> = Vec::new();
    for &arg in args {
        let d = dnf(arena, arg, negate, relax_int)?;
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
fn atom_literal(arena: &TermArena, atom: TermId, negate: bool, relax_int: bool) -> Option<Literal> {
    let TermNode::App { op, args } = arena.node(atom) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (lhs, rhs) = (args[0], args[1]);
    // Real comparisons / real equalities are always in scope. Under the integer
    // relaxation, the Int order comparisons and Int equalities are *also* in
    // scope (treated over the reals): `Int ⊆ Real`, so a real-valid `∀x:Real. φ`
    // implies the integer universal — the only verdict the relaxation acts on.
    let is_real_cmp = matches!(op, Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe);
    let is_real_eq = matches!(op, Op::Eq) && arena.sort_of(lhs) == Sort::Real;
    let is_int_cmp = relax_int && matches!(op, Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe);
    let is_int_eq = relax_int && matches!(op, Op::Eq) && arena.sort_of(lhs) == Sort::Int;
    if !is_real_cmp && !is_real_eq && !is_int_cmp && !is_int_eq {
        return None;
    }
    let left = affine(arena, lhs)?;
    let right = affine(arena, rhs)?;

    // Build `expr` and base relation so the atom is `expr ⋈ 0` (pre-negation).
    // The Int and Real order/equality ops share the same affine normalization
    // (the relaxation treats Int atoms over the reals).
    let (expr, rel) = match op {
        Op::RealLt | Op::IntLt => (left.sub(&right), Rel::Lt), // a - b < 0
        Op::RealLe | Op::IntLe => (left.sub(&right), Rel::Le), // a - b ≤ 0
        Op::RealGt | Op::IntGt => (right.sub(&left), Rel::Lt), // b - a < 0
        Op::RealGe | Op::IntGe => (right.sub(&left), Rel::Le), // b - a ≤ 0
        Op::Eq => (left.sub(&right), Rel::Eq),                 // a - b = 0
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The closed integer path must **decline** an *open* universal — one whose
    /// FM bounds carry a free symbol — because its exact integer-emptiness test
    /// applies only to concrete rational endpoints. This is checked directly
    /// (returns `None`) rather than end-to-end through `solve`, whose downstream
    /// quantifier search does not terminate quickly on this shape.
    #[test]
    fn closed_path_declines_open_disjunctive_universal() {
        // ∀x:Int. (x ≤ y ∨ x ≥ y + 1) with a FREE integer `y`: an open universal
        // (symbolic bounds `y`, `y+1`) ⇒ the closed path declines (`None`).
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let one = arena.int_const(1);
        let y_plus_1 = arena.int_add(yv, one).unwrap();
        let le_y = arena.int_le(xv, yv).unwrap();
        let ge_y1 = arena.int_ge(xv, y_plus_1).unwrap();
        let body = arena.or(le_y, ge_y1).unwrap();
        let forall = arena.forall(x, body).unwrap();
        assert!(
            eliminate_int_universal_closed(&mut arena, forall).is_none(),
            "open universal (symbolic bounds) must DECLINE the closed path"
        );
    }

    /// The closed path also declines an open *single-atom* universal — a
    /// symbolic bound on a lone comparison — for the same reason.
    #[test]
    fn closed_path_declines_open_single_atom_universal() {
        // ∀x:Int. x ≤ y with a free `y`: symbolic upper bound ⇒ decline.
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let y = arena.declare("y", Sort::Int).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let body = arena.int_le(xv, yv).unwrap();
        let forall = arena.forall(x, body).unwrap();
        assert!(eliminate_int_universal_closed(&mut arena, forall).is_none());
    }

    /// A *closed* gap universal `∀x:Int. (x ≤ 0 ∨ x ≥ 1)` is decided exactly:
    /// no integer lies in the real hole `(0,1)`, so the closed path rewrites the
    /// assertion to the constant `true`.
    #[test]
    fn closed_path_rewrites_gap_universal_to_true() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let le0 = arena.int_le(xv, zero).unwrap();
        let ge1 = arena.int_ge(xv, one).unwrap();
        let body = arena.or(le0, ge1).unwrap();
        let forall = arena.forall(x, body).unwrap();
        match eliminate_int_universal_closed(&mut arena, forall) {
            Some(FmOutcome::Rewrite(t)) => {
                assert!(matches!(arena.node(t), TermNode::BoolConst(true)));
            }
            other => panic!("expected Rewrite(true), got {other:?}"),
        }
    }

    /// A *closed* universal whose negation's hole contains an integer
    /// (`∀x:Int. (x ≤ 0 ∨ x ≥ 2)`, hole `(0,2)` ∋ 1) is decided **unsat**.
    #[test]
    fn closed_path_decides_hole_with_integer_unsat() {
        let mut arena = TermArena::new();
        let x = arena.declare("x", Sort::Int).unwrap();
        let xv = arena.var(x);
        let zero = arena.int_const(0);
        let two = arena.int_const(2);
        let le0 = arena.int_le(xv, zero).unwrap();
        let ge2 = arena.int_ge(xv, two).unwrap();
        let body = arena.or(le0, ge2).unwrap();
        let forall = arena.forall(x, body).unwrap();
        assert!(matches!(
            eliminate_int_universal_closed(&mut arena, forall),
            Some(FmOutcome::Unsat)
        ));
    }

    /// Integer ceil/floor of rational endpoints, with strictness.
    #[test]
    fn integer_endpoint_rounding_is_exact() {
        // floor / ceil on a non-integer rational 1/2.
        let half = Rational::new(1, 2);
        assert_eq!(rational_floor(half), 0);
        assert_eq!(rational_ceil(half), 1);
        // negative non-integer -3/2: floor = -2, ceil = -1.
        let neg = Rational::new(-3, 2);
        assert_eq!(rational_floor(neg), -2);
        assert_eq!(rational_ceil(neg), -1);
        // an integer is its own floor and ceil.
        let two = Rational::integer(2);
        assert_eq!(rational_floor(two), 2);
        assert_eq!(rational_ceil(two), 2);
        // lower bound: `x ≥ 1/2` admits ceil = 1; `x > 1/2` admits floor+1 = 1.
        assert_eq!(int_lower(half, false), 1);
        assert_eq!(int_lower(half, true), 1);
        // `x ≥ 1` admits 1; `x > 1` admits 2 (floor(1)+1).
        let one = Rational::integer(1);
        assert_eq!(int_lower(one, false), 1);
        assert_eq!(int_lower(one, true), 2);
        // upper bound: `x ≤ 1/2` admits floor = 0; `x < 1/2` admits ceil-1 = 0.
        assert_eq!(int_upper(half, false), 0);
        assert_eq!(int_upper(half, true), 0);
        // `x ≤ 1` admits 1; `x < 1` admits 0 (ceil(1)-1).
        assert_eq!(int_upper(one, false), 1);
        assert_eq!(int_upper(one, true), 0);
    }
}
