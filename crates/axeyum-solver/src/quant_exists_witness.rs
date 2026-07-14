//! Bounded `∀∃` decision by Skolem-witness synthesis (sat-side, one-directional).
//!
//! The infinite-domain quantifier fallbacks ([`crate::prove_unsat_by_instantiation`]
//! / MBQI / e-matching) can only ever conclude `unsat`/`unknown`, and the
//! sat-side universal passes ([`crate::quant_valid_universal`],
//! [`crate::quant_vacuous_universal`]) decide only *standalone* universals. None
//! of them handles a genuine **∀∃** query such as
//!
//! ```text
//! ∀x:Int. ∃z:Int. z > x
//! ```
//!
//! which is **satisfiable** (pick `z := x + 1`) but comes back `unknown`. This
//! pass closes that gap for a restricted, soundly-decidable class.
//!
//! ## The math (sound, ONE-DIRECTIONAL — `sat` only)
//!
//! A query with a leading `∀` prefix and one supported positive existential —
//! either prenex `∃z. body` or a direct `guard ∨ ∃z. body` (ADR-0098) — is
//! **satisfiable** if there is a Skolem witness `z = g(x⃗)` (a term over the
//! universals only) such that
//!
//! ```text
//! ∀x⃗. body(x⃗, g(x⃗))   is VALID,
//! ```
//!
//! because then `z := g(x⃗)` witnesses `∃z` for *every* `x⃗`, so the original
//! formula holds in every model. This is sound **one-directionally**: a *found*
//! witness ⇒ `sat`; *no* witness ⇒ **decline** (`Unknown`), never `unsat`. A
//! query we cannot witness might still be satisfiable by a cleverer `g` (or
//! unsatisfiable), so the only verdict this pass may act on is `sat`.
//!
//! ## Witness synthesis
//!
//! The witness is read off the comparison atoms that *bound* `z`. In each atom
//! mentioning `z`, the body is linearized; `z` must appear with net coefficient
//! exactly `±1` (so the rearranged bound is a clean term — `2·z > x` is
//! declined), and the remainder `t(x⃗)` must be `z`-free. From a single bound:
//!
//! - lower bound `z > t` ⇒ candidate `g = t + 1`; `z ≥ t` ⇒ `g = t`;
//! - upper bound `z < t` ⇒ `g = t − 1`; `z ≤ t` ⇒ `g = t`;
//! - equality `z = t` ⇒ `g = t`.
//!
//! When `z` is bounded *both* ways the simplest candidates (`a + 1`, `a`, `b − 1`,
//! `b`, …) are tried in turn. Every candidate is **verified** by the validity
//! check above; the synthesis only proposes, the check decides, so a wrong
//! proposal can never yield a wrong verdict — it merely fails to validate and the
//! next candidate (or a decline) follows.
//!
//! Any `z` occurrence the linearizer cannot account for with coefficient `±1` —
//! a non-linear product, a `div`/`mod`, a uninterpreted-function argument, an
//! array index, … — makes the query **decline**.
//!
//! ## Validity check (and its termination)
//!
//! `∀x⃗. body[z := g]` is valid iff `¬(body[z := g])[x⃗ := c⃗]` is **unsat** for
//! fresh uninterpreted constants `c⃗` (one per universal) — exactly the
//! universal-closure validity check of [`crate::quant_valid_universal`]. The
//! negated, substituted body is quantifier-free, so it is decided by the
//! quantifier-free front door [`crate::check_auto`], which never re-enters the
//! quantifier path: there is exactly one bounded QF solve per candidate, so the
//! pass terminates.
//!
//! ## Soundness summary
//!
//! Only an otherwise-`unknown` verdict is ever turned into `sat`, and only for a
//! **validated** witness. A candidate whose validity check returns `sat`/`unknown`
//! (not `unsat`) is *not* a witness; the pass tries the next candidate and then
//! declines. It never concludes `unsat` and never produces a wrong `sat`.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_ir::{Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::quant_sat_cert::affine_skolem_witness;
use crate::{Model, QuantifiedSkolemSatCertificate, check_quantified_skolem_sat};

/// Decides a supported `∀x⃗. ∃z. body` or positive `∀x⃗. guard ∨ ∃z. body`
/// query by synthesizing and validating a Skolem witness for `z`.
///
/// Returns `Ok(Some(CheckResult::Sat(_)))` when *exactly one* assertion is such a
/// query and a witness `g(x⃗)` is found whose universal closure `∀x⃗. body[z := g]`
/// validates; `Ok(None)` to **decline** in every other case (a different shape,
/// more than one assertion, `z` outside the clean `±1`-coefficient linear fragment,
/// or no candidate that validates). A decline is sound: the caller proceeds to the
/// existing quantifier fallbacks. This pass *never* returns `unsat`.
///
/// The returned model carries a typed Skolem certificate. The certificate is
/// independently checked against the original quantified assertion; a validated
/// search candidate that the small checker cannot prove is declined.
///
/// # Errors
///
/// Returns [`SolverError`] only from an internal IR builder failure or the QF
/// validity sub-solve; a candidate that does not validate is *not* an error.
pub fn decide_forall_exists_by_witness(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    // This shape is a single quantified assertion. With multiple assertions the
    // witness for one must still satisfy the rest, which this pass does not check,
    // so it declines (the existing path handles the conjunction).
    if assertions.len() != 1 {
        return Ok(None);
    }
    decide_single(arena, assertions[0], config)
}

/// Decides one assertion if it has a supported `∀*`/positive-`∃` shape.
fn decide_single(
    arena: &mut TermArena,
    assertion: TermId,
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    let original_term_count = arena.len();
    // Peel the leading `∀` prefix.
    let mut universals: Vec<SymbolId> = Vec::new();
    let mut cursor = assertion;
    while let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(cursor)
    {
        universals.push(*var);
        cursor = args[0];
    }
    // There must be at least one universal (a bare `∃z. body` is the standalone
    // existential the top-level skolemizer already handles).
    if universals.is_empty() {
        return Ok(None);
    }

    // Then either one prenex `∃z.body`, or one direct positive
    // `guard ∨ ∃z.body` (ADR-0098). The latter is pulled only for untrusted
    // search; the certificate checker independently re-matches the original.
    let Some((z, body)) = extract_witness_problem(arena, cursor) else {
        return Ok(None);
    };
    if universals.contains(&z) {
        return Ok(None);
    }

    // Arithmetic synthesis covers `Int`/`Real`; ADR-0141 additionally permits
    // an exact same-width source term over only the leading BV universals.
    let z_sort = arena.symbol(z).1;
    if !matches!(z_sort, Sort::Int | Sort::Real | Sort::BitVec(_)) {
        return Ok(None);
    }

    // The body must be quantifier-free: a further quantifier would make the
    // validity sub-check itself quantified (and could shadow `z`/`x⃗`).
    if contains_quantifier(arena, body) {
        return Ok(None);
    }

    // Identity witnesses are common nested-QE results. Try each same-sort
    // universal directly; the separate checker accepts only when substitution
    // makes the body a reflexive/affine tautology.
    for &universal in &universals {
        if arena.symbol(universal).1 != z_sort {
            continue;
        }
        let witness = arena.var(universal);
        let Some(witness) = affine_skolem_witness(arena, witness, original_term_count) else {
            continue;
        };
        let cert = QuantifiedSkolemSatCertificate {
            assertion,
            universals: universals.clone(),
            existential: z,
            witness,
        };
        if check_quantified_skolem_sat(arena, assertion, &cert) {
            return Ok(Some(CheckResult::Sat(certified_model(cert))));
        }
    }

    // ADR-0141 source-term witnesses are extracted only from the opposite side
    // of an exact equality or non-strict BV order atom that directly names the
    // existential. Search merely proposes the existing term. The certificate
    // checker independently enforces original-arena membership, sort, binder
    // scope, and exact-source substitution before reflexivity can grant SAT.
    if matches!(z_sort, Sort::BitVec(_)) {
        for candidate in bv_source_term_candidates(arena, body, z, z_sort) {
            let Some(witness) = affine_skolem_witness(arena, candidate, original_term_count)
            else {
                continue;
            };
            let cert = QuantifiedSkolemSatCertificate {
                assertion,
                universals: universals.clone(),
                existential: z,
                witness,
            };
            if check_quantified_skolem_sat(arena, assertion, &cert) {
                return Ok(Some(CheckResult::Sat(certified_model(cert))));
            }
        }
        return Ok(None);
    }

    // Collect the atoms that bound `z`. EVERY occurrence of `z` in the body must
    // sit in an analyzable arithmetic atom with `z`-coefficient `±1`; any other
    // occurrence (non-linear, UF argument, …) makes the whole query decline.
    let Some(bounds) = collect_z_bounds(arena, body, z) else {
        return Ok(None);
    };
    // No bounding atom at all means `z` does not occur — not the `∀∃z.…(z)` shape
    // this pass targets (and the existential is vacuous; leave it to other passes).
    if bounds.is_empty() {
        return Ok(None);
    }

    // Propose candidate witnesses `g(x⃗)` from the bounds, simplest first.
    let candidates = synthesize_candidates(arena, &bounds, z_sort)?;
    if candidates.is_empty() {
        return Ok(None);
    }

    // Verify each candidate: `∀x⃗. body[z := g]` valid ⇒ original is `sat`.
    for g in candidates {
        if witness_validates(arena, body, z, g, &universals, config)? {
            let Some(witness) = affine_skolem_witness(arena, g, original_term_count) else {
                continue;
            };
            let cert = QuantifiedSkolemSatCertificate {
                assertion,
                universals: universals.clone(),
                existential: z,
                witness,
            };
            if check_quantified_skolem_sat(arena, assertion, &cert) {
                return Ok(Some(CheckResult::Sat(certified_model(cert))));
            }
        }
    }

    // No candidate validated: decline (never `unsat`).
    Ok(None)
}

/// Returns deterministic exact-source BV witness candidates.
///
/// Only a direct occurrence of the existential as one operand of equality or
/// non-strict signed/unsigned order contributes the opposite operand. The
/// independent certificate checker owns all semantic admission; in particular,
/// candidates containing the existential, a free symbol, a nested quantifier,
/// or the wrong sort fail closed there.
fn bv_source_term_candidates(
    arena: &mut TermArena,
    body: TermId,
    existential: SymbolId,
    sort: Sort,
) -> Vec<TermId> {
    let existential_term = arena.var(existential);
    let mut candidates = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        if matches!(op, Op::Eq | Op::BvSle | Op::BvUle)
            && let [left, right] = &**args
        {
            if *left == existential_term && arena.sort_of(*right) == sort {
                candidates.insert(*right);
            }
            if *right == existential_term && arena.sort_of(*left) == sort {
                candidates.insert(*left);
            }
        }
        stack.extend(args.iter().copied());
    }
    candidates.into_iter().collect()
}

/// Extracts the quantifier-free body used by witness search.
///
/// Pulling `exists z` through `or` is sound only in positive position, when the
/// other child does not mention `z`, and because the supported Int/Real domains
/// are nonempty. This helper deliberately recognizes no other Boolean context.
fn extract_witness_problem(arena: &mut TermArena, term: TermId) -> Option<(SymbolId, TermId)> {
    if let TermNode::App {
        op: Op::Exists(z),
        args,
    } = arena.node(term)
    {
        let [body] = &**args else {
            return None;
        };
        return (!contains_quantifier(arena, *body)).then_some((*z, *body));
    }

    let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let (left, right) = (*left, *right);
    extract_exists_or_side(arena, left, right, true)
        .or_else(|| extract_exists_or_side(arena, right, left, false))
}

fn extract_exists_or_side(
    arena: &mut TermArena,
    exists_side: TermId,
    guard: TermId,
    exists_first: bool,
) -> Option<(SymbolId, TermId)> {
    let TermNode::App {
        op: Op::Exists(z),
        args,
    } = arena.node(exists_side)
    else {
        return None;
    };
    let [inner] = &**args else {
        return None;
    };
    let (z, inner) = (*z, *inner);
    if contains_quantifier(arena, guard)
        || contains_quantifier(arena, inner)
        || occurs(arena, guard, z)
    {
        return None;
    }
    let combined = if exists_first {
        arena.or(inner, guard).ok()?
    } else {
        arena.or(guard, inner).ok()?
    };
    Some((z, combined))
}

fn certified_model(cert: QuantifiedSkolemSatCertificate) -> Model {
    let mut model = Model::new();
    model.set_quantified_sat_certificate(cert);
    model
}

/// A comparison relation between `z` and a `z`-free bound term `t`, as recovered
/// from a body atom after isolating `z` (coefficient `±1`).
#[derive(Clone, Copy)]
enum Bound {
    /// `z > t`.
    Gt(TermId),
    /// `z ≥ t`.
    Ge(TermId),
    /// `z < t`.
    Lt(TermId),
    /// `z ≤ t`.
    Le(TermId),
    /// `z = t`.
    Eq(TermId),
}

/// Walks the Boolean structure of `body` collecting every atom that bounds `z`.
///
/// Returns `Some(bounds)` when **every** occurrence of `z` is inside an arithmetic
/// comparison/equality atom whose net `z`-coefficient is exactly `±1` and whose
/// remainder is `z`-free (so the atom rearranges to a clean `z ⋈ t`); `None` to
/// decline when `z` appears anywhere the affine analysis cannot isolate it with
/// coefficient `±1`.
fn collect_z_bounds(arena: &mut TermArena, body: TermId, z: SymbolId) -> Option<Vec<Bound>> {
    let mut bounds = Vec::new();
    if collect_node(arena, body, z, &mut bounds) {
        Some(bounds)
    } else {
        None
    }
}

/// Recursive bound collection at one node. Returns `false` (decline) on any `z`
/// occurrence that is not a clean `±1`-coefficient arithmetic atom.
fn collect_node(arena: &mut TermArena, term: TermId, z: SymbolId, out: &mut Vec<Bound>) -> bool {
    // A `z`-free subtree contributes no bound and is always fine.
    if !occurs(arena, term, z) {
        return true;
    }
    let TermNode::App { op, args } = arena.node(term).clone() else {
        // A bare `Symbol(z)` in a Boolean position cannot occur (z is Int/Real);
        // any other leaf does not contain z (short-circuited above).
        return false;
    };
    match op {
        // Boolean connectives: recurse to the atoms.
        Op::BoolNot | Op::BoolAnd | Op::BoolOr | Op::BoolImplies | Op::BoolXor => {
            args.iter().all(|&a| collect_node(arena, a, z, out))
        }
        // Arithmetic comparison / equality atoms — the only place `z` may appear.
        Op::Eq
        | Op::IntLt
        | Op::IntLe
        | Op::IntGt
        | Op::IntGe
        | Op::RealLt
        | Op::RealLe
        | Op::RealGt
        | Op::RealGe => bound_from_atom(arena, op, &args, z, out),
        // Any other operator carrying `z` (UF apply, array, BV, `ite`, non-linear
        // product, `div`/`mod`, …) is not cleanly isolable: decline.
        _ => false,
    }
}

/// Recovers a [`Bound`] (`z ⋈ t`) from a single arithmetic atom, appending it to
/// `out`. Returns `false` if the atom does not isolate `z` with coefficient `±1`.
fn bound_from_atom(
    arena: &mut TermArena,
    op: Op,
    args: &[TermId],
    z: SymbolId,
    out: &mut Vec<Bound>,
) -> bool {
    if args.len() != 2 {
        return false;
    }
    let (lhs, rhs) = (args[0], args[1]);
    // `Eq` over a non-arithmetic sort that still carries `z` is not isolable.
    let sort = arena.sort_of(lhs);
    if !matches!(sort, Sort::Int | Sort::Real) {
        return false;
    }
    // Linearize `lhs - rhs` into `coeff_z·z + remainder(x⃗)`.
    let Some(left) = affine(arena, lhs, z) else {
        return false;
    };
    let Some(right) = affine(arena, rhs, z) else {
        return false;
    };
    // An `i128` overflow forming `lhs − rhs` ⇒ not cleanly isolable (decline).
    let Some(diff) = left.sub(&right) else {
        return false;
    };
    let cz = diff.coeff(z);
    // `z` must appear with net coefficient exactly `±1`.
    let one = Rational::integer(1);
    let neg_one = Rational::integer(-1);
    let positive = if cz == one {
        true
    } else if cz == neg_one {
        false
    } else {
        return false;
    };

    // Canonicalize the source operator to a relation `lhs REL rhs`, i.e.
    // `diff REL 0` (since diff = lhs − rhs).
    let Some(rel) = Rel::from_op(op) else {
        return false;
    };

    // The remainder `r = diff − cz·z` is the `z`-free part. The atom is
    // `cz·z + r REL 0`. Rearrange to `z REL' t`:
    //   cz = +1 :  z + r REL 0  ⟺  z REL (−r)       (relation kept)
    //   cz = −1 : −z + r REL 0  ⟺  z REL.flip() r   (relation flipped)
    let mut remainder = diff.clone();
    remainder.coeffs.remove(&z);
    let (rel, r) = if positive {
        // Negating the remainder can overflow ⇒ decline.
        let Some(neg) = remainder.neg() else {
            return false;
        };
        (rel, neg)
    } else {
        (rel.flip(), remainder)
    };
    let Some(t) = affine_to_term(arena, &r, sort) else {
        return false;
    };
    out.push(rel.into_bound(t));
    true
}

/// A canonical comparison relation `z REL t`, with the `Eq` case for `=`.
#[derive(Clone, Copy)]
enum Rel {
    Lt,
    Le,
    Gt,
    Ge,
    Eq,
}

impl Rel {
    /// Maps a body comparison operator to its canonical relation; `None` for any
    /// non-comparison operator.
    fn from_op(op: Op) -> Option<Self> {
        Some(match op {
            Op::IntLt | Op::RealLt => Self::Lt,
            Op::IntLe | Op::RealLe => Self::Le,
            Op::IntGt | Op::RealGt => Self::Gt,
            Op::IntGe | Op::RealGe => Self::Ge,
            Op::Eq => Self::Eq,
            _ => return None,
        })
    }

    /// The relation with its two sides swapped (`a < b` ⟺ `b > a`), used when the
    /// `z`-coefficient is `−1` so the atom `−z + r REL 0` becomes `z REL.flip() r`.
    fn flip(self) -> Self {
        match self {
            Self::Lt => Self::Gt,
            Self::Le => Self::Ge,
            Self::Gt => Self::Lt,
            Self::Ge => Self::Le,
            Self::Eq => Self::Eq,
        }
    }

    /// The [`Bound`] `z REL t`.
    fn into_bound(self, t: TermId) -> Bound {
        match self {
            Self::Lt => Bound::Lt(t),
            Self::Le => Bound::Le(t),
            Self::Gt => Bound::Gt(t),
            Self::Ge => Bound::Ge(t),
            Self::Eq => Bound::Eq(t),
        }
    }
}

/// Proposes candidate witnesses `g(x⃗)` from the collected bounds, simplest first.
///
/// Each [`Bound`] suggests the witness that makes its atom hold (`z > t` ⇒ `t + 1`,
/// `z ≤ t` ⇒ `t`, …). Every proposal is later verified, so over-generating is safe
/// — a candidate that does not satisfy the *other* atoms simply fails validation.
fn synthesize_candidates(
    arena: &mut TermArena,
    bounds: &[Bound],
    sort: Sort,
) -> Result<Vec<TermId>, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut out: Vec<TermId> = Vec::new();
    let mut push = |arena: &mut TermArena, t: TermId| -> Result<(), SolverError> {
        if !out.contains(&t) {
            out.push(t);
        }
        let _ = arena;
        Ok(())
    };
    for &b in bounds {
        match b {
            // `z = t`, `z ≥ t`, and `z ≤ t` are all witnessed by `g = t` itself.
            Bound::Eq(t) | Bound::Ge(t) | Bound::Le(t) => push(arena, t)?,
            Bound::Gt(t) => {
                let plus = add_one(arena, t, sort).map_err(err)?;
                push(arena, plus)?;
            }
            Bound::Lt(t) => {
                let minus = sub_one(arena, t, sort).map_err(err)?;
                push(arena, minus)?;
            }
        }
    }
    Ok(out)
}

/// `t + 1` at `sort`.
fn add_one(arena: &mut TermArena, t: TermId, sort: Sort) -> Result<TermId, axeyum_ir::IrError> {
    match sort {
        Sort::Int => {
            let one = arena.int_const(1);
            arena.int_add(t, one)
        }
        Sort::Real => {
            let one = arena.real_const(Rational::integer(1));
            arena.real_add(t, one)
        }
        _ => unreachable!("witness sort guarded to Int/Real"),
    }
}

/// `t − 1` at `sort`.
fn sub_one(arena: &mut TermArena, t: TermId, sort: Sort) -> Result<TermId, axeyum_ir::IrError> {
    match sort {
        Sort::Int => {
            let one = arena.int_const(1);
            arena.int_sub(t, one)
        }
        Sort::Real => {
            let one = arena.real_const(Rational::integer(1));
            arena.real_sub(t, one)
        }
        _ => unreachable!("witness sort guarded to Int/Real"),
    }
}

/// Verifies the witness `g` for `z`: substitutes `z := g` in `body`, then checks
/// `∀x⃗. body[z := g]` is **valid** via the universal-closure check (fresh
/// constants for `x⃗`, then `¬(body[z:=g])[x⃗:=c⃗]` must be `unsat`).
///
/// Returns `true` only on a *definitive* `unsat` of the negated, substituted body
/// (⇒ the universal is valid ⇒ the original `∀∃` is `sat`). A `sat`/`unknown`
/// validity result returns `false` (this candidate is not a witness).
fn witness_validates(
    arena: &mut TermArena,
    body: TermId,
    z: SymbolId,
    g: TermId,
    universals: &[SymbolId],
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    // body[z := g].
    let mut zmap: HashMap<TermId, TermId> = HashMap::new();
    let zvar = arena.var(z);
    zmap.insert(zvar, g);
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let substituted = replace_subterms(arena, body, &zmap, &mut memo).map_err(err)?;

    // Universal-closure validity: replace each universal with a fresh constant.
    let mut umap: HashMap<TermId, TermId> = HashMap::new();
    for (k, &u) in universals.iter().enumerate() {
        let sort = arena.symbol(u).1;
        let name = format!("!few_{k}");
        let c = arena.declare_internal(&name, sort).map_err(err)?;
        umap.insert(arena.var(u), arena.var(c));
    }
    let mut umemo: HashMap<TermId, TermId> = HashMap::new();
    let instance = replace_subterms(arena, substituted, &umap, &mut umemo).map_err(err)?;

    // `∀x⃗. body[z:=g]` valid ⟺ `¬instance` unsat. The negated body is
    // quantifier-free, so `check_auto` decides it without re-entering this path.
    let negated = arena.not(instance).map_err(err)?;
    Ok(matches!(
        check_auto(arena, &[negated], config)?,
        CheckResult::Unsat
    ))
}

/// An affine expression `Σ coeff_i · symbol_i + Σ coeff_j · opaque_j + constant`.
///
/// `coeffs` carries the symbol leaves (including `z`, whose coefficient drives the
/// bound extraction); `opaque` carries `z`-free non-arithmetic-structure subterms
/// (a UF application, a `div`, …) keyed by their source [`TermId`], so the bound
/// term `t` can be reconstructed faithfully when it mentions such subterms.
#[derive(Clone)]
struct Affine {
    coeffs: BTreeMap<SymbolId, Rational>,
    opaque: BTreeMap<TermId, Rational>,
    constant: Rational,
}

impl Affine {
    fn constant(value: Rational) -> Self {
        Self {
            coeffs: BTreeMap::new(),
            opaque: BTreeMap::new(),
            constant: value,
        }
    }

    fn symbol(sym: SymbolId) -> Self {
        let mut coeffs = BTreeMap::new();
        coeffs.insert(sym, Rational::integer(1));
        Self {
            coeffs,
            opaque: BTreeMap::new(),
            constant: Rational::zero(),
        }
    }

    /// A single `z`-free opaque subterm with coefficient `1`.
    fn opaque_term(term: TermId) -> Self {
        let mut opaque = BTreeMap::new();
        opaque.insert(term, Rational::integer(1));
        Self {
            coeffs: BTreeMap::new(),
            opaque,
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
        let mut opaque = BTreeMap::new();
        for (&t, &c) in &self.opaque {
            opaque.insert(t, c.checked_neg()?);
        }
        Some(Self {
            coeffs,
            opaque,
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
        let mut opaque = self.opaque.clone();
        for (&t, &c) in &other.opaque {
            let entry = opaque.entry(t).or_insert_with(Rational::zero);
            *entry = entry.checked_add(c)?;
        }
        Some(Self {
            coeffs,
            opaque,
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
        let mut opaque = BTreeMap::new();
        for (&t, &c) in &self.opaque {
            opaque.insert(t, c.checked_mul(factor)?);
        }
        Some(Self {
            coeffs,
            opaque,
            constant: self.constant.checked_mul(factor)?,
        })
    }
}

/// Linearizes `term` (`Int`/`Real`-sorted) into an [`Affine`] form, or `None` if it
/// is not a purely affine expression in which the existential variable `z` is fully
/// accounted for.
///
/// Handled: int/real constants, symbols (opaque leaves with coefficient `1`), `+`,
/// `-` (binary and unary), `*` only when one operand is a constant (linear scaling),
/// and the transparent `Int → Real` embedding. Returns `None` for any construct
/// under which `z` could hide unaccounted (a product of two non-constants,
/// `div`/`mod`/`abs`, a UF application, a `select`, …).
fn affine(arena: &TermArena, term: TermId, z: SymbolId) -> Option<Affine> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(Affine::constant(Rational::integer(*value))),
        TermNode::RealConst(value) => Some(Affine::constant(*value)),
        TermNode::Symbol(sym) => Some(Affine::symbol(*sym)),
        TermNode::App { op, args } => match op {
            Op::IntAdd | Op::RealAdd => {
                let a = affine(arena, args[0], z)?;
                let b = affine(arena, args[1], z)?;
                a.add(&b)
            }
            Op::IntSub | Op::RealSub => {
                let a = affine(arena, args[0], z)?;
                let b = affine(arena, args[1], z)?;
                a.sub(&b)
            }
            Op::IntNeg | Op::RealNeg => {
                let a = affine(arena, args[0], z)?;
                a.neg()
            }
            Op::IntMul | Op::RealMul => {
                let a = affine(arena, args[0], z)?;
                let b = affine(arena, args[1], z)?;
                if a.coeffs.is_empty() {
                    b.scale(a.constant)
                } else if b.coeffs.is_empty() {
                    a.scale(b.constant)
                } else {
                    None
                }
            }
            Op::IntToReal => affine(arena, args[0], z),
            // Opaque construct: only safe if it does not hide `z`.
            _ => {
                if occurs(arena, term, z) {
                    None
                } else {
                    Some(Affine::opaque_term(term))
                }
            }
        },
        _ => {
            if occurs(arena, term, z) {
                None
            } else {
                Some(Affine::opaque_term(term))
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

/// Reconstructs a [`TermId`] for the affine form `Σ coeff_i · symbol_i + constant`
/// at `sort`, or `None` if a coefficient/constant is not integral for an `Int`-sort
/// result (an `Int` witness term cannot carry a fractional coefficient).
///
/// The witness this builds is only ever *proposed*; the validity check is the
/// safety net, so any reconstruction that does not denote the intended bound simply
/// fails to validate. We nonetheless build it faithfully from the linear algebra.
fn affine_to_term(arena: &mut TermArena, a: &Affine, sort: Sort) -> Option<TermId> {
    match sort {
        Sort::Int => {
            // Every coefficient and the constant must be integral.
            for c in a.coeffs.values() {
                if !c.is_integer() {
                    return None;
                }
            }
            if !a.constant.is_integer() {
                return None;
            }
            let mut acc: Option<TermId> = None;
            for (&sym, &c) in &a.coeffs {
                if c.is_zero() {
                    continue;
                }
                let var = arena.var(sym);
                let coeff = arena.int_const(c.numerator());
                let term = arena.int_mul(coeff, var).ok()?;
                acc = Some(match acc {
                    Some(prev) => arena.int_add(prev, term).ok()?,
                    None => term,
                });
            }
            if !a.constant.is_zero() {
                let k = arena.int_const(a.constant.numerator());
                acc = Some(match acc {
                    Some(prev) => arena.int_add(prev, k).ok()?,
                    None => k,
                });
            }
            Some(acc.unwrap_or_else(|| arena.int_const(0)))
        }
        Sort::Real => {
            let mut acc: Option<TermId> = None;
            for (&sym, &c) in &a.coeffs {
                if c.is_zero() {
                    continue;
                }
                let var = arena.var(sym);
                let coeff = arena.real_const(c);
                let term = arena.real_mul(coeff, var).ok()?;
                acc = Some(match acc {
                    Some(prev) => arena.real_add(prev, term).ok()?,
                    None => term,
                });
            }
            if !a.constant.is_zero() {
                let k = arena.real_const(a.constant);
                acc = Some(match acc {
                    Some(prev) => arena.real_add(prev, k).ok()?,
                    None => k,
                });
            }
            Some(acc.unwrap_or_else(|| arena.real_const(Rational::zero())))
        }
        _ => None,
    }
}
