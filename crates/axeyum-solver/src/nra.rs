//! A first nonlinear-real-arithmetic (NRA) slice by **linear abstraction +
//! replay** — the same sound relaxation pattern used for the lazy bit-vector and
//! datatype paths.
//!
//! Each genuinely nonlinear product `x·y` (a `RealMul` whose operands are *both*
//! non-constant; `c·y` stays linear) is replaced by a fresh, unconstrained real
//! variable, and the residual — now pure linear real arithmetic — is sent to the
//! LRA solver. Because the fresh variable is unconstrained, the abstraction only
//! *enlarges* the model space, so:
//!
//! - `unsat` of the abstraction ⇒ `unsat` of the original (sound): if even the
//!   relaxation has no model, neither does the original. This already decides
//!   queries where the contradiction does not need the nonlinear fact — e.g.
//!   `x·y = 5 ∧ x·y = 6` (the *same* product maps to one variable).
//! - `sat` of the abstraction is a *candidate*: it is **replayed** against the
//!   original assertions with the ground evaluator (which computes the true
//!   products), and accepted only if it genuinely satisfies them; otherwise the
//!   refinement loop adds exact point lemmas (`r = x·y` at the candidate point)
//!   and retries, finally returning `unknown` if it does not converge. So
//!   `x·y = 6 ∧ x = 2 ∧ y = 3` is `sat`.
//!
//! Beyond the bare abstraction, the relaxation is strengthened with **sound
//! product lemmas** — the sign rules `(a≥0∧b≥0)→r≥0`, … and the zero rule
//! `r=0 ⟺ a=0 ∨ b=0` — plus `McCormick` envelopes over extracted variable
//! bounds and spatial branch-and-bound. These are enough to decide many
//! sign-based queries with no model at all, e.g. `x·x < 0` is **unsat** (`x² ≥ 0`
//! follows from the sign rules since the two factors are the same `x`), and
//! `x>0 ∧ x·y<0 → y<0`.
//!
//! Sound in both directions; incomplete. `unknown` is first-class, never wrong.

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{IrError, Op, Sort, TermArena, TermId, TermNode, Value, eval};
use axeyum_rewrite::replace_subterms;

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::dpll_t::check_with_lra_dpll;
use crate::model::Model;

/// Bound on the incremental-linearization refinement rounds before returning
/// `unknown` (the loop adds exact point lemmas for inconsistent leaf products).
const MAX_REFINE_ROUNDS: usize = 12;

/// Maximum spatial branch-and-bound depth before a subdomain is reported
/// `unknown` (each level halves one variable's interval).
const MAX_BNB_DEPTH: usize = 6;

type Bounds = HashMap<TermId, (axeyum_ir::Rational, axeyum_ir::Rational)>;

/// Decides a (possibly nonlinear) real-arithmetic query by linear abstraction of
/// nonlinear products, `McCormick` envelopes, spatial branch-and-bound, and replay.
///
/// # Errors
///
/// Returns [`SolverError`] from the rewrite or the LRA solver.
pub fn check_with_nra(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Eliminate real division first: `x/y → r` with `(y = 0) ∨ (x = r·y)`,
    // matching SMT-LIB's unspecified division by zero. The `r·y` product is then
    // handled by the nonlinear abstraction below (or is linear when `y` is
    // constant). Exact encoding, so soundness is preserved.
    let assertions = &eliminate_real_div(arena, assertions)?;

    let products = nonlinear_products(arena, assertions);
    if products.is_empty() {
        // Already linear — straight to LRA.
        return check_with_lra_dpll(arena, assertions, config);
    }

    // Abstract each distinct nonlinear product with a fresh real variable,
    // recording (operand_a, operand_b, fresh_var) for the lemmas below.
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut triples: Vec<(TermId, TermId, TermId)> = Vec::new();
    for (i, &product) in products.iter().enumerate() {
        let TermNode::App { args, .. } = arena.node(product) else {
            continue;
        };
        let (pa, pb) = (args[0], args[1]);
        let fresh = arena
            .declare(&format!("!nra_{i}"), Sort::Real)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let var = arena.var(fresh);
        map.insert(product, var);
        triples.push((pa, pb, var));
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();

    // `base`: the abstracted assertions plus the sign/zero product lemmas (valid
    // for `r = a·b`). McCormick envelopes and interval bounds are added per
    // branch-and-bound node, since they depend on the (shrinking) variable box.
    let mut base = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        base.push(
            replace_subterms(arena, assertion, &map, &mut memo)
                .map_err(|e| SolverError::Backend(e.to_string()))?,
        );
    }
    for &(pa, pb, r) in &triples {
        for lemma in product_lemmas(arena, pa, pb, r)? {
            let rewritten = replace_subterms(arena, lemma, &map, &mut memo)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            base.push(rewritten);
        }
    }

    // Initial box: constant bounds on each product-operand *variable*, read off
    // the top-level assertions. These are assertion-implied, so the root box
    // covers every model (unbounded operands are simply left unrestricted).
    let mut bounds: Bounds = HashMap::new();
    for &(pa, pb, _) in &triples {
        for operand in [pa, pb] {
            if !matches!(arena.node(operand), TermNode::Symbol(_)) || bounds.contains_key(&operand)
            {
                continue;
            }
            if let (Some(lo), Some(hi)) = extract_bounds(arena, assertions, operand) {
                bounds.insert(operand, (lo, hi));
            }
        }
    }

    branch_and_bound(
        arena, &base, &triples, &products, assertions, config, &bounds, 0,
    )
}

/// Spatial branch-and-bound over the variable box. Solves the `McCormick`
/// relaxation on the current box; on `unknown`, halves the widest variable's
/// interval and recurses. `sat` (a replayed model) and `unsat` (the `McCormick`
/// relaxation is itself unsat — sound, since the box's interval constraints are
/// implied by the assertions and a split's two halves exactly cover the parent's
/// range for that bounded variable) both transfer; only an undecided subdomain
/// at the depth limit yields `unknown`.
#[allow(clippy::too_many_arguments)]
fn branch_and_bound(
    arena: &mut TermArena,
    base: &[TermId],
    triples: &[(TermId, TermId, TermId)],
    products: &BTreeSet<TermId>,
    original: &[TermId],
    config: &SolverConfig,
    bounds: &Bounds,
    depth: usize,
) -> Result<CheckResult, SolverError> {
    // Hitting the (tunable) branch-and-bound depth budget is a ResourceLimit —
    // a deeper search could still decide — not fundamental incompleteness.
    let unknown = || {
        Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: "nonlinear abstraction: branch-and-bound depth budget reached".to_owned(),
        }))
    };

    match solve_relaxation(arena, base, triples, products, original, bounds, config)? {
        CheckResult::Sat(model) => Ok(CheckResult::Sat(model)),
        CheckResult::Unsat => Ok(CheckResult::Unsat),
        CheckResult::Unknown(reason) => {
            if depth >= MAX_BNB_DEPTH {
                return unknown();
            }
            // Halve the widest splittable interval; the two halves cover it.
            let Some((var, lo, hi)) = widest_split(bounds) else {
                return Ok(CheckResult::Unknown(reason));
            };
            let Some(mid) = rat_mid(lo, hi) else {
                return Ok(CheckResult::Unknown(reason)); // overflow → cannot split
            };
            let mut any_unknown = false;
            for (sub_lo, sub_hi) in [(lo, mid), (mid, hi)] {
                let mut child = bounds.clone();
                child.insert(var, (sub_lo, sub_hi));
                match branch_and_bound(
                    arena,
                    base,
                    triples,
                    products,
                    original,
                    config,
                    &child,
                    depth + 1,
                )? {
                    CheckResult::Sat(model) => return Ok(CheckResult::Sat(model)),
                    CheckResult::Unsat => {}
                    CheckResult::Unknown(_) => any_unknown = true,
                }
            }
            if any_unknown {
                unknown()
            } else {
                Ok(CheckResult::Unsat)
            }
        }
    }
}

/// Solve the `McCormick` relaxation on one box: `base` plus the interval
/// constraints and `McCormick` envelopes for `bounds`, run through the
/// point-lemma refinement loop. Returns a genuine (replayed) `sat`, a relaxation
/// `unsat`, or `unknown` for this subdomain.
#[allow(clippy::too_many_arguments)]
fn solve_relaxation(
    arena: &mut TermArena,
    base: &[TermId],
    triples: &[(TermId, TermId, TermId)],
    products: &BTreeSet<TermId>,
    original: &[TermId],
    bounds: &Bounds,
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let mut reduced = base.to_vec();
    // Interval constraints `lo ≤ v ≤ hi` for this box.
    for (&var, &(lo, hi)) in bounds {
        let lo_c = arena.real_const(lo);
        let hi_c = arena.real_const(hi);
        let ge = arena.real_ge(var, lo_c)?;
        let le = arena.real_le(var, hi_c)?;
        reduced.push(ge);
        reduced.push(le);
    }
    // McCormick envelopes using this box's bounds.
    for &(pa, pb, r) in triples {
        let (Some(&(a_lo, a_hi)), Some(&(b_lo, b_hi))) = (bounds.get(&pa), bounds.get(&pb)) else {
            continue;
        };
        for lemma in mccormick_lemmas(arena, pa, pb, a_lo, a_hi, b_lo, b_hi, r)? {
            reduced.push(lemma);
        }
    }

    // Incremental-linearization refinement: solve, replay, add exact point
    // lemmas for inconsistent leaf products, re-solve. Bounded rounds → unknown.
    // `hit_round_bound` distinguishes "ran out of the (tunable) round budget"
    // (retryable → ResourceLimit) from "refinement reached a fixpoint without
    // deciding" (fundamental for this relaxation → Incomplete).
    let mut hit_round_bound = true;
    for _ in 0..MAX_REFINE_ROUNDS {
        let result = check_with_lra_dpll(arena, &reduced, config)?;
        let CheckResult::Sat(model) = result else {
            return Ok(result); // unsat/unknown transfer (the box is a relaxation)
        };
        let assignment = model.to_assignment();
        if original
            .iter()
            .all(|&a| matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))))
        {
            let mut out = Model::new();
            for (symbol, name, _sort) in arena.symbols() {
                if name.starts_with("!nra_") {
                    continue;
                }
                if let Some(value) = assignment.get(symbol) {
                    out.set(symbol, value);
                }
            }
            return Ok(CheckResult::Sat(out));
        }
        let mut added = false;
        for &(pa, pb, r) in triples {
            if products.contains(&pa) || products.contains(&pb) {
                continue;
            }
            let (Some(a0), Some(b0), Some(r0)) = (
                real_value(arena, pa, &assignment),
                real_value(arena, pb, &assignment),
                real_value(arena, r, &assignment),
            ) else {
                continue;
            };
            let (Some(num), Some(den)) = (
                a0.numerator().checked_mul(b0.numerator()),
                a0.denominator().checked_mul(b0.denominator()),
            ) else {
                continue;
            };
            let prod = axeyum_ir::Rational::new(num, den);
            if r0 == prod {
                continue;
            }
            // Safety net: a refinement that chases an escalating witness can drive
            // the candidate magnitudes up until the exact-rational simplex overflows
            // `i128` (it cross-multiplies, so even sub-`i128` coefficients can blow
            // up combining). Stop refining a product once its candidate point grows
            // past a conservative bound — that product is left to `unknown` rather
            // than risking a panic. The bound is far below `√i128::MAX`, leaving the
            // simplex ample headroom.
            if too_large_to_refine(a0) || too_large_to_refine(b0) || too_large_to_refine(prod) {
                continue;
            }
            let lemma = point_lemma(arena, pa, a0, pb, b0, r, prod)?;
            reduced.push(lemma);
            added = true;
        }
        if !added {
            hit_round_bound = false; // refinement stalled, not out of budget
            break;
        }
    }
    let (kind, detail) = if hit_round_bound {
        (
            UnknownKind::ResourceLimit,
            "nonlinear abstraction: refinement round bound reached (raise the budget to attempt more)",
        )
    } else {
        (
            UnknownKind::Incomplete,
            "nonlinear abstraction: refinement reached a fixpoint without deciding",
        )
    };
    Ok(CheckResult::Unknown(UnknownReason {
        kind,
        detail: detail.to_owned(),
    }))
}

/// The bounded variable with the widest interval (`hi > lo`), for splitting.
fn widest_split(bounds: &Bounds) -> Option<(TermId, axeyum_ir::Rational, axeyum_ir::Rational)> {
    let mut best: Option<(TermId, axeyum_ir::Rational, axeyum_ir::Rational)> = None;
    let mut best_w: Option<axeyum_ir::Rational> = None;
    for (&var, &(lo, hi)) in bounds {
        let Some(w) = rat_width(lo, hi) else { continue };
        if w <= axeyum_ir::Rational::integer(0) {
            continue; // already a point
        }
        if best_w.is_none_or(|bw| w > bw) {
            best_w = Some(w);
            best = Some((var, lo, hi));
        }
    }
    best
}

/// Midpoint `(lo + hi) / 2`, `None` on i128 overflow.
fn rat_mid(lo: axeyum_ir::Rational, hi: axeyum_ir::Rational) -> Option<axeyum_ir::Rational> {
    let num = lo
        .numerator()
        .checked_mul(hi.denominator())?
        .checked_add(hi.numerator().checked_mul(lo.denominator())?)?;
    let den = lo
        .denominator()
        .checked_mul(hi.denominator())?
        .checked_mul(2)?;
    Some(axeyum_ir::Rational::new(num, den))
}

/// Interval width `hi − lo`, `None` on i128 overflow.
fn rat_width(lo: axeyum_ir::Rational, hi: axeyum_ir::Rational) -> Option<axeyum_ir::Rational> {
    let num = hi
        .numerator()
        .checked_mul(lo.denominator())?
        .checked_sub(lo.numerator().checked_mul(hi.denominator())?)?;
    let den = hi.denominator().checked_mul(lo.denominator())?;
    Some(axeyum_ir::Rational::new(num, den))
}

/// Replaces each `x / y` (`RealDiv`) with a fresh real `r` constrained by
/// `(y = 0) ∨ (x = r·y)` — the exact SMT-LIB semantics (division by zero is an
/// unspecified value, so `r` is left free there). The `r·y` term is a `RealMul`
/// the nonlinear abstraction then handles. Equisatisfiable; soundness preserved.
fn eliminate_real_div(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    // Collect distinct RealDiv subterms.
    let mut divs: Vec<TermId> = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            let op = *op;
            let args = args.clone();
            if op == Op::RealDiv {
                divs.push(t);
            }
            stack.extend(args);
        }
    }
    if divs.is_empty() {
        return Ok(assertions.to_vec());
    }

    let err = |e: IrError| SolverError::Backend(e.to_string());
    let zero = arena.real_const(axeyum_ir::Rational::integer(0));
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut constraints: Vec<TermId> = Vec::new();
    for (i, div) in divs.into_iter().enumerate() {
        let TermNode::App { args, .. } = arena.node(div) else {
            continue;
        };
        let (x, y) = (args[0], args[1]);
        let fresh = arena
            .declare(&format!("!div_{i}"), Sort::Real)
            .map_err(err)?;
        let r = arena.var(fresh);
        map.insert(div, r);
        // (y = 0) ∨ (x = r·y)
        let y_zero = arena.eq(y, zero).map_err(err)?;
        let ry = arena.real_mul(r, y).map_err(err)?;
        let x_eq = arena.eq(x, ry).map_err(err)?;
        constraints.push(arena.or(y_zero, x_eq).map_err(err)?);
    }

    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len() + constraints.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
    }
    for c in constraints {
        out.push(replace_subterms(arena, c, &map, &mut memo).map_err(err)?);
    }
    Ok(out)
}

/// The model value of a real term, if it evaluates to a `Real`.
fn real_value(
    arena: &TermArena,
    term: TermId,
    assignment: &axeyum_ir::Assignment,
) -> Option<axeyum_ir::Rational> {
    match eval(arena, term, assignment) {
        Ok(Value::Real(r)) => Some(r),
        _ => None,
    }
}

/// The exact point lemma `(a = a0 ∧ b = b0) → r = a0·b0`.
fn point_lemma(
    arena: &mut TermArena,
    a: TermId,
    a0: axeyum_ir::Rational,
    b: TermId,
    b0: axeyum_ir::Rational,
    r: TermId,
    prod: axeyum_ir::Rational,
) -> Result<TermId, IrError> {
    let a0c = arena.real_const(a0);
    let b0c = arena.real_const(b0);
    let prodc = arena.real_const(prod);
    let a_eq = arena.eq(a, a0c)?;
    let b_eq = arena.eq(b, b0c)?;
    let r_eq = arena.eq(r, prodc)?;
    let prem = arena.and(a_eq, b_eq)?;
    let nprem = arena.not(prem)?;
    arena.or(nprem, r_eq)
}

/// Sound linear lemmas about the product `r = a·b`: the sign rules and the zero
/// rule. All are valid facts about real multiplication, so adding them keeps the
/// abstraction a relaxation (original models, with `r = a·b`, satisfy them) while
/// making it strong enough to decide sign-based nonlinear queries.
#[allow(clippy::similar_names)] // a_ge/a_le/b_ge/… mirror the sign-rule structure
fn product_lemmas(
    arena: &mut TermArena,
    a: TermId,
    b: TermId,
    r: TermId,
) -> Result<Vec<TermId>, IrError> {
    let zero = arena.real_const(axeyum_ir::Rational::integer(0));
    let a_ge = arena.real_ge(a, zero)?;
    let a_le = arena.real_le(a, zero)?;
    let b_ge = arena.real_ge(b, zero)?;
    let b_le = arena.real_le(b, zero)?;
    let r_ge = arena.real_ge(r, zero)?;
    let r_le = arena.real_le(r, zero)?;
    let a_z = arena.eq(a, zero)?;
    let b_z = arena.eq(b, zero)?;
    let r_z = arena.eq(r, zero)?;

    // implication p → q, as ¬p ∨ q.
    let imp = |arena: &mut TermArena, p: TermId, q: TermId| -> Result<TermId, IrError> {
        let np = arena.not(p)?;
        arena.or(np, q)
    };
    let mut out = Vec::new();
    // sign rules
    let pp = arena.and(a_ge, b_ge)?;
    out.push(imp(arena, pp, r_ge)?); // (a≥0 ∧ b≥0) → r≥0
    let nn = arena.and(a_le, b_le)?;
    out.push(imp(arena, nn, r_ge)?); // (a≤0 ∧ b≤0) → r≥0
    let pn = arena.and(a_ge, b_le)?;
    out.push(imp(arena, pn, r_le)?); // (a≥0 ∧ b≤0) → r≤0
    let np_ = arena.and(a_le, b_ge)?;
    out.push(imp(arena, np_, r_le)?); // (a≤0 ∧ b≥0) → r≤0
    // zero rule, both directions: r = 0 ⟺ a = 0 ∨ b = 0
    let either_z = arena.or(a_z, b_z)?;
    out.push(imp(arena, either_z, r_z)?);
    out.push(imp(arena, r_z, either_z)?);

    // Monotonicity at threshold 1: multiplying by a factor ≥ 1 moves the other
    // operand away from 0. Each is a sound consequence of r = a·b — e.g. a≥1 ∧ b≥0
    // ⇒ a·b ≥ 1·b = b. These decide cases the sign/zero rules miss, such as
    // `x≥1 ∧ y≥1 ∧ x·y < 1` (unsat: x·y ≥ y ≥ 1).
    //
    // Only for genuine two-operand products (`a ≠ b`): for a square these reduce to
    // `r ≥ x`, which, on an *unbounded* square, makes the incremental-linearization
    // refinement chase a quadratically-escalating witness (and the exact-rational
    // simplex would overflow before the round bound). A square is already pinned by
    // the sign rule (`x² ≥ 0`), so it loses nothing here.
    if a == b {
        return Ok(out);
    }
    let one = arena.real_const(axeyum_ir::Rational::integer(1));
    let a_ge1 = arena.real_ge(a, one)?;
    let b_ge1 = arena.real_ge(b, one)?;
    let r_ge_b = arena.real_ge(r, b)?;
    let r_le_b = arena.real_le(r, b)?;
    let r_ge_a = arena.real_ge(r, a)?;
    let r_le_a = arena.real_le(r, a)?;
    let a1_bge = arena.and(a_ge1, b_ge)?;
    out.push(imp(arena, a1_bge, r_ge_b)?); // (a≥1 ∧ b≥0) → r≥b
    let a1_ble = arena.and(a_ge1, b_le)?;
    out.push(imp(arena, a1_ble, r_le_b)?); // (a≥1 ∧ b≤0) → r≤b
    let b1_age = arena.and(b_ge1, a_ge)?;
    out.push(imp(arena, b1_age, r_ge_a)?); // (b≥1 ∧ a≥0) → r≥a
    let b1_ale = arena.and(b_ge1, a_le)?;
    out.push(imp(arena, b1_ale, r_le_a)?); // (b≥1 ∧ a≤0) → r≤a
    Ok(out)
}

/// The real constant a node denotes, if it is one.
fn as_real_const(arena: &TermArena, t: TermId) -> Option<axeyum_ir::Rational> {
    match arena.node(t) {
        TermNode::RealConst(r) => Some(*r),
        _ => None,
    }
}

/// Tightest constant lower/upper bounds on `t` read off the **top-level**
/// assertions (each of which holds unconditionally), from the direct comparison
/// forms `t ≤ c`, `c ≤ t`, `t ≥ c`, `c ≥ t` (strict variants give the same
/// non-strict bound — sound, slightly loose) and `t = c`. Returns `(lower,
/// upper)`, each `None` if unbounded. Only syntactic operand-vs-constant bounds
/// are recognised; that is enough for the common bounded-variable case and keeps
/// every bound sound.
fn extract_bounds(
    arena: &TermArena,
    assertions: &[TermId],
    t: TermId,
) -> (Option<axeyum_ir::Rational>, Option<axeyum_ir::Rational>) {
    let mut lo: Option<axeyum_ir::Rational> = None;
    let mut hi: Option<axeyum_ir::Rational> = None;
    let mut see_lo = |c: axeyum_ir::Rational| lo = Some(lo.map_or(c, |x| x.max(c)));
    let mut see_hi = |c: axeyum_ir::Rational| hi = Some(hi.map_or(c, |x| x.min(c)));
    for &asrt in assertions {
        let TermNode::App { op, args } = arena.node(asrt) else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        let (op, l, r) = (*op, args[0], args[1]);
        let (lc, rc) = (as_real_const(arena, l), as_real_const(arena, r));
        match op {
            Op::RealLe | Op::RealLt => {
                if l == t {
                    if let Some(c) = rc {
                        see_hi(c); // t ≤ c
                    }
                }
                if r == t {
                    if let Some(c) = lc {
                        see_lo(c); // c ≤ t
                    }
                }
            }
            Op::RealGe | Op::RealGt => {
                if l == t {
                    if let Some(c) = rc {
                        see_lo(c); // t ≥ c
                    }
                }
                if r == t {
                    if let Some(c) = lc {
                        see_hi(c); // c ≥ t
                    }
                }
            }
            Op::Eq => {
                if l == t {
                    if let Some(c) = rc {
                        see_lo(c);
                        see_hi(c);
                    }
                }
                if r == t {
                    if let Some(c) = lc {
                        see_lo(c);
                        see_hi(c);
                    }
                }
            }
            _ => {}
        }
    }
    (lo, hi)
}

/// Whether a candidate value's magnitude is large enough that feeding it to the
/// exact-rational simplex risks an `i128` overflow (the simplex cross-multiplies,
/// so even sub-`i128` coefficients can blow up when combined). The bound `2^31` is
/// far below `√i128::MAX ≈ 2^63`, leaving ample headroom; a value past it is left
/// to `unknown` instead of being refined.
fn too_large_to_refine(q: axeyum_ir::Rational) -> bool {
    const REFINE_BOUND: u128 = 1 << 31;
    q.numerator().unsigned_abs() > REFINE_BOUND || q.denominator().unsigned_abs() > REFINE_BOUND
}

/// Exact rational product, `None` on i128 overflow.
fn rat_mul(p: axeyum_ir::Rational, q: axeyum_ir::Rational) -> Option<axeyum_ir::Rational> {
    let num = p.numerator().checked_mul(q.numerator())?;
    let den = p.denominator().checked_mul(q.denominator())?;
    Some(axeyum_ir::Rational::new(num, den))
}

/// The four `McCormick` envelope inequalities for the product `r = a*b`, given
/// `a` in `[a_lo, a_hi]` and `b` in `[b_lo, b_hi]` (all valid for any such
/// operands): the two lower bounds use the matching corner products and the two
/// upper bounds use the opposite corners. Any inequality whose constant term
/// overflows the `i128` rational is skipped.
#[allow(clippy::similar_names, clippy::too_many_arguments)]
fn mccormick_lemmas(
    arena: &mut TermArena,
    a: TermId,
    b: TermId,
    a_lo: axeyum_ir::Rational,
    a_hi: axeyum_ir::Rational,
    b_lo: axeyum_ir::Rational,
    b_hi: axeyum_ir::Rational,
    r: TermId,
) -> Result<Vec<TermId>, IrError> {
    // term for `k·t`
    fn scaled(arena: &mut TermArena, k: axeyum_ir::Rational, t: TermId) -> Result<TermId, IrError> {
        let kc = arena.real_const(k);
        arena.real_mul(kc, t)
    }
    // rhs = ka·b + kb·a − const, then compare r against it (ge = `≥`, else `≤`).
    let build = |arena: &mut TermArena,
                 ka: axeyum_ir::Rational,
                 kb: axeyum_ir::Rational,
                 ge: bool|
     -> Result<Option<TermId>, IrError> {
        let Some(cst) = rat_mul(ka, kb) else {
            return Ok(None); // constant term overflowed; skip this inequality
        };
        let t1 = scaled(arena, ka, b)?;
        let t2 = scaled(arena, kb, a)?;
        let sum = arena.real_add(t1, t2)?;
        let cc = arena.real_const(cst);
        let rhs = arena.real_sub(sum, cc)?;
        let lemma = if ge {
            arena.real_ge(r, rhs)?
        } else {
            arena.real_le(r, rhs)?
        };
        Ok(Some(lemma))
    };

    let mut out = Vec::new();
    if let Some(l) = build(arena, a_lo, b_lo, true)? {
        out.push(l);
    }
    if let Some(l) = build(arena, a_hi, b_hi, true)? {
        out.push(l);
    }
    if let Some(l) = build(arena, a_hi, b_lo, false)? {
        out.push(l);
    }
    if let Some(l) = build(arena, a_lo, b_hi, false)? {
        out.push(l);
    }
    Ok(out)
}

/// Collects every `RealMul` subterm whose operands are both non-constant (a
/// genuinely nonlinear product; `const · term` is linear and left alone).
fn nonlinear_products(arena: &TermArena, roots: &[TermId]) -> BTreeSet<TermId> {
    let mut products = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(term) else {
            continue;
        };
        let op = *op;
        let args = args.clone();
        if op == Op::RealMul && args.len() == 2 {
            let a_const = matches!(arena.node(args[0]), TermNode::RealConst(_));
            let b_const = matches!(arena.node(args[1]), TermNode::RealConst(_));
            if !a_const && !b_const {
                products.insert(term);
            }
        }
        stack.extend(args.iter().copied());
    }
    products
}
