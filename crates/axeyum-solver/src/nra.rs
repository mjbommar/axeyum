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
use crate::dpll_t::{check_with_lra_dpll_within, check_with_nra_dpll_within};
use crate::model::Model;

// Native uses the std clock; wasm uses the `web_time` drop-in (ADR-0017).
use std::time::Duration;
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

/// Wall-clock budget for the cheap sign/zero refutation attempted before the
/// cross-product admission cap declines. Sign-refutable instances converge in well
/// under this; the bound keeps a *capped* instance declining promptly even when the
/// caller set no global timeout (a tighter global deadline still wins).
const SIGN_REFUTE_BUDGET: Duration = Duration::from_millis(500);

/// An `unknown` result attributed to the wall-clock timeout (a resource limit,
/// not fundamental incompleteness).
fn timed_out() -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::ResourceLimit,
        detail: "nonlinear abstraction: wall-clock timeout reached".to_owned(),
    })
}

/// Whether `deadline` (if set) has passed.
fn past_deadline(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|d| Instant::now() >= d)
}

/// The earlier of two optional deadlines (`None` means "no bound on that side").
fn earliest_deadline(a: Option<Instant>, b: Option<Instant>) -> Option<Instant> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (Some(x), None) => Some(x),
        (None, y) => y,
    }
}

/// Bound on the incremental-linearization refinement rounds before returning
/// `unknown` (the loop adds exact point lemmas for inconsistent leaf products).
const MAX_REFINE_ROUNDS: usize = 12;

/// Maximum spatial branch-and-bound depth before a subdomain is reported
/// `unknown` (each level halves one variable's interval).
const MAX_BNB_DEPTH: usize = 6;

/// Deterministic admission bound on **distinct-operand cross-products** — genuine
/// products `a·b` with `a ≠ b`. Each cross-product contributes the dense
/// disjunctive monotonicity/sign/zero lemma set (≈14 clauses) *and* couples to the
/// others through the sum-of-squares lemmas, so a handful of them produce a hard
/// Boolean+arithmetic combination the DPLL(T)/exact-rational LRA relaxation chokes
/// on — exhausting memory *inside a single solve call* (so neither the per-round
/// nor the per-node wall-clock check can intercept it). This is measured: the
/// 3-variable case `a²+b²+c² ⋈ ab+bc+ca` (three cross-products `ab`, `bc`, `ca`)
/// blows up the relaxation **whether or not the variables are bounded** — bounds do
/// *not* tame it (`McCormick` adds yet more lemmas). Above this bound we therefore
/// refuse with a deterministic `Unknown` rather than risk an OOM, upholding the
/// standing rule "graceful `unknown`, never OOM/crash."
///
/// The bound counts **only** cross-products: squares (`a == b`, which skip the
/// monotonicity lemmas and the SOS coupling) are cheap and never counted — the
/// square-only multi-variable cases (e.g. `x²+y²+z²+1 = 0`) stay decidable. The
/// value `2` is the documented boundary between the working 2-variable SOS frontier
/// (`a²+b² < 2ab`, one cross-product `ab`) and the blowing-up 3-variable case (three
/// cross-products). Multi-variable SOS / Cauchy–Schwarz over more cross-products is
/// gated on a future principled engine (nlsat/CAD or an exact-rational work budget).
const MAX_CROSS_PRODUCTS: usize = 2;

type Bounds = HashMap<TermId, (axeyum_ir::Rational, axeyum_ir::Rational)>;

/// Decides a (possibly nonlinear) real-arithmetic query by linear abstraction of
/// nonlinear products, `McCormick` envelopes, spatial branch-and-bound, and replay.
///
/// This wrapper adds a **final soundness guard**: any `sat` model returned by the
/// internal engine is re-checked against the **original** assertions (with real
/// division intact) under the ground evaluator. Internal division elimination
/// rewrites `x/y` to a fresh variable constrained by `(y=0) ∨ (x=r·y)`, so a
/// candidate can satisfy the *eliminated* form via the `y=0` branch with `r` free,
/// while the original `x/0` evaluates (in the ground evaluator, the soundness trust
/// anchor) to a fixed value that does **not** satisfy the atom — a wrong `sat`.
/// Re-checking here converts any such spurious `sat` to a first-class `unknown`,
/// never a wrong verdict. (The internal engine already replays against the
/// *eliminated* form; this guard closes the gap between that form and the
/// evaluator's div-by-zero semantics.)
///
/// # Errors
///
/// Returns [`SolverError`] from the rewrite or the LRA solver.
pub fn check_with_nra(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let result = check_with_nra_impl(arena, assertions, config)?;
    if let CheckResult::Sat(model) = &result {
        let assignment = model.to_assignment();
        let all_true = assertions
            .iter()
            .all(|&a| matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))));
        if !all_true {
            // The candidate does not satisfy the original (division) semantics —
            // decline rather than return a wrong `sat`.
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::Incomplete,
                detail: "nra: sat candidate failed replay against the original \
                         (real-division) semantics"
                    .to_owned(),
            }));
        }
    }
    Ok(result)
}

/// The internal NRA engine (see [`check_with_nra`] for the final soundness guard).
fn check_with_nra_impl(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Complete, exact decision for pure real-polynomial constraints (single- and
    // multi-variable), including polynomial *identities* whose negation collapses to
    // a constant comparison `0 ⋈ 0`. This is the same sound decider the `solve`
    // auto-path runs *before* falling here; hooking it at the top of the NRA engine
    // means DIRECT `check_with_nra` callers (examples, downstream consumers) get the
    // same completeness instead of grinding the abstraction search to a timeout. It
    // returns `None` (declines) on anything it cannot decide exactly, so it never
    // weakens the search below or risks an unsound verdict.
    if let Some(result) = crate::nra_real_root::decide_real_poly_constraint(arena, assertions)? {
        return Ok(result);
    }

    // The TRUE original assertions (with real division intact) — the replay target
    // for every `sat` candidate below. Division elimination (next) rewrites `x/y`
    // to a fresh `r` constrained by `(y=0) ∨ (x=r·y)`, so a candidate can satisfy
    // the *eliminated* form via the `y=0` branch with `r` free while the original
    // `x/0` evaluates (ground evaluator) to a fixed value that does not. Replaying
    // against THIS rejects such spurious candidates and lets the search find a
    // genuine model (e.g. `1/w < 0` at `w < 0`, not the spurious `w = 0`).
    let original: Vec<TermId> = assertions.to_vec();

    // Wall-clock deadline (only when a timeout is configured): an *absolute*
    // instant shared by every sub-solve below, so the branch-and-bound, the
    // refinement loop, *and* each lazy-SMT solve bail to a timely `unknown`
    // rather than overrunning the budget inside a single solve (#15). Derived
    // once here so the clock is not reset per call.
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));

    // Boolean structure over nonlinear atoms (the flat-conjunction CAD above
    // declined): run the NRA lazy-SMT loop on the ORIGINAL assertions, **before**
    // division elimination, so its `finish_sat` replays against the true division
    // semantics. A cube that still contains `x/y` is non-polynomial → the CAD
    // declines it → `unknown` → we fall through to elimination + relaxation. This
    // handles original Boolean structure (e.g. `distinct`/`and` over nonlinear
    // atoms) without ever asserting a division-induced spurious model. Strictly
    // additive; `DISAGREE=0` on `nra_differential_fuzz` (incl. division) vs Z3.
    match check_with_nra_dpll_within(arena, &original, config, deadline)? {
        result @ (CheckResult::Sat(_) | CheckResult::Unsat) => return Ok(result),
        CheckResult::Unknown(_) => {}
    }

    // Eliminate real division: `x/y → r` with `(y = 0) ∨ (x = r·y)` (+ the division
    // congruence axioms in `eliminate_real_div`). The eliminated form drives the
    // abstraction/relaxation below; every `sat` candidate is replayed against
    // `original` (with division), never the eliminated form.
    let assertions = &eliminate_real_div(arena, &original)?;

    let products = nonlinear_products(arena, assertions);
    if products.is_empty() {
        // Already linear (after elimination). The LRA loop replays internally
        // against the eliminated form; the `check_with_nra` wrapper's final guard
        // re-checks any `sat` against `original`, so div-by-zero stays sound.
        return check_with_lra_dpll_within(arena, assertions, config, deadline);
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

    // `base`: start with the abstracted assertions (each nonlinear product replaced
    // by its fresh var). Product/sign/SOS lemmas and per-box McCormick envelopes are
    // added below; the bare abstraction is a pure-linear *relaxation* of the original.
    let mut base = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        base.push(
            replace_subterms(arena, assertion, &map, &mut memo)
                .map_err(|e| SolverError::Backend(e.to_string()))?,
        );
    }

    // Cheap, sound pre-check on the bare abstraction (no product lemmas yet, so it is
    // pure linear arithmetic and cannot blow up): if even this relaxation is already
    // `unsat`, the original is `unsat` (a relaxation only enlarges the model space).
    // This decides the same-product-contradiction class (e.g. `x·y=5 ∧ x·y=6 ∧ …`)
    // for *any* number of products, so the cross-product admission bound below does
    // not cost us those easy refutations. A `sat`/`unknown` here is just a candidate
    // (the abstraction is too weak), so only `unsat` is acted on.
    if let CheckResult::Unsat = check_with_lra_dpll_within(arena, &base, config, deadline)? {
        return Ok(CheckResult::Unsat);
    }

    // Deterministic memory guard (graceful `unknown`, never OOM): refuse instances
    // with too many distinct-operand cross-products *before* building the dense
    // product lemmas or entering the relaxation. These products carry the disjunctive
    // monotonicity lemmas and the sum-of-squares coupling that drive the DPLL(T)/LRA
    // relaxation to OOM inside a single solve call — bounded or not (see
    // `MAX_CROSS_PRODUCTS`). Squares are cheap and excluded, so square-only
    // multi-variable instances stay decidable.
    // Count cross-products from the NORMALIZED polynomials of the assertions when
    // they are representable as multivariate polynomial comparisons (like monomials
    // collected, zero-coefficient and cancelling monomials dropped). This corrects
    // the raw term-tree over-count — e.g. `2 + 0·y·y + 0·y·z − 1 > 0` (the
    // `0·`-coefficient monomials vanish) and `−2·x·y + 2·x·y + x = 0` (the products
    // cancel to `x`). A genuinely-nonlinear instance with > 2 *distinct* normalized
    // cross-product monomials still trips the bound, so the OOM guard is intact; only
    // the inflated counts are corrected. Falls back to the raw distinct-operand count
    // for shapes the normalizer cannot represent (so the gate never weakens there).
    let cross_products = crate::nra_real_root::normalized_cross_product_count(arena, assertions)
        .unwrap_or_else(|| triples.iter().filter(|&&(pa, pb, _)| pa != pb).count());
    if cross_products > MAX_CROSS_PRODUCTS {
        // Before declining, try a CHEAP sign/zero refutation. The sign and zero
        // lemmas for each `r = a·b` are small disjunctive *linear* implications
        // (`¬p ∨ q`, a handful per product) with **no** McCormick envelopes and
        // **no** sum-of-squares coupling — the parts that make the full relaxation
        // OOM. So they are safe to apply past the cross-product bound. Many capped
        // multi-variable instances are refutable by sign alone — e.g.
        // `b>0 ∧ c>0 ∧ a·b·c·d² < 0` (a positive product cannot be negative) or
        // `b,c,d ≥ 1 ∧ b·c·d < 1` (via the sign chain) — so this turns a cap
        // `unknown` into a real `unsat` without lifting the OOM guard.
        //
        // Sound: the sign/zero lemmas are valid facts about `r = a·b`, so
        // `base + sign_lemmas` is a *relaxation* of the original (every real model,
        // with `r = a·b`, satisfies them); an `unsat` of the relaxation therefore
        // transfers to the original. Only `unsat` is acted on — a `sat`/`unknown`
        // of this weak relaxation proves nothing and falls through to the decline —
        // so it can never produce a wrong verdict.
        let mut sign_base = base.clone();
        for &(pa, pb, r) in &triples {
            for lemma in sign_zero_lemmas(arena, pa, pb, r)? {
                let rewritten = replace_subterms(arena, lemma, &map, &mut memo)
                    .map_err(|e| SolverError::Backend(e.to_string()))?;
                sign_base.push(rewritten);
            }
        }
        // Bound the pre-check so a capped instance still declines promptly even with
        // no global timeout; a tighter caller deadline still wins. A hit here is a
        // sound `unknown` (never a wrong verdict), so cutting it short only forgoes a
        // possible refutation, never risks one.
        let sign_deadline =
            earliest_deadline(deadline, Instant::now().checked_add(SIGN_REFUTE_BUDGET));
        if let CheckResult::Unsat =
            check_with_lra_dpll_within(arena, &sign_base, config, sign_deadline)?
        {
            return Ok(CheckResult::Unsat);
        }
        return Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: format!(
                "nonlinear abstraction: {cross_products} cross-products exceed the deterministic \
                 admission bound of {MAX_CROSS_PRODUCTS} (the multi-variable nonlinear case can OOM \
                 the relaxation; this needs a nlsat/CAD engine)"
            ),
        }));
    }

    // Add the sign/zero product lemmas (valid for `r = a·b`) to `base`. McCormick
    // envelopes and interval bounds are added per branch-and-bound node, since they
    // depend on the (shrinking) variable box.
    for &(pa, pb, r) in &triples {
        for lemma in product_lemmas(arena, pa, pb, r)? {
            let rewritten = replace_subterms(arena, lemma, &map, &mut memo)
                .map_err(|e| SolverError::Backend(e.to_string()))?;
            base.push(rewritten);
        }
    }
    // Sum-of-squares lemmas coupling the per-pair products (a², b², ab). These are
    // already stated over the result vars, so they bypass the operand→var remap.
    for lemma in sos_lemmas(arena, &triples)? {
        base.push(lemma);
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

    // `deadline` (derived at entry) bounds the spatial branch-and-bound, which can
    // otherwise explore ~2^depth boxes × refinement rounds, *and* is threaded into
    // each lazy-SMT solve so no single solve overruns the budget (#15).
    branch_and_bound(
        // Replay target = the TRUE original (with division), so a candidate is
        // accepted only if it satisfies the real `x/y` semantics — never the
        // div-eliminated form (which a `y=0`/free-`r` spurious model would satisfy).
        arena, &base, &triples, &products, &original, config, &bounds, 0, deadline,
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
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    // Wall-clock bound: bail to `unknown` rather than keep exploring (#15).
    if past_deadline(deadline) {
        return Ok(timed_out());
    }
    // Hitting the (tunable) branch-and-bound depth budget is a ResourceLimit —
    // a deeper search could still decide — not fundamental incompleteness.
    let unknown = || {
        Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: "nonlinear abstraction: branch-and-bound depth budget reached".to_owned(),
        }))
    };

    match solve_relaxation(
        arena, base, triples, products, original, bounds, config, deadline,
    )? {
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
                    deadline,
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
    deadline: Option<Instant>,
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
        // Wall-clock bound inside the (potentially expensive) refinement loop (#15).
        if past_deadline(deadline) {
            return Ok(timed_out());
        }
        let result = check_with_lra_dpll_within(arena, &reduced, config, deadline)?;
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
        // Compared to zero, the cross-multiplication never overflows.
        if w <= axeyum_ir::Rational::integer(0) {
            continue; // already a point
        }
        // Overflow during the width comparison just skips this candidate as the
        // new widest (sound — splitting is heuristic; `Ord` would panic).
        let wider = best_w.is_none_or(|bw: axeyum_ir::Rational| {
            w.checked_cmp(&bw) == Some(core::cmp::Ordering::Greater)
        });
        if wider {
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
    // (dividend, divisor, result-var) per distinct div term, kept so the
    // division-congruence constraints below can relate results with equal args.
    let mut div_terms: Vec<(TermId, TermId, TermId)> = Vec::new();
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
        div_terms.push((x, y, r));
    }
    // Division congruence: `/` is a *total function*, so equal arguments give
    // equal results — `(xᵢ = xⱼ ∧ yᵢ = yⱼ) ⟹ rᵢ = rⱼ`. Without this, the
    // fresh-per-occurrence result vars are left independent when the divisor is 0
    // (both `(y=0) ∨ (x=r·y)` disjunctions are satisfied by the `y=0` branch,
    // leaving `r` free), which loses the SMT-LIB congruence
    // `x = y ⟹ (/ x 0) = (/ y 0)` and admits spurious models (e.g. the curated
    // `div.04`/`div.07`). Adding the Ackermann congruence axioms only *restricts*
    // the model space (they are valid consequences of `/`'s totality), so `unsat`
    // stays sound and a prior spurious `sat` is correctly ruled out. O(k²) in the
    // number of distinct div terms `k` (small in practice).
    for i in 0..div_terms.len() {
        for j in (i + 1)..div_terms.len() {
            let (xi, yi, ri) = div_terms[i];
            let (xj, yj, rj) = div_terms[j];
            let xe = arena.eq(xi, xj).map_err(err)?;
            let ye = arena.eq(yi, yj).map_err(err)?;
            let args_eq = arena.and(xe, ye).map_err(err)?;
            let res_eq = arena.eq(ri, rj).map_err(err)?;
            constraints.push(arena.implies(args_eq, res_eq).map_err(err)?);
        }
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

/// The **sign and zero** lemmas about the product `r = a·b` — the cheap linear
/// core of [`product_lemmas`]. Each is a valid fact about real multiplication and,
/// crucially, a small disjunctive *linear* implication (`¬p ∨ q`): a handful per
/// product, with **no** `McCormick` envelopes and **no** sum-of-squares coupling. So
/// unlike the full relaxation they cannot blow up a single LRA/DPLL(T) solve, which
/// is why they can be applied even past the cross-product admission bound (see the
/// sign-refutation pre-check in [`check_with_nra_impl`]).
#[allow(clippy::similar_names)] // a_ge/a_le/b_ge/… mirror the sign-rule structure
fn sign_zero_lemmas(
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
    Ok(out)
}

/// Sound linear lemmas about the product `r = a·b`: the sign rules and the zero
/// rule ([`sign_zero_lemmas`]), plus threshold-1 monotonicity. All are valid facts
/// about real multiplication, so adding them keeps the abstraction a relaxation
/// (original models, with `r = a·b`, satisfy them) while making it strong enough to
/// decide sign-based nonlinear queries.
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

    // implication p → q, as ¬p ∨ q.
    let imp = |arena: &mut TermArena, p: TermId, q: TermId| -> Result<TermId, IrError> {
        let np = arena.not(p)?;
        arena.or(np, q)
    };
    // sign + zero rules (the cheap, blowup-free core).
    let mut out = sign_zero_lemmas(arena, a, b, r)?;

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

    // Shrinking at threshold 1: a factor in [0,1] moves the other operand toward 0
    // — e.g. 0≤a≤1 ∧ b≥0 ⇒ a·b ≤ 1·b = b. These need only *one* operand bounded
    // (a≤1), so they fire where the two-sided McCormick envelopes cannot, e.g.
    // `0≤x≤1 ∧ y≥0 ∧ x·y > y` (unsat: x·y ≤ y).
    let a_le1 = arena.real_le(a, one)?;
    let b_le1 = arena.real_le(b, one)?;
    let a01 = arena.and(a_ge, a_le1)?; // 0 ≤ a ≤ 1
    let b01 = arena.and(b_ge, b_le1)?; // 0 ≤ b ≤ 1
    let a01_bge = arena.and(a01, b_ge)?;
    out.push(imp(arena, a01_bge, r_le_b)?); // (0≤a≤1 ∧ b≥0) → r≤b
    let a01_ble = arena.and(a01, b_le)?;
    out.push(imp(arena, a01_ble, r_ge_b)?); // (0≤a≤1 ∧ b≤0) → r≥b
    let b01_age = arena.and(b01, a_ge)?;
    out.push(imp(arena, b01_age, r_le_a)?); // (0≤b≤1 ∧ a≥0) → r≤a
    let b01_ale = arena.and(b01, a_le)?;
    out.push(imp(arena, b01_ale, r_ge_a)?); // (0≤b≤1 ∧ a≤0) → r≥a
    Ok(out)
}

/// **Sum-of-squares lemmas** linking the abstracted products of a variable *pair*.
///
/// For operands `a`, `b` whose squares `a·a`, `b·b` and cross product `a·b` are all
/// abstracted (to result vars `r_aa`, `r_bb`, `r_ab`), the identities `(a−b)² ≥ 0`
/// and `(a+b)² ≥ 0` expand to two **sound linear facts over the abstraction vars**:
///
/// ```text
///   r_aa + r_bb − 2·r_ab ≥ 0     (from (a−b)² = a² − 2ab + b²)
///   r_aa + r_bb + 2·r_ab ≥ 0     (from (a+b)² = a² + 2ab + b²)
/// ```
///
/// They hold in *every* real model (`r_aa = a²`, etc.), so adding them keeps the
/// abstraction a relaxation — but they capture the cross-product coupling that
/// independent product abstraction throws away, so the LRA relaxation can now refute
/// AM–GM-class goals (`a²+b² ≥ 2ab`, the 2-variable Cauchy–Schwarz) that the
/// sign/monotonicity/McCormick lemmas leave `unknown`. The lemmas are over the
/// result vars already, so they need no operand→var remap.
fn sos_lemmas(
    arena: &mut TermArena,
    triples: &[(TermId, TermId, TermId)],
) -> Result<Vec<TermId>, IrError> {
    // square_of[x] = the result var abstracting x·x.
    let mut square_of: HashMap<TermId, TermId> = HashMap::new();
    for &(a, b, r) in triples {
        if a == b {
            square_of.insert(a, r);
        }
    }
    let zero = arena.real_const(axeyum_ir::Rational::integer(0));
    let mut out = Vec::new();
    for &(a, b, r_ab) in triples {
        if a == b {
            continue; // a square is its own operand; the SOS pair is a≠b
        }
        let (Some(&r_aa), Some(&r_bb)) = (square_of.get(&a), square_of.get(&b)) else {
            continue; // need both squares abstracted to state the identity
        };
        let sum = arena.real_add(r_aa, r_bb)?; // a² + b²
        let two_ab = arena.real_add(r_ab, r_ab)?; // 2·ab
        let diff_sq = arena.real_sub(sum, two_ab)?; // (a−b)²
        out.push(arena.real_ge(diff_sq, zero)?);
        let sum_sq = arena.real_add(sum, two_ab)?; // (a+b)²
        out.push(arena.real_ge(sum_sq, zero)?);
    }
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
    // Overflow-safe tightening: if comparing two constants cross-multiplies out of
    // `i128` range, keep the existing bound (only loses tightness — still sound,
    // never a wrong verdict, and `Ord` would otherwise panic).
    let mut see_lo = |c: axeyum_ir::Rational| {
        lo = Some(
            lo.map_or(c, |x: axeyum_ir::Rational| match x.checked_cmp(&c) {
                Some(core::cmp::Ordering::Less) => c,
                _ => x,
            }),
        );
    };
    let mut see_hi = |c: axeyum_ir::Rational| {
        hi = Some(
            hi.map_or(c, |x: axeyum_ir::Rational| match x.checked_cmp(&c) {
                Some(core::cmp::Ordering::Greater) => c,
                _ => x,
            }),
        );
    };
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
                if l == t
                    && let Some(c) = rc
                {
                    see_hi(c); // t ≤ c
                }
                if r == t
                    && let Some(c) = lc
                {
                    see_lo(c); // c ≤ t
                }
            }
            Op::RealGe | Op::RealGt => {
                if l == t
                    && let Some(c) = rc
                {
                    see_lo(c); // t ≥ c
                }
                if r == t
                    && let Some(c) = lc
                {
                    see_hi(c); // c ≥ t
                }
            }
            Op::Eq => {
                if l == t
                    && let Some(c) = rc
                {
                    see_lo(c);
                    see_hi(c);
                }
                if r == t
                    && let Some(c) = lc
                {
                    see_lo(c);
                    see_hi(c);
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
