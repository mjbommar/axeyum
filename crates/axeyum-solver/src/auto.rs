//! Unified solver front door: [`solve`] decides any supported query, and
//! [`check_auto`] the quantifier-free fragment, by routing on theory features.
//!
//! Engines:
//!
//! - the **bit-blasting composition** ([`crate::check_with_all_theories`]) for
//!   Bool, bit-vectors, arrays, uninterpreted functions, and bounded integers —
//!   it handles arbitrary Boolean structure natively, since `or`/`ite`/… lower
//!   straight to CNF;
//! - the **lazy-SMT / DPLL(T)** loop ([`crate::check_with_lra_dpll`]) for linear
//!   real arithmetic, which also drives a *complete combination* of reals with
//!   the bit-blasted theories: reals share no sort with them, so the only
//!   coupling is propositional and the loop's case split suffices (no
//!   interface-equality propagation);
//! - **quantifiers** ([`check_with_quantifiers`] finite-domain expansion, with a
//!   sound [`prove_unsat_by_instantiation`] fallback for infinite domains),
//!   chained by [`solve`].
//!
//! Every `sat` is replayed through the ground evaluator against the original
//! query, so no routing or combination step can yield an unsound `sat`.

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode, Value, eval};
use axeyum_rewrite::{
    QuantExpandError, expand_quantifiers, instantiate_universals, instantiate_with_triggers,
    replace_subterms,
};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::combined::check_with_all_theories;
use crate::dpll_lia::{check_with_arith_dpll, check_with_lia_dpll};
use crate::lia::DEFAULT_INT_WIDTH;
use crate::lra::check_with_lia_simplex;
use crate::sat_bv_backend::SatBvBackend;

/// The unified front door: decides any supported query — quantifier-free or
/// quantified, over any combination of the supported theories.
///
/// - A **quantifier-free** query is dispatched by [`check_auto`].
/// - A **quantified** query is first decided by finite-domain expansion
///   ([`check_with_quantifiers`], complete for `Bool`/`BitVec` domains); if a
///   quantifier ranges over an infinite domain (`Int`/`Real`), it falls back to
///   sound enumerative instantiation ([`prove_unsat_by_instantiation`], which
///   establishes `unsat` and otherwise reports `unknown`).
///
/// # Errors
///
/// Returns [`SolverError`] from the chosen engine; constructs outside the
/// supported fragment surface as [`SolverError::Unsupported`].
pub fn solve(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    if !has_quantifier(arena, assertions) {
        return check_auto(arena, assertions, config);
    }
    match check_with_quantifiers(arena, assertions, config) {
        // An infinite quantifier domain defeats finite expansion; fall back to
        // sound trigger-based (E-matching) instantiation, which subsumes plain
        // leaf enumeration.
        Err(SolverError::Unsupported(_)) => prove_unsat_by_ematching(arena, assertions, config),
        other => other,
    }
}

/// Extracts a **minimal unsatisfiable core** of `assertions`: the indices of a
/// jointly-unsatisfiable subset in which every member is necessary (dropping any
/// one makes the rest satisfiable or undecided). Theory-agnostic — it works for
/// any query [`solve`] can decide.
///
/// The algorithm is deletion-based: starting from the full (unsat) set, it tries
/// removing each assertion in turn and keeps the removal only when the remainder
/// is still **definitively** `unsat` (an `unknown` remainder is conservatively
/// kept, so the result is always a genuine core). It costs `O(n)` solver calls
/// for `n` assertions and re-decides the final core as a defensive self-check.
///
/// Returns `Ok(None)` when the whole set is satisfiable or could not be decided
/// (`unknown`), so there is no core to report.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for queries outside the supported
/// fragment, or [`SolverError`] from the underlying engine, including a
/// [`SolverError::Backend`] if the extracted core fails to re-decide as `unsat`.
pub fn unsat_core(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<Option<Vec<usize>>, SolverError> {
    // Only an unsatisfiable query has a core.
    if !matches!(solve(arena, assertions, config)?, CheckResult::Unsat) {
        return Ok(None);
    }

    // Deletion-based minimization over the assertion indices, in a fixed order
    // for determinism. `core` always denotes an unsatisfiable subset.
    let mut core: Vec<usize> = (0..assertions.len()).collect();
    for candidate in 0..assertions.len() {
        if !core.contains(&candidate) {
            continue;
        }
        let trial: Vec<TermId> = core
            .iter()
            .filter(|&&i| i != candidate)
            .map(|&i| assertions[i])
            .collect();
        // Keep the removal only if the smaller set is *definitively* unsat; an
        // `unknown` remainder cannot justify dropping the assertion.
        if !trial.is_empty() && matches!(solve(arena, &trial, config)?, CheckResult::Unsat) {
            core.retain(|&i| i != candidate);
        }
    }

    // Defensive self-check: the minimized subset must still be unsat.
    let subset: Vec<TermId> = core.iter().map(|&i| assertions[i]).collect();
    if !matches!(solve(arena, &subset, config)?, CheckResult::Unsat) {
        return Err(SolverError::Backend(
            "unsat-core self-check failed: extracted core is not unsatisfiable".to_owned(),
        ));
    }
    Ok(Some(core))
}

/// Whether any assertion contains a quantifier.
fn has_quantifier(arena: &TermArena, assertions: &[TermId]) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            stack.extend(args.iter().copied());
        }
    }
    false
}

/// Decides any supported quantifier-free query, dispatching to the appropriate
/// engine: the lazy-SMT loop when reals are present (combined with the
/// bit-blasted theories), the bit-blasting composition otherwise. Integer
/// reasoning uses the default bounded bit-blasting width ([`DEFAULT_INT_WIDTH`]);
/// use the specific entry points for finer control.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for queries outside the supported
/// fragment, or [`SolverError`] from the chosen engine.
pub fn check_auto(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Int↔Real coercions (`to_real`/`to_int`/`is_int`) couple the int and real
    // theories; a complete decision needs Nelson-Oppen. We relax each coercion to
    // a fresh variable of its result sort — shared per distinct term, so a
    // contradiction on the *same* coerced value (e.g. `to_real(i) > 5 ∧
    // to_real(i) < 5`) is still proven — dispatch the decoupled query, and replay
    // any `sat` candidate against the *original* (where the evaluator computes the
    // true coercion). `unsat` of the relaxation is sound; a candidate whose
    // coupling fails on replay is `unknown`.
    let (relaxed, had_coercion) = relax_coercions(arena, assertions)?;
    if !had_coercion {
        return check_auto_dispatch(arena, assertions, config);
    }
    match check_auto_dispatch(arena, &relaxed, config)? {
        CheckResult::Sat(model) => {
            let assignment = model.to_assignment();
            if assertions
                .iter()
                .all(|&a| matches!(eval(arena, a, &assignment), Ok(Value::Bool(true))))
            {
                Ok(CheckResult::Sat(model))
            } else {
                Ok(CheckResult::Unknown(UnknownReason {
                    kind: UnknownKind::Incomplete,
                    detail: "int↔real coercion relaxation: candidate fails the original coupling"
                        .to_owned(),
                }))
            }
        }
        other => Ok(other), // Unsat (sound) or Unknown
    }
}

/// The theory dispatcher (coercions already relaxed away by [`check_auto`]).
fn check_auto_dispatch(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let features = Features::scan(arena, assertions);
    if features.has_datatype {
        // Datatypes: fold read-over-construct, then decide the residual (or
        // report Unsupported if datatype variables remain). The residual is
        // datatype-free, so this does not re-enter here (ADR-0022).
        return crate::datatype_elim::check_with_datatype_elimination(arena, assertions, config);
    }
    if features.has_real && features.has_int {
        // Combined linear arithmetic (QF_LIRA): the lazy-SMT loop theory-checks
        // integer and real atoms with their exact simplices independently (they
        // share no sort). Falls back to the real loop on non-arithmetic atoms
        // (mixed BV/array), which bit-blasts them.
        match check_with_arith_dpll(arena, assertions, config) {
            Ok(result) => return Ok(result),
            Err(SolverError::Unsupported(_)) => {}
            Err(other) => return Err(other),
        }
    }
    if features.has_real {
        // Reals plus (optionally) the bit-blasted theories: the lazy-SMT loop
        // abstracts the real atoms and lets the bit-blasting backend decide the
        // rest. Reals share no sort with those theories, so the only coupling is
        // propositional and this is a complete combination. Routed through the
        // NRA layer, which abstracts any nonlinear products (relaxation + replay,
        // ADR-pending) and otherwise delegates straight to the LRA loop.
        return crate::nra::check_with_nra(arena, assertions, config);
    }
    if features.has_int {
        // Conjunctive pure-integer queries are decided soundly for *both* sat and
        // unsat by branch-and-bound over the simplex (ADR-0020); the bounded
        // bit-blasting fallback is sat-only. Boolean-structured pure-integer
        // queries (disjunctions/implications of integer atoms) are decided by the
        // lazy-SMT loop over that simplex. Anything outside the integer-arithmetic
        // fragment (mixed BV/array/UF terms) surfaces as `Unsupported` and falls
        // through to bit-blasting, which handles it.
        //
        // `div`/`mod`-by-constant and `abs` are first eliminated into exact linear
        // constraints (equisatisfiable), so the *complete* simplex/DPLL path
        // decides them for both `sat` and `unsat` — not just the sat-only
        // bit-blaster (whose in-range `unsat` is only `unknown`).
        let lin = axeyum_rewrite::eliminate_int_divmod(arena, assertions)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        match check_with_lia_simplex(arena, &lin) {
            Ok(result) => return Ok(result),
            Err(SolverError::Unsupported(_)) => {}
            Err(other) => return Err(other),
        }
        match check_with_lia_dpll(arena, &lin, config) {
            Ok(result) => return Ok(result),
            Err(SolverError::Unsupported(_)) => {}
            Err(other) => return Err(other),
        }
    }
    let mut backend = SatBvBackend::new();
    check_with_all_theories(&mut backend, arena, assertions, DEFAULT_INT_WIDTH, config)
}

/// Decides a (possibly quantified) query by **finite-domain quantifier
/// expansion** (ADR-0016) followed by [`check_auto`].
///
/// Every quantifier over a finite domain is expanded to its conjunction/
/// disjunction of instances, the quantifier-free result is dispatched, and a
/// `sat` model is **replayed against the original quantified formula** through
/// the enumerating ground evaluator (the trust anchor — an expansion bug cannot
/// yield an unsound `sat`).
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for a non-enumerable quantifier domain
/// or a query outside the supported fragment, or [`SolverError`] from the chosen
/// engine; a `sat` model that fails to replay is a [`SolverError::Backend`].
pub fn check_with_quantifiers(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let expanded = expand_quantifiers(arena, assertions).map_err(|error| match error {
        QuantExpandError::UnsupportedDomain(sort) => {
            SolverError::Unsupported(format!("quantifier over non-enumerable domain {sort}"))
        }
        QuantExpandError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;

    // `unsat`/`unknown` of the equivalent quantifier-free formula carries over
    // to the original (expansion is equivalence-preserving).
    let model = match check_auto(arena, &expanded, config)? {
        CheckResult::Sat(model) => model,
        other => return Ok(other),
    };

    // Replay the original *quantified* assertions through the enumerating
    // evaluator — the trust anchor for a quantified `sat`.
    let assignment = model.to_assignment();
    for &assertion in assertions {
        match eval(arena, assertion, &assignment) {
            Ok(Value::Bool(true)) => {}
            Ok(_) => {
                return Err(SolverError::Backend(format!(
                    "quantified sat model replay failed: assertion #{} not satisfied",
                    assertion.index()
                )));
            }
            Err(error) => {
                return Err(SolverError::Backend(format!(
                    "quantified sat model replay failed: assertion #{} evaluation error: {error}",
                    assertion.index()
                )));
            }
        }
    }
    Ok(CheckResult::Sat(model))
}

/// Attempts to **refute** a (possibly infinite-domain) quantified query by
/// enumerative ground instantiation of its top-level universals (the E-matching
/// family), then deciding the quantifier-free result with [`check_auto`].
///
/// Because instantiation only *weakens* (each instance follows from its
/// universal), a returned [`CheckResult::Unsat`] transfers soundly to the
/// original. A satisfiable instantiation does **not** establish the original is
/// satisfiable, so it is reported [`CheckResult::Unknown`] — *unless* no
/// universal was actually instantiated (a quantifier-free query), in which case
/// the exact `sat`/`unsat` is returned. This is the refutation tool for `Int`/
/// `Real` quantifiers that finite-domain expansion ([`check_with_quantifiers`])
/// cannot enumerate.
///
/// # Errors
///
/// Returns [`SolverError::Backend`] on an internal rewrite failure, or
/// [`SolverError`] from the underlying engine.
pub fn prove_unsat_by_instantiation(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let instantiation = instantiate_universals(arena, assertions)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    decide_instantiation(arena, &instantiation, config)
}

/// Attempts to **refute** a (possibly infinite-domain) quantified query by
/// **trigger-based E-matching** instantiation of its top-level universals, then
/// deciding the result with [`check_auto`].
///
/// Like [`prove_unsat_by_instantiation`] but more capable: each universal's
/// function/array triggers are matched against the formula's ground subterms, so
/// `x` is instantiated with **compound** ground terms (`f(a)`, `select(m,i)`),
/// not only leaves — refuting goals that pure leaf enumeration cannot reach. The
/// bindings still only *weaken* the query, so a returned [`CheckResult::Unsat`]
/// transfers soundly to the original (a satisfiable instantiation is `unknown`;
/// a quantifier-free query decides exactly).
///
/// # Errors
///
/// Returns [`SolverError::Backend`] on an internal rewrite failure, or
/// [`SolverError`] from the underlying engine.
pub fn prove_unsat_by_ematching(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let instantiation = instantiate_with_triggers(arena, assertions)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    decide_instantiation(arena, &instantiation, config)
}

/// Shared back half of the instantiation-based refutation entries: decides the
/// instantiated assertions and maps the result under the weakening contract.
fn decide_instantiation(
    arena: &mut TermArena,
    instantiation: &axeyum_rewrite::Instantiation,
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Quantifiers left after instantiation (nested, existential, or non-top
    // level) cannot be decided by the quantifier-free engines.
    if instantiation.residual_quantifier {
        return Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: "query has quantifiers instantiation does not reach (nested, \
                     existential, or non-top-level)"
                .to_owned(),
        }));
    }

    let result = check_auto(arena, &instantiation.assertions, config)?;
    if !instantiation.instantiated {
        // No universal was weakened: the result is exact.
        return Ok(result);
    }
    // Instantiation weakened the query: `unsat` transfers, anything else is
    // inconclusive for the original.
    match result {
        CheckResult::Unsat => Ok(CheckResult::Unsat),
        CheckResult::Sat(_) => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: "instantiation is satisfiable; the universal may still be violated \
                     outside the instantiated terms"
                .to_owned(),
        })),
        CheckResult::Unknown(reason) => Ok(CheckResult::Unknown(reason)),
    }
}

/// Replaces each Int↔Real coercion (`to_real`/`to_int`/`is_int`) with a fresh
/// variable of its result sort, shared per distinct term so a contradiction on
/// the same coerced value is preserved. Returns the rewritten assertions and
/// whether any coercion was found. A pure relaxation (the fresh variable is
/// unconstrained relative to the operand); soundness for `sat` comes from
/// replaying the original.
fn relax_coercions(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<(Vec<TermId>, bool), SolverError> {
    let mut terms: Vec<TermId> = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            let (op, args) = (*op, args.clone());
            if matches!(op, Op::IntToReal | Op::RealToInt | Op::RealIsInt) {
                terms.push(t);
            }
            stack.extend(args);
        }
    }
    if terms.is_empty() {
        return Ok((assertions.to_vec(), false));
    }
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    for (i, t) in terms.into_iter().enumerate() {
        let sort = arena.sort_of(t);
        let sym = arena.declare(&format!("!coerce_{i}"), sort).map_err(err)?;
        map.insert(t, arena.var(sym));
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
    }
    Ok((out, true))
}

/// Which theory features a query uses.
// A flat set of independent theory-presence flags reads better than a packed
// enum; each is checked independently in `check_auto`.
#[allow(clippy::struct_excessive_bools)]
struct Features {
    has_real: bool,
    /// Any sort/operator handled by the bit-blasting composition (bit-vectors,
    /// arrays, integers, uninterpreted functions) — i.e. not pure Bool/real.
    has_bitblast: bool,
    has_int: bool,
    /// Any datatype sort or constructor/selector/tester op (ADR-0022).
    has_datatype: bool,
}

impl Features {
    fn scan(arena: &TermArena, assertions: &[TermId]) -> Self {
        let mut features = Features {
            has_real: false,
            has_bitblast: false,
            has_int: false,
            has_datatype: false,
        };
        let mut seen = BTreeSet::new();
        let mut stack = assertions.to_vec();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match arena.sort_of(term) {
                Sort::Real => features.has_real = true,
                Sort::Int => {
                    features.has_bitblast = true;
                    features.has_int = true;
                }
                Sort::BitVec(_) | Sort::Array { .. } => features.has_bitblast = true,
                Sort::Datatype(_) => features.has_datatype = true,
                Sort::Bool => {}
            }
            if let TermNode::App { op, args } = arena.node(term) {
                if matches!(op, Op::Apply(_)) {
                    features.has_bitblast = true;
                }
                if matches!(
                    op,
                    Op::DtConstruct { .. } | Op::DtSelect { .. } | Op::DtTest(_)
                ) {
                    features.has_datatype = true;
                }
                stack.extend(args.iter().copied());
            }
        }
        features
    }
}
