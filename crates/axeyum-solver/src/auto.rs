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
        // model-based instantiation (MBQI), which loops adding model-violated
        // instances and itself defers to trigger-based (E-matching) instantiation
        // when it cannot refine.
        Err(SolverError::Unsupported(_)) => prove_unsat_by_mbqi(arena, assertions, config),
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
    // Lift Int/Real `ite` to the Boolean level (`ite(c,a,b)` → fresh `t` with
    // `c→t=a ∧ ¬c→t=b`) so the arithmetic linearizers, which only accept linear
    // arith terms, see a plain variable. An exact (equisatisfiable) rewrite, so
    // the dispatched result transfers directly. (BV `ite` is left for the
    // bit-blaster, which handles it natively.)
    let lifted = lift_arith_ite(arena, assertions)?;
    let assertions = &lifted;
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

/// Maximum model-based instantiation rounds before reporting `unknown`.
const MAX_MBQI_ROUNDS: usize = 16;

/// A `Value` as a constant term (scalar sorts only).
fn value_to_const(arena: &mut TermArena, value: &Value) -> Option<TermId> {
    match value {
        Value::Bool(b) => Some(arena.bool_const(*b)),
        Value::Int(n) => Some(arena.int_const(*n)),
        Value::Real(r) => Some(arena.real_const(*r)),
        Value::Bv { width, value } => arena.bv_const(*width, *value).ok(),
        _ => None,
    }
}

/// Model-based quantifier instantiation (MBQI): a refutation loop for top-level
/// universals over infinite domains. Each round decides `ground ∧ instances`; on
/// a `sat` candidate, every universal `∀x. body` is checked against the model at
/// the values the model assigns (its candidate instantiation set), and any
/// instance the model **falsifies** — a consequence of the universal that the
/// model violates — is added, blocking that model. `unsat` of the augmented
/// (still-implied) query transfers soundly; if no universal can be refined the
/// result is `unknown` (an infinite `∀` cannot be confirmed `sat` here).
///
/// # Errors
///
/// Returns [`SolverError`] from the underlying engine or an internal builder.
#[allow(clippy::too_many_lines)]
pub fn prove_unsat_by_mbqi(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Split into ground assertions and top-level universals `(bound_var, body)`.
    // This loop only handles single-variable universals with quantifier-free
    // bodies: a quantified body (multi-variable `forall`) or a quantifier in a
    // ground position (existential, nested) is outside its scope, so the whole
    // query defers to the trigger-based fallback (which instantiates uniformly).
    let mut ground: Vec<TermId> = Vec::new();
    let mut universals: Vec<(axeyum_ir::SymbolId, TermId)> = Vec::new();
    for &a in assertions {
        if let TermNode::App { op: Op::Forall(sym), args } = arena.node(a) {
            if has_quantifier(arena, &[args[0]]) {
                return prove_unsat_by_ematching(arena, assertions, config);
            }
            universals.push((*sym, args[0]));
        } else if has_quantifier(arena, &[a]) {
            return prove_unsat_by_ematching(arena, assertions, config);
        } else {
            ground.push(a);
        }
    }
    if universals.is_empty() {
        // No top-level universal to instantiate; defer to the trigger fallback.
        return prove_unsat_by_ematching(arena, assertions, config);
    }
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());

    let mut instances: Vec<TermId> = Vec::new();
    for _ in 0..MAX_MBQI_ROUNDS {
        let mut query = ground.clone();
        query.extend(instances.iter().copied());
        // The query is now quantifier-free (ground + instances).
        let result = check_auto(arena, &query, config)?;
        let CheckResult::Sat(model) = result else {
            // `unsat` (sound — instances are implied) or `unknown` transfers.
            return Ok(result);
        };
        let assignment = model.to_assignment();
        // Candidate instantiation values: the distinct values the model assigns,
        // grouped by sort, plus 0/1 defaults for arithmetic robustness.
        let mut added = false;
        for &(sym, body) in &universals {
            let sort = arena.symbol(sym).1;
            let var = arena.var(sym);
            let mut candidates: Vec<Value> = Vec::new();
            for (_, v) in model.iter() {
                if v.sort() == sort && !candidates.contains(&v) {
                    candidates.push(v);
                }
            }
            // The key MBQI heuristic: evaluate the body's ground subterms (those
            // not mentioning the bound variable) of the right sort under the
            // model and use their values — so a violation at e.g. `a + b` is found.
            let mut seen = BTreeSet::new();
            let mut stack = vec![body];
            while let Some(t) = stack.pop() {
                if t == var || !seen.insert(t) {
                    continue;
                }
                if arena.sort_of(t) == sort
                    && let Ok(v) = eval(arena, t, &assignment)
                    && !candidates.contains(&v)
                {
                    candidates.push(v);
                }
                if let TermNode::App { args, .. } = arena.node(t) {
                    let args = args.clone();
                    stack.extend(args);
                }
            }
            match sort {
                Sort::Int => {
                    for d in [0i128, 1, -1] {
                        let v = Value::Int(d);
                        if !candidates.contains(&v) {
                            candidates.push(v);
                        }
                    }
                }
                Sort::Bool => {
                    candidates.push(Value::Bool(false));
                    candidates.push(Value::Bool(true));
                }
                _ => {}
            }
            for v in candidates {
                let mut probe = assignment.clone();
                probe.set(sym, v.clone());
                if matches!(eval(arena, body, &probe), Ok(Value::Bool(false))) {
                    // The model falsifies `body[x:=v]`; add it (implied by ∀x.body).
                    let Some(c) = value_to_const(arena, &v) else {
                        continue;
                    };
                    let var = arena.var(sym);
                    let mut map: HashMap<TermId, TermId> = HashMap::new();
                    map.insert(var, c);
                    let mut memo: HashMap<TermId, TermId> = HashMap::new();
                    let inst = replace_subterms(arena, body, &map, &mut memo).map_err(err)?;
                    if !instances.contains(&inst) {
                        instances.push(inst);
                        added = true;
                    }
                    break;
                }
            }
        }
        if !added {
            // No universal could be refined at this model: the trigger-based
            // family may still refute via compound terms; otherwise `unknown`.
            return prove_unsat_by_ematching(arena, assertions, config);
        }
    }
    Ok(CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: format!("MBQI did not converge within {MAX_MBQI_ROUNDS} rounds"),
    }))
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

/// Lifts each Int/Real-sorted `ite(c, a, b)` to a fresh variable `t` plus the
/// Boolean constraints `c → t = a` and `¬c → t = b` (i.e. `¬c ∨ t=a`, `c ∨ t=b`).
/// An exact, equisatisfiable rewrite that moves arithmetic `ite` out of the
/// linear-arithmetic terms (which the simplices' linearizers do not accept) into
/// the propositional structure the lazy-SMT loop handles.
fn lift_arith_ite(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    let mut ites: Vec<TermId> = Vec::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            let (op, args) = (*op, args.clone());
            if op == Op::Ite && matches!(arena.sort_of(t), Sort::Int | Sort::Real) {
                ites.push(t);
            }
            stack.extend(args);
        }
    }
    if ites.is_empty() {
        return Ok(assertions.to_vec());
    }
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut constraints: Vec<TermId> = Vec::new();
    for (k, t) in ites.iter().enumerate() {
        let TermNode::App { args, .. } = arena.node(*t) else {
            continue;
        };
        let (c, a, b) = (args[0], args[1], args[2]);
        let sort = arena.sort_of(*t);
        let sym = arena.declare(&format!("!ite_{k}"), sort).map_err(err)?;
        let tv = arena.var(sym);
        map.insert(*t, tv);
        let nc = arena.not(c).map_err(err)?;
        let ta = arena.eq(tv, a).map_err(err)?;
        let tb = arena.eq(tv, b).map_err(err)?;
        constraints.push(arena.or(nc, ta).map_err(err)?);
        constraints.push(arena.or(c, tb).map_err(err)?);
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

/// Maximum integer range over which a bounded `to_real(i)` is linked exactly to
/// its operand (a finite case-split); wider ranges fall back to relaxation.
const MAX_COERCION_LINK: i128 = 64;

/// Replaces each Int↔Real coercion (`to_real`/`to_int`/`is_int`) with a fresh
/// variable of its result sort, shared per distinct term so a contradiction on
/// the same coerced value is preserved. For a `to_real(i)` whose integer operand
/// has a small constant range, also appends exact linking constraints
/// `(i = v) → (r = v)` for each `v` in range — making that coercion *complete*
/// (not just a relaxation). Returns the rewritten assertions (plus any links) and
/// whether any coercion was found; `sat` soundness still comes from replay.
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
    let mut links: Vec<TermId> = Vec::new();
    for (idx, t) in terms.into_iter().enumerate() {
        let sort = arena.sort_of(t);
        let sym = arena.declare(&format!("!coerce_{idx}"), sort).map_err(err)?;
        let fresh = arena.var(sym);
        map.insert(t, fresh);
        // Exact linking for a bounded `to_real(i)`: r = i over its finite range.
        if let TermNode::App { op: Op::IntToReal, args } = arena.node(t) {
            let operand = args[0];
            if let (Some(lo), Some(hi)) = int_bounds(arena, assertions, operand) {
                if hi >= lo && hi - lo <= MAX_COERCION_LINK {
                    for v in lo..=hi {
                        let iv = arena.int_const(v);
                        let rv = arena.real_const(axeyum_ir::Rational::integer(v));
                        let i_eq = arena.eq(operand, iv).map_err(err)?;
                        let r_eq = arena.eq(fresh, rv).map_err(err)?;
                        let n = arena.not(i_eq).map_err(err)?;
                        links.push(arena.or(n, r_eq).map_err(err)?); // (i=v) → (r=v)
                    }
                }
            }
        }
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len() + links.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
    }
    out.extend(links);
    Ok((out, true))
}

/// Tightest constant `(lower, upper)` bounds on integer `term` from the
/// top-level assertions (`term ≤ c`, `c ≤ term`, `<`/`>` with the ±1 shift, and
/// `term = c`); each `None` if unbounded.
fn int_bounds(
    arena: &TermArena,
    assertions: &[TermId],
    term: TermId,
) -> (Option<i128>, Option<i128>) {
    let mut lo: Option<i128> = None;
    let mut hi: Option<i128> = None;
    let mut see_lo = |c: i128| lo = Some(lo.map_or(c, |x: i128| x.max(c)));
    let mut see_hi = |c: i128| hi = Some(hi.map_or(c, |x: i128| x.min(c)));
    let int_const = |t: TermId| match arena.node(t) {
        TermNode::IntConst(n) => Some(*n),
        _ => None,
    };
    for &a in assertions {
        let TermNode::App { op, args } = arena.node(a) else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        let (op, l, r) = (*op, args[0], args[1]);
        let (lc, rc) = (int_const(l), int_const(r));
        match op {
            Op::IntLe => {
                if l == term && let Some(c) = rc {
                    see_hi(c);
                }
                if r == term && let Some(c) = lc {
                    see_lo(c);
                }
            }
            Op::IntLt => {
                if l == term && let Some(c) = rc {
                    see_hi(c - 1);
                }
                if r == term && let Some(c) = lc {
                    see_lo(c + 1);
                }
            }
            Op::IntGe => {
                if l == term && let Some(c) = rc {
                    see_lo(c);
                }
                if r == term && let Some(c) = lc {
                    see_hi(c);
                }
            }
            Op::IntGt => {
                if l == term && let Some(c) = rc {
                    see_lo(c + 1);
                }
                if r == term && let Some(c) = lc {
                    see_hi(c - 1);
                }
            }
            Op::Eq => {
                if l == term && let Some(c) = rc {
                    see_lo(c);
                    see_hi(c);
                }
                if r == term && let Some(c) = lc {
                    see_lo(c);
                    see_hi(c);
                }
            }
            _ => {}
        }
    }
    (lo, hi)
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
