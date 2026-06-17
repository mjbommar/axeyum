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

use axeyum_ir::{Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_rewrite::{
    QuantExpandError, build_app, expand_quantifiers, instantiate_universals,
    instantiate_with_triggers, replace_subterms,
};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::combined::check_with_all_theories;
use crate::dpll_lia::{check_with_arith_dpll, check_with_lia_dpll};
use crate::lia::DEFAULT_INT_WIDTH;
use crate::lra::{check_with_lia_simplex, check_with_lra};
use crate::model::Model;
use crate::qinst_egraph::prove_quantified_unsat_via_egraph;
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
    // Skolemize top-level existential assertions: `∃x. body` is equisatisfiable
    // with `body[x := fresh]` (the solver picks the witness), so this is exact and
    // — unlike finite expansion — decides infinite-domain existentials too.
    let skolemized = skolemize_top_existentials(arena, assertions)?;
    let assertions = &skolemized;

    if !has_quantifier(arena, assertions) {
        return check_auto(arena, assertions, config);
    }
    match check_with_quantifiers(arena, assertions, config) {
        // An infinite quantifier domain defeats finite expansion; fall back to
        // sound refutation. Try congruence-aware e-matching on the e-graph keystone
        // first (Track 2, P2.6): it instantiates inferred triggers *modulo the
        // ground congruence*, so equalities the bespoke loop misses fire here. Its
        // result is only ever `unsat` (sound — instances are implied) or `unknown`;
        // on `unknown` the model-based instantiation loop (MBQI, which itself defers
        // to the trigger-based family) takes over.
        Err(SolverError::Unsupported(_)) => {
            match prove_quantified_unsat_via_egraph(arena, assertions, config)? {
                CheckResult::Unsat => Ok(CheckResult::Unsat),
                _ => prove_unsat_by_mbqi(arena, assertions, config),
            }
        }
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

/// Skolemizes each top-level existential assertion `∃x. body` to `body[x := s]`
/// for a fresh constant `s` of `x`'s sort — equisatisfiable, and (unlike finite
/// expansion) complete for infinite domains. Non-existential assertions and
/// existentials in non-top-level positions are left unchanged.
fn skolemize_top_existentials(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut out = Vec::with_capacity(assertions.len());
    let mut k = 0u32;
    for &a in assertions {
        if let TermNode::App {
            op: Op::Exists(sym),
            args,
        } = arena.node(a)
        {
            let (sym, body) = (*sym, args[0]);
            let sort = arena.symbol(sym).1;
            let skolem = arena.declare(&format!("!sk_{k}"), sort).map_err(err)?;
            k += 1;
            let bound = arena.var(sym);
            let fresh = arena.var(skolem);
            let mut map: HashMap<TermId, TermId> = HashMap::new();
            map.insert(bound, fresh);
            let mut memo: HashMap<TermId, TermId> = HashMap::new();
            out.push(replace_subterms(arena, body, &map, &mut memo).map_err(err)?);
        } else {
            out.push(a);
        }
    }
    Ok(out)
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
    // `to_real` is a ring homomorphism, so fold `to_real(a) ± to_real(b)` into
    // `to_real(a ± b)` (bottom-up): a linear combination of coerced integers
    // collapses to one coercion, which the comparison rewrites below can then
    // eliminate exactly (e.g. `to_real(x) + to_real(y) ≤ 10`).
    let folded = fold_to_real_sums(arena, assertions)?;
    // A `to_real(i)` compared to a rational constant is order-isomorphic to an
    // integer comparison (`to_real(i) ≤ c ⟺ i ≤ ⌊c⌋`, etc.), so rewrite those
    // *exactly* to pure-integer atoms — eliminating the coercion completely (no
    // relaxation, no `unknown`) for the common "coerced int vs literal" pattern.
    // Dually, `to_int(r) = ⌊r⌋` compared to an integer constant rewrites to a
    // pure-real comparison (`to_int(r) ≤ c ⟺ r < c+1`, etc.).
    let r1 = eliminate_to_real_const_compare(arena, &folded)?;
    let assertions = &eliminate_to_int_const_compare(arena, &r1)?;

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
    // A `to_real` coercion couples the integer and real theories. Before the
    // (sound but incomplete) relaxation above, try exact mixed-integer linear
    // branch-and-bound: solve the LP relaxation with the Farkas-checked LRA
    // engine and branch on any coerced integer that comes back fractional. This
    // is *complete* for the linear mixed fragment — `unsat` is anchored by the
    // per-node Farkas certificate and `sat` by replay against the original. Out
    // of that fragment (or on the node budget) it returns `unknown`, and we fall
    // through to the relaxation.
    match check_with_milp(arena, assertions) {
        Ok(CheckResult::Sat(model)) => return Ok(CheckResult::Sat(model)),
        Ok(CheckResult::Unsat) => return Ok(CheckResult::Unsat),
        Ok(CheckResult::Unknown(_)) | Err(_) => {}
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

/// Node budget for the mixed-integer branch-and-bound; on exhaustion the result
/// is `unknown` (and `check_auto` falls back to the coercion relaxation).
const MAX_MILP_NODES: u32 = 2_000;

/// Decides a conjunctive mixed integer/real (`QF_LIRA`) query — with `to_real`
/// coercions intact — by mixed-integer linear branch-and-bound.
///
/// The query is lowered to an all-real LP by mapping every integer symbol to a
/// fresh real symbol and `to_real(i)` to that same symbol (so the coupling is
/// exact, not relaxed); the integer symbols are remembered as the integrality
/// constraints. Each branch-and-bound node solves the LP with the
/// Farkas-checked [`check_with_lra`] engine: `unsat` at a node is sound
/// (the LP relaxation has *more* solutions than the original), and a `sat` leaf
/// whose integer columns are all integral is **replayed against the original**
/// mixed query through the ground evaluator. Anything outside the linear mixed
/// fragment (nonlinear, `to_int`/`is_int`, bit-vectors, …) or the node budget
/// yields `unknown`, so the caller falls back to the sound relaxation.
fn check_with_milp(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<CheckResult, SolverError> {
    let mut lower = LiraLower::default();
    let mut real_assertions = Vec::with_capacity(assertions.len());
    for &a in assertions {
        real_assertions.push(lower.lower(arena, a)?);
    }
    // The fresh real symbols that must take integer values (former int symbols),
    // paired with the original integer symbol for model projection.
    let int_cols: Vec<(SymbolId, SymbolId)> =
        lower.int_to_real.iter().map(|(&i, &r)| (r, i)).collect();
    let mut budget = MAX_MILP_NODES;
    milp_bnb(arena, &real_assertions, &int_cols, assertions, &mut budget)
}

/// One branch-and-bound subtree over the all-real lowering `real_assertions`.
/// `int_cols` pairs each integrality-constrained real symbol with its original
/// integer symbol; `original` is the untouched mixed query (for `sat` replay).
fn milp_bnb(
    arena: &mut TermArena,
    real_assertions: &[TermId],
    int_cols: &[(SymbolId, SymbolId)],
    original: &[TermId],
    budget: &mut u32,
) -> Result<CheckResult, SolverError> {
    if *budget == 0 {
        // A deterministic search budget was hit (retryable with a larger budget),
        // not fundamental incompleteness — report ResourceLimit consistently with
        // the NRA branch-and-bound / refinement bounds.
        return Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: format!("MILP branch-and-bound exceeded {MAX_MILP_NODES} nodes"),
        }));
    }
    *budget -= 1;
    let model = match check_with_lra(arena, real_assertions)? {
        CheckResult::Unsat => return Ok(CheckResult::Unsat), // LP relaxation unsat ⇒ MILP unsat
        CheckResult::Unknown(r) => return Ok(CheckResult::Unknown(r)),
        CheckResult::Sat(model) => model,
    };
    // Find an integrality-constrained variable with a fractional LP value.
    for &(real_sym, _) in int_cols {
        let Some(Value::Real(q)) = model.get(real_sym) else {
            continue;
        };
        if q.is_integer() {
            continue;
        }
        let floor = q.numerator().div_euclid(q.denominator());
        let var = arena.var(real_sym);
        let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
        // Left branch: var ≤ floor.
        let le_c = arena.real_const(Rational::integer(floor));
        let le = arena.real_le(var, le_c).map_err(err)?;
        let mut left = real_assertions.to_vec();
        left.push(le);
        let left_res = milp_bnb(arena, &left, int_cols, original, budget)?;
        if let CheckResult::Sat(m) = left_res {
            return Ok(CheckResult::Sat(m));
        }
        // Right branch: var ≥ floor + 1.
        let ge_c = arena.real_const(Rational::integer(floor + 1));
        let ge = arena.real_ge(var, ge_c).map_err(err)?;
        let mut right = real_assertions.to_vec();
        right.push(ge);
        let right_res = milp_bnb(arena, &right, int_cols, original, budget)?;
        // The two half-spaces var≤floor / var≥floor+1 cover every integer value,
        // so: sat if either branch is sat; unsat only if *both* are unsat; else
        // unknown (a branch hit the budget).
        return Ok(match (left_res, right_res) {
            (_, CheckResult::Sat(m)) | (CheckResult::Sat(m), _) => CheckResult::Sat(m),
            (CheckResult::Unsat, CheckResult::Unsat) => CheckResult::Unsat,
            (CheckResult::Unknown(r), _) | (_, CheckResult::Unknown(r)) => CheckResult::Unknown(r),
        });
    }
    // All integrality columns are integral: a genuine MILP candidate. Replay it
    // against the *original* mixed query through the ground evaluator.
    let mut assignment = axeyum_ir::Assignment::new();
    let mut projected = Model::new();
    for &(real_sym, int_sym) in int_cols {
        let value = match model.get(real_sym) {
            Some(Value::Real(q)) if q.is_integer() => Value::Int(q.numerator()),
            _ => return Ok(milp_unknown()),
        };
        assignment.set(int_sym, value.clone());
        projected.set(int_sym, value);
    }
    // Carry the genuine real variables straight through.
    for (sym, value) in model.iter() {
        if int_cols.iter().any(|&(r, _)| r == sym) {
            continue; // integer column, already projected to its int symbol
        }
        assignment.set(sym, value.clone());
        projected.set(sym, value);
    }
    for &a in original {
        match eval(arena, a, &assignment) {
            Ok(Value::Bool(true)) => {}
            _ => return Ok(milp_unknown()),
        }
    }
    Ok(CheckResult::Sat(projected))
}

fn milp_unknown() -> CheckResult {
    CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: "MILP candidate failed replay against the original query".to_owned(),
    })
}

/// Lowers a mixed integer/real query to an all-real one for the MILP LP oracle:
/// each integer symbol becomes a fresh real symbol, `to_real(i)` becomes that
/// symbol, and the integer linear operators map to their real counterparts.
#[derive(Default)]
struct LiraLower {
    /// Original integer symbol → fresh real symbol.
    int_to_real: std::collections::BTreeMap<SymbolId, SymbolId>,
    memo: HashMap<TermId, TermId>,
}

impl LiraLower {
    fn real_of_int(
        &mut self,
        arena: &mut TermArena,
        int_sym: SymbolId,
    ) -> Result<TermId, SolverError> {
        if let Some(&r) = self.int_to_real.get(&int_sym) {
            return Ok(arena.var(r));
        }
        let name = format!("!milp.{}", int_sym.index());
        let r = arena
            .declare(&name, Sort::Real)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        self.int_to_real.insert(int_sym, r);
        Ok(arena.var(r))
    }

    #[allow(clippy::too_many_lines)]
    fn lower(&mut self, arena: &mut TermArena, t: TermId) -> Result<TermId, SolverError> {
        if let Some(&c) = self.memo.get(&t) {
            return Ok(c);
        }
        let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
        let node = arena.node(t).clone();
        let out = match node {
            TermNode::BoolConst(_) | TermNode::RealConst(_) => t,
            // Bit-vectors (and any other leaf) are outside the mixed LIA/LRA
            // fragment this oracle lowers.
            TermNode::BvConst { .. } | TermNode::WideBvConst(_) => {
                return Err(milp_out_of_fragment());
            }
            TermNode::IntConst(n) => arena.real_const(Rational::integer(n)),
            TermNode::Symbol(s) => match arena.sort_of(t) {
                Sort::Int => self.real_of_int(arena, s)?,
                Sort::Real | Sort::Bool => t,
                _ => return Err(milp_out_of_fragment()),
            },
            TermNode::App { op, args } => {
                // `to_real(i)` collapses to the lowered (real) integer operand.
                if matches!(op, Op::IntToReal) {
                    let inner = self.lower(arena, args[0])?;
                    self.memo.insert(t, inner);
                    return Ok(inner);
                }
                let mut low = Vec::with_capacity(args.len());
                for &a in &args {
                    low.push(self.lower(arena, a)?);
                }
                match op {
                    Op::IntNeg => arena.real_neg(low[0]).map_err(err)?,
                    Op::IntAdd => arena.real_add(low[0], low[1]).map_err(err)?,
                    Op::IntSub => arena.real_sub(low[0], low[1]).map_err(err)?,
                    Op::IntMul => arena.real_mul(low[0], low[1]).map_err(err)?,
                    Op::IntLt => arena.real_lt(low[0], low[1]).map_err(err)?,
                    Op::IntLe => arena.real_le(low[0], low[1]).map_err(err)?,
                    Op::IntGt => arena.real_gt(low[0], low[1]).map_err(err)?,
                    Op::IntGe => arena.real_ge(low[0], low[1]).map_err(err)?,
                    Op::Eq
                    | Op::BoolAnd
                    | Op::BoolOr
                    | Op::BoolNot
                    | Op::BoolXor
                    | Op::BoolImplies
                    | Op::Ite
                    | Op::RealNeg
                    | Op::RealAdd
                    | Op::RealSub
                    | Op::RealMul
                    | Op::RealLt
                    | Op::RealLe
                    | Op::RealGt
                    | Op::RealGe => build_app(arena, op, &low).map_err(err)?,
                    // to_int/is_int, integer div/mod/abs, bit-vectors, arrays, …
                    // are outside the linear mixed fragment this oracle handles.
                    _ => return Err(milp_out_of_fragment()),
                }
            }
        };
        self.memo.insert(t, out);
        Ok(out)
    }
}

fn milp_out_of_fragment() -> SolverError {
    SolverError::Unsupported("term outside the linear mixed integer/real fragment".to_owned())
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
        // Datatype structural axioms (acyclicity / distinctness / injectivity):
        // a forced containment cycle (`x = cons(h, x)`), two constructors on one
        // value (`x = nil ∧ x = cons(…)`), or an injectivity-vs-disequality clash
        // (`cons(h,x) = cons(h,y) ∧ x ≠ y`) is `unsat` — sound refutations the eager
        // tag/field expansion misses. Cheap; only ever fast-paths a correct `unsat`.
        if crate::datatype_acyclicity::prove_datatype_unsat_structurally(arena, assertions) {
            return Ok(CheckResult::Unsat);
        }
        // Datatypes: first fold read-over-construct and decide the residual
        // (ADR-0022 step A). If free datatype variables remain (under `is-c`/
        // `select`), that path reports `Unsupported`; decide those natively by
        // eager tag/field expansion (ADR-0022 step B).
        match crate::datatype_elim::check_with_datatype_elimination(arena, assertions, config) {
            Ok(result) => return Ok(result),
            Err(SolverError::Unsupported(_)) => {
                return crate::datatype_native::check_with_datatype_native(
                    arena, assertions, config,
                );
            }
            Err(other) => return Err(other),
        }
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
        // GCD divisibility test: a top-level integer equation whose coefficient gcd
        // does not divide its constant (e.g. `2x + 4y = 3`) is `unsat` — a sound
        // refutation that decides even *unbounded* equations the simplex/B&B cannot
        // terminate on. Cheap; only ever fast-paths a correct `unsat`.
        if crate::lia_gcd::prove_lia_unsat_by_gcd(arena, &lin) {
            return Ok(CheckResult::Unsat);
        }
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
    // Uninterpreted functions: try the lazy EUF path on the e-graph first. It
    // decides the equality/UF structure with congruence (no Ackermann blow-up) and
    // returns a replay-checked `sat` model or a congruence `unsat`; a result it
    // cannot soundly settle (base-sort semantics outside congruence) comes back
    // `unknown` and falls through to the complete bit-blasting Ackermann path. Both
    // its `sat` (replay-checked) and `unsat` (congruence, independently re-checked)
    // are sound for QF_UFBV, so this only ever fast-paths a correct answer.
    if features.has_function {
        // Try the **online** DPLL(T) decider on the backtrackable e-graph first: it
        // keeps one incremental congruence graph across the Boolean search (vs the
        // offline per-model rebuild) and is differentially validated against both
        // `check_qf_uf` and the Ackermann path. Both its `sat` (replay-checked) and
        // `unsat` (root-level congruence conflict) are sound. On `unknown` (no
        // equality atoms or Boolean structure outside its Tseitin encoder) fall
        // through to the offline enumeration, then to bit-blasting.
        match crate::euf_egraph::solve_qf_uf_online(arena, assertions) {
            CheckResult::Sat(model) => return Ok(CheckResult::Sat(model)),
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(_) => {}
        }
        match crate::euf_egraph::check_qf_uf(arena, assertions) {
            CheckResult::Sat(model) => return Ok(CheckResult::Sat(model)),
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(_) => {}
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
        if let TermNode::App {
            op: Op::Forall(sym),
            args,
        } = arena.node(a)
        {
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
                    // Also probe one above/below each integer candidate: bound
                    // universals like `∀x. x ≤ c` are violated at `c+1`, which the
                    // exact subterm value `c` does not surface on its own.
                    let neighbours: Vec<i128> = candidates
                        .iter()
                        .filter_map(|v| match v {
                            Value::Int(n) => Some(*n),
                            _ => None,
                        })
                        .flat_map(|n| [n.checked_add(1), n.checked_sub(1)])
                        .flatten()
                        .collect();
                    for n in neighbours.into_iter().chain([0, 1, -1]) {
                        let v = Value::Int(n);
                        if !candidates.contains(&v) {
                            candidates.push(v);
                        }
                    }
                }
                Sort::Real => {
                    // Probe one above/below each real candidate (e.g. `∀r. r ≤ c`
                    // is violated at `c + 1`); `±1` suffices to step across an
                    // open bound expressed by `<`/`≤`/`>`/`≥`.
                    let one = axeyum_ir::Rational::integer(1);
                    let neighbours: Vec<axeyum_ir::Rational> = candidates
                        .iter()
                        .filter_map(|v| match v {
                            Value::Real(r) => Some(*r),
                            _ => None,
                        })
                        .flat_map(|r| [r + one, r - one])
                        .collect();
                    for r in neighbours {
                        let v = Value::Real(r);
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

/// Folds `to_real(a) ± to_real(b)` into `to_real(a ± b)` bottom-up (the `Int→Real`
/// embedding is a ring homomorphism), collapsing a linear combination of coerced
/// integers into a single coercion. Equisatisfiable; enables the exact
/// comparison rewrites downstream.
fn fold_to_real_sums(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &a in assertions {
        out.push(fold_to_real_rec(arena, a, &mut memo).map_err(err)?);
    }
    Ok(out)
}

fn fold_to_real_rec(
    arena: &mut TermArena,
    term: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> Result<TermId, axeyum_ir::IrError> {
    if let Some(&c) = memo.get(&term) {
        return Ok(c);
    }
    let result = match arena.node(term) {
        TermNode::App { op, args } => {
            let (op, args) = (*op, args.clone());
            let mut new_args = Vec::with_capacity(args.len());
            for arg in &args {
                new_args.push(fold_to_real_rec(arena, *arg, memo)?);
            }
            let to_real_arg = |arena: &TermArena, t: TermId| match arena.node(t) {
                TermNode::App {
                    op: Op::IntToReal,
                    args,
                } => Some(args[0]),
                _ => None,
            };
            // to_real(a) +/- to_real(b)  ->  to_real(a +/- b)
            if matches!(op, Op::RealAdd | Op::RealSub)
                && let (Some(a), Some(b)) = (
                    to_real_arg(arena, new_args[0]),
                    to_real_arg(arena, new_args[1]),
                )
            {
                let int = if op == Op::RealAdd {
                    arena.int_add(a, b)?
                } else {
                    arena.int_sub(a, b)?
                };
                arena.int_to_real(int)?
            } else {
                build_app(arena, op, &new_args)?
            }
        }
        _ => term,
    };
    memo.insert(term, result);
    Ok(result)
}

/// Rewrites comparisons between `to_real(i)` and a rational constant into the
/// equivalent pure-integer atom (exact, since the integer embedding is
/// order-isomorphic): `to_real(i) ≤ c ⟺ i ≤ ⌊c⌋`, `< ⟺ i ≤ ⌈c⌉−1`,
/// `≥ ⟺ i ≥ ⌈c⌉`, `> ⟺ i ≥ ⌊c⌋+1`, `= c ⟺ i = c` if `c` is integral else
/// false. Eliminates the coercion entirely for these (no relaxation).
fn eliminate_to_real_const_compare(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    // Collect (comparison_atom -> replacement) for matching atoms.
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(t) else {
            continue;
        };
        let (op, args) = (*op, args.clone());
        // Recurse first so nested atoms are also considered.
        stack.extend(args.iter().copied());
        let is_cmp = matches!(
            op,
            Op::RealLt | Op::RealLe | Op::RealGt | Op::RealGe | Op::Eq
        );
        if !is_cmp || args.len() != 2 {
            continue;
        }
        // Identify `to_real(i)` and a real constant among the two operands.
        let to_real_arg = |t: TermId| match arena.node(t) {
            TermNode::App {
                op: Op::IntToReal,
                args,
            } => Some(args[0]),
            _ => None,
        };
        let real_const = |t: TermId| match arena.node(t) {
            TermNode::RealConst(r) => Some(*r),
            _ => None,
        };
        // `to_real(i) op to_real(j)` ⟺ `i op j` (both integer-valued): rewrite to
        // the integer comparison, eliminating both coercions exactly.
        if let (Some(i), Some(j)) = (to_real_arg(args[0]), to_real_arg(args[1])) {
            let new = match op {
                Op::RealLt => arena.int_lt(i, j).map_err(err)?,
                Op::RealLe => arena.int_le(i, j).map_err(err)?,
                Op::RealGt => arena.int_gt(i, j).map_err(err)?,
                Op::RealGe => arena.int_ge(i, j).map_err(err)?,
                Op::Eq => arena.eq(i, j).map_err(err)?,
                _ => continue,
            };
            map.insert(t, new);
            continue;
        }
        // Normalize to `to_real(i) <op'> c` (flip if the constant is on the left).
        let (i, c, flipped) =
            if let (Some(i), Some(c)) = (to_real_arg(args[0]), real_const(args[1])) {
                (i, c, false)
            } else if let (Some(c), Some(i)) = (real_const(args[0]), to_real_arg(args[1])) {
                (i, c, true)
            } else {
                continue;
            };
        let floor = c.numerator().div_euclid(c.denominator());
        let is_int = c.denominator() == 1;
        let ceil = if is_int { floor } else { floor + 1 };
        // Effective relation with `to_real(i)` on the left.
        let rel = match (op, flipped) {
            (Op::RealLt, false) | (Op::RealGt, true) => "lt",
            (Op::RealLe, false) | (Op::RealGe, true) => "le",
            (Op::RealGt, false) | (Op::RealLt, true) => "gt",
            (Op::RealGe, false) | (Op::RealLe, true) => "ge",
            (Op::Eq, _) => "eq",
            _ => continue,
        };
        let new = match rel {
            // i < c  ⟺  i ≤ ⌈c⌉−1
            "lt" => {
                let k = arena.int_const(ceil - 1);
                arena.int_le(i, k).map_err(err)?
            }
            "le" => {
                let k = arena.int_const(floor);
                arena.int_le(i, k).map_err(err)?
            }
            "gt" => {
                let k = arena.int_const(floor + 1);
                arena.int_ge(i, k).map_err(err)?
            }
            "ge" => {
                let k = arena.int_const(ceil);
                arena.int_ge(i, k).map_err(err)?
            }
            // i = c  ⟺  (c integral ∧ i = c) else false
            _ => {
                if is_int {
                    let k = arena.int_const(floor);
                    arena.eq(i, k).map_err(err)?
                } else {
                    arena.bool_const(false)
                }
            }
        };
        map.insert(t, new);
    }
    if map.is_empty() {
        return Ok(assertions.to_vec());
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
    }
    Ok(out)
}

/// Rewrites comparisons between `to_int(r)` (= ⌊r⌋) and an integer constant into
/// the equivalent pure-real atom (exact): `to_int(r) ≤ c ⟺ r < c+1`,
/// `< c ⟺ r < c`, `≥ c ⟺ r ≥ c`, `> c ⟺ r ≥ c+1`, `= c ⟺ c ≤ r < c+1`.
/// Eliminates the coercion for the common "floor vs integer literal" pattern.
fn eliminate_to_int_const_compare(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, SolverError> {
    let err = |e: axeyum_ir::IrError| SolverError::Backend(e.to_string());
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        let TermNode::App { op, args } = arena.node(t) else {
            continue;
        };
        let (op, args) = (*op, args.clone());
        stack.extend(args.iter().copied());
        if !matches!(op, Op::IntLt | Op::IntLe | Op::IntGt | Op::IntGe | Op::Eq) || args.len() != 2
        {
            continue;
        }
        let to_int_arg = |t: TermId| match arena.node(t) {
            TermNode::App {
                op: Op::RealToInt,
                args,
            } => Some(args[0]),
            _ => None,
        };
        let int_const = |t: TermId| match arena.node(t) {
            TermNode::IntConst(n) => Some(*n),
            _ => None,
        };
        let (r, c, flipped) = if let (Some(r), Some(c)) = (to_int_arg(args[0]), int_const(args[1]))
        {
            (r, c, false)
        } else if let (Some(c), Some(r)) = (int_const(args[0]), to_int_arg(args[1])) {
            (r, c, true)
        } else {
            continue;
        };
        let rel = match (op, flipped) {
            (Op::IntLt, false) | (Op::IntGt, true) => "lt",
            (Op::IntLe, false) | (Op::IntGe, true) => "le",
            (Op::IntGt, false) | (Op::IntLt, true) => "gt",
            (Op::IntGe, false) | (Op::IntLe, true) => "ge",
            (Op::Eq, _) => "eq",
            _ => continue,
        };
        let c_real = arena.real_const(axeyum_ir::Rational::integer(c));
        let c_plus_real = arena.real_const(axeyum_ir::Rational::integer(c + 1));
        let new = match rel {
            "lt" => arena.real_lt(r, c_real).map_err(err)?, // ⌊r⌋<c ⟺ r<c
            "le" => arena.real_lt(r, c_plus_real).map_err(err)?, // ⌊r⌋≤c ⟺ r<c+1
            "ge" => arena.real_ge(r, c_real).map_err(err)?, // ⌊r⌋≥c ⟺ r≥c
            "gt" => arena.real_ge(r, c_plus_real).map_err(err)?, // ⌊r⌋>c ⟺ r≥c+1
            _ => {
                // ⌊r⌋ = c ⟺ c ≤ r < c+1
                let ge = arena.real_ge(r, c_real).map_err(err)?;
                let lt = arena.real_lt(r, c_plus_real).map_err(err)?;
                arena.and(ge, lt).map_err(err)?
            }
        };
        map.insert(t, new);
    }
    if map.is_empty() {
        return Ok(assertions.to_vec());
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut out = Vec::with_capacity(assertions.len());
    for &a in assertions {
        out.push(replace_subterms(arena, a, &map, &mut memo).map_err(err)?);
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
        let sym = arena
            .declare(&format!("!coerce_{idx}"), sort)
            .map_err(err)?;
        let fresh = arena.var(sym);
        map.insert(t, fresh);
        // Exact linking for a bounded `to_real(i)`: r = i over its finite range.
        if let TermNode::App {
            op: Op::IntToReal,
            args,
        } = arena.node(t)
        {
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
                if l == term
                    && let Some(c) = rc
                {
                    see_hi(c);
                }
                if r == term
                    && let Some(c) = lc
                {
                    see_lo(c);
                }
            }
            Op::IntLt => {
                if l == term
                    && let Some(c) = rc
                {
                    see_hi(c - 1);
                }
                if r == term
                    && let Some(c) = lc
                {
                    see_lo(c + 1);
                }
            }
            Op::IntGe => {
                if l == term
                    && let Some(c) = rc
                {
                    see_lo(c);
                }
                if r == term
                    && let Some(c) = lc
                {
                    see_hi(c);
                }
            }
            Op::IntGt => {
                if l == term
                    && let Some(c) = rc
                {
                    see_lo(c + 1);
                }
                if r == term
                    && let Some(c) = lc
                {
                    see_hi(c - 1);
                }
            }
            Op::Eq => {
                if l == term
                    && let Some(c) = rc
                {
                    see_lo(c);
                    see_hi(c);
                }
                if r == term
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
    /// Any uninterpreted-function application (`Op::Apply`).
    has_function: bool,
}

impl Features {
    fn scan(arena: &TermArena, assertions: &[TermId]) -> Self {
        let mut features = Features {
            has_real: false,
            has_bitblast: false,
            has_int: false,
            has_datatype: false,
            has_function: false,
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
                Sort::BitVec(_) | Sort::Array { .. } | Sort::Float { .. } => {
                    features.has_bitblast = true;
                }
                Sort::Datatype(_) => features.has_datatype = true,
                Sort::Bool => {}
            }
            if let TermNode::App { op, args } = arena.node(term) {
                if matches!(op, Op::Apply(_)) {
                    features.has_bitblast = true;
                    features.has_function = true;
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

#[cfg(test)]
mod tests {
    use super::*;

    /// `solve` routes a *too-wide-to-enumerate* (`BitVec(32)`) quantified EUF
    /// refutation through the e-graph keystone instantiation loop: finite-domain
    /// expansion refuses a 2³² domain (`QUANT_EXPAND_BIT_LIMIT`), so the fallback
    /// fires, and the congruence-aware trigger instantiation refutes it by firing
    /// `f(x)` at the ground `f(a)`. This pins the dispatch wiring (`solve` →
    /// keystone) in place. (UF is finite-scalar-only in the IR, so a 33-bit-plus
    /// domain is how an unbounded UF quantifier surfaces here.)
    #[test]
    #[allow(clippy::many_single_char_names)]
    fn solve_refutes_wide_bv_quantified_euf_via_keystone() {
        let mut arena = TermArena::new();
        let w = 32;
        let bv = Sort::BitVec(w);
        let f = arena.declare_fun("f", &[bv], bv).unwrap();
        let a = arena.bv_var("a", w).unwrap();
        let b = arena.bv_var("b", w).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        // f(a) = b ∧ a ≠ b
        let fa_eq_b = arena.eq(fa, b).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let a_ne_b = arena.not(a_eq_b).unwrap();
        // ∀x. f(x) = x  (over a domain too wide to enumerate)
        let x = arena.declare("x", bv).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let body = arena.eq(fx, xv).unwrap();
        let forall = arena.forall(x, body).unwrap();

        // Instantiating x↦a gives f(a)=a, which with f(a)=b forces a=b ⨯ a≠b.
        let config = SolverConfig::default();
        let result = solve(&mut arena, &[forall, fa_eq_b, a_ne_b], &config).unwrap();
        assert!(
            matches!(result, CheckResult::Unsat),
            "expected Unsat from keystone instantiation, got {result:?}"
        );
    }
}
