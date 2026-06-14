//! Finite-domain quantifier expansion (ADR-0016 follow-on).
//!
//! `forall x:S. P(x)` over a finite sort `S` is equivalent to the conjunction of
//! its instances `P(v_0) ∧ … ∧ P(v_k)` over every value of `S`; `exists` is the
//! disjunction. [`expand_quantifiers`] performs this expansion bottom-up,
//! substituting each domain value for the bound symbol, producing a
//! **quantifier-free** formula the existing engines decide. It is complete for
//! finite domains (`Bool`, small `BitVec`); infinite/over-wide domains are an
//! error. The expansion is untrusted — the caller replays the *original*
//! quantified formula through the enumerating ground evaluator.

use std::collections::HashMap;

use axeyum_ir::{IrError, Op, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::canonical::build_app;

/// The largest bit-vector width a quantifier may be expanded over (`2^10`
/// instances); wider domains would blow up the formula and are rejected.
pub const QUANT_EXPAND_BIT_LIMIT: u32 = 10;

/// Error from quantifier expansion.
#[derive(Debug, Clone)]
pub enum QuantExpandError {
    /// A quantifier ranges over a domain expansion cannot enumerate (an infinite
    /// sort, or a bit-vector wider than [`QUANT_EXPAND_BIT_LIMIT`]).
    UnsupportedDomain(Sort),
    /// An IR builder error while constructing instances.
    Ir(IrError),
}

impl core::fmt::Display for QuantExpandError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            QuantExpandError::UnsupportedDomain(sort) => {
                write!(f, "cannot expand quantifier over domain {sort}")
            }
            QuantExpandError::Ir(error) => write!(f, "quantifier expansion IR error: {error}"),
        }
    }
}

impl core::error::Error for QuantExpandError {}

impl From<IrError> for QuantExpandError {
    fn from(error: IrError) -> Self {
        QuantExpandError::Ir(error)
    }
}

/// Expands every quantifier in `assertions` to quantifier-free form.
///
/// If no assertion contains a quantifier, the assertions are returned unchanged.
///
/// # Errors
///
/// Returns [`QuantExpandError`] for a non-enumerable quantifier domain or an
/// internal IR builder error.
pub fn expand_quantifiers(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Vec<TermId>, QuantExpandError> {
    let mut expander = Expander::default();
    let mut out = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        out.push(expander.expand(arena, assertion)?);
    }
    Ok(out)
}

#[derive(Default)]
struct Expander {
    memo: HashMap<TermId, TermId>,
}

impl Expander {
    fn expand(&mut self, arena: &mut TermArena, term: TermId) -> Result<TermId, QuantExpandError> {
        if let Some(&cached) = self.memo.get(&term) {
            return Ok(cached);
        }
        let node = arena.node(term).clone();
        let result = match node {
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_)
            | TermNode::Symbol(_) => term,
            TermNode::App {
                op: Op::Forall(var),
                args,
            } => {
                let body = self.expand(arena, args[0])?;
                instantiate(arena, var, body, true)?
            }
            TermNode::App {
                op: Op::Exists(var),
                args,
            } => {
                let body = self.expand(arena, args[0])?;
                instantiate(arena, var, body, false)?
            }
            TermNode::App { op, args } => {
                let mut expanded = Vec::with_capacity(args.len());
                for &arg in &args {
                    expanded.push(self.expand(arena, arg)?);
                }
                build_app(arena, op, &expanded)?
            }
        };
        self.memo.insert(term, result);
        Ok(result)
    }
}

/// Expands `forall var. body` (or `exists`) over `var`'s finite domain by
/// substituting each value and folding with `and` (`forall`) / `or` (`exists`).
/// `body` is already quantifier-free.
fn instantiate(
    arena: &mut TermArena,
    var: SymbolId,
    body: TermId,
    is_forall: bool,
) -> Result<TermId, QuantExpandError> {
    let values = domain_values(arena, var)?;
    let mut acc: Option<TermId> = None;
    for value in values {
        let mut subst_memo = HashMap::new();
        let instance = substitute(arena, body, var, value, &mut subst_memo)?;
        acc = Some(match acc {
            Some(prev) => {
                if is_forall {
                    arena.and(prev, instance)?
                } else {
                    arena.or(prev, instance)?
                }
            }
            None => instance,
        });
    }
    // Bool and BitVec domains are non-empty, so `acc` is always set.
    Ok(acc.expect("quantifier domain is non-empty"))
}

/// The constant terms making up a finite domain for `var`.
fn domain_values(arena: &mut TermArena, var: SymbolId) -> Result<Vec<TermId>, QuantExpandError> {
    match arena.symbol(var).1 {
        Sort::Bool => Ok(vec![arena.bool_const(false), arena.bool_const(true)]),
        Sort::BitVec(width) if width <= QUANT_EXPAND_BIT_LIMIT => {
            let mut values = Vec::with_capacity(1usize << width);
            for value in 0..(1u128 << width) {
                values.push(arena.bv_const(width, value)?);
            }
            Ok(values)
        }
        // A floating-point domain is finite (`exp + sig` bits); enumerate every
        // bit pattern as a `Float`-sorted constant (ADR-0026), so small FP formats
        // (FP8/FP4) quantify by exhaustive expansion just like bit-vectors.
        Sort::Float { exp, sig } if exp + sig <= QUANT_EXPAND_BIT_LIMIT => {
            let width = exp + sig;
            let mut values = Vec::with_capacity(1usize << width);
            for value in 0..(1u128 << width) {
                let bv = arena.bv_const(width, value)?;
                values.push(arena.fp_from_bits(bv, exp, sig)?);
            }
            Ok(values)
        }
        other => Err(QuantExpandError::UnsupportedDomain(other)),
    }
}

/// Substitutes `replacement` for every free occurrence of `var` in `term`.
/// `term` is quantifier-free, so there is no binder shadowing to handle.
fn substitute(
    arena: &mut TermArena,
    term: TermId,
    var: SymbolId,
    replacement: TermId,
    memo: &mut HashMap<TermId, TermId>,
) -> Result<TermId, QuantExpandError> {
    if let Some(&cached) = memo.get(&term) {
        return Ok(cached);
    }
    let node = arena.node(term).clone();
    let result = match node {
        TermNode::Symbol(symbol) if symbol == var => replacement,
        TermNode::BoolConst(_)
        | TermNode::BvConst { .. }
        | TermNode::WideBvConst(_)
        | TermNode::IntConst(_)
        | TermNode::RealConst(_)
        | TermNode::Symbol(_) => term,
        TermNode::App { op, args } => {
            let mut new_args = Vec::with_capacity(args.len());
            for &arg in &args {
                new_args.push(substitute(arena, arg, var, replacement, memo)?);
            }
            build_app(arena, op, &new_args)?
        }
    };
    memo.insert(term, result);
    Ok(result)
}

/// The result of [`instantiate_universals`].
#[derive(Debug, Clone)]
pub struct Instantiation {
    /// The rewritten assertions: each top-level `forall` replaced by the
    /// conjunction of its ground instances.
    pub assertions: Vec<TermId>,
    /// Whether any universal was instantiated (and thus weakened). When `false`,
    /// the assertions are unchanged and any solver result is exact; when `true`,
    /// only an `unsat` result transfers soundly to the original.
    pub instantiated: bool,
    /// Whether a quantifier remains after instantiation (a nested quantifier, an
    /// existential, or a non-top-level binder). If so the result is not purely
    /// quantifier-free and a caller must not trust a quantifier-free decision.
    pub residual_quantifier: bool,
}

/// **Enumerative ground instantiation** of top-level universals, for sound
/// refutation of (possibly infinite-domain) quantified formulas.
///
/// Each top-level `forall x. body` (with a quantifier-free `body`) is replaced by
/// the conjunction of `body[x := t]` over every **ground term** `t` of `x`'s sort
/// appearing in the assertions (constants and free variables). Since
/// `forall x. body` implies each instance, the rewritten set is *weaker*, so if
/// it is unsatisfiable the original is too — a sound `unsat` procedure that, for
/// `Int`/`Real` universals, succeeds where finite-domain expansion cannot.
/// (A satisfiable instantiation says nothing about the original.)
///
/// # Errors
///
/// Returns [`QuantExpandError`] on an internal IR builder error.
pub fn instantiate_universals(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Instantiation, QuantExpandError> {
    let bound = bound_variables(arena, assertions);
    let universe = ground_universe(arena, assertions, &bound);

    let mut out = Vec::with_capacity(assertions.len());
    let mut instantiated = false;
    for &assertion in assertions {
        if let Some((vars, body)) = peel_universals(arena, assertion) {
            // Per-variable bindings: the ground leaves of each variable's sort.
            let per_var: Vec<Vec<TermId>> = vars
                .iter()
                .map(|&v| {
                    let sort = arena.symbol(v).1;
                    universe.get(&sort).cloned().unwrap_or_default()
                })
                .collect();
            match instantiate_chain(arena, &vars, body, &per_var)? {
                Some(term) => {
                    instantiated = true;
                    out.push(term);
                }
                // Over the cartesian-instance cap: leave the universal in place
                // (reported as a residual quantifier → `unknown`, sound).
                None => out.push(assertion),
            }
            continue;
        }
        out.push(assertion);
    }

    let residual_quantifier = out.iter().any(|&a| contains_quantifier(arena, a));
    Ok(Instantiation {
        assertions: out,
        instantiated,
        residual_quantifier,
    })
}

/// The cap on the number of cartesian-product instances a single universal chain
/// may expand to; above it the chain is left uninstantiated (a sound `unknown`).
const CHAIN_INSTANCE_CAP: usize = 4096;

/// Peels a (possibly nested) prenex universal chain `forall x1. … forall xk.
/// body` into its bound variables and quantifier-free `body`. Returns `None` if
/// `assertion` is not a universal, or if the body still contains a quantifier
/// (a non-prenex or existential residual the instantiation does not handle).
fn peel_universals(arena: &TermArena, assertion: TermId) -> Option<(Vec<SymbolId>, TermId)> {
    let mut vars = Vec::new();
    let mut current = assertion;
    while let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(current)
    {
        vars.push(*var);
        current = args[0];
    }
    if vars.is_empty() || contains_quantifier(arena, current) {
        return None;
    }
    Some((vars, current))
}

/// Instantiates `forall vars. body` over the cartesian product of each
/// variable's `per_var` bindings, folding the instances with `and`. Returns
/// `Ok(None)` if the product exceeds [`CHAIN_INSTANCE_CAP`]. An empty product
/// (some variable has no binding) drops the universal to `true` (sound
/// weakening). Bindings are ground, so sequential substitution is capture-free.
fn instantiate_chain(
    arena: &mut TermArena,
    vars: &[SymbolId],
    body: TermId,
    per_var: &[Vec<TermId>],
) -> Result<Option<TermId>, QuantExpandError> {
    // Total instances = product of per-variable binding counts (capped).
    let mut total: usize = 1;
    for bindings in per_var {
        if bindings.is_empty() {
            return Ok(Some(arena.bool_const(true)));
        }
        total = match total.checked_mul(bindings.len()) {
            Some(t) if t <= CHAIN_INSTANCE_CAP => t,
            _ => return Ok(None),
        };
    }

    // Enumerate the cartesian product via a mixed-radix index vector.
    let mut indices = vec![0usize; vars.len()];
    let mut conjunction: Option<TermId> = None;
    for _ in 0..total {
        let mut instance = body;
        for (slot, &var) in vars.iter().enumerate() {
            let replacement = per_var[slot][indices[slot]];
            let mut memo = HashMap::new();
            instance = substitute(arena, instance, var, replacement, &mut memo)?;
        }
        conjunction = Some(match conjunction {
            Some(acc) => arena.and(acc, instance)?,
            None => instance,
        });
        // Increment the mixed-radix counter.
        for slot in (0..indices.len()).rev() {
            indices[slot] += 1;
            if indices[slot] < per_var[slot].len() {
                break;
            }
            indices[slot] = 0;
        }
    }
    Ok(Some(
        conjunction.expect("total >= 1 so at least one instance"),
    ))
}

/// **Trigger-based E-matching instantiation** of top-level universals — a more
/// targeted, and strictly more capable, alternative to [`instantiate_universals`].
///
/// For each top-level `forall x. body`, it picks the *triggers* of the body — the
/// uninterpreted-function (`apply`) and array (`select`) subterms that mention
/// `x` — and instantiates `x` with every ground term that makes a trigger match a
/// ground subterm of the assertions (E-matching). Crucially this binds `x` to
/// **compound** ground terms (e.g. `f(a)`, `select(m,i)`), which the
/// leaves-only enumeration in [`instantiate_universals`] never tries, so it
/// refutes goals that pure enumeration cannot. When a universal has no
/// function/array trigger (e.g. `forall x. x > 0`), it falls back to the
/// enumerative ground leaves of `x`'s sort.
///
/// Soundness is identical to enumerative instantiation: every instance follows
/// from the universal, so the rewritten set is weaker and a returned `unsat`
/// transfers to the original. Trigger selection only affects *which* (sound)
/// instances are produced, never correctness.
///
/// # Errors
///
/// Returns [`QuantExpandError`] on an internal IR builder error.
pub fn instantiate_with_triggers(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<Instantiation, QuantExpandError> {
    let bound = bound_variables(arena, assertions);
    let ground = ground_subterms(arena, assertions, &bound);
    let leaves = ground_universe(arena, assertions, &bound);
    // Congruence closure over the ground subterms, seeded by the asserted ground
    // equalities, so trigger matching is performed **modulo equality** (proper
    // E-matching): `g(x)` matches `g(c)` even when only `g(a)` is present, given
    // `a = c`.
    let egraph = EGraph::build(
        arena,
        &ground,
        &collect_ground_equalities(arena, assertions),
    );

    let mut out = Vec::with_capacity(assertions.len());
    let mut instantiated = false;
    for &assertion in assertions {
        if let Some((vars, body)) = peel_universals(arena, assertion) {
            // Per-variable bindings: enumerative leaves augmented with the
            // (possibly compound) terms found by E-matching the body's triggers
            // modulo congruence, including triggers that bind several of the
            // chain's variables at once (e.g. `g(x, y)` against `g(f(c), h(c))`).
            let per_var = trigger_per_var_bindings(arena, body, &vars, &leaves, &egraph);
            match instantiate_chain(arena, &vars, body, &per_var)? {
                Some(term) => {
                    instantiated = true;
                    out.push(term);
                }
                None => out.push(assertion),
            }
            continue;
        }
        out.push(assertion);
    }

    let residual_quantifier = out.iter().any(|&a| contains_quantifier(arena, a));
    Ok(Instantiation {
        assertions: out,
        instantiated,
        residual_quantifier,
    })
}

/// Per-variable instantiation bindings for a universal chain over `vars`: each
/// variable's enumerative ground leaves **augmented** with the terms it receives
/// when the body's triggers are E-matched **modulo congruence** against the
/// ground subterms (using the [`EGraph`]).
///
/// Matching is multi-variable (one trigger can bind several chain variables) and
/// congruence-aware (a trigger matches any ground term in the same equivalence
/// class, at every position). Each bound value joins its variable's candidate
/// set; the chain instantiation then takes the cartesian product. The union with
/// the leaves keeps it strictly at least as capable as [`instantiate_universals`].
/// With no asserted equalities every class is a singleton and matching reduces to
/// the syntactic case.
fn trigger_per_var_bindings(
    arena: &TermArena,
    body: TermId,
    vars: &[SymbolId],
    leaves: &HashMap<Sort, Vec<TermId>>,
    egraph: &EGraph,
) -> Vec<Vec<TermId>> {
    let var_set: std::collections::BTreeSet<SymbolId> = vars.iter().copied().collect();

    // E-match every trigger against the equivalence classes whose members share
    // the trigger's head, collecting the variable bindings each match induces.
    let mut matches: Vec<HashMap<SymbolId, TermId>> = Vec::new();
    for &trigger in &collect_triggers(arena, body, &var_set) {
        let TermNode::App { op: trigger_op, .. } = arena.node(trigger) else {
            continue;
        };
        for (&class_rep, members) in &egraph.classes {
            let head_matches = members
                .iter()
                .any(|&g| matches!(arena.node(g), TermNode::App { op, .. } if op == trigger_op));
            if !head_matches {
                continue;
            }
            for binding in ematch(arena, trigger, class_rep, &var_set, egraph) {
                if !binding.is_empty() && !matches.contains(&binding) {
                    matches.push(binding);
                }
                if matches.len() > MATCH_CAP {
                    break;
                }
            }
        }
    }

    vars.iter()
        .map(|&v| {
            let sort = arena.symbol(v).1;
            let mut candidates = leaves.get(&sort).cloned().unwrap_or_default();
            for binding in &matches {
                if let Some(&term) = binding.get(&v) {
                    if !candidates.contains(&term) {
                        candidates.push(term);
                    }
                }
            }
            candidates
        })
        .collect()
}

/// A backstop on the number of E-match substitutions collected, guarding against
/// blow-up from large equivalence classes.
const MATCH_CAP: usize = 4096;

/// The triggers of `body`: `apply`/`select` subterms mentioning at least one of
/// the chain's variables. Deterministic order.
fn collect_triggers(
    arena: &TermArena,
    body: TermId,
    var_set: &std::collections::BTreeSet<SymbolId>,
) -> Vec<TermId> {
    let mut triggers = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Apply(_) | Op::Select) && contains_any_var(arena, term, var_set) {
                triggers.push(term);
            }
            stack.extend(args.iter().copied());
        }
    }
    triggers.sort_by_key(|t| t.index());
    triggers
}

/// A congruence closure over ground terms: an equivalence partition under the
/// asserted ground equalities, closed so that applications with pairwise-equal
/// arguments are themselves equal. Used to match triggers modulo equality.
struct EGraph {
    /// Each ground term mapped to its class representative.
    rep: HashMap<TermId, TermId>,
    /// Each representative mapped to the ground terms in its class.
    classes: HashMap<TermId, Vec<TermId>>,
}

/// Union–find root with path compression.
fn uf_find(parent: &mut [usize], mut i: usize) -> usize {
    while parent[i] != i {
        parent[i] = parent[parent[i]];
        i = parent[i];
    }
    i
}

/// Union–find merge; returns whether the two were in distinct classes.
fn uf_union(parent: &mut [usize], a: usize, b: usize) -> bool {
    let (ra, rb) = (uf_find(parent, a), uf_find(parent, b));
    if ra == rb {
        return false;
    }
    parent[ra.max(rb)] = ra.min(rb);
    true
}

impl EGraph {
    /// Builds the congruence closure over `ground`, seeded with `equalities`.
    fn build(arena: &TermArena, ground: &[TermId], equalities: &[(TermId, TermId)]) -> Self {
        // Union–find over a dense index of the ground terms.
        let index: HashMap<TermId, usize> =
            ground.iter().enumerate().map(|(i, &t)| (t, i)).collect();
        let mut parent: Vec<usize> = (0..ground.len()).collect();

        for &(a, b) in equalities {
            if let (Some(&ia), Some(&ib)) = (index.get(&a), index.get(&b)) {
                uf_union(&mut parent, ia, ib);
            }
        }

        // Congruence fixpoint: merge same-head applications with pairwise-equal
        // arguments. Ground sets are small, so an O(n²) sweep per pass is fine.
        let apps: Vec<usize> = ground
            .iter()
            .enumerate()
            .filter(|&(_, &t)| matches!(arena.node(t), TermNode::App { .. }))
            .map(|(i, _)| i)
            .collect();
        loop {
            let mut changed = false;
            for (a_pos, &ia) in apps.iter().enumerate() {
                for &ib in &apps[a_pos + 1..] {
                    if uf_find(&mut parent, ia) == uf_find(&mut parent, ib) {
                        continue;
                    }
                    if congruent(arena, ground[ia], ground[ib], &index, &mut parent)
                        && uf_union(&mut parent, ia, ib)
                    {
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }

        // Materialize representatives (the smallest-index member is canonical)
        // and class memberships.
        let mut rep = HashMap::new();
        let mut classes: HashMap<TermId, Vec<TermId>> = HashMap::new();
        for (i, &t) in ground.iter().enumerate() {
            let r = ground[uf_find(&mut parent, i)];
            rep.insert(t, r);
            classes.entry(r).or_default().push(t);
        }
        EGraph { rep, classes }
    }

    /// The representative ground term of `t`'s class (or `t` itself if `t` is not
    /// a tracked ground term).
    fn rep_of(&self, t: TermId) -> TermId {
        self.rep.get(&t).copied().unwrap_or(t)
    }
}

/// Whether two ground applications are congruent: same head/arity with
/// pairwise class-equal arguments.
fn congruent(
    arena: &TermArena,
    a: TermId,
    b: TermId,
    index: &HashMap<TermId, usize>,
    parent: &mut [usize],
) -> bool {
    match (arena.node(a), arena.node(b)) {
        (TermNode::App { op: oa, args: aa }, TermNode::App { op: ob, args: ab })
            if oa == ob && aa.len() == ab.len() =>
        {
            aa.iter()
                .zip(ab.iter())
                .all(|(&x, &y)| match (index.get(&x), index.get(&y)) {
                    (Some(&ix), Some(&iy)) => uf_find(parent, ix) == uf_find(parent, iy),
                    _ => x == y,
                })
        }
        _ => false,
    }
}

/// E-matches `pattern` against the equivalence class represented by `class_rep`,
/// modulo congruence, returning every variable substitution that matches. Bound
/// variables (`var_set`) bind to the class representative ground term.
fn ematch(
    arena: &TermArena,
    pattern: TermId,
    class_rep: TermId,
    var_set: &std::collections::BTreeSet<SymbolId>,
    egraph: &EGraph,
) -> Vec<HashMap<SymbolId, TermId>> {
    if let TermNode::Symbol(symbol) = arena.node(pattern) {
        if var_set.contains(symbol) {
            // Bind the variable to the class's representative ground term (sorts
            // must agree).
            if arena.sort_of(class_rep) == arena.sort_of(pattern) {
                return vec![HashMap::from([(*symbol, class_rep)])];
            }
            return Vec::new();
        }
    }
    match arena.node(pattern) {
        TermNode::App {
            op: pop,
            args: pargs,
        } => {
            let pargs = pargs.clone();
            let mut results = Vec::new();
            let Some(members) = egraph.classes.get(&class_rep) else {
                return results;
            };
            for &g in members {
                if let TermNode::App {
                    op: gop,
                    args: gargs,
                } = arena.node(g)
                {
                    if gop == pop && gargs.len() == pargs.len() {
                        let gargs = gargs.clone();
                        // Combine, by consistent merge, the substitutions from
                        // matching each argument against the class of g's argument.
                        let mut combos: Vec<HashMap<SymbolId, TermId>> = vec![HashMap::new()];
                        for (p_arg, g_arg) in pargs.iter().zip(gargs.iter()) {
                            let sub = ematch(arena, *p_arg, egraph.rep_of(*g_arg), var_set, egraph);
                            combos = merge_substitutions(&combos, &sub);
                            if combos.is_empty() {
                                break;
                            }
                        }
                        results.extend(combos);
                    }
                }
            }
            results
        }
        // A ground leaf (constant or free symbol) matches the class iff it is in
        // it.
        _ => {
            if egraph.rep_of(pattern) == class_rep {
                vec![HashMap::new()]
            } else {
                Vec::new()
            }
        }
    }
}

/// Cartesian product of two substitution lists, keeping only pairs that agree on
/// every shared variable.
fn merge_substitutions(
    a: &[HashMap<SymbolId, TermId>],
    b: &[HashMap<SymbolId, TermId>],
) -> Vec<HashMap<SymbolId, TermId>> {
    let mut out = Vec::new();
    for ma in a {
        for mb in b {
            let consistent = mb
                .iter()
                .all(|(k, v)| ma.get(k).is_none_or(|existing| existing == v));
            if consistent {
                let mut merged = ma.clone();
                merged.extend(mb.iter().map(|(&k, &v)| (k, v)));
                out.push(merged);
            }
        }
    }
    out
}

/// Collects the ground equalities entailed by `assertions`: the `(a, b)` pairs of
/// every top-level conjunct `a = b` whose sides are both ground (so the equality
/// holds in every model and is sound to use for congruence).
fn collect_ground_equalities(arena: &TermArena, assertions: &[TermId]) -> Vec<(TermId, TermId)> {
    let bound = bound_variables(arena, assertions);
    let mut equalities = Vec::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut seen = std::collections::BTreeSet::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            match op {
                // Descend through top-level conjunctions.
                Op::BoolAnd => stack.extend(args.iter().copied()),
                Op::Eq if args.len() == 2 => {
                    let (a, b) = (args[0], args[1]);
                    if is_ground(arena, a, &bound) && is_ground(arena, b, &bound) {
                        equalities.push((a, b));
                    }
                }
                _ => {}
            }
        }
    }
    equalities
}

/// Whether `term` is free of every bound variable (a ground term).
fn is_ground(
    arena: &TermArena,
    term: TermId,
    bound: &std::collections::BTreeSet<SymbolId>,
) -> bool {
    let mut memo = HashMap::new();
    term_is_ground(arena, term, bound, &mut memo)
}

/// Whether `term` contains a free occurrence of any variable in `var_set`.
fn contains_any_var(
    arena: &TermArena,
    term: TermId,
    var_set: &std::collections::BTreeSet<SymbolId>,
) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(symbol) if var_set.contains(symbol) => return true,
            TermNode::App { args, .. } => stack.extend(args.iter().copied()),
            _ => {}
        }
    }
    false
}

/// All ground subterms (no bound variable anywhere inside) of `assertions`,
/// **including compound terms** like `f(a)` — the E-matching candidate set.
fn ground_subterms(
    arena: &TermArena,
    assertions: &[TermId],
    bound: &std::collections::BTreeSet<SymbolId>,
) -> Vec<TermId> {
    // Memoized groundness, then collect the ground subterms in stable order.
    let mut is_ground: HashMap<TermId, bool> = HashMap::new();
    let mut order: Vec<TermId> = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    // First gather all subterms (post-order via an explicit stack).
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        order.push(term);
        if let TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    // Evaluate groundness; children appear later in `order`, so resolve by a
    // fixpoint-free recursive helper with the memo.
    let mut ground: Vec<TermId> = Vec::new();
    for &term in &order {
        if term_is_ground(arena, term, bound, &mut is_ground) {
            ground.push(term);
        }
    }
    ground.sort_by_key(|t| t.index());
    ground.dedup();
    ground
}

/// Memoized: whether `term` is free of every bound variable.
fn term_is_ground(
    arena: &TermArena,
    term: TermId,
    bound: &std::collections::BTreeSet<SymbolId>,
    memo: &mut HashMap<TermId, bool>,
) -> bool {
    if let Some(&cached) = memo.get(&term) {
        return cached;
    }
    let result = match arena.node(term) {
        TermNode::BoolConst(_)
        | TermNode::BvConst { .. }
        | TermNode::WideBvConst(_)
        | TermNode::IntConst(_)
        | TermNode::RealConst(_) => true,
        TermNode::Symbol(symbol) => !bound.contains(symbol),
        TermNode::App { args, .. } => args
            .clone()
            .iter()
            .all(|&arg| term_is_ground(arena, arg, bound, memo)),
    };
    memo.insert(term, result);
    result
}

/// All symbols bound by a quantifier anywhere in `assertions`.
fn bound_variables(
    arena: &TermArena,
    assertions: &[TermId],
) -> std::collections::BTreeSet<SymbolId> {
    let mut bound = std::collections::BTreeSet::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if let Op::Forall(var) | Op::Exists(var) = op {
                bound.insert(*var);
            }
            stack.extend(args.iter().copied());
        }
    }
    bound
}

/// Ground terms (constants and free variables) of each sort appearing in
/// `assertions`, keyed by sort — the instantiation universe.
fn ground_universe(
    arena: &TermArena,
    assertions: &[TermId],
    bound: &std::collections::BTreeSet<SymbolId>,
) -> HashMap<Sort, Vec<TermId>> {
    let mut universe: HashMap<Sort, Vec<TermId>> = HashMap::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        let ground = match arena.node(term) {
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_) => true,
            TermNode::Symbol(symbol) => !bound.contains(symbol),
            TermNode::App { args, .. } => {
                stack.extend(args.iter().copied());
                false
            }
        };
        if ground {
            let entry = universe.entry(arena.sort_of(term)).or_default();
            if !entry.contains(&term) {
                entry.push(term);
            }
        }
    }
    universe
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
    use super::expand_quantifiers;
    use axeyum_ir::{Assignment, Sort, TermArena, Value, eval};

    #[test]
    fn no_quantifiers_passes_through() {
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 4).unwrap();
        let one = arena.bv_const(4, 1).unwrap();
        let f = arena.eq(x, one).unwrap();
        assert_eq!(expand_quantifiers(&mut arena, &[f]).unwrap(), vec![f]);
    }

    #[test]
    fn forall_expands_to_conjunction_matching_the_evaluator() {
        // forall x:BV2. x + 0 == x  expands to a quantifier-free tautology.
        let mut arena = TermArena::new();
        let x_sym = arena.declare("x", Sort::BitVec(2)).unwrap();
        let x = arena.var(x_sym);
        let zero = arena.bv_const(2, 0).unwrap();
        let sum = arena.bv_add(x, zero).unwrap();
        let body = arena.eq(sum, x).unwrap();
        let all = arena.forall(x_sym, body).unwrap();

        let expanded = expand_quantifiers(&mut arena, &[all]).unwrap();
        // The expanded form is quantifier-free and evaluates to the same value
        // as the original quantifier (true) under the empty assignment.
        let asg = Assignment::new();
        assert_eq!(
            eval(&arena, expanded[0], &asg).unwrap(),
            eval(&arena, all, &asg).unwrap()
        );
        assert_eq!(eval(&arena, expanded[0], &asg).unwrap(), Value::Bool(true));
    }

    #[test]
    fn infinite_domain_is_rejected() {
        let mut arena = TermArena::new();
        let r_sym = arena.declare("r", Sort::Real).unwrap();
        let r = arena.var(r_sym);
        let zero = arena.real_ratio(0, 1);
        let ge = arena.real_ge(r, zero).unwrap();
        let all = arena.forall(r_sym, ge).unwrap();
        assert!(expand_quantifiers(&mut arena, &[all]).is_err());
    }
}
