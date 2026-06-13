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

    let mut out = Vec::with_capacity(assertions.len());
    let mut instantiated = false;
    for &assertion in assertions {
        if let Some((vars, body)) = peel_universals(arena, assertion) {
            // Per-variable bindings: enumerative leaves augmented with the
            // (possibly compound) terms found by E-matching the body's triggers,
            // including triggers that bind several of the chain's variables at
            // once (e.g. `g(x, y)` against `g(f(c), h(c))`).
            let per_var = trigger_per_var_bindings(arena, body, &vars, &ground, &leaves);
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
/// when the body's triggers are E-matched against the ground subterms.
///
/// Matching is **multi-variable**: a single trigger (e.g. `g(x, y)`) can bind
/// several chain variables at once (`x := f(c)`, `y := h(c)` against
/// `g(f(c), h(c))`), and each bound value is added to that variable's candidate
/// set. The chain instantiation then takes the cartesian product, which includes
/// the coupled tuple — so this refutes goals that need compound bindings of more
/// than one variable, which neither leaf enumeration nor single-variable
/// matching can reach. The union with the leaves keeps it strictly at least as
/// capable as [`instantiate_universals`].
fn trigger_per_var_bindings(
    arena: &TermArena,
    body: TermId,
    vars: &[SymbolId],
    ground: &[TermId],
    leaves: &HashMap<Sort, Vec<TermId>>,
) -> Vec<Vec<TermId>> {
    let var_set: std::collections::BTreeSet<SymbolId> = vars.iter().copied().collect();

    // Match every trigger against every ground subterm, collecting the variable
    // bindings each match induces.
    let mut matches: Vec<HashMap<SymbolId, TermId>> = Vec::new();
    for &trigger in &collect_triggers(arena, body, &var_set) {
        for &candidate in ground {
            let mut binding = HashMap::new();
            if match_multi(arena, trigger, candidate, &var_set, &mut binding) && !binding.is_empty()
            {
                matches.push(binding);
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

/// Matches trigger `pattern` against the ground term `candidate`, binding any of
/// the chain's variables (`var_set`) it covers into `binding` (consistently).
/// Returns `true` on a match.
fn match_multi(
    arena: &TermArena,
    pattern: TermId,
    candidate: TermId,
    var_set: &std::collections::BTreeSet<SymbolId>,
    binding: &mut HashMap<SymbolId, TermId>,
) -> bool {
    if let TermNode::Symbol(symbol) = arena.node(pattern) {
        if var_set.contains(symbol) {
            // A bound-variable position: bind it to `candidate` (sorts must
            // agree), or require consistency with an earlier binding.
            if arena.sort_of(candidate) != arena.sort_of(pattern) {
                return false;
            }
            if let Some(&prev) = binding.get(symbol) {
                return prev == candidate;
            }
            binding.insert(*symbol, candidate);
            return true;
        }
    }
    match (arena.node(pattern), arena.node(candidate)) {
        (TermNode::App { op: po, args: pa }, TermNode::App { op: go, args: ga })
            if po == go && pa.len() == ga.len() =>
        {
            let pairs: Vec<(TermId, TermId)> = pa.iter().copied().zip(ga.iter().copied()).collect();
            pairs
                .into_iter()
                .all(|(p, g)| match_multi(arena, p, g, var_set, binding))
        }
        // Non-variable leaves (constants, free symbols) match only their
        // hash-consed equal; a structural mismatch fails.
        _ => pattern == candidate,
    }
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
