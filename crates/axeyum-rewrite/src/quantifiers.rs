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
        if let TermNode::App {
            op: Op::Forall(var),
            args,
        } = arena.node(assertion).clone()
        {
            let body = args[0];
            if !contains_quantifier(arena, body) {
                instantiated = true;
                let sort = arena.symbol(var).1;
                let terms = universe.get(&sort).cloned().unwrap_or_default();
                let mut conjunction: Option<TermId> = None;
                for term in terms {
                    let mut memo = HashMap::new();
                    let instance = substitute(arena, body, var, term, &mut memo)?;
                    conjunction = Some(match conjunction {
                        Some(acc) => arena.and(acc, instance)?,
                        None => instance,
                    });
                }
                // An empty universe drops the universal entirely (sound
                // weakening): represent it as `true`.
                out.push(conjunction.unwrap_or_else(|| arena.bool_const(true)));
                continue;
            }
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
        if let TermNode::App {
            op: Op::Forall(var),
            args,
        } = arena.node(assertion).clone()
        {
            let body = args[0];
            if !contains_quantifier(arena, body) {
                instantiated = true;
                let var_sort = arena.symbol(var).1;
                let bindings = trigger_bindings(arena, body, var, var_sort, &ground, &leaves);
                let mut conjunction: Option<TermId> = None;
                for term in bindings {
                    let mut memo = HashMap::new();
                    let instance = substitute(arena, body, var, term, &mut memo)?;
                    conjunction = Some(match conjunction {
                        Some(acc) => arena.and(acc, instance)?,
                        None => instance,
                    });
                }
                out.push(conjunction.unwrap_or_else(|| arena.bool_const(true)));
                continue;
            }
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

/// The ground terms to instantiate `var` with: the enumerative ground leaves of
/// `var`'s sort **augmented** with the compound ground terms found by matching
/// the body's function/array triggers. The union makes this strictly at least as
/// capable as [`instantiate_universals`] — it tries every leaf binding *and* the
/// compound bindings (e.g. `f(a)`) that leaves-only enumeration misses.
fn trigger_bindings(
    arena: &TermArena,
    body: TermId,
    var: SymbolId,
    var_sort: Sort,
    ground: &[TermId],
    leaves: &HashMap<Sort, Vec<TermId>>,
) -> Vec<TermId> {
    let mut bindings: Vec<TermId> = leaves.get(&var_sort).cloned().unwrap_or_default();
    for &trigger in &collect_triggers(arena, body, var) {
        for &candidate in ground {
            let mut binding: Option<TermId> = None;
            if match_trigger(arena, trigger, candidate, var, var_sort, &mut binding) {
                if let Some(term) = binding {
                    if !bindings.contains(&term) {
                        bindings.push(term);
                    }
                }
            }
        }
    }
    bindings
}

/// The triggers of `body` for `var`: `apply`/`select` subterms that mention
/// `var`. Deterministic order (first occurrence in a stable traversal).
fn collect_triggers(arena: &TermArena, body: TermId, var: SymbolId) -> Vec<TermId> {
    let mut triggers = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![body];
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Apply(_) | Op::Select) && contains_var(arena, term, var) {
                triggers.push(term);
            }
            stack.extend(args.iter().copied());
        }
    }
    // Stable order independent of the traversal's pop order.
    triggers.sort_by_key(|t| t.index());
    triggers
}

/// Matches trigger `pattern` (which may contain `var`) against the ground term
/// `candidate`, binding `var` consistently. Returns `true` on a match.
fn match_trigger(
    arena: &TermArena,
    pattern: TermId,
    candidate: TermId,
    var: SymbolId,
    var_sort: Sort,
    binding: &mut Option<TermId>,
) -> bool {
    if let TermNode::Symbol(symbol) = arena.node(pattern) {
        if *symbol == var {
            // `var` position: bind it to `candidate` (sorts must agree), or
            // require consistency with an earlier binding.
            if arena.sort_of(candidate) != var_sort {
                return false;
            }
            if let Some(bound) = binding {
                return *bound == candidate;
            }
            *binding = Some(candidate);
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
                .all(|(p, g)| match_trigger(arena, p, g, var, var_sort, binding))
        }
        // Non-`var` leaves (constants, free symbols) match only their hash-consed
        // equal; a structural mismatch fails.
        _ => pattern == candidate,
    }
}

/// Whether `term` contains a free occurrence of `var`.
fn contains_var(arena: &TermArena, term: TermId, var: SymbolId) -> bool {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(symbol) if *symbol == var => return true,
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
