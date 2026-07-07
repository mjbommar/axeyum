//! MBQI model-finding for the almost-uninterpreted fragment (P2.6 T2.6.5).
//!
//! The MBQI refutation loop in [`crate::auto::prove_unsat_by_mbqi`] can only
//! ever conclude `unsat` or `unknown` for a top-level universal over an infinite
//! domain: a `sat` candidate model of the ground-plus-instances query is not, on
//! its own, a model of the original `∀x. body` (the universal may be violated at
//! some `x` outside the instantiated terms). This module supplies the missing
//! `sat` direction: it certifies that a candidate quantifier-free model is a
//! **genuine** model of the universals, opening the quantified `sat` direction
//! *soundly* — it only ever turns `unknown` into `sat`, never a wrong verdict.
//!
//! # The fragment and why the finite check is exhaustive
//!
//! The certificate is sound-and-complete only for the *almost-uninterpreted*
//! fragment (Ge & de Moura 2009): the bound variable `x` is `Int` or `Real` and
//! every occurrence of `x` in `body` is a **direct argument of an
//! uninterpreted-function application** `(f … x …)`. In that fragment the truth
//! of `body[x]` under a candidate model is a function of the *finite* profile of
//! the outputs `(f₁(… x …), f₂(… x …), …)` of the UFs applied directly to `x`.
//! A candidate model interprets each UF as a **finite table plus a default**
//! ([`axeyum_ir::FuncValue`]) — a total interpretation — so as `x` ranges over
//! its infinite domain each `fᵢ(… x …)` takes only finitely many values: the
//! table entries whose key matches at `x`'s position, or the default otherwise.
//! A tuple `(… x …)` is a table key only if `x` equals the key's component at
//! `x`'s position, so the *special* `x`-values are a subset of the components of
//! the relevant UFs' table keys. Checking `body[x := v]` at
//!
//! * every table-key component `v` of every UF applied directly to `x` (which
//!   covers every "special" profile), plus
//! * **one** generic value `g` chosen outside all of them (for which every such
//!   UF returns its default — the single all-defaults profile),
//!
//! is therefore *exhaustive over the distinct profiles*: if every check
//! evaluates to `true`, `∀x. body` holds in the model over the entire domain.
//!
//! # Soundness
//!
//! [`all_universals_genuine`] returns `true` **only** when the check is
//! exhaustive and every instance evaluates to `Bool(true)`. It returns `false`
//! (decline — never a wrong `true`) whenever any universal is outside the
//! fragment, references a UF the model does not interpret, produces an
//! over-large candidate set, or has any instance that does not evaluate to
//! `Bool(true)` (including an evaluation error). The caller ([`crate::auto`])
//! only maps a `true` verdict to `sat`; a `false` verdict leaves the existing
//! refutation logic (and its `unsat`/`unknown` results) byte-identical.

use std::collections::{BTreeSet, HashMap};

use axeyum_ir::{FuncId, Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode, Value, eval};
use axeyum_rewrite::replace_subterms;

use crate::model::Model;

/// Cap on the per-universal instantiation set. A genuine check beyond this size
/// declines to `false` rather than risk an unbounded replay.
const MAX_INSTANTIATION_SET: usize = 4096;

/// Certifies `model` is a **genuine** model of every universal in `universals`
/// — i.e. for each `∀x. body`, the total interpretation `model` (finite UF
/// tables plus defaults) satisfies `∀x. body` over the *entire* domain of `x`.
///
/// Returns `true` only when the almost-uninterpreted finite check is exhaustive
/// for every universal and every instance evaluates to `Bool(true)`; otherwise
/// `false` (decline — never a wrong `true`). See the module docs for the
/// fragment boundary and the exhaustiveness argument.
pub(crate) fn all_universals_genuine(
    arena: &mut TermArena,
    universals: &[(SymbolId, TermId)],
    model: &Model,
) -> bool {
    if universals.is_empty() {
        return false;
    }
    let assignment = model.to_assignment();
    // Every universal must be certifiable: a single out-of-fragment universal
    // means the model is not exhaustively confirmed, so decline the whole query.
    universals
        .iter()
        .all(|&(sym, body)| universal_genuine(arena, sym, body, model, &assignment))
}

/// Certifies one universal `∀sym. body` against `model` (see
/// [`all_universals_genuine`]).
fn universal_genuine(
    arena: &mut TermArena,
    sym: SymbolId,
    body: TermId,
    model: &Model,
    assignment: &axeyum_ir::Assignment,
) -> bool {
    let sort = arena.symbol(sym).1;
    // The generic-value argument needs an infinite domain from which to draw a
    // value outside a finite set; `Int`/`Real` qualify. (`Bool`/`BitVec` are
    // finite and decided by finite expansion before reaching MBQI.)
    if !matches!(sort, Sort::Int | Sort::Real) {
        return false;
    }
    let var = arena.var(sym);
    // Fragment gate: every occurrence of `var` in `body` is a direct UF argument.
    if !var_only_under_uf(arena, body, var, false) {
        return false;
    }
    // The UFs applied *directly* to `var`; their table-key components at `var`'s
    // position are the "special" instantiation points.
    let funcs = relevant_funcs(arena, body, var);
    if funcs.is_empty() {
        // `var` does not flow into any UF (a `var`-free or purely-interpreted
        // body); outside this fragment — let the other passes handle it.
        return false;
    }
    // Every relevant UF must be interpreted by the model (else the candidate
    // set is incomplete and the replay would error): decline if any is missing.
    let mut candidates: Vec<Value> = Vec::new();
    for &f in &funcs {
        let Some(interp) = model.function(f) else {
            return false;
        };
        collect_key_components(interp, sort, &mut candidates);
        if candidates.len() > MAX_INSTANTIATION_SET {
            return false;
        }
    }
    // The single all-defaults profile: a generic value outside every table-key
    // component, so every relevant UF returns its default there.
    let Some(generic) = fresh_value(sort, &candidates) else {
        return false;
    };
    candidates.push(generic);

    // Replay `body[var := v]` at each candidate; every one must be `true`.
    for v in candidates {
        let Some(c) = value_to_const(arena, &v) else {
            return false;
        };
        let mut map: HashMap<TermId, TermId> = HashMap::new();
        map.insert(var, c);
        let mut memo: HashMap<TermId, TermId> = HashMap::new();
        let Ok(inst) = replace_subterms(arena, body, &map, &mut memo) else {
            return false;
        };
        if !matches!(eval(arena, inst, assignment), Ok(Value::Bool(true))) {
            return false;
        }
    }
    true
}

/// Whether every occurrence of `var` in `term` is a **direct argument** of an
/// uninterpreted-function application (`Op::Apply`). `parent_is_apply` records
/// whether `term`'s immediate parent is such an application.
///
/// A `var` reached with `parent_is_apply == false` (e.g. `(> var 0)`, `(+ var
/// 1)`, or a bare top-level `var`) is an interpreted-position occurrence and
/// fails the gate. `var` never occurring at all trivially passes (the caller
/// then declines via an empty relevant-function set).
fn var_only_under_uf(arena: &TermArena, term: TermId, var: TermId, parent_is_apply: bool) -> bool {
    if term == var {
        return parent_is_apply;
    }
    match arena.node(term) {
        TermNode::App { op, args } => {
            let child_ctx = matches!(op, Op::Apply(_));
            let args = args.clone();
            args.iter()
                .all(|&arg| var_only_under_uf(arena, arg, var, child_ctx))
        }
        _ => true,
    }
}

/// The uninterpreted functions applied with `var` as a **direct** argument in
/// `body` (deterministic, sorted by [`FuncId`]).
fn relevant_funcs(arena: &TermArena, body: TermId, var: TermId) -> BTreeSet<FuncId> {
    let mut out = BTreeSet::new();
    let mut seen = BTreeSet::new();
    let mut stack = vec![body];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(t) {
            if let Op::Apply(f) = op
                && args.contains(&var)
            {
                out.insert(*f);
            }
            let args = args.clone();
            stack.extend(args);
        }
    }
    out
}

/// Appends every table-key component of `interp` whose sort is `sort` to `out`
/// (deduplicated). These are the "special" instantiation points at which a
/// relevant UF may deviate from its default.
fn collect_key_components(interp: &axeyum_ir::FuncValue, sort: Sort, out: &mut Vec<Value>) {
    // Arithmetic (`Int`/`Real`) interpretations always use full-value storage,
    // so the value-keyed entries carry the concrete key components.
    for (key, _) in interp.value_entries() {
        for component in key {
            if component.sort() == sort && !out.contains(component) {
                out.push(component.clone());
            }
        }
    }
}

/// A value of `sort` (`Int`/`Real`) that is **not** in `avoid`, so every UF whose
/// table-key components are `avoid` returns its default there. Searches the
/// small integers `0, 1, -1, 2, -2, …`, which always finds a fresh value within
/// `avoid.len() + 1` steps; returns `None` only if the search bound is exceeded.
fn fresh_value(sort: Sort, avoid: &[Value]) -> Option<Value> {
    let bound = avoid.len() + 2;
    let mut n: i128 = 0;
    for _ in 0..=bound {
        let candidate = match sort {
            Sort::Int => Value::Int(n),
            Sort::Real => Value::Real(Rational::integer(n)),
            _ => return None,
        };
        if !avoid.contains(&candidate) {
            return Some(candidate);
        }
        // 0, 1, -1, 2, -2, … — a bounded search that must hit a fresh value.
        n = if n > 0 { -n } else { -n + 1 };
    }
    None
}

/// A `Value` as a ground constant term (`Int`/`Real` only).
fn value_to_const(arena: &mut TermArena, value: &Value) -> Option<TermId> {
    match value {
        Value::Int(n) => Some(arena.int_const(*n)),
        Value::Real(r) => Some(arena.real_const(*r)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fragment_gate_accepts_var_only_under_uf() {
        // body = (>= (f x) 0): `x` occurs only as a direct argument of `f`.
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let s = arena.declare("x", Sort::Int).unwrap();
        let x = arena.var(s);
        let fx = arena.apply(f, &[x]).unwrap();
        let zero = arena.int_const(0);
        let body = arena.int_ge(fx, zero).unwrap();
        assert!(var_only_under_uf(&arena, body, x, false));
        // `f` is the one relevant UF applied directly to `x`.
        assert_eq!(relevant_funcs(&arena, body, x), BTreeSet::from([f]));
    }

    #[test]
    fn fragment_gate_rejects_var_in_arithmetic() {
        // body = (>= (+ (f x) x) 0): `x` also occurs directly under `+`.
        let mut arena = TermArena::new();
        let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let s = arena.declare("x", Sort::Int).unwrap();
        let x = arena.var(s);
        let fx = arena.apply(f, &[x]).unwrap();
        let sum = arena.int_add(fx, x).unwrap();
        let zero = arena.int_const(0);
        let body = arena.int_ge(sum, zero).unwrap();
        assert!(!var_only_under_uf(&arena, body, x, false));
    }

    #[test]
    fn fragment_gate_rejects_bare_var_comparison() {
        // body = (>= x 0): `x` occurs in an interpreted position (no UF).
        let mut arena = TermArena::new();
        let s = arena.declare("x", Sort::Int).unwrap();
        let x = arena.var(s);
        let zero = arena.int_const(0);
        let body = arena.int_ge(x, zero).unwrap();
        assert!(!var_only_under_uf(&arena, body, x, false));
        assert!(relevant_funcs(&arena, body, x).is_empty());
    }

    #[test]
    fn fresh_value_avoids_the_given_set() {
        let avoid = vec![Value::Int(0), Value::Int(1), Value::Int(-1), Value::Int(2)];
        let g = fresh_value(Sort::Int, &avoid).expect("a fresh int exists");
        assert!(
            !avoid.contains(&g),
            "fresh value must be outside the avoid set"
        );
        let g_real = fresh_value(Sort::Real, &[Value::Real(Rational::integer(0))])
            .expect("a fresh real exists");
        assert!(matches!(g_real, Value::Real(_)));
    }
}
