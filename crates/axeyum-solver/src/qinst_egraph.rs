//! E-matching quantifier instantiation on the e-graph keystone (Track 2, P2.6).
//!
//! [`instantiate_forall_via_egraph`] is the keystone-driven path for instantiating
//! a universal `∀x. body`: it builds an [`EGraph`] over the ground terms, selects a
//! trigger — a function-application subterm mentioning the bound variable, which
//! may be **nested** (`f(g(x))`) or **multi-argument with ground parts**
//! (`g(x, a)`) — e-matches it against the e-graph **modulo congruence**
//! ([`EGraph::ematch`]), and for each match substitutes the bound variable with a
//! representative of the matched argument class, producing the ground instances to
//! add and re-check.
//!
//! Matching on the e-graph is congruence-aware for free: if the ground terms force
//! `a = b`, then `f(a)` and `f(b)` are one class and the trigger fires once, so the
//! instances follow the *semantic* term structure, not the syntactic one. This is
//! the migration of trigger instantiation onto the backtrackable, independently
//! checkable keystone (vs the bespoke congruence closure the existing
//! `axeyum_rewrite::instantiate_with_triggers` carries); deeper triggers,
//! inference, and the full instantiation loop build on it.

use std::collections::{HashMap, HashSet};

use axeyum_egraph::{EGraph, ENodeId, Pattern};
use axeyum_ir::{FuncId, Op, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};

/// Default e-matching instantiation rounds before giving up (`unknown`).
const MAX_INSTANTIATION_ROUNDS: usize = 8;

/// Tries to refute a (possibly quantified) conjunction by **e-matching
/// instantiation on the e-graph** (Track 2, P2.6): it separates the ground
/// assertions from the universals, and repeatedly instantiates each universal over
/// the current ground terms ([`instantiate_forall_via_egraph`]), adds the fresh
/// instances, and re-checks the ground set with [`check_auto`] — until the ground
/// set is `unsat` (⇒ the original is `unsat`, since the universals entail every
/// instance), a round adds no new instance (instantiation fixpoint), or the round
/// budget is exhausted.
///
/// **Sound, incomplete:** a ground `unsat` is a real refutation; otherwise the
/// result is `unknown` (e-matching may simply not have found the refuting
/// instance). Quantifier-free inputs go straight to [`check_auto`].
///
/// # Errors
///
/// Propagates any [`SolverError`] from the ground solver.
pub fn prove_quantified_unsat_via_egraph(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let mut ground: Vec<TermId> = Vec::new();
    let mut foralls: Vec<TermId> = Vec::new();
    for &a in assertions {
        if matches!(arena.node(a), TermNode::App { op, .. } if matches!(op, Op::Forall(_))) {
            foralls.push(a);
        } else {
            ground.push(a);
        }
    }
    if foralls.is_empty() {
        return check_auto(arena, &ground, config);
    }

    let mut seen: HashSet<TermId> = ground.iter().copied().collect();
    for _ in 0..MAX_INSTANTIATION_ROUNDS {
        // A ground refutation at any point is a refutation of the whole problem.
        if matches!(check_auto(arena, &ground, config)?, CheckResult::Unsat) {
            return Ok(CheckResult::Unsat);
        }
        // Instantiate every universal over the current ground terms.
        let mut added = false;
        let universals = foralls.clone();
        for quantifier in universals {
            for instance in instantiate_forall_via_egraph(arena, &ground, quantifier) {
                if seen.insert(instance) {
                    ground.push(instance);
                    added = true;
                }
            }
        }
        if !added {
            break; // instantiation fixpoint: no new ground facts
        }
    }
    // Final ground check (may now be unsat with the last round's instances).
    match check_auto(arena, &ground, config)? {
        CheckResult::Unsat => Ok(CheckResult::Unsat),
        _ => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: "e-matching instantiation did not refute within the round budget".to_owned(),
        })),
    }
}

/// Instantiates the universal `forall_term` by e-matching a trigger against the
/// `ground` terms, returning the ground instances of its body. Returns an empty
/// vector when `forall_term` is not a universal, has no trigger covering all bound
/// variables, or the trigger's symbols do not occur in the ground terms.
///
/// # Panics
///
/// Panics only if the quantifier binds more than `u32::MAX` variables (which no
/// real input does).
#[must_use]
pub fn instantiate_forall_via_egraph(
    arena: &mut TermArena,
    ground: &[TermId],
    forall_term: TermId,
) -> Vec<TermId> {
    // Peel the (possibly nested) universal prefix `∀x. ∀y. … body`.
    let (vars, body) = peel_foralls(arena, forall_term);
    if vars.is_empty() {
        return Vec::new();
    }
    let var_index: HashMap<SymbolId, u32> = vars
        .iter()
        .enumerate()
        .map(|(i, &v)| (v, u32::try_from(i).expect("variable count fits u32")))
        .collect();

    // Pick one trigger (a function application) mentioning *all* bound variables.
    let Some(trigger) = select_trigger(arena, body, &var_index) else {
        return Vec::new();
    };

    let mut bridge = InstBridge::new();
    for &g in ground {
        bridge.add_term(arena, g);
        // A top-level ground equality `(= s t)` asserts s = t — merge it so matching
        // is genuinely modulo the ground congruence.
        if let TermNode::App { op, args } = arena.node(g) {
            if matches!(op, Op::Eq) && args.len() == 2 {
                let (s, t) = (args[0], args[1]);
                let ns = bridge.add_term(arena, s);
                let nt = bridge.add_term(arena, t);
                bridge.egraph.merge(ns, nt, 0);
            }
        }
    }

    // Convert the trigger to an e-matching pattern (each bound var → its Var index,
    // every ground subterm → an application by its bridge decl).
    let pattern = bridge.trigger_to_pattern(arena, trigger, &var_index);
    let var_terms: Vec<TermId> = vars.iter().map(|&v| arena.var(v)).collect();
    let mut instances = Vec::new();
    for subst in bridge.egraph.ematch(&pattern) {
        // Build the substitution from every bound variable to a ground witness of
        // its matched class; skip incomplete matches.
        let mut replacements = HashMap::new();
        let complete = (0..vars.len()).all(|i| {
            subst
                .get(i)
                .copied()
                .flatten()
                .and_then(|class| bridge.repr_term.get(&class).copied())
                .is_some_and(|repr| replacements.insert(var_terms[i], repr).is_none())
        });
        if !complete {
            continue;
        }
        let mut memo = HashMap::new();
        if let Ok(instance) = replace_subterms(arena, body, &replacements, &mut memo) {
            instances.push(instance);
        }
    }
    instances.sort_by_key(|t| t.index());
    instances.dedup();
    instances
}

/// Peels the universal prefix `∀v1. ∀v2. … body`, returning the bound variables
/// (outer first) and the innermost non-quantified body.
fn peel_foralls(arena: &TermArena, mut term: TermId) -> (Vec<SymbolId>, TermId) {
    let mut vars = Vec::new();
    while let Some((var, body)) = as_forall(arena, term) {
        vars.push(var);
        term = body;
    }
    (vars, term)
}

/// Decomposes a `(forall x body)` term into its bound variable and body.
fn as_forall(arena: &TermArena, term: TermId) -> Option<(SymbolId, TermId)> {
    match arena.node(term) {
        TermNode::App { op, args } if matches!(op, Op::Forall(_)) && args.len() == 1 => {
            let Op::Forall(var) = op else {
                unreachable!("matched Forall above")
            };
            Some((*var, args[0]))
        }
        _ => None,
    }
}

/// Selects a trigger: the outermost function-application subterm of `body` that
/// mentions **every** bound variable (e.g. `f(x)`, `f(g(x))`, `g(x, y)`). A valid
/// trigger must be headed by a function symbol so the e-graph can enumerate it.
fn select_trigger(
    arena: &TermArena,
    body: TermId,
    vars: &HashMap<SymbolId, u32>,
) -> Option<TermId> {
    if let TermNode::App { op, args } = arena.node(body) {
        if matches!(op, Op::Apply(_)) && mentions_all(arena, body, vars) {
            return Some(body);
        }
        let args = args.clone();
        for a in args {
            if let Some(found) = select_trigger(arena, a, vars) {
                return Some(found);
            }
        }
    }
    None
}

/// Whether `term` mentions every variable in `vars`.
fn mentions_all(arena: &TermArena, term: TermId, vars: &HashMap<SymbolId, u32>) -> bool {
    let mut seen = std::collections::HashSet::new();
    collect_vars(arena, term, vars, &mut seen);
    seen.len() == vars.len()
}

/// Records which `vars` occur in `term`.
fn collect_vars(
    arena: &TermArena,
    term: TermId,
    vars: &HashMap<SymbolId, u32>,
    seen: &mut std::collections::HashSet<SymbolId>,
) {
    match arena.node(term) {
        TermNode::Symbol(s) if vars.contains_key(s) => {
            seen.insert(*s);
        }
        TermNode::App { args, .. } => {
            let args = args.clone();
            for a in args {
                collect_vars(arena, a, vars, seen);
            }
        }
        _ => {}
    }
}

/// Bridges ground IR terms to the e-graph for instantiation: it builds e-nodes,
/// assigns each symbol/function/constant a `decl`, and remembers a representative
/// ground term per class (to substitute back on a match).
struct InstBridge {
    egraph: EGraph,
    term_to_node: HashMap<TermId, ENodeId>,
    func_decls: HashMap<FuncId, u32>,
    symbol_decls: HashMap<usize, u32>,
    op_decls: HashMap<String, u32>,
    /// First ground term seen per class root — the instantiation witness.
    repr_term: HashMap<ENodeId, TermId>,
    next_decl: u32,
}

impl InstBridge {
    fn new() -> Self {
        Self {
            egraph: EGraph::new(),
            term_to_node: HashMap::new(),
            func_decls: HashMap::new(),
            symbol_decls: HashMap::new(),
            op_decls: HashMap::new(),
            repr_term: HashMap::new(),
            next_decl: 0,
        }
    }

    fn fresh_decl(&mut self) -> u32 {
        let d = self.next_decl;
        self.next_decl += 1;
        d
    }

    fn add_term(&mut self, arena: &TermArena, term: TermId) -> ENodeId {
        if let Some(&n) = self.term_to_node.get(&term) {
            return n;
        }
        let node = match arena.node(term) {
            TermNode::Symbol(s) => {
                let decl = self.symbol_decl(s.index());
                self.egraph.add(decl, &[])
            }
            TermNode::App {
                op: Op::Apply(func),
                args,
            } => {
                let func = *func;
                let args = args.clone();
                let children: Vec<ENodeId> =
                    args.iter().map(|&a| self.add_term(arena, a)).collect();
                let decl = self.func_decl(func);
                self.egraph.add(decl, &children)
            }
            TermNode::App { op, args } => {
                // Other interpreted operators are treated as uninterpreted for the
                // purposes of matching (sound: matching only fires on real terms).
                let op = format!("{op:?}");
                let args = args.clone();
                let children: Vec<ENodeId> =
                    args.iter().map(|&a| self.add_term(arena, a)).collect();
                let decl = self.op_decl(&op);
                self.egraph.add(decl, &children)
            }
            _ => {
                // A literal constant: each distinct value is its own leaf.
                let key = format!("c:{:?}", arena.node(term));
                let decl = self.op_decl(&key);
                self.egraph.add(decl, &[])
            }
        };
        let root = self.egraph.root(node);
        self.repr_term.entry(root).or_insert(term);
        self.term_to_node.insert(term, node);
        node
    }

    fn symbol_decl(&mut self, sym: usize) -> u32 {
        if let Some(&d) = self.symbol_decls.get(&sym) {
            return d;
        }
        let d = self.fresh_decl();
        self.symbol_decls.insert(sym, d);
        d
    }

    fn func_decl(&mut self, func: FuncId) -> u32 {
        if let Some(&d) = self.func_decls.get(&func) {
            return d;
        }
        let d = self.fresh_decl();
        self.func_decls.insert(func, d);
        d
    }

    fn op_decl(&mut self, key: &str) -> u32 {
        if let Some(&d) = self.op_decls.get(key) {
            return d;
        }
        let d = self.fresh_decl();
        self.op_decls.insert(key.to_owned(), d);
        d
    }

    /// Converts a trigger term to an e-matching [`Pattern`] under this bridge's
    /// decl assignment: the bound `var` becomes `Var(0)`, and every other subterm
    /// (symbols, applications, constants, interpreted ops) becomes an application
    /// keyed by the same decl the ground terms use — so a ground subterm in the
    /// trigger matches its own class, while only `var` is free.
    fn trigger_to_pattern(
        &mut self,
        arena: &TermArena,
        term: TermId,
        vars: &HashMap<SymbolId, u32>,
    ) -> Pattern {
        match arena.node(term) {
            TermNode::Symbol(s) if vars.contains_key(s) => Pattern::Var(vars[s]),
            TermNode::Symbol(s) => Pattern::App(self.symbol_decl(s.index()), Vec::new()),
            TermNode::App {
                op: Op::Apply(func),
                args,
            } => {
                let func = *func;
                let args = args.clone();
                let subs = args
                    .iter()
                    .map(|&a| self.trigger_to_pattern(arena, a, vars))
                    .collect();
                Pattern::App(self.func_decl(func), subs)
            }
            TermNode::App { op, args } => {
                let key = format!("{op:?}");
                let args = args.clone();
                let subs = args
                    .iter()
                    .map(|&a| self.trigger_to_pattern(arena, a, vars))
                    .collect();
                Pattern::App(self.op_decl(&key), subs)
            }
            _ => Pattern::App(
                self.op_decl(&format!("c:{:?}", arena.node(term))),
                Vec::new(),
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Sort;

    /// Builds `∀x. (= (f x) c)` and ground terms mentioning `f(a)`, `f(b)`.
    #[allow(clippy::many_single_char_names)]
    fn setup() -> (
        TermArena,
        TermId,
        [TermId; 2],
        TermId,
        TermId,
        FuncId,
        SymbolId,
    ) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        // A ground assertion that contains f(a) and f(b).
        let sum = arena.bv_add(fa, fb).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(sum, zero).unwrap();

        // Body referencing the bound variable: (= (f x) c).
        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let body = arena.eq(fx, c).unwrap();
        let forall = arena.forall(x, body).unwrap();

        (arena, forall, [a, b], c, ground0, f, x)
    }

    #[test]
    fn instantiates_over_ground_applications() {
        let (mut arena, forall, [a, b], c, ground0, f, _x) = setup();
        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);

        // Expect (= (f a) c) and (= (f b) c).
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let want_a = arena.eq(fa, c).unwrap();
        let want_b = arena.eq(fb, c).unwrap();
        assert!(instances.contains(&want_a), "instance for a missing");
        assert!(instances.contains(&want_b), "instance for b missing");
        assert_eq!(instances.len(), 2);
    }

    #[test]
    fn instantiation_is_modulo_congruence() {
        // Add a = b to the ground: f(a) and f(b) become one class, so the trigger
        // fires once and there is a single instance.
        let (mut arena, forall, [a, b], _c, ground0, _f, _x) = setup();
        let a_eq_b = arena.eq(a, b).unwrap();
        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0, a_eq_b], forall);
        assert_eq!(
            instances.len(),
            1,
            "congruent f-applications instantiate once, got {instances:?}"
        );
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn instantiates_over_a_nested_trigger() {
        // ∀x. (= (f (g x)) c), ground containing f(g(a)): instance (= (f (g a)) c).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let ga = arena.apply(g, &[a]).unwrap();
        let fga = arena.apply(f, &[ga]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(fga, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let gx = arena.apply(g, &[xv]).unwrap();
        let fgx = arena.apply(f, &[gx]).unwrap();
        let body = arena.eq(fgx, c).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);
        let want = arena.eq(fga, c).unwrap();
        assert_eq!(instances, vec![want], "nested trigger f(g(x)) → x = a");
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn instantiates_over_a_binary_trigger_with_a_ground_argument() {
        // ∀x. (= (h x a) c), ground containing h(b, a) and h(d, a): two instances;
        // the ground argument `a` in the trigger is matched by its class.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let d = arena.bv_var("d", 8).unwrap();
        let h = arena.declare_fun("h", &[sort, sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let hba = arena.apply(h, &[b, a]).unwrap();
        let hda = arena.apply(h, &[d, a]).unwrap();
        // A decoy h(a, b) whose ground argument is b, not a — must NOT match h(x, a).
        let hab = arena.apply(h, &[a, b]).unwrap();
        let hba_hda = arena.bv_add(hba, hda).unwrap();
        let sum = arena.bv_add(hba_hda, hab).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(sum, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let hxa = arena.apply(h, &[xv, a]).unwrap();
        let body = arena.eq(hxa, c).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);
        let want_b = arena.eq(hba, c).unwrap();
        let want_d = arena.eq(hda, c).unwrap();
        assert!(instances.contains(&want_b));
        assert!(instances.contains(&want_d));
        assert_eq!(
            instances.len(),
            2,
            "only h(_, a) matches, got {instances:?}"
        );
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn instantiation_loop_refutes_a_quantified_contradiction() {
        // f(a) ≠ 0  ∧  ∀x. (= (f x) 0): instantiating x = a gives f(a) = 0,
        // contradicting the ground disequality → UNSAT.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let fa_eq_0 = arena.eq(fa, zero).unwrap();
        let fa_ne_0 = arena.not(fa_eq_0).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_0 = arena.eq(fx, zero).unwrap();
        let forall = arena.forall(x, fx_eq_0).unwrap();

        let result = prove_quantified_unsat_via_egraph(
            &mut arena,
            &[fa_ne_0, forall],
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(result, CheckResult::Unsat);
    }

    #[test]
    fn instantiation_loop_passes_through_quantifier_free() {
        // No universals: routes straight to check_auto (here, sat).
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a_eq_1 = arena.eq(a, one).unwrap();
        let result =
            prove_quantified_unsat_via_egraph(&mut arena, &[a_eq_1], &SolverConfig::default())
                .unwrap();
        assert!(matches!(result, CheckResult::Sat(_)));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn instantiates_a_two_variable_quantifier() {
        // ∀x. ∀y. (= (g x y) c), ground containing g(a, b): instance (= (g a b) c).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let g = arena.declare_fun("g", &[sort, sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let gab = arena.apply(g, &[a, b]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(gab, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let y = arena.declare("y", sort).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let gxy = arena.apply(g, &[xv, yv]).unwrap();
        let inner_body = arena.eq(gxy, c).unwrap();
        let inner = arena.forall(y, inner_body).unwrap();
        let forall = arena.forall(x, inner).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);
        let want = arena.eq(gab, c).unwrap();
        assert_eq!(instances, vec![want], "x↦a, y↦b from the g(x,y) trigger");
    }

    #[test]
    fn non_forall_or_no_trigger_yields_nothing() {
        let mut arena = TermArena::new();
        let p = arena.bool_var("p").unwrap();
        // Not a forall.
        assert!(instantiate_forall_via_egraph(&mut arena, &[p], p).is_empty());
        // A forall whose body has no unary trigger over the bound variable.
        let x = arena.declare("x", Sort::Bool).unwrap();
        let xv = arena.var(x);
        let body = arena.or(xv, p).unwrap();
        let forall = arena.forall(x, body).unwrap();
        assert!(instantiate_forall_via_egraph(&mut arena, &[p], forall).is_empty());
    }
}
