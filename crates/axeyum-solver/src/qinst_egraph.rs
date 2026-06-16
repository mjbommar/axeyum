//! E-matching quantifier instantiation on the e-graph keystone (Track 2, P2.6).
//!
//! [`instantiate_forall_via_egraph`] is the keystone-driven path for instantiating
//! a universal `∀x. body`: it builds an [`EGraph`] over the ground terms, picks a
//! unary trigger `f(x)` from the body, e-matches it against the e-graph **modulo
//! congruence** ([`EGraph::ematch`]), and for each match substitutes the bound
//! variable with a representative of the matched argument class — producing the
//! ground instances to add and re-check.
//!
//! Matching on the e-graph is congruence-aware for free: if the ground terms force
//! `a = b`, then `f(a)` and `f(b)` are one class and the trigger fires once, so the
//! instances follow the *semantic* term structure, not the syntactic one. This is
//! the migration of trigger instantiation onto the backtrackable, independently
//! checkable keystone (vs the bespoke congruence closure the existing
//! `axeyum_rewrite::instantiate_with_triggers` carries); deeper triggers,
//! inference, and the full instantiation loop build on it.

use std::collections::HashMap;

use axeyum_egraph::{EGraph, ENodeId, Pattern};
use axeyum_ir::{FuncId, Op, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

/// Instantiates the universal `forall_term` by e-matching a unary trigger against
/// the `ground` terms, returning the ground instances of its body. Returns an
/// empty vector when `forall_term` is not a universal, has no usable unary trigger,
/// or the trigger's function does not occur in the ground terms.
#[must_use]
pub fn instantiate_forall_via_egraph(
    arena: &mut TermArena,
    ground: &[TermId],
    forall_term: TermId,
) -> Vec<TermId> {
    let Some((var, body)) = as_forall(arena, forall_term) else {
        return Vec::new();
    };
    let Some(trigger_func) = unary_trigger_function(arena, body, var) else {
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
    let Some(decl) = bridge.func_decls.get(&trigger_func).copied() else {
        return Vec::new(); // the trigger's function never appears in the ground terms
    };

    let pattern = Pattern::App(decl, vec![Pattern::Var(0)]);
    let mut instances = Vec::new();
    let var_term = arena.var(var);
    for subst in bridge.egraph.ematch(&pattern) {
        let Some(class) = subst[0] else { continue };
        let Some(&repr) = bridge.repr_term.get(&class) else {
            continue;
        };
        let replacements = HashMap::from([(var_term, repr)]);
        let mut memo = HashMap::new();
        if let Ok(instance) = replace_subterms(arena, body, &replacements, &mut memo) {
            instances.push(instance);
        }
    }
    instances.sort_by_key(|t| t.index());
    instances.dedup();
    instances
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

/// Finds a unary trigger `f(var)` in `body`: a function application whose only
/// argument is the bound variable. Returns its function symbol.
fn unary_trigger_function(arena: &TermArena, body: TermId, var: SymbolId) -> Option<FuncId> {
    if let TermNode::App { op, args } = arena.node(body) {
        if let Op::Apply(func) = op {
            if args.len() == 1 {
                if let TermNode::Symbol(s) = arena.node(args[0]) {
                    if *s == var {
                        return Some(*func);
                    }
                }
            }
        }
        let args = args.clone();
        for a in args {
            if let Some(found) = unary_trigger_function(arena, a, var) {
                return Some(found);
            }
        }
    }
    None
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
