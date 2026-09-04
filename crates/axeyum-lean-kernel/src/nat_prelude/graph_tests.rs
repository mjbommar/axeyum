//! Concrete-instance tests for `nat_prelude::graph`.
//!
//! **The kernel cannot tell a `Definition` is wrong.** `Nat.Graph.adjB`,
//! `neighbors`, `degree`, `andB`, `orB` and `neB` are all admitted on their
//! TYPE, and a function computing the wrong value has the right type, an empty
//! axiom footprint, and passes every sweep in this repository. So every check
//! here reduces a closed term to a numeral (or to `Bool.true`/`Bool.false`)
//! with the kernel's own `def_eq` and compares it against an independently
//! hand-computed value, and every positive is paired with the specific wrong
//! formula it rules out.
//!
//! The discriminating fixtures are the two the brief names: a **triangle**, in
//! which every degree is `2` (so a `degree` that counted the vertex itself
//! would give `3`), and a **path on three vertices**, whose degrees are
//! `1, 2, 1` (so a `degree` that ignored the relation and counted the whole
//! range would give `3, 3, 3`, and one that counted only forward edges would
//! give `1, 1, 0`).
//!
//! Every magnitude here is tiny on purpose: this prelude's numerals are unary
//! `Nat.succ` towers, so cost is superlinear in the largest magnitude FORMED.
//! The largest order any fold below runs over is `5`.

use crate::expr::ExprId;
use crate::{Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    fn and_b(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let name = self.p.graph_and_b;
        self.const_app(name, &[a, b])
    }

    fn or_b(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let name = self.p.graph_or_b;
        self.const_app(name, &[a, b])
    }

    /// `Nat.Graph.mk rel order`, where `rel` fires exactly on the listed
    /// ORDERED pairs. Orientations are listed explicitly so a test can build a
    /// deliberately asymmetric relation.
    fn graph_of(&mut self, pairs: &[(u32, u32)], order: u32) -> ExprId {
        let nat = self.nat_ty();
        let i_fv = self.fresh_fvar();
        let i = self.k.fvar(i_fv);
        let j_fv = self.fresh_fvar();
        let j = self.k.fvar(j_fv);
        let mut body = self.bool_false();
        for &(a, b) in pairs.iter().rev() {
            let a_lit = self.num(a);
            let b_lit = self.num(b);
            let hit_i = self.beq(i, a_lit);
            let hit_j = self.beq(j, b_lit);
            let hit = self.and_b(hit_i, hit_j);
            body = self.or_b(hit, body);
        }
        let rel = {
            let inner = self.lam_fv(j_fv, nat, body);
            self.lam_fv(i_fv, nat, inner)
        };
        let n = self.num(order);
        let name = self.p.graph_mk;
        self.const_app(name, &[rel, n])
    }

    /// `Nat.Graph.mk (fun _ _ => true) order` — every ordered pair related,
    /// including the diagonal, so it exercises the irreflexivity guard.
    fn all_pairs(&mut self, order: u32) -> ExprId {
        let nat = self.nat_ty();
        let i_fv = self.fresh_fvar();
        let j_fv = self.fresh_fvar();
        let t = self.bool_true();
        let rel = {
            let inner = self.lam_fv(j_fv, nat, t);
            self.lam_fv(i_fv, nat, inner)
        };
        let n = self.num(order);
        let name = self.p.graph_mk;
        self.const_app(name, &[rel, n])
    }

    /// The undirected graph on `order` vertices with the listed edges, each
    /// stored in both orientations.
    fn undirected(&mut self, edges: &[(u32, u32)], order: u32) -> ExprId {
        let mut pairs: Vec<(u32, u32)> = Vec::new();
        for &(a, b) in edges {
            pairs.push((a, b));
            pairs.push((b, a));
        }
        self.graph_of(&pairs, order)
    }

    fn adj(&mut self, g: ExprId, i: u32, j: u32) -> ExprId {
        let i_lit = self.num(i);
        let j_lit = self.num(j);
        let name = self.p.graph_adj_b;
        self.const_app(name, &[g, i_lit, j_lit])
    }

    fn degree(&mut self, g: ExprId, v: u32) -> ExprId {
        let v_lit = self.num(v);
        let name = self.p.graph_degree;
        self.const_app(name, &[g, v_lit])
    }

    fn order(&mut self, g: ExprId) -> ExprId {
        let name = self.p.graph_order;
        self.const_app(name, &[g])
    }

    fn mem_neighbors(&mut self, g: ExprId, v: u32, i: u32) -> ExprId {
        let v_lit = self.num(v);
        let nb_name = self.p.graph_neighbors;
        let nb = self.const_app(nb_name, &[g, v_lit]);
        let i_lit = self.num(i);
        let mem = self.p.finset_mem_b;
        self.const_app(mem, &[nb, i_lit])
    }

    /// `Nat.Graph.neB i j`.
    fn ne_b(&mut self, i: u32, j: u32) -> ExprId {
        let i_lit = self.num(i);
        let j_lit = self.num(j);
        let name = self.p.graph_ne_b;
        self.const_app(name, &[i_lit, j_lit])
    }

    fn assert_bool(&mut self, term: ExprId, expected: bool, message: &str) {
        let want = if expected {
            self.bool_true()
        } else {
            self.bool_false()
        };
        let other = if expected {
            self.bool_false()
        } else {
            self.bool_true()
        };
        assert!(self.k.def_eq(term, want), "{message}");
        assert!(
            !self.k.def_eq(term, other),
            "negative control: {message} -- must NOT reduce to the other Bool"
        );
    }

    fn assert_num(&mut self, term: ExprId, expected: u32, message: &str) {
        let want = self.num(expected);
        assert!(self.k.def_eq(term, want), "{message}");
    }

    fn assert_not_num(&mut self, term: ExprId, wrong: u32, message: &str) {
        let bad = self.num(wrong);
        assert!(!self.k.def_eq(term, bad), "negative control: {message}");
    }
}

/// `Nat.Graph.order` reads back the bound the constructor was given, and
/// `Nat.Graph.rel` is NOT the observable adjacency.
#[test]
fn order_projects_the_stored_bound() {
    let mut f = Fixture::new();
    let g = f.undirected(&[(0, 1), (1, 2)], 3);
    let o = f.order(g);
    f.assert_num(o, 3, "order of a 3-vertex path must be 3");
    f.assert_not_num(o, 2, "order must not be the edge count");
}

/// The `Bool` algebra computes what its name says. `neB` is the one with a
/// wrong-value failure mode that nothing else would catch: a `neB` that forgot
/// to invert would make every graph edgeless off the diagonal instead of on it.
#[test]
fn bool_algebra_computes_and_or_and_ne() {
    let mut f = Fixture::new();
    let t = f.bool_true();
    let fa = f.bool_false();

    let tt = f.and_b(t, fa);
    f.assert_bool(tt, false, "andB true false must be false");
    let ff = f.and_b(t, t);
    f.assert_bool(ff, true, "andB true true must be true");
    let o1 = f.or_b(fa, t);
    f.assert_bool(o1, true, "orB false true must be true");
    let o2 = f.or_b(fa, fa);
    f.assert_bool(o2, false, "orB false false must be false");

    let same = f.ne_b(2, 2);
    f.assert_bool(same, false, "neB 2 2 must be false");
    let differ = f.ne_b(2, 3);
    f.assert_bool(differ, true, "neB 2 3 must be true");
}

/// A TRIANGLE has every degree `2`.
///
/// The negative control is `3`: a `degree` that counted the vertex itself — an
/// `adjB` that dropped the `neB` guard — would land there, and `3` is also
/// what a `degree` that ignored the relation and counted the whole range would
/// give. Both wrong formulas are ruled out by the same numeral, at all three
/// vertices.
#[test]
fn every_degree_of_a_triangle_is_two() {
    let mut f = Fixture::new();
    for v in 0..3 {
        let k3 = f.undirected(&[(0, 1), (1, 2), (0, 2)], 3);
        let deg = f.degree(k3, v);
        f.assert_num(deg, 2, "every degree of a triangle must be 2");
        f.assert_not_num(deg, 3, "a degree counting the vertex itself would be 3");
        f.assert_not_num(deg, 1, "a degree counting one orientation would be 1");
    }
}

/// A PATH on three vertices has degrees `1, 2, 1`.
///
/// This is the discriminating fixture: the three values are not all equal, so a
/// `degree` that returned a constant — the order, the order minus one, or zero
/// — fails at at least one vertex. The middle vertex rules out "count only the
/// forward edge" (which would give `1`) and the two ends rule out "count the
/// whole range" (which would give `3`).
#[test]
fn a_path_on_three_vertices_has_degrees_one_two_one() {
    let mut f = Fixture::new();
    for (v, want) in [(0u32, 1u32), (1, 2), (2, 1)] {
        let p3 = f.undirected(&[(0, 1), (1, 2)], 3);
        let deg = f.degree(p3, v);
        f.assert_num(deg, want, "path degree mismatch");
        f.assert_not_num(deg, 3, "a degree ignoring the relation would be 3");
    }
    // The end vertices are NOT adjacent — a `degree` that took the transitive
    // closure would make this a triangle.
    let p3 = f.undirected(&[(0, 1), (1, 2)], 3);
    let ends = f.adj(p3, 0, 2);
    f.assert_bool(ends, false, "the ends of a path must not be adjacent");
}

/// `adjB` is irreflexive and truncates at the order, on EVERY graph — here on
/// the one whose stored relation is constantly `true`.
///
/// A relation that is `true` everywhere is exactly the adversary for both
/// guards: without the `neB` guard `adjB g 1 1` would be `true`, and without
/// the range guard `adjB g 1 5` would be `true` at a vertex the graph does not
/// have. The degree check pins the same two facts numerically: `2`, not `3`
/// (self) and not more (out of range).
#[test]
fn adjacency_is_irreflexive_and_truncated() {
    let mut f = Fixture::new();
    let g = f.all_pairs(3);

    let loop_ = f.adj(g, 1, 1);
    f.assert_bool(loop_, false, "adjB g 1 1 must be false");
    let inside = f.adj(g, 1, 2);
    f.assert_bool(inside, true, "adjB g 1 2 must be true");
    let outside = f.adj(g, 1, 5);
    f.assert_bool(
        outside,
        false,
        "adjB g 1 5 must be false -- 5 is not a vertex",
    );
    let both_outside = f.adj(g, 5, 6);
    f.assert_bool(both_outside, false, "adjB g 5 6 must be false");

    let deg = f.degree(g, 1);
    f.assert_num(deg, 2, "the all-pairs graph on 3 vertices has degree 2");
    f.assert_not_num(deg, 3, "a degree counting the self-loop would be 3");

    let deg_out = f.degree(g, 5);
    f.assert_num(deg_out, 0, "a vertex outside the order has degree 0");
}

/// Symmetrization is by CONJUNCTION: a one-sided entry in the stored relation
/// is not an edge.
///
/// This is the test that pins the design choice. The stored relation holds at
/// `(0,1)` and nowhere else, so under the disjunctive ("symmetric closure")
/// reading `adjB g 0 1` would be `true` and vertex `0` would have degree `1`.
/// Under the conjunctive reading both directions must be recorded, so the graph
/// is edgeless. The second half is the positive control: add the reverse pair
/// and the edge appears.
#[test]
fn a_one_sided_relation_is_not_an_edge() {
    let mut f = Fixture::new();

    let one_way = f.graph_of(&[(0, 1)], 2);
    let forward = f.adj(one_way, 0, 1);
    f.assert_bool(forward, false, "a one-sided entry must not be an edge");
    let backward = f.adj(one_way, 1, 0);
    f.assert_bool(backward, false, "and it must not be an edge the other way");
    let deg = f.degree(one_way, 0);
    f.assert_num(deg, 0, "the one-sided graph is edgeless");
    f.assert_not_num(deg, 1, "the disjunctive reading would give 1");

    let two_way = f.graph_of(&[(0, 1), (1, 0)], 2);
    let there = f.adj(two_way, 0, 1);
    f.assert_bool(there, true, "both orientations recorded IS an edge");
    let deg2 = f.degree(two_way, 0);
    f.assert_num(deg2, 1, "and then the degree is 1");
}

/// The neighbourhood is a `Nat.Finset` whose membership IS adjacency, at
/// indices inside AND outside the order.
#[test]
fn neighbourhood_membership_is_adjacency() {
    let mut f = Fixture::new();
    let p3 = f.undirected(&[(0, 1), (1, 2)], 3);

    let at_1 = f.mem_neighbors(p3, 0, 1);
    f.assert_bool(at_1, true, "1 is a neighbour of 0 in the path");
    let at_2 = f.mem_neighbors(p3, 0, 2);
    f.assert_bool(at_2, false, "2 is not a neighbour of 0 in the path");
    let at_self = f.mem_neighbors(p3, 0, 0);
    f.assert_bool(at_self, false, "no vertex is its own neighbour");
    let outside = f.mem_neighbors(p3, 0, 7);
    f.assert_bool(outside, false, "a non-vertex is nobody's neighbour");
}

/// A five-cycle is 2-regular, and its non-edges are non-edges.
///
/// This is the graph the Ramsey lower bound rests on, so its shape is pinned
/// here independently of that proof: every degree is `2` (not `4`, which is
/// what the complete graph on five vertices would give) and the two chords out
/// of vertex `0` are absent.
#[test]
fn the_five_cycle_is_two_regular() {
    let mut f = Fixture::new();
    let edges = [(0u32, 1u32), (1, 2), (2, 3), (3, 4), (4, 0)];
    for v in 0..5 {
        let c5 = f.undirected(&edges, 5);
        let deg = f.degree(c5, v);
        f.assert_num(deg, 2, "every degree of C5 must be 2");
        f.assert_not_num(deg, 4, "the complete graph on 5 vertices would give 4");
    }
    let c5 = f.undirected(&edges, 5);
    let chord_a = f.adj(c5, 0, 2);
    f.assert_bool(chord_a, false, "0-2 is not an edge of C5");
    let chord_b = f.adj(c5, 0, 3);
    f.assert_bool(chord_b, false, "0-3 is not an edge of C5");
    let rim = f.adj(c5, 4, 0);
    f.assert_bool(rim, true, "4-0 IS an edge of C5");
}

/// **Every declaration this lane adds is axiom-free, and the set is derived
/// from the live environment rather than from a list in this file.**
///
/// The sweep walks the environment for the two namespace prefixes and requires
/// an empty `Kernel::axiom_footprint` for each. A prefix sweep can go vacuously
/// green if the prefix is wrong, so the second half is the control: the
/// load-bearing names are read out of `NatPrelude` -- the authority -- and each
/// must have been seen by the sweep.
#[test]
fn every_graph_hall_and_ramsey_declaration_is_axiom_free() {
    let f = Fixture::new();
    let mut seen: Vec<String> = Vec::new();
    for (&name, _) in f.k.environment().iter() {
        let rendered = f.k.display_name(name).to_string();
        if rendered.starts_with("Nat.Graph.") || rendered.starts_with("Nat.Hall.") {
            let footprint = f.k.axiom_footprint(name);
            assert!(
                footprint.is_empty(),
                "{rendered} must be axiom-free; footprint = {footprint:?}"
            );
            seen.push(rendered);
        }
    }
    assert!(
        seen.len() >= 30,
        "the prefix sweep found only {} declarations, which means the prefix is \
         wrong rather than that the lane is small",
        seen.len()
    );

    for name in [
        f.p.graph_adj_b,
        f.p.graph_degree,
        f.p.graph_mem_b_neighbors,
        f.p.graph_ramsey_three_three,
        f.p.graph_ramsey33_arrows_six,
        f.p.graph_ramsey33_not_arrows_five,
        f.p.hall_condition_of_is_matching,
    ] {
        let rendered = f.k.display_name(name).to_string();
        assert!(
            seen.contains(&rendered),
            "{rendered} was not reached by the prefix sweep -- the sweep is not \
             covering what it claims to cover"
        );
    }
}
