//! Concrete-instance tests for `nat_prelude::ramsey`.
//!
//! Two things need pinning that a type-check cannot see.
//!
//! **The definitions compute what their names say.** `Nat.Graph.compl` and
//! `Nat.Graph.noClique3B` are admitted on their TYPE, and a `compl` that
//! forgot to negate, or a `noClique3B` that looked for a triangle instead of
//! refuting one, would have the right type and an empty axiom footprint. So
//! each is reduced to a `Bool` at tiny discriminating arguments and paired with
//! the specific wrong formula it rules out.
//!
//! **The search is a search.** `search_ramsey_lower` is untrusted Rust, and its
//! result is what the kernel then re-checks; the test below re-derives the
//! witness independently (from the definition of "no monochromatic triple") and
//! checks the *properties* rather than trusting the returned edge list.

use crate::expr::ExprId;
use crate::{Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

use super::ramsey::search_ramsey_lower;

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
    counter: u32,
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
        Self {
            k,
            p,
            st,
            counter: 0,
        }
    }

    /// A fresh scratch name for an accept/reject control.
    fn scratch(&mut self) -> crate::NameId {
        self.counter += 1;
        let anon = self.k.anon();
        let root = self.k.name_str(anon, "ramseyControl");
        let leaf = format!("c{}", self.counter);
        self.k.name_str(root, &leaf)
    }

    /// Offer `value` to the trusted gate at type `ty`. `true` means the kernel
    /// ADMITTED it -- nothing here reads a boolean out of a checker of its own.
    fn admits(&mut self, ty: ExprId, value: ExprId) -> bool {
        let name = self.scratch();
        self.k
            .add_declaration(crate::env::Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
            .is_ok()
    }

    fn dev(&mut self) -> super::ops::NatDev<'_> {
        let p = self.p;
        super::ops::NatDev::new(&mut self.k, p)
    }

    fn witness(&mut self) -> ExprId {
        let name = self.p.graph_ramsey33_witness;
        self.k.const_(name, vec![])
    }

    fn compl(&mut self, g: ExprId) -> ExprId {
        let name = self.p.graph_compl;
        self.const_app(name, &[g])
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

    fn no_clique3(&mut self, g: ExprId, n: u32) -> ExprId {
        let n_lit = self.num(n);
        let name = self.p.graph_no_clique3_b;
        self.const_app(name, &[g, n_lit])
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
}

/// The untrusted search returns a graph with neither a triangle nor an
/// independent triple, and the property is re-derived here rather than read off
/// the returned list.
///
/// The negative control is the empty edge set, which the same predicate must
/// REJECT — otherwise the check would be vacuous.
#[test]
fn the_search_returns_a_graph_with_no_monochromatic_triple() {
    let edges = search_ramsey_lower().expect("a five-vertex witness must exist");

    let mut adj = [[false; 5]; 5];
    for &(a, b) in &edges {
        adj[a as usize][b as usize] = true;
        adj[b as usize][a as usize] = true;
    }
    let mono = |table: &[[bool; 5]; 5], want: bool| {
        for a in 0..5 {
            for b in (a + 1)..5 {
                for c in (b + 1)..5 {
                    if table[a][b] == want && table[b][c] == want && table[a][c] == want {
                        return true;
                    }
                }
            }
        }
        false
    };
    assert!(!mono(&adj, true), "the witness must have no triangle");
    assert!(
        !mono(&adj, false),
        "the witness must have no independent triple"
    );

    let empty = [[false; 5]; 5];
    assert!(
        mono(&empty, false),
        "negative control: the empty graph DOES have an independent triple, \
         so the predicate above is not vacuously true"
    );

    // Five edges, and every vertex on exactly two of them: the five-cycle.
    assert_eq!(edges.len(), 5, "the witness must have five edges");
    for v in 0..5u32 {
        let deg = edges.iter().filter(|&&(a, b)| a == v || b == v).count();
        assert_eq!(deg, 2, "the witness must be 2-regular at {v}");
    }
}

/// `Nat.Graph.compl` inverts adjacency inside the order and stays empty
/// outside it.
///
/// The two halves are the discriminating pair: a `compl` that forgot the
/// negation would agree with `g` on the first line, and one that dropped the
/// range guard would make `5` adjacent to `0` in the complement even though the
/// graph has no vertex `5`.
#[test]
fn the_complement_inverts_adjacency_inside_the_order() {
    let mut f = Fixture::new();
    let w = f.witness();
    let cw = f.compl(w);

    // `0-3` is an edge of the witness, so it is a non-edge of the complement.
    let in_g = f.adj(w, 0, 3);
    f.assert_bool(in_g, true, "0-3 is an edge of the witness");
    let in_c = f.adj(cw, 0, 3);
    f.assert_bool(in_c, false, "0-3 must NOT be an edge of the complement");

    // `0-1` is a non-edge of the witness, so it IS an edge of the complement.
    let out_g = f.adj(w, 0, 1);
    f.assert_bool(out_g, false, "0-1 is a non-edge of the witness");
    let out_c = f.adj(cw, 0, 1);
    f.assert_bool(out_c, true, "0-1 must be an edge of the complement");

    // The complement is still irreflexive and still truncated.
    let loop_ = f.adj(cw, 2, 2);
    f.assert_bool(loop_, false, "the complement has no self-loop");
    let outside = f.adj(cw, 0, 5);
    f.assert_bool(
        outside,
        false,
        "5 is not a vertex, in g or in its complement",
    );

    // On five vertices with five edges, the complement also has five edges, so
    // it is 2-regular too — the five-cycle is self-complementary.
    let deg = f.degree(cw, 0);
    let two = f.num(2);
    let four = f.num(4);
    assert!(f.k.def_eq(deg, two), "the complement is 2-regular");
    assert!(
        !f.k.def_eq(deg, four),
        "negative control: a complement that ignored the graph would give 4"
    );
}

/// `Nat.Graph.noClique3B` is the decision the kernel actually runs in the
/// lower-bound proof, so it is checked here on BOTH sides.
///
/// The positives are the witness and its complement at `5`, which is what
/// `ramsey33_not_arrows_five` relies on. The negatives are what make the check
/// non-vacuous: a triangle must be detected, so `noClique3B` on the complete
/// graph is `false`.
#[test]
fn the_triangle_decision_fires_on_both_sides() {
    let mut f = Fixture::new();
    let w = f.witness();
    let cw = f.compl(w);

    let clean = f.no_clique3(w, 5);
    f.assert_bool(clean, true, "the witness has no triangle below 5");
    let clean_c = f.no_clique3(cw, 5);
    f.assert_bool(clean_c, true, "its complement has no triangle below 5");

    // Negative control: a graph that DOES have a triangle.
    let nat = f.nat_ty();
    let i_fv = f.fresh_fvar();
    let j_fv = f.fresh_fvar();
    let t = f.bool_true();
    let all = {
        let inner = f.lam_fv(j_fv, nat, t);
        f.lam_fv(i_fv, nat, inner)
    };
    let three = f.num(3);
    let mk = f.p.graph_mk;
    let k3 = f.const_app(mk, &[all, three]);
    let dirty = f.no_clique3(k3, 3);
    f.assert_bool(
        dirty,
        false,
        "the complete graph on 3 vertices DOES have a triangle",
    );
}

/// `Nat.Graph.ramsey_three_three` says `R(3,3) = 6` and NOT `R(3,3) = 5`.
///
/// The trusted gate cannot tell a THEOREM's statement is not what its name
/// says: an `IsRamseyNumber33` whose leastness clause pointed at the wrong
/// numeral would be admitted, carry an empty footprint, and pass every other
/// check here. So the same proof term is offered at both types and the second
/// must be REJECTED -- an accept alone would not distinguish the two.
#[test]
fn ramsey_three_three_is_leastness_at_six_and_not_at_five() {
    let mut f = Fixture::new();

    let (ty_six, value) = {
        let p = f.p;
        let mut d = f.dev();
        let six = d.num(6);
        let ty = d.const_app(p.graph_is_ramsey33, &[six]);
        let value = d.kernel().const_(p.graph_ramsey_three_three, vec![]);
        (ty, value)
    };
    assert!(
        f.admits(ty_six, value),
        "ramsey_three_three must have type IsRamseyNumber33 6"
    );

    let (ty_five, value) = {
        let p = f.p;
        let mut d = f.dev();
        let five = d.num(5);
        let ty = d.const_app(p.graph_is_ramsey33, &[five]);
        let value = d.kernel().const_(p.graph_ramsey_three_three, vec![]);
        (ty, value)
    };
    assert!(
        !f.admits(ty_five, value),
        "negative control: the same term must NOT prove IsRamseyNumber33 5"
    );
}

/// The upper bound is `Arrows33 6` and the lower bound refutes `Arrows33 5`,
/// so the two halves sit at ADJACENT numerals and neither can be slid.
///
/// `Arrows33` is antimonotone in its argument -- a statement about graphs with
/// at least five vertices is strictly stronger than one about graphs with at
/// least six -- so the upper bound must NOT prove `Arrows33 5`, which is
/// exactly what the lower bound refutes. Each half is checked in both
/// directions.
#[test]
fn the_two_halves_sit_at_adjacent_numerals() {
    let mut f = Fixture::new();

    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let six = d.num(6);
        let ty = d.const_app(p.graph_arrows33, &[six]);
        let value = d.kernel().const_(p.graph_ramsey33_arrows_six, vec![]);
        (ty, value)
    };
    assert!(f.admits(ty, value), "the upper bound must be Arrows33 6");

    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let five = d.num(5);
        let ty = d.const_app(p.graph_arrows33, &[five]);
        let value = d.kernel().const_(p.graph_ramsey33_arrows_six, vec![]);
        (ty, value)
    };
    assert!(
        !f.admits(ty, value),
        "negative control: the upper bound must NOT prove Arrows33 5"
    );

    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let five = d.num(5);
        let arrows = d.const_app(p.graph_arrows33, &[five]);
        let false_prop = d.kernel().const_(p.logic.false_, vec![]);
        let ty = d.arrow(arrows, false_prop);
        let value = d.kernel().const_(p.graph_ramsey33_not_arrows_five, vec![]);
        (ty, value)
    };
    assert!(
        f.admits(ty, value),
        "the lower bound must refute Arrows33 5"
    );

    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let six = d.num(6);
        let arrows = d.const_app(p.graph_arrows33, &[six]);
        let false_prop = d.kernel().const_(p.logic.false_, vec![]);
        let ty = d.arrow(arrows, false_prop);
        let value = d.kernel().const_(p.graph_ramsey33_not_arrows_five, vec![]);
        (ty, value)
    };
    assert!(
        !f.admits(ty, value),
        "negative control: the lower bound must NOT refute Arrows33 6 -- that \
         statement is TRUE and the theorem would be inconsistent"
    );
}
