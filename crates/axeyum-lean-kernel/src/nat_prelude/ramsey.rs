//! `R(3,3) = 6` — Ramsey's theorem for two colours at the first non-trivial
//! parameter, both halves in the kernel (ADR-1608).
//!
//! # The statement
//!
//! A two-colouring of the edges of a complete graph **is** a graph: call one
//! colour class "present" and the other "absent". A monochromatic triangle is
//! then either a triangle of `g` or a triangle of its complement, and no
//! separate colouring object is needed.
//!
//! ```text
//! Nat.Graph.compl g            := mk (fun i j => notB (adjB g i j)) (order g)
//! Nat.Graph.HasClique3 g       := ∃ a b c, adjB g a b ∧ adjB g b c ∧ adjB g a c
//! Nat.Graph.Arrows33 n         := ∀ g, n ≤ order g → HasClique3 g ∨ HasClique3 (compl g)
//! Nat.Graph.IsRamseyNumber33 n := Arrows33 n ∧ ∀ k < n, ¬ Arrows33 k
//! ```
//!
//! `HasClique3` carries **no** range or distinctness conjuncts, and that is the
//! payoff of `graph.rs`'s design choice: `Nat.Graph.lt_order_of_adjB` recovers
//! `a < order g` from an edge and `Nat.Graph.ne_of_adjB` recovers `a ≠ b`,
//! because `adjB` truncates and is irreflexive inside its own definition. Under
//! a side-condition design each of the three existentials would need six extra
//! conjuncts, and both proofs below would have to carry them.
//!
//! # The upper bound is a proof, not an enumeration
//!
//! There are `2^15 = 32768` graphs on six vertices, and — unlike the `2^5`
//! colourings `Nat.Rado.schur_arrows_five` enumerates — a graph is a *function*
//! stored in the carrier, so the kernel cannot case over "every graph" at all.
//! The proof is therefore the textbook argument, encoded as a case tree over
//! the **five edges at vertex 0** (`2^5 = 32` leaves):
//!
//! * three of `1..5` share a colour with respect to `0` — pigeonhole on five
//!   objects in two classes, discharged by the enumeration itself, since the
//!   builder computes the majority class at each of the 32 leaves;
//! * given three neighbours of `0`, either two of them are adjacent (a triangle
//!   with `0`) or all three are pairwise non-adjacent (a triangle of the
//!   complement) — [`declare_triangle_or_indep`], four leaves, proved **once**;
//! * given three non-neighbours of `0`, the mirror image —
//!   [`declare_antitriangle_or_indep`], four leaves, proved once.
//!
//! So the emitted term has 32 leaves, each one application of a shared lemma,
//! rather than 256 spelled-out cases.
//!
//! # The lower bound is a search, checked by reflection
//!
//! [`search_ramsey_lower`] enumerates the `2^10` graphs on five vertices and
//! returns the first with neither a triangle nor an independent triple. It
//! finds `{0-3, 0-4, 1-2, 1-4, 2-3}` — the five-cycle, relabelled — which is
//! the unique such graph up to isomorphism. Nothing about that search is
//! trusted: the certificate is transcribed as `Nat.Graph.ramsey33Witness` and
//! the kernel then *recomputes* both refutations itself, through
//! `Nat.Graph.noClique3B`, a `Bool` triple loop over `Nat.Finset.allBelow`
//! whose `true` value `Nat.Finset.allBelow_true_at` reads back at the three
//! existential witnesses. That is this project's thesis in one proof term, and
//! the same route `Nat.Rado.schur_not_arrows_four` takes.
//!
//! **The exit status depends on the finding.** If the search returned `None` —
//! that is, if every graph on five vertices had a monochromatic triangle —
//! [`declare_lower_bound`] declares nothing, and `Nat.Graph.ramsey_three_three`
//! then names a theorem that does not exist, so the kernel rejects it and the
//! whole `Nat` prelude fails to build. There is no path on which a failed
//! search yields a green suite.
//!
//! # Why `Arrows33` is stated with `Le n (order g)` and not `order g = n`
//!
//! An equality hypothesis would force every vertex bound to be transported
//! through it. With `Le n (order g)` the bound `k < order g` is
//! `le_trans (succ k) n (order g)` against a concrete `Le (succ k) n`, and
//! monotonicity — `Arrows33 m → Arrows33 n` for `m ≤ n`, since a larger order
//! is a *stronger* hypothesis and hence a weaker statement — is three lines
//! instead of a case analysis. Monotonicity is what makes "least" and "false at
//! the predecessor" the same statement, exactly as `Nat.Rado.arrows_of_le` does
//! for Rado numbers.

#![allow(
    clippy::many_single_char_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::NatPrelude;
use super::graph::{adj_b, and_b, bool_congr, g_order, graph_ty, not_b, or_b};
use super::helpers::{and_left, and_right};
use super::ops::{NatDev, NatOps, bool_true_or_false};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// The vertex count the lower-bound search runs over.
const LOWER_N: u32 = 5;

/// The vertex count the upper bound is proved at. It is `succ LOWER_N`, so
/// `isRamseyNumber33_of_succ` applies with no numeral arithmetic.
const UPPER_N: u32 = LOWER_N + 1;

// ---------------------------------------------------------------------------
// The untrusted half: search.
//
// Nothing below is trusted. The certificate it returns is re-checked by the
// kernel through `noClique3B`; a `None` means nothing is declared.
// ---------------------------------------------------------------------------

/// The ten unordered pairs on five vertices, in the order the search
/// enumerates their bits.
const PAIRS5: [(u32, u32); 10] = [
    (0, 1),
    (0, 2),
    (0, 3),
    (0, 4),
    (1, 2),
    (1, 3),
    (1, 4),
    (2, 3),
    (2, 4),
    (3, 4),
];

/// The symmetric adjacency table of the graph on `[0,5)` whose edge set is the
/// bit pattern `bits` over [`PAIRS5`].
fn table_from_bits(bits: u32) -> [[bool; 5]; 5] {
    let mut adj = [[false; 5]; 5];
    for (index, &(a, b)) in PAIRS5.iter().enumerate() {
        if (bits >> index) & 1 == 1 {
            adj[a as usize][b as usize] = true;
            adj[b as usize][a as usize] = true;
        }
    }
    adj
}

/// Does the table hold three vertices that are pairwise `want`-related?
/// `want = true` asks for a triangle, `want = false` for an independent triple.
fn has_mono_triple(adj: &[[bool; 5]; 5], want: bool) -> bool {
    for a in 0..5usize {
        for b in (a + 1)..5usize {
            for c in (b + 1)..5usize {
                if adj[a][b] == want && adj[b][c] == want && adj[a][c] == want {
                    return true;
                }
            }
        }
    }
    false
}

/// The edge list of a graph on five vertices with neither a triangle nor an
/// independent triple, or `None` if every such graph has one — which would be
/// the statement `R(3,3) <= 5`.
///
/// Enumerated in a fixed bit order so the emitted certificate is
/// deterministic. It returns `{0-3, 0-4, 1-2, 1-4, 2-3}`.
pub(super) fn search_ramsey_lower() -> Option<Vec<(u32, u32)>> {
    for bits in 0..(1u32 << PAIRS5.len()) {
        let adj = table_from_bits(bits);
        if !has_mono_triple(&adj, true) && !has_mono_triple(&adj, false) {
            return Some(
                PAIRS5
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| (bits >> index) & 1 == 1)
                    .map(|(_, &pair)| pair)
                    .collect(),
            );
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Small term builders.
// ---------------------------------------------------------------------------

/// `Prop`.
fn prop(d: &mut NatDev<'_>) -> ExprId {
    d.kernel().sort_zero()
}

/// `Exists.{1} Nat pred`.
fn exists_nat(d: &mut NatDev<'_>, p: &NatPrelude, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `Exists.intro.{1} Nat pred w h`.
fn exists_intro_nat(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    w: ExprId,
    h: ExprId,
) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    d.apply(intro, &[nat, pred, w, h])
}

/// `Exists.rec.{1}` into a `Prop` goal.
fn exists_elim_nat(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    goal: ExprId,
    minor: ExprId,
    proof: ExprId,
) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let ex_ty = exists_nat(d, p, pred);
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, ex_ty, goal, BinderInfo::Default);
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    d.apply(rec, &[nat, pred, motive, minor, proof])
}

/// `Nat.le lo hi` at two concrete magnitudes.
fn le_proof(d: &mut NatDev<'_>, p: &NatPrelude, lo: u32, hi: u32) -> ExprId {
    assert!(lo <= hi, "le_proof: {lo} > {hi}");
    let lo_e = d.num(lo);
    let mut proof = d.const_app(p.le_refl, &[lo_e]);
    for step in lo..hi {
        let from = d.num(step);
        proof = d.const_app(p.le_step, &[lo_e, from, proof]);
    }
    proof
}

/// `Nat.Graph.compl g`.
fn compl(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId) -> ExprId {
    d.const_app(p.graph_compl, &[g])
}

/// `Nat.Graph.HasClique3 g`.
fn has_clique3(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId) -> ExprId {
    d.const_app(p.graph_has_clique3, &[g])
}

/// `Or (HasClique3 g) (HasClique3 (compl g))` — the conclusion of everything
/// in this module.
fn mono_goal(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId) -> ExprId {
    let left = has_clique3(d, p, g);
    let cg = compl(d, p, g);
    let right = has_clique3(d, p, cg);
    d.const_app(p.logic.or, &[left, right])
}

/// `Eq Bool (adjB g i j) true`.
fn adj_true(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId, i: ExprId, j: ExprId) -> ExprId {
    let a = adj_b(d, p, g, i, j);
    let t = d.bool_true();
    d.bool_eq(a, t)
}

/// `Eq Bool (adjB g i j) false`.
fn adj_false(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId, i: ExprId, j: ExprId) -> ExprId {
    let a = adj_b(d, p, g, i, j);
    let f = d.bool_false();
    d.bool_eq(a, f)
}

/// `Eq Bool (beq i j) false`.
fn beq_false(d: &mut NatDev<'_>, i: ExprId, j: ExprId) -> ExprId {
    let b = d.beq(i, j);
    let f = d.bool_false();
    d.bool_eq(b, f)
}

/// The right-nested `And` chain a `HasClique3` witness carries.
fn clique3_body(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    g: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
) -> ExprId {
    let e1 = adj_true(d, p, g, a, b);
    let e2 = adj_true(d, p, g, b, c);
    let e3 = adj_true(d, p, g, a, c);
    let tail = d.const_app(p.logic.and, &[e2, e3]);
    d.const_app(p.logic.and, &[e1, tail])
}

/// `fun c => <clique3_body at a b c>`.
fn clique3_pred_c(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let body = clique3_body(d, p, g, a, b, c);
    d.lam_fv(c_fv, nat, body)
}

/// `fun b => Exists (clique3_pred_c …)`.
fn clique3_pred_b(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId, a: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let inner = clique3_pred_c(d, p, g, a, b);
    let body = exists_nat(d, p, inner);
    d.lam_fv(b_fv, nat, body)
}

/// `fun a => Exists (clique3_pred_b …)`.
fn clique3_pred_a(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let inner = clique3_pred_b(d, p, g, a);
    let body = exists_nat(d, p, inner);
    d.lam_fv(a_fv, nat, body)
}

/// The unfolded `HasClique3 g`.
fn has_clique3_unfolded(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId) -> ExprId {
    let pred = clique3_pred_a(d, p, g);
    exists_nat(d, p, pred)
}

/// Assemble a `HasClique3 g` from its three edges.
fn mk_has_clique3(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    g: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    hab: ExprId,
    hbc: ExprId,
    hac: ExprId,
) -> ExprId {
    let e1 = adj_true(d, p, g, a, b);
    let e2 = adj_true(d, p, g, b, c);
    let e3 = adj_true(d, p, g, a, c);
    let tail_ty = d.const_app(p.logic.and, &[e2, e3]);
    let tail = d.const_app(p.logic.and_intro, &[e2, e3, hbc, hac]);
    let body = d.const_app(p.logic.and_intro, &[e1, tail_ty, hab, tail]);
    let pc = clique3_pred_c(d, p, g, a, b);
    let ez = exists_intro_nat(d, p, pc, c, body);
    let pb = clique3_pred_b(d, p, g, a);
    let ey = exists_intro_nat(d, p, pb, b, ez);
    let pa = clique3_pred_a(d, p, g);
    exists_intro_nat(d, p, pa, a, ey)
}

/// `Or.elim` over the `b = true` / `b = false` dichotomy.
fn bool_or_elim(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    b: ExprId,
    goal: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let t = d.bool_true();
    let f = d.bool_false();
    let is_true = d.bool_eq(b, t);
    let is_false = d.bool_eq(b, f);
    let dichotomy = bool_true_or_false(d, p, b);
    d.const_app(
        p.logic.or_elim,
        &[is_true, is_false, goal, dichotomy, on_true, on_false],
    )
}

/// `h : adjB g i j = true ⊢ adjB g j i = true` — one `adjB_symm` step.
fn flip_adj_true(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    g: ExprId,
    i: ExprId,
    j: ExprId,
    h: ExprId,
) -> ExprId {
    let lhs = adj_b(d, p, g, j, i);
    let rhs = adj_b(d, p, g, i, j);
    let t = d.bool_true();
    let symm = d.const_app(p.graph_adj_b_symm, &[g, j, i]);
    d.bool_trans(lhs, rhs, t, symm, h)
}

/// `h : adjB g i j = false ⊢ adjB g j i = false`.
fn flip_adj_false(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    g: ExprId,
    i: ExprId,
    j: ExprId,
    h: ExprId,
) -> ExprId {
    let lhs = adj_b(d, p, g, j, i);
    let rhs = adj_b(d, p, g, i, j);
    let f = d.bool_false();
    let symm = d.const_app(p.graph_adj_b_symm, &[g, j, i]);
    d.bool_trans(lhs, rhs, f, symm, h)
}

// ---------------------------------------------------------------------------
// The definitions.
// ---------------------------------------------------------------------------

/// `fun c => notB (andB (adjB g a b) (andB (adjB g b c) (adjB g a c)))` — the
/// innermost loop body of `noClique3B`.
fn loop_c(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let ab = adj_b(d, p, g, a, b);
    let bc = adj_b(d, p, g, b, c);
    let ac = adj_b(d, p, g, a, c);
    let inner = and_b(d, p, bc, ac);
    let whole = and_b(d, p, ab, inner);
    let body = not_b(d, p, whole);
    d.lam_fv(c_fv, nat, body)
}

/// `fun b => allBelow (loop_c …) n`.
fn loop_b(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId, n: ExprId, a: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let inner = loop_c(d, p, g, a, b);
    let body = d.const_app(p.finset_all_below, &[inner, n]);
    d.lam_fv(b_fv, nat, body)
}

/// `fun a => allBelow (loop_b …) n`.
fn loop_a(d: &mut NatDev<'_>, p: &NatPrelude, g: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let inner = loop_b(d, p, g, n, a);
    let body = d.const_app(p.finset_all_below, &[inner, n]);
    d.lam_fv(a_fv, nat, body)
}

fn declare_definitions(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let prop_ty = prop(d);
    let gr = graph_ty(d, &p);

    // compl : Graph -> Graph := fun g => mk (fun i j => notB (adjB g i j)) (order g)
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let rel = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let a = adj_b(d, &p, g, i, j);
            let body = not_b(d, &p, a);
            let inner = d.lam_fv(j_fv, nat, body);
            d.lam_fv(i_fv, nat, inner)
        };
        let n = g_order(d, &p, g);
        let built = d.const_app(p.graph_mk, &[rel, n]);
        let value = d.lam_fv(g_fv, gr, built);
        let ty = d.arrow(gr, gr);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_compl,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // HasClique3 : Graph -> Prop
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let body = has_clique3_unfolded(d, &p, g);
        let value = d.lam_fv(g_fv, gr, body);
        let ty = d.arrow(gr, prop_ty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_has_clique3,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
    }

    // noClique3B : Graph -> Nat -> Bool
    {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let outer = loop_a(d, &p, g, n);
        let body = d.const_app(p.finset_all_below, &[outer, n]);
        let value = {
            let inner = d.lam_fv(n_fv, nat, body);
            d.lam_fv(g_fv, gr, inner)
        };
        let ty = {
            let inner = d.arrow(nat, bool_ty);
            d.arrow(gr, inner)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_no_clique3_b,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    // Arrows33 n := ∀ g, Le n (order g) -> Or (HasClique3 g) (HasClique3 (compl g))
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let ord = g_order(d, &p, g);
            let hyp = d.le(n, ord);
            let concl = mono_goal(d, &p, g);
            let step = d.arrow(hyp, concl);
            d.pi_fv(g_fv, gr, step)
        };
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, prop_ty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_arrows33,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(7),
        })?;
    }

    // IsRamseyNumber33 n := Arrows33 n ∧ ∀ k, Lt k n -> Arrows33 k -> False
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let upper = d.const_app(p.graph_arrows33, &[n]);
        let least = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let arrows_k = d.const_app(p.graph_arrows33, &[k]);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let inner = d.arrow(arrows_k, false_ty);
            let lt = d.lt(k, n);
            let step = d.arrow(lt, inner);
            d.pi_fv(k_fv, nat, step)
        };
        let body = d.const_app(p.logic.and, &[upper, least]);
        let value = d.lam_fv(n_fv, nat, body);
        let ty = d.arrow(nat, prop_ty);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_is_ramsey33,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(8),
        })?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The complement law and the reflection refutation.
// ---------------------------------------------------------------------------

/// `Nat.Graph.adjB_compl_of_not_adjB : ∀ g i j, Lt i (order g) →
/// Lt j (order g) → beq i j = false → adjB g i j = false →
/// adjB (compl g) i j = true`.
///
/// `order (compl g)` is `order g` by ι and `rel (compl g) i j` is
/// `notB (adjB g i j)`, so the whole content is two `notB` congruences fed to
/// `Nat.Graph.adjB_of_rel`. The `adjB g j i = false` half comes from
/// `adjB_symm`, which is where the conjunctive symmetrization is paid for.
fn declare_compl_law(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let gr = graph_ty(d, &p);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let n = g_order(d, &p, g);
    let false_ = d.bool_false();

    let hi_ty = d.lt(i, n);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let hj_ty = d.lt(j, n);
    let hj_fv = d.fresh_fvar();
    let hj = d.kernel().fvar(hj_fv);
    let hne_ty = beq_false(d, i, j);
    let hne_fv = d.fresh_fvar();
    let hne = d.kernel().fvar(hne_fv);
    let hadj_ty = adj_false(d, &p, g, i, j);
    let hadj_fv = d.fresh_fvar();
    let hadj = d.kernel().fvar(hadj_fv);

    let cg = compl(d, &p, g);
    let a_ij = adj_b(d, &p, g, i, j);
    let a_ji = adj_b(d, &p, g, j, i);
    let hadj_flipped = flip_adj_false(d, &p, g, i, j, hadj);
    let hr1 = bool_congr(d, a_ij, false_, hadj, &|d, x| not_b(d, &p, x));
    let hr2 = bool_congr(d, a_ji, false_, hadj_flipped, &|d, x| not_b(d, &p, x));
    let proof = d.const_app(p.graph_adj_b_of_rel, &[cg, i, j, hi, hj, hne, hr1, hr2]);
    let concl = adj_true(d, &p, cg, i, j);

    let ty = {
        let s7 = d.arrow(hadj_ty, concl);
        let s6 = d.arrow(hne_ty, s7);
        let s5 = d.arrow(hj_ty, s6);
        let s4 = d.arrow(hi_ty, s5);
        let s3 = d.pi_fv(j_fv, nat, s4);
        let s2 = d.pi_fv(i_fv, nat, s3);
        d.pi_fv(g_fv, gr, s2)
    };
    let value = {
        let s7 = d.lam_fv(hadj_fv, hadj_ty, proof);
        let s6 = d.lam_fv(hne_fv, hne_ty, s7);
        let s5 = d.lam_fv(hj_fv, hj_ty, s6);
        let s4 = d.lam_fv(hi_fv, hi_ty, s5);
        let s3 = d.lam_fv(j_fv, nat, s4);
        let s2 = d.lam_fv(i_fv, nat, s3);
        d.lam_fv(g_fv, gr, s2)
    };
    d.declare_theorem(p.graph_adj_b_compl_of_not_adj_b, ty, value)
}

/// `Nat.Graph.not_hasClique3_of_decide : ∀ g,
/// Eq Bool (noClique3B g (order g)) true → HasClique3 g → False`.
///
/// The REFLECTION half. The three existential witnesses are pulled out with
/// `Exists.rec`, their vertex bounds are recovered from the edges themselves
/// (`lt_order_of_adjB`, and one `adjB_symm` for the third vertex, which only
/// appears on the right of an edge), and `Nat.Finset.allBelow_true_at` reads
/// the decided loop back at exactly those three indices.
fn declare_reflection(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let gr = graph_ty(d, &p);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n = g_order(d, &p, g);
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let false_prop = d.kernel().const_(p.logic.false_, vec![]);

    let decided = d.const_app(p.graph_no_clique3_b, &[g, n]);
    let hdec_ty = d.bool_eq(decided, true_);
    let hdec_fv = d.fresh_fvar();
    let hdec = d.kernel().fvar(hdec_fv);
    let hcl_ty = has_clique3(d, &p, g);
    let hcl_fv = d.fresh_fvar();
    let hcl = d.kernel().fvar(hcl_fv);

    let outer_loop = loop_a(d, &p, g, n);

    let minor_a = {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let pred_b_at_a = clique3_pred_b(d, &p, g, a);
        let ha_ty = exists_nat(d, &p, pred_b_at_a);
        let ha_fv = d.fresh_fvar();
        let ha = d.kernel().fvar(ha_fv);

        let minor_b = {
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let pred_c_at_ab = clique3_pred_c(d, &p, g, a, b);
            let hb_ty = exists_nat(d, &p, pred_c_at_ab);
            let hb_fv = d.fresh_fvar();
            let hb = d.kernel().fvar(hb_fv);

            let minor_c = {
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let hc_ty = clique3_body(d, &p, g, a, b, c);
                let hc_fv = d.fresh_fvar();
                let hc = d.kernel().fvar(hc_fv);

                let e1 = adj_true(d, &p, g, a, b);
                let e2 = adj_true(d, &p, g, b, c);
                let e3 = adj_true(d, &p, g, a, c);
                let tail_ty = d.const_app(p.logic.and, &[e2, e3]);
                let h1 = and_left(d, e1, tail_ty, hc);
                let rest = and_right(d, e1, tail_ty, hc);
                let h2 = and_left(d, e2, e3, rest);
                let h3 = and_right(d, e2, e3, rest);

                let ha_lt = d.const_app(p.graph_lt_order_of_adj_b, &[g, a, b, h1]);
                let hb_lt = d.const_app(p.graph_lt_order_of_adj_b, &[g, b, c, h2]);
                let hcb = flip_adj_true(d, &p, g, b, c, h2);
                let hc_lt = d.const_app(p.graph_lt_order_of_adj_b, &[g, c, b, hcb]);

                let level_b = loop_b(d, &p, g, n, a);
                let level_c = loop_c(d, &p, g, a, b);
                let s1 = d.const_app(p.finset_all_below_true_at, &[outer_loop, n, hdec, a, ha_lt]);
                let s2 = d.const_app(p.finset_all_below_true_at, &[level_b, n, s1, b, hb_lt]);
                let s3 = d.const_app(p.finset_all_below_true_at, &[level_c, n, s2, c, hc_lt]);

                let ab = adj_b(d, &p, g, a, b);
                let bc = adj_b(d, &p, g, b, c);
                let ac = adj_b(d, &p, g, a, c);
                let inner_ty = and_b(d, &p, bc, ac);
                let inner = d.const_app(p.graph_and_b_intro, &[bc, ac, h2, h3]);
                let whole_ty = and_b(d, &p, ab, inner_ty);
                let whole = d.const_app(p.graph_and_b_intro, &[ab, inner_ty, h1, inner]);
                let negated = not_b(d, &p, whole_ty);
                let hnot = bool_congr(d, whole_ty, true_, whole, &|d, x| not_b(d, &p, x));
                let flipped = d.bool_symm(negated, false_, hnot);
                let absurd = d.bool_trans(false_, negated, true_, flipped, s3);
                let body = d.false_true_elim(false_prop, absurd);

                let with_hc = d.lam_fv(hc_fv, hc_ty, body);
                d.lam_fv(c_fv, nat, with_hc)
            };

            let body = exists_elim_nat(d, &p, pred_c_at_ab, false_prop, minor_c, hb);
            let with_hb = d.lam_fv(hb_fv, hb_ty, body);
            d.lam_fv(b_fv, nat, with_hb)
        };

        let body = exists_elim_nat(d, &p, pred_b_at_a, false_prop, minor_b, ha);
        let with_ha = d.lam_fv(ha_fv, ha_ty, body);
        d.lam_fv(a_fv, nat, with_ha)
    };

    let pred_a = clique3_pred_a(d, &p, g);
    let proof = exists_elim_nat(d, &p, pred_a, false_prop, minor_a, hcl);

    let ty = {
        let s3 = d.arrow(hcl_ty, false_prop);
        let s2 = d.arrow(hdec_ty, s3);
        d.pi_fv(g_fv, gr, s2)
    };
    let value = {
        let s3 = d.lam_fv(hcl_fv, hcl_ty, proof);
        let s2 = d.lam_fv(hdec_fv, hdec_ty, s3);
        d.lam_fv(g_fv, gr, s2)
    };
    d.declare_theorem(p.graph_not_has_clique3_of_decide, ty, value)
}

// ---------------------------------------------------------------------------
// The two shared four-leaf case analyses.
// ---------------------------------------------------------------------------

/// `Nat.Graph.triangle_or_indep : ∀ g v x y z,
/// adjB g v x = true → adjB g v y = true → adjB g v z = true →
/// beq x y = false → beq y z = false → beq x z = false →
/// HasClique3 g ∨ HasClique3 (compl g)`.
///
/// Three neighbours of `v`: if any two of them are adjacent that pair closes a
/// triangle with `v`, and otherwise the three are pairwise non-adjacent and
/// form a triangle of the complement. The vertex bounds the complement branch
/// needs are recovered from the three edges rather than assumed.
fn declare_triangle_or_indep(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let gr = graph_ty(d, &p);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);

    let hvx_ty = adj_true(d, &p, g, v, x);
    let hvx_fv = d.fresh_fvar();
    let hvx = d.kernel().fvar(hvx_fv);
    let hvy_ty = adj_true(d, &p, g, v, y);
    let hvy_fv = d.fresh_fvar();
    let hvy = d.kernel().fvar(hvy_fv);
    let hvz_ty = adj_true(d, &p, g, v, z);
    let hvz_fv = d.fresh_fvar();
    let hvz = d.kernel().fvar(hvz_fv);
    let hxy_ty = beq_false(d, x, y);
    let hxy_fv = d.fresh_fvar();
    let hxy = d.kernel().fvar(hxy_fv);
    let hyz_ty = beq_false(d, y, z);
    let hyz_fv = d.fresh_fvar();
    let hyz = d.kernel().fvar(hyz_fv);
    let hxz_ty = beq_false(d, x, z);
    let hxz_fv = d.fresh_fvar();
    let hxz = d.kernel().fvar(hxz_fv);

    let goal = mono_goal(d, &p, g);
    let left_ty = has_clique3(d, &p, g);
    let cg = compl(d, &p, g);
    let right_ty = has_clique3(d, &p, cg);

    // Bounds, from the three edges at `v`.
    let hxv = flip_adj_true(d, &p, g, v, x, hvx);
    let hyv = flip_adj_true(d, &p, g, v, y, hvy);
    let hzv = flip_adj_true(d, &p, g, v, z, hvz);
    let hx_lt = d.const_app(p.graph_lt_order_of_adj_b, &[g, x, v, hxv]);
    let hy_lt = d.const_app(p.graph_lt_order_of_adj_b, &[g, y, v, hyv]);
    let hz_lt = d.const_app(p.graph_lt_order_of_adj_b, &[g, z, v, hzv]);

    let a_xy = adj_b(d, &p, g, x, y);
    let a_yz = adj_b(d, &p, g, y, z);
    let a_xz = adj_b(d, &p, g, x, z);

    let proof = {
        // adjB g x y ?
        let on_xy_true = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let h_ty = adj_true(d, &p, g, x, y);
            let clique = mk_has_clique3(d, &p, g, v, x, y, hvx, h, hvy);
            let body = d.const_app(p.logic.or_inl, &[left_ty, right_ty, clique]);
            d.lam_fv(h_fv, h_ty, body)
        };
        let on_xy_false = {
            let hxy_f_fv = d.fresh_fvar();
            let hxy_f = d.kernel().fvar(hxy_f_fv);
            let hxy_f_ty = adj_false(d, &p, g, x, y);

            // adjB g y z ?
            let on_yz_true = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let h_ty = adj_true(d, &p, g, y, z);
                let clique = mk_has_clique3(d, &p, g, v, y, z, hvy, h, hvz);
                let body = d.const_app(p.logic.or_inl, &[left_ty, right_ty, clique]);
                d.lam_fv(h_fv, h_ty, body)
            };
            let on_yz_false = {
                let hyz_f_fv = d.fresh_fvar();
                let hyz_f = d.kernel().fvar(hyz_f_fv);
                let hyz_f_ty = adj_false(d, &p, g, y, z);

                // adjB g x z ?
                let on_xz_true = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let h_ty = adj_true(d, &p, g, x, z);
                    let clique = mk_has_clique3(d, &p, g, v, x, z, hvx, h, hvz);
                    let body = d.const_app(p.logic.or_inl, &[left_ty, right_ty, clique]);
                    d.lam_fv(h_fv, h_ty, body)
                };
                let on_xz_false = {
                    let hxz_f_fv = d.fresh_fvar();
                    let hxz_f = d.kernel().fvar(hxz_f_fv);
                    let hxz_f_ty = adj_false(d, &p, g, x, z);
                    let c_xy = d.const_app(
                        p.graph_adj_b_compl_of_not_adj_b,
                        &[g, x, y, hx_lt, hy_lt, hxy, hxy_f],
                    );
                    let c_yz = d.const_app(
                        p.graph_adj_b_compl_of_not_adj_b,
                        &[g, y, z, hy_lt, hz_lt, hyz, hyz_f],
                    );
                    let c_xz = d.const_app(
                        p.graph_adj_b_compl_of_not_adj_b,
                        &[g, x, z, hx_lt, hz_lt, hxz, hxz_f],
                    );
                    let clique = mk_has_clique3(d, &p, cg, x, y, z, c_xy, c_yz, c_xz);
                    let body = d.const_app(p.logic.or_inr, &[left_ty, right_ty, clique]);
                    d.lam_fv(hxz_f_fv, hxz_f_ty, body)
                };
                let body = bool_or_elim(d, &p, a_xz, goal, on_xz_true, on_xz_false);
                d.lam_fv(hyz_f_fv, hyz_f_ty, body)
            };
            let body = bool_or_elim(d, &p, a_yz, goal, on_yz_true, on_yz_false);
            d.lam_fv(hxy_f_fv, hxy_f_ty, body)
        };
        bool_or_elim(d, &p, a_xy, goal, on_xy_true, on_xy_false)
    };

    let ty = {
        let s11 = d.arrow(hxz_ty, goal);
        let s10 = d.arrow(hyz_ty, s11);
        let s9 = d.arrow(hxy_ty, s10);
        let s8 = d.arrow(hvz_ty, s9);
        let s7 = d.arrow(hvy_ty, s8);
        let s6 = d.arrow(hvx_ty, s7);
        let s5 = d.pi_fv(z_fv, nat, s6);
        let s4 = d.pi_fv(y_fv, nat, s5);
        let s3 = d.pi_fv(x_fv, nat, s4);
        let s2 = d.pi_fv(v_fv, nat, s3);
        d.pi_fv(g_fv, gr, s2)
    };
    let value = {
        let s11 = d.lam_fv(hxz_fv, hxz_ty, proof);
        let s10 = d.lam_fv(hyz_fv, hyz_ty, s11);
        let s9 = d.lam_fv(hxy_fv, hxy_ty, s10);
        let s8 = d.lam_fv(hvz_fv, hvz_ty, s9);
        let s7 = d.lam_fv(hvy_fv, hvy_ty, s8);
        let s6 = d.lam_fv(hvx_fv, hvx_ty, s7);
        let s5 = d.lam_fv(z_fv, nat, s6);
        let s4 = d.lam_fv(y_fv, nat, s5);
        let s3 = d.lam_fv(x_fv, nat, s4);
        let s2 = d.lam_fv(v_fv, nat, s3);
        d.lam_fv(g_fv, gr, s2)
    };
    d.declare_theorem(p.graph_triangle_or_indep, ty, value)
}

/// `Nat.Graph.antitriangle_or_indep` — the mirror image: three NON-neighbours
/// of `v`. If any two of them are non-adjacent that pair closes a triangle of
/// the complement with `v`, and otherwise the three are pairwise adjacent and
/// form a triangle of `g`.
///
/// Non-adjacency carries no vertex bound, so unlike
/// [`declare_triangle_or_indep`] this one takes the four bounds and the three
/// `v`-vs-`x` distinctness facts as hypotheses. At the 32 call sites they are
/// `le_trans` against a concrete bound and `Eq.refl Bool false`.
fn declare_antitriangle_or_indep(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let gr = graph_ty(d, &p);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let n = g_order(d, &p, g);

    let hv_lt_ty = d.lt(v, n);
    let hv_lt_fv = d.fresh_fvar();
    let hv_lt = d.kernel().fvar(hv_lt_fv);
    let hx_lt_ty = d.lt(x, n);
    let hx_lt_fv = d.fresh_fvar();
    let hx_lt = d.kernel().fvar(hx_lt_fv);
    let hy_lt_ty = d.lt(y, n);
    let hy_lt_fv = d.fresh_fvar();
    let hy_lt = d.kernel().fvar(hy_lt_fv);
    let hz_lt_ty = d.lt(z, n);
    let hz_lt_fv = d.fresh_fvar();
    let hz_lt = d.kernel().fvar(hz_lt_fv);

    let hvx_ne_ty = beq_false(d, v, x);
    let hvx_ne_fv = d.fresh_fvar();
    let hvx_ne = d.kernel().fvar(hvx_ne_fv);
    let hvy_ne_ty = beq_false(d, v, y);
    let hvy_ne_fv = d.fresh_fvar();
    let hvy_ne = d.kernel().fvar(hvy_ne_fv);
    let hvz_ne_ty = beq_false(d, v, z);
    let hvz_ne_fv = d.fresh_fvar();
    let hvz_ne = d.kernel().fvar(hvz_ne_fv);
    let hxy_ne_ty = beq_false(d, x, y);
    let hxy_ne_fv = d.fresh_fvar();
    let hxy_ne = d.kernel().fvar(hxy_ne_fv);
    let hyz_ne_ty = beq_false(d, y, z);
    let hyz_ne_fv = d.fresh_fvar();
    let hyz_ne = d.kernel().fvar(hyz_ne_fv);
    let hxz_ne_ty = beq_false(d, x, z);
    let hxz_ne_fv = d.fresh_fvar();
    let hxz_ne = d.kernel().fvar(hxz_ne_fv);

    let hvx_ty = adj_false(d, &p, g, v, x);
    let hvx_fv = d.fresh_fvar();
    let hvx = d.kernel().fvar(hvx_fv);
    let hvy_ty = adj_false(d, &p, g, v, y);
    let hvy_fv = d.fresh_fvar();
    let hvy = d.kernel().fvar(hvy_fv);
    let hvz_ty = adj_false(d, &p, g, v, z);
    let hvz_fv = d.fresh_fvar();
    let hvz = d.kernel().fvar(hvz_fv);

    let goal = mono_goal(d, &p, g);
    let left_ty = has_clique3(d, &p, g);
    let cg = compl(d, &p, g);
    let right_ty = has_clique3(d, &p, cg);

    let c_vx = d.const_app(
        p.graph_adj_b_compl_of_not_adj_b,
        &[g, v, x, hv_lt, hx_lt, hvx_ne, hvx],
    );
    let c_vy = d.const_app(
        p.graph_adj_b_compl_of_not_adj_b,
        &[g, v, y, hv_lt, hy_lt, hvy_ne, hvy],
    );
    let c_vz = d.const_app(
        p.graph_adj_b_compl_of_not_adj_b,
        &[g, v, z, hv_lt, hz_lt, hvz_ne, hvz],
    );

    let a_xy = adj_b(d, &p, g, x, y);
    let a_yz = adj_b(d, &p, g, y, z);
    let a_xz = adj_b(d, &p, g, x, z);

    let proof = {
        let on_xy_false = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let h_ty = adj_false(d, &p, g, x, y);
            let c_xy = d.const_app(
                p.graph_adj_b_compl_of_not_adj_b,
                &[g, x, y, hx_lt, hy_lt, hxy_ne, h],
            );
            let clique = mk_has_clique3(d, &p, cg, v, x, y, c_vx, c_xy, c_vy);
            let body = d.const_app(p.logic.or_inr, &[left_ty, right_ty, clique]);
            d.lam_fv(h_fv, h_ty, body)
        };
        let on_xy_true = {
            let hxy_t_fv = d.fresh_fvar();
            let hxy_t = d.kernel().fvar(hxy_t_fv);
            let hxy_t_ty = adj_true(d, &p, g, x, y);

            let on_yz_false = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let h_ty = adj_false(d, &p, g, y, z);
                let c_yz = d.const_app(
                    p.graph_adj_b_compl_of_not_adj_b,
                    &[g, y, z, hy_lt, hz_lt, hyz_ne, h],
                );
                let clique = mk_has_clique3(d, &p, cg, v, y, z, c_vy, c_yz, c_vz);
                let body = d.const_app(p.logic.or_inr, &[left_ty, right_ty, clique]);
                d.lam_fv(h_fv, h_ty, body)
            };
            let on_yz_true = {
                let hyz_t_fv = d.fresh_fvar();
                let hyz_t = d.kernel().fvar(hyz_t_fv);
                let hyz_t_ty = adj_true(d, &p, g, y, z);

                let on_xz_false = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let h_ty = adj_false(d, &p, g, x, z);
                    let c_xz = d.const_app(
                        p.graph_adj_b_compl_of_not_adj_b,
                        &[g, x, z, hx_lt, hz_lt, hxz_ne, h],
                    );
                    let clique = mk_has_clique3(d, &p, cg, v, x, z, c_vx, c_xz, c_vz);
                    let body = d.const_app(p.logic.or_inr, &[left_ty, right_ty, clique]);
                    d.lam_fv(h_fv, h_ty, body)
                };
                let on_xz_true = {
                    let hxz_t_fv = d.fresh_fvar();
                    let hxz_t = d.kernel().fvar(hxz_t_fv);
                    let hxz_t_ty = adj_true(d, &p, g, x, z);
                    let clique = mk_has_clique3(d, &p, g, x, y, z, hxy_t, hyz_t, hxz_t);
                    let body = d.const_app(p.logic.or_inl, &[left_ty, right_ty, clique]);
                    d.lam_fv(hxz_t_fv, hxz_t_ty, body)
                };
                let body = bool_or_elim(d, &p, a_xz, goal, on_xz_true, on_xz_false);
                d.lam_fv(hyz_t_fv, hyz_t_ty, body)
            };
            let body = bool_or_elim(d, &p, a_yz, goal, on_yz_true, on_yz_false);
            d.lam_fv(hxy_t_fv, hxy_t_ty, body)
        };
        bool_or_elim(d, &p, a_xy, goal, on_xy_true, on_xy_false)
    };

    let ty = {
        let s = d.arrow(hvz_ty, goal);
        let s = d.arrow(hvy_ty, s);
        let s = d.arrow(hvx_ty, s);
        let s = d.arrow(hxz_ne_ty, s);
        let s = d.arrow(hyz_ne_ty, s);
        let s = d.arrow(hxy_ne_ty, s);
        let s = d.arrow(hvz_ne_ty, s);
        let s = d.arrow(hvy_ne_ty, s);
        let s = d.arrow(hvx_ne_ty, s);
        let s = d.arrow(hz_lt_ty, s);
        let s = d.arrow(hy_lt_ty, s);
        let s = d.arrow(hx_lt_ty, s);
        let s = d.arrow(hv_lt_ty, s);
        let s = d.pi_fv(z_fv, nat, s);
        let s = d.pi_fv(y_fv, nat, s);
        let s = d.pi_fv(x_fv, nat, s);
        let s = d.pi_fv(v_fv, nat, s);
        d.pi_fv(g_fv, gr, s)
    };
    let value = {
        let s = d.lam_fv(hvz_fv, hvz_ty, proof);
        let s = d.lam_fv(hvy_fv, hvy_ty, s);
        let s = d.lam_fv(hvx_fv, hvx_ty, s);
        let s = d.lam_fv(hxz_ne_fv, hxz_ne_ty, s);
        let s = d.lam_fv(hyz_ne_fv, hyz_ne_ty, s);
        let s = d.lam_fv(hxy_ne_fv, hxy_ne_ty, s);
        let s = d.lam_fv(hvz_ne_fv, hvz_ne_ty, s);
        let s = d.lam_fv(hvy_ne_fv, hvy_ne_ty, s);
        let s = d.lam_fv(hvx_ne_fv, hvx_ne_ty, s);
        let s = d.lam_fv(hz_lt_fv, hz_lt_ty, s);
        let s = d.lam_fv(hy_lt_fv, hy_lt_ty, s);
        let s = d.lam_fv(hx_lt_fv, hx_lt_ty, s);
        let s = d.lam_fv(hv_lt_fv, hv_lt_ty, s);
        let s = d.lam_fv(z_fv, nat, s);
        let s = d.lam_fv(y_fv, nat, s);
        let s = d.lam_fv(x_fv, nat, s);
        let s = d.lam_fv(v_fv, nat, s);
        d.lam_fv(g_fv, gr, s)
    };
    d.declare_theorem(p.graph_antitriangle_or_indep, ty, value)
}

// ---------------------------------------------------------------------------
// Monotonicity, and the reduction a certificate needs.
// ---------------------------------------------------------------------------

fn declare_monotonicity(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let gr = graph_ty(d, &p);

    // arrows33_of_le : ∀ m n, Le m n → Arrows33 m → Arrows33 n
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let hmn_ty = d.le(m, n);
        let hmn_fv = d.fresh_fvar();
        let hmn = d.kernel().fvar(hmn_fv);
        let ham_ty = d.const_app(p.graph_arrows33, &[m]);
        let ham_fv = d.fresh_fvar();
        let ham = d.kernel().fvar(ham_fv);
        let concl = d.const_app(p.graph_arrows33, &[n]);

        let body = {
            let g_fv = d.fresh_fvar();
            let g = d.kernel().fvar(g_fv);
            let ord = g_order(d, &p, g);
            let hg_ty = d.le(n, ord);
            let hg_fv = d.fresh_fvar();
            let hg = d.kernel().fvar(hg_fv);
            let widened = d.const_app(p.le_trans, &[m, n, ord, hmn, hg]);
            let step = d.apply(ham, &[g, widened]);
            let with_hg = d.lam_fv(hg_fv, hg_ty, step);
            d.lam_fv(g_fv, gr, with_hg)
        };

        let ty = {
            let s4 = d.arrow(ham_ty, concl);
            let s3 = d.arrow(hmn_ty, s4);
            let s2 = d.pi_fv(n_fv, nat, s3);
            d.pi_fv(m_fv, nat, s2)
        };
        let value = {
            let s4 = d.lam_fv(ham_fv, ham_ty, body);
            let s3 = d.lam_fv(hmn_fv, hmn_ty, s4);
            let s2 = d.lam_fv(n_fv, nat, s3);
            d.lam_fv(m_fv, nat, s2)
        };
        d.declare_theorem(p.graph_arrows33_of_le, ty, value)?;
    }

    // isRamseyNumber33_of_succ : ∀ m, Arrows33 (succ m) →
    //   (Arrows33 m → False) → IsRamseyNumber33 (succ m)
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let succ_m = d.succ(m);
        let false_prop = d.kernel().const_(p.logic.false_, vec![]);

        let hup_ty = d.const_app(p.graph_arrows33, &[succ_m]);
        let hup_fv = d.fresh_fvar();
        let hup = d.kernel().fvar(hup_fv);
        let arrows_m = d.const_app(p.graph_arrows33, &[m]);
        let hlow_ty = d.arrow(arrows_m, false_prop);
        let hlow_fv = d.fresh_fvar();
        let hlow = d.kernel().fvar(hlow_fv);
        let concl = d.const_app(p.graph_is_ramsey33, &[succ_m]);

        let least_ty = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let arrows_k = d.const_app(p.graph_arrows33, &[k]);
            let inner = d.arrow(arrows_k, false_prop);
            let lt = d.lt(k, succ_m);
            let step = d.arrow(lt, inner);
            d.pi_fv(k_fv, nat, step)
        };
        let least = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let lt_ty = d.lt(k, succ_m);
            let hk_fv = d.fresh_fvar();
            let hk = d.kernel().fvar(hk_fv);
            let hak_ty = d.const_app(p.graph_arrows33, &[k]);
            let hak_fv = d.fresh_fvar();
            let hak = d.kernel().fvar(hak_fv);
            let hle = d.lemma(p.le_of_lt_succ, &[k, m, hk]);
            let lifted = d.const_app(p.graph_arrows33_of_le, &[k, m, hle, hak]);
            let body = d.apply(hlow, &[lifted]);
            let with_hak = d.lam_fv(hak_fv, hak_ty, body);
            let with_hk = d.lam_fv(hk_fv, lt_ty, with_hak);
            d.lam_fv(k_fv, nat, with_hk)
        };
        let proof = d.const_app(p.logic.and_intro, &[hup_ty, least_ty, hup, least]);

        let ty = {
            let s3 = d.arrow(hlow_ty, concl);
            let s2 = d.arrow(hup_ty, s3);
            d.pi_fv(m_fv, nat, s2)
        };
        let value = {
            let s3 = d.lam_fv(hlow_fv, hlow_ty, proof);
            let s2 = d.lam_fv(hup_fv, hup_ty, s3);
            d.lam_fv(m_fv, nat, s2)
        };
        d.declare_theorem(p.graph_is_ramsey33_of_succ, ty, value)?;
    }

    Ok(())
}

// ---------------------------------------------------------------------------
// The upper bound: a 32-leaf case tree over the edges at vertex 0.
// ---------------------------------------------------------------------------

/// What the case tree carries down to its leaves.
struct UpperCtx {
    /// The graph the theorem quantifies over.
    g: ExprId,
    /// `Or (HasClique3 g) (HasClique3 (compl g))`.
    goal: ExprId,
    /// `bounds[k] : Lt k (order g)` for `k` in `[0, UPPER_N)`.
    bounds: Vec<ExprId>,
}

/// One leaf: five decided edges at vertex `0`, so one colour class has at least
/// three members and the matching shared lemma closes the goal.
fn upper_leaf(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    ctx: &UpperCtx,
    facts: &[(u32, bool, ExprId)],
) -> ExprId {
    let neighbours: Vec<(u32, ExprId)> = facts
        .iter()
        .filter(|(_, adjacent, _)| *adjacent)
        .map(|&(k, _, h)| (k, h))
        .collect();
    let strangers: Vec<(u32, ExprId)> = facts
        .iter()
        .filter(|(_, adjacent, _)| !*adjacent)
        .map(|&(k, _, h)| (k, h))
        .collect();
    // Five vertices in two classes: one class has at least three members.
    assert!(
        neighbours.len() >= 3 || strangers.len() >= 3,
        "pigeonhole: {} neighbours and {} strangers of vertex 0",
        neighbours.len(),
        strangers.len()
    );

    let zero = d.num(0);
    let false_ = d.bool_false();
    if neighbours.len() >= 3 {
        let (kx, hx) = neighbours[0];
        let (ky, hy) = neighbours[1];
        let (kz, hz) = neighbours[2];
        let x = d.num(kx);
        let y = d.num(ky);
        let z = d.num(kz);
        let ne_xy = d.bool_refl(false_);
        let ne_yz = d.bool_refl(false_);
        let ne_xz = d.bool_refl(false_);
        d.const_app(
            p.graph_triangle_or_indep,
            &[ctx.g, zero, x, y, z, hx, hy, hz, ne_xy, ne_yz, ne_xz],
        )
    } else {
        let (kx, hx) = strangers[0];
        let (ky, hy) = strangers[1];
        let (kz, hz) = strangers[2];
        let x = d.num(kx);
        let y = d.num(ky);
        let z = d.num(kz);
        let bv = ctx.bounds[0];
        let bx = ctx.bounds[kx as usize];
        let by = ctx.bounds[ky as usize];
        let bz = ctx.bounds[kz as usize];
        let ne_vx = d.bool_refl(false_);
        let ne_vy = d.bool_refl(false_);
        let ne_vz = d.bool_refl(false_);
        let ne_xy = d.bool_refl(false_);
        let ne_yz = d.bool_refl(false_);
        let ne_xz = d.bool_refl(false_);
        d.const_app(
            p.graph_antitriangle_or_indep,
            &[
                ctx.g, zero, x, y, z, bv, bx, by, bz, ne_vx, ne_vy, ne_vz, ne_xy, ne_yz, ne_xz, hx,
                hy, hz,
            ],
        )
    }
}

/// Split on `adjB g 0 k` for `k = next … UPPER_N - 1`, then close at the leaf.
fn upper_tree(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    ctx: &UpperCtx,
    next: u32,
    facts: &mut Vec<(u32, bool, ExprId)>,
) -> ExprId {
    if next >= UPPER_N {
        return upper_leaf(d, p, ctx, facts);
    }
    let zero = d.num(0);
    let k = d.num(next);
    let adj = adj_b(d, p, ctx.g, zero, k);
    let on_true = {
        let h_ty = adj_true(d, p, ctx.g, zero, k);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        facts.push((next, true, h));
        let body = upper_tree(d, p, ctx, next + 1, facts);
        facts.pop();
        d.lam_fv(h_fv, h_ty, body)
    };
    let on_false = {
        let h_ty = adj_false(d, p, ctx.g, zero, k);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        facts.push((next, false, h));
        let body = upper_tree(d, p, ctx, next + 1, facts);
        facts.pop();
        d.lam_fv(h_fv, h_ty, body)
    };
    bool_or_elim(d, p, adj, ctx.goal, on_true, on_false)
}

/// `Nat.Graph.ramsey33_arrows_six : Arrows33 6`.
fn declare_upper_bound(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let gr = graph_ty(d, &p);

    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let ord = g_order(d, &p, g);
    let six = d.num(UPPER_N);
    let h6_ty = d.le(six, ord);
    let h6_fv = d.fresh_fvar();
    let h6 = d.kernel().fvar(h6_fv);
    let goal = mono_goal(d, &p, g);

    // `k < order g` for every vertex, from `succ k <= 6 <= order g`.
    let bounds: Vec<ExprId> = (0..UPPER_N)
        .map(|k| {
            let succ_k = d.num(k + 1);
            let small = le_proof(d, &p, k + 1, UPPER_N);
            d.const_app(p.le_trans, &[succ_k, six, ord, small, h6])
        })
        .collect();

    let ctx = UpperCtx { g, goal, bounds };
    let mut facts: Vec<(u32, bool, ExprId)> = Vec::new();
    let tree = upper_tree(d, &p, &ctx, 1, &mut facts);

    let value = {
        let inner = d.lam_fv(h6_fv, h6_ty, tree);
        d.lam_fv(g_fv, gr, inner)
    };
    let ty = d.const_app(p.graph_arrows33, &[six]);
    d.declare_theorem(p.graph_ramsey33_arrows_six, ty, value)
}

// ---------------------------------------------------------------------------
// The lower bound: the search certificate, refuted by reflection.
// ---------------------------------------------------------------------------

/// `Nat.Graph.mk rel 5` for the searched edge set, each edge stored in both
/// orientations so the conjunctive symmetrization sees it.
fn witness_graph(d: &mut NatDev<'_>, p: &NatPrelude, edges: &[(u32, u32)]) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let mut pairs: Vec<(u32, u32)> = Vec::new();
    for &(a, b) in edges {
        pairs.push((a, b));
        pairs.push((b, a));
    }
    let mut body = d.bool_false();
    for &(a, b) in pairs.iter().rev() {
        let a_lit = d.num(a);
        let b_lit = d.num(b);
        let hit_i = d.beq(i, a_lit);
        let hit_j = d.beq(j, b_lit);
        let hit = and_b(d, p, hit_i, hit_j);
        body = or_b(d, p, hit, body);
    }
    let rel = {
        let inner = d.lam_fv(j_fv, nat, body);
        d.lam_fv(i_fv, nat, inner)
    };
    let n = d.num(LOWER_N);
    d.const_app(p.graph_mk, &[rel, n])
}

/// `Nat.Graph.ramsey33Witness` and `Nat.Graph.ramsey33_not_arrows_five`.
///
/// Declares NOTHING when the search finds no witness, which makes
/// `declare_ramsey_number` name a theorem that does not exist and the whole
/// prelude fail to build. That is deliberate: the exit status depends on the
/// finding.
fn declare_lower_bound(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let gr = graph_ty(d, &p);
    let Some(edges) = search_ramsey_lower() else {
        return Ok(());
    };

    // ramsey33Witness : Nat.Graph
    {
        let value = witness_graph(d, &p, &edges);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.graph_ramsey33_witness,
            uparams: vec![],
            ty: gr,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // ramsey33_not_arrows_five : Arrows33 5 → False
    {
        let five = d.num(LOWER_N);
        let h_ty = d.const_app(p.graph_arrows33, &[five]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let false_prop = d.kernel().const_(p.logic.false_, vec![]);
        let true_ = d.bool_true();

        let w = d.kernel().const_(p.graph_ramsey33_witness, vec![]);
        let refl_five = d.const_app(p.le_refl, &[five]);
        let disjunction = d.apply(h, &[w, refl_five]);
        let left_ty = has_clique3(d, &p, w);
        let cw = compl(d, &p, w);
        let right_ty = has_clique3(d, &p, cw);

        let on_left = {
            let hc_fv = d.fresh_fvar();
            let hc = d.kernel().fvar(hc_fv);
            let decided = d.bool_refl(true_);
            let body = d.const_app(p.graph_not_has_clique3_of_decide, &[w, decided, hc]);
            d.lam_fv(hc_fv, left_ty, body)
        };
        let on_right = {
            let hc_fv = d.fresh_fvar();
            let hc = d.kernel().fvar(hc_fv);
            let decided = d.bool_refl(true_);
            let body = d.const_app(p.graph_not_has_clique3_of_decide, &[cw, decided, hc]);
            d.lam_fv(hc_fv, right_ty, body)
        };
        let proof = d.const_app(
            p.logic.or_elim,
            &[
                left_ty,
                right_ty,
                false_prop,
                disjunction,
                on_left,
                on_right,
            ],
        );

        let ty = d.arrow(h_ty, false_prop);
        let value = d.lam_fv(h_fv, h_ty, proof);
        d.declare_theorem(p.graph_ramsey33_not_arrows_five, ty, value)?;
    }

    Ok(())
}

/// `Nat.Graph.ramsey_three_three : IsRamseyNumber33 6`.
fn declare_ramsey_number(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let five = d.num(LOWER_N);
    let six = d.num(UPPER_N);
    let upper = d.kernel().const_(p.graph_ramsey33_arrows_six, vec![]);
    let lower = d.kernel().const_(p.graph_ramsey33_not_arrows_five, vec![]);
    let value = d.const_app(p.graph_is_ramsey33_of_succ, &[five, upper, lower]);
    let ty = d.const_app(p.graph_is_ramsey33, &[six]);
    d.declare_theorem(p.graph_ramsey_three_three, ty, value)
}

// ---------------------------------------------------------------------------
// Entry point.
// ---------------------------------------------------------------------------

/// Declare the Ramsey family and `R(3,3) = 6`.
///
/// # Errors
///
/// Returns the kernel's rejection if any declaration fails to type-check —
/// including the case where the lower-bound search found no witness, since
/// `ramsey_three_three` then names a theorem that was never declared.
pub(super) fn declare_ramsey_all(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    declare_definitions(d, p)?;
    declare_compl_law(d, p)?;
    declare_reflection(d, p)?;
    declare_triangle_or_indep(d, p)?;
    declare_antitriangle_or_indep(d, p)?;
    declare_monotonicity(d, p)?;
    declare_upper_bound(d, p)?;
    declare_lower_bound(d, p)?;
    declare_ramsey_number(d, p)?;
    Ok(())
}
