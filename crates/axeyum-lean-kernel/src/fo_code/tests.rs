//! Evaluation tests for `fo_code.rs`.
//!
//! Every definition in the parent module is a `Definition`, so the kernel
//! admitting it proves only that it is well-formed — a `pair` that dropped its
//! `tri`, or a `step` with its two branches swapped, would type-check
//! identically. Each test below hand-computes the expected value first and
//! then asserts it by `Kernel::def_eq` at concrete small arguments.
//!
//! The theorems are pinned differently: `Environment::contains` FIRST (an
//! absent name has an empty axiom footprint too), then
//! `Kernel::axiom_footprint` empty.

use super::*;
use crate::Kernel;

struct Fixture {
    kernel: Kernel,
    p: FoCodePrelude,
    c: CodeNames,
}

impl Fixture {
    fn new() -> Self {
        let mut kernel = Kernel::new();
        let p = build_fo_code_prelude(&mut kernel).expect("FO code prelude must build");
        let c = CodeNames::rebuild(&mut kernel, p.syntax.nat);
        Self { kernel, p, c }
    }

    /// The unary numeral `Nat.succ^n Nat.zero`. Kept tiny throughout.
    fn num(&mut self, n: u32) -> ExprId {
        let mut e = nzero(&mut self.kernel, &self.c);
        for _ in 0..n {
            e = nsucc(&mut self.kernel, &self.c, e);
        }
        e
    }

    fn tri(&mut self, n: u32) -> ExprId {
        let arg = self.num(n);
        tri_app(&mut self.kernel, &self.c, arg)
    }

    fn pair(&mut self, a: u32, b: u32) -> ExprId {
        let av = self.num(a);
        let bv = self.num(b);
        pair_app(&mut self.kernel, &self.c, av, bv)
    }

    fn unpair(&mut self, n: u32) -> ExprId {
        let arg = self.num(n);
        let f = self.kernel.const_(self.p.unpair, vec![]);
        self.kernel.app(f, arg)
    }

    fn mk(&mut self, a: u32, b: u32) -> ExprId {
        let av = self.num(a);
        let bv = self.num(b);
        pmk(&mut self.kernel, &self.c, av, bv)
    }

    fn code_fst(&mut self, n: u32) -> ExprId {
        let arg = self.num(n);
        let f = self.kernel.const_(self.p.fst, vec![]);
        self.kernel.app(f, arg)
    }

    fn code_snd(&mut self, n: u32) -> ExprId {
        let arg = self.num(n);
        let f = self.kernel.const_(self.p.snd, vec![]);
        self.kernel.app(f, arg)
    }

    fn assert_eq_expr(&mut self, got: ExprId, want: ExprId, what: &str) {
        assert!(
            self.kernel.def_eq(got, want),
            "{what}: got {}, want {}",
            self.kernel.render_lean(got),
            self.kernel.render_lean(want)
        );
    }

    fn assert_ne_expr(&mut self, got: ExprId, want: ExprId, what: &str) {
        assert!(
            !self.kernel.def_eq(got, want),
            "{what}: expected these to DIFFER, both are {}",
            self.kernel.render_lean(got)
        );
    }

    /// `Environment::contains` first — an absent name has an empty axiom
    /// footprint too, so footprint-only would be a vacuous check.
    fn assert_axiom_free(&mut self, name: NameId, what: &str) {
        assert!(
            self.kernel.environment().contains(name),
            "{what}: not in the environment at all"
        );
        let footprint = self.kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{what}: axiom footprint must be empty, got {footprint:?}"
        );
    }
}

#[test]
fn tri_computes_the_triangular_numbers() {
    let mut f = Fixture::new();
    // 0, 1, 3, 6, 10, 15
    for (arg, want) in [(0_u32, 0_u32), (1, 1), (2, 3), (3, 6), (4, 10), (5, 15)] {
        let got = f.tri(arg);
        let expect = f.num(want);
        f.assert_eq_expr(got, expect, &format!("tri {arg}"));
    }
}

/// The whole anti-diagonal enumeration up to `a + b = 3`, hand-listed:
///
/// ```text
/// (0,0)=0 (0,1)=1 (1,0)=2 (0,2)=3 (1,1)=4 (2,0)=5 (0,3)=6 (1,2)=7 (2,1)=8 (3,0)=9
/// ```
///
/// A transposed `pair` (`tri (a+b) + b`) agrees at every diagonal endpoint and
/// differs at `(1,2)`/`(2,1)`, so this table is discriminating rather than
/// decorative.
#[test]
fn pair_enumerates_the_anti_diagonals() {
    let mut f = Fixture::new();
    let table = [
        (0_u32, 0_u32, 0_u32),
        (0, 1, 1),
        (1, 0, 2),
        (0, 2, 3),
        (1, 1, 4),
        (2, 0, 5),
        (0, 3, 6),
        (1, 2, 7),
        (2, 1, 8),
        (3, 0, 9),
    ];
    for (a, b, want) in table {
        let got = f.pair(a, b);
        let expect = f.num(want);
        f.assert_eq_expr(got, expect, &format!("pair {a} {b}"));
    }
}

/// `pair` is not symmetric — the control that a `tri (a + b) + b` or an
/// `a + b`-only implementation would fail.
#[test]
fn pair_is_not_symmetric() {
    let mut f = Fixture::new();
    let left = f.pair(1, 2);
    let right = f.pair(2, 1);
    f.assert_ne_expr(left, right, "pair 1 2 vs pair 2 1");
}

#[test]
fn unpair_inverts_the_enumeration_at_every_small_code() {
    let mut f = Fixture::new();
    let table = [
        (0_u32, 0_u32, 0_u32),
        (1, 0, 1),
        (2, 1, 0),
        (3, 0, 2),
        (4, 1, 1),
        (5, 2, 0),
        (6, 0, 3),
        (7, 1, 2),
        (8, 2, 1),
        (9, 3, 0),
    ];
    for (n, a, b) in table {
        let got = f.unpair(n);
        let expect = f.mk(a, b);
        f.assert_eq_expr(got, expect, &format!("unpair {n}"));
    }
}

#[test]
fn the_two_projections_read_the_components_back() {
    let mut f = Fixture::new();
    for (n, a, b) in [(0_u32, 0_u32, 0_u32), (4, 1, 1), (7, 1, 2), (8, 2, 1)] {
        let got_fst = f.code_fst(n);
        let want_fst = f.num(a);
        f.assert_eq_expr(got_fst, want_fst, &format!("fst {n}"));
        let got_snd = f.code_snd(n);
        let want_snd = f.num(b);
        f.assert_eq_expr(got_snd, want_snd, &format!("snd {n}"));
    }
}

/// The `step` equations, checked directly rather than only through `unpair`:
/// `step (mk a 0) = mk 0 (succ a)` and `step (mk a (succ b)) = mk (succ a) b`.
/// Swapping the two branches is invisible on the diagonal `(0, 0)` alone.
#[test]
fn step_walks_and_restarts_the_diagonal() {
    let mut f = Fixture::new();
    let step = f.kernel.const_(f.p.step, vec![]);
    for (a, b, wa, wb) in [(2_u32, 0_u32, 0_u32, 3_u32), (1, 2, 2, 1), (0, 1, 1, 0)] {
        let arg = f.mk(a, b);
        let got = f.kernel.app(step, arg);
        let want = f.mk(wa, wb);
        f.assert_eq_expr(got, want, &format!("step (mk {a} {b})"));
    }
}

#[test]
fn every_declaration_of_this_slice_is_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;
    for (name, label) in [
        (p.tri, "FO.Code.tri"),
        (p.pair, "FO.Code.pair"),
        (p.step, "FO.Code.step"),
        (p.unpair, "FO.Code.unpair"),
        (p.fst, "FO.Code.fst"),
        (p.snd, "FO.Code.snd"),
        (p.pair_zero_succ, "FO.Code.pair_zero_succ"),
        (p.pair_succ, "FO.Code.pair_succ"),
        (p.unpair_pair, "FO.Code.unpair_pair"),
        (p.fst_pair, "FO.Code.fst_pair"),
        (p.snd_pair, "FO.Code.snd_pair"),
        (p.pair_inj_left, "FO.Code.pair_inj_left"),
        (p.pair_inj_right, "FO.Code.pair_inj_right"),
    ] {
        f.assert_axiom_free(name, label);
    }
}
