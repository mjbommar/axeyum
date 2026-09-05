//! Evaluation tests for `fo_numbering.rs`.
//!
//! `FO.Term.code` and `FO.Formula.code` are `Definition`s: a numbering that
//! gave two constructors the same tag, or dropped a field from the payload,
//! type-checks exactly as readily as the intended one. Every expected value
//! below is hand-computed from `FO.Code.pair a b = tri (a + b) + a` and then
//! asserted by `def_eq`.
//!
//! The two `code_injective` theorems are pinned by their INFERRED type against
//! a rebuilt statement, with the converse (`t = u -> code t = code u`, which is
//! true but is congruence rather than injectivity) as the negative control.

use super::*;
use crate::Kernel;
use crate::fo_code::{nsucc, nzero, tri_app};

struct Fixture {
    kernel: Kernel,
    p: FoNumberingPrelude,
    c: CodeNames,
    term_ty: ExprId,
    formula_ty: ExprId,
}

impl Fixture {
    fn new() -> Self {
        let mut kernel = Kernel::new();
        let p = build_fo_numbering_prelude(&mut kernel).expect("FO numbering prelude must build");
        let c = CodeNames::rebuild(&mut kernel, p.code.syntax.nat);
        let term_ty = kernel.const_(p.code.syntax.term, vec![]);
        let formula_ty = kernel.const_(p.code.syntax.formula, vec![]);
        Self {
            kernel,
            p,
            c,
            term_ty,
            formula_ty,
        }
    }

    fn num(&mut self, n: u32) -> ExprId {
        let mut e = nzero(&mut self.kernel, &self.c);
        for _ in 0..n {
            e = nsucc(&mut self.kernel, &self.c, e);
        }
        e
    }

    fn ctor(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        let head = self.kernel.const_(name, vec![]);
        apply_all(&mut self.kernel, head, args)
    }

    fn var(&mut self, i: u32) -> ExprId {
        let idx = self.num(i);
        let name = self.p.code.syntax.var;
        self.ctor(name, &[idx])
    }

    fn f0(&mut self, k: u32) -> ExprId {
        let idx = self.num(k);
        let name = self.p.code.syntax.f0;
        self.ctor(name, &[idx])
    }

    fn tcode(&mut self, t: ExprId) -> ExprId {
        let f = self.kernel.const_(self.p.term_code, vec![]);
        self.kernel.app(f, t)
    }

    fn fcode(&mut self, p: ExprId) -> ExprId {
        let f = self.kernel.const_(self.p.formula_code, vec![]);
        self.kernel.app(f, p)
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

/// `tri` is what every expected value below is computed from, so it is
/// re-derived here rather than trusted: 0, 1, 3, 6, 10, 15, 21, 28, 36.
#[test]
fn the_triangular_numbers_this_file_computes_with() {
    let mut f = Fixture::new();
    for (arg, want) in [(6_u32, 21_u32), (7, 28), (8, 36)] {
        let n = f.num(arg);
        let got = tri_app(&mut f.kernel, &f.c, n);
        let expect = f.num(want);
        f.assert_eq_expr(got, expect, &format!("tri {arg}"));
    }
}

/// ```text
/// ⌜var 0⌝   = pair 0 0             = 0
/// ⌜var 2⌝   = pair 0 2             = tri 2 + 0 = 3
/// ⌜f0 0⌝    = pair 1 0             = tri 1 + 1 = 2
/// ⌜f0 1⌝    = pair 1 1             = tri 2 + 1 = 4
/// ⌜f1 0 (var 0)⌝ = pair 2 (pair 0 0) = pair 2 0 = tri 2 + 2 = 5
/// ⌜f2 0 (var 0) (var 0)⌝ = pair 3 (pair 0 (pair 0 0)) = pair 3 0 = tri 3 + 3 = 9
/// ```
#[test]
fn term_code_at_small_terms() {
    let mut f = Fixture::new();

    let v0 = f.var(0);
    let got = f.tcode(v0);
    let want = f.num(0);
    f.assert_eq_expr(got, want, "code (var 0)");

    let v2 = f.var(2);
    let got = f.tcode(v2);
    let want = f.num(3);
    f.assert_eq_expr(got, want, "code (var 2)");

    let c0 = f.f0(0);
    let got = f.tcode(c0);
    let want = f.num(2);
    f.assert_eq_expr(got, want, "code (f0 0)");

    let c1 = f.f0(1);
    let got = f.tcode(c1);
    let want = f.num(4);
    f.assert_eq_expr(got, want, "code (f0 1)");

    let inner = f.var(0);
    let k = f.num(0);
    let name = f.p.code.syntax.f1;
    let t = f.ctor(name, &[k, inner]);
    let got = f.tcode(t);
    let want = f.num(5);
    f.assert_eq_expr(got, want, "code (f1 0 (var 0))");

    let a = f.var(0);
    let b = f.var(0);
    let k = f.num(0);
    let name = f.p.code.syntax.f2;
    let t = f.ctor(name, &[k, a, b]);
    let got = f.tcode(t);
    let want = f.num(9);
    f.assert_eq_expr(got, want, "code (f2 0 (var 0) (var 0))");
}

/// The discriminating pair: `var 0` and `f0 0` differ only in their TAG, so a
/// numbering that gave two constructors the same tag would collapse them.
#[test]
fn different_constructors_at_the_same_argument_get_different_codes() {
    let mut f = Fixture::new();
    let v = f.var(0);
    let lhs = f.tcode(v);
    let k = f.f0(0);
    let rhs = f.tcode(k);
    f.assert_ne_expr(lhs, rhs, "code (var 0) vs code (f0 0)");
}

/// ```text
/// ⌜bot⌝            = pair 0 0              = 0
/// ⌜eqf (var 0) (var 0)⌝ = pair 1 (pair 0 0) = pair 1 0 = tri 1 + 1 = 2
/// ⌜imp bot bot⌝    = pair 6 (pair 0 0)     = pair 6 0 = tri 6 + 6 = 27
/// ⌜all bot⌝        = pair 7 0              = tri 7 + 7 = 35
/// ⌜ex bot⌝         = pair 8 0              = tri 8 + 8 = 44
/// ```
#[test]
fn formula_code_at_small_formulas() {
    let mut f = Fixture::new();

    let bot = f.kernel.const_(f.p.code.syntax.bot, vec![]);
    let got = f.fcode(bot);
    let want = f.num(0);
    f.assert_eq_expr(got, want, "code bot");

    let a = f.var(0);
    let b = f.var(0);
    let name = f.p.code.syntax.eqf;
    let e = f.ctor(name, &[a, b]);
    let got = f.fcode(e);
    let want = f.num(2);
    f.assert_eq_expr(got, want, "code (eqf (var 0) (var 0))");

    let name = f.p.code.syntax.imp;
    let i = f.ctor(name, &[bot, bot]);
    let got = f.fcode(i);
    let want = f.num(27);
    f.assert_eq_expr(got, want, "code (imp bot bot)");

    let name = f.p.code.syntax.all;
    let q = f.ctor(name, &[bot]);
    let got = f.fcode(q);
    let want = f.num(35);
    f.assert_eq_expr(got, want, "code (all bot)");

    let name = f.p.code.syntax.ex;
    let q = f.ctor(name, &[bot]);
    let got = f.fcode(q);
    let want = f.num(44);
    f.assert_eq_expr(got, want, "code (ex bot)");
}

/// `all` and `ex` are the pair a copy-paste between the two quantifier cases
/// would collapse, and they carry the same field.
#[test]
fn the_two_quantifiers_get_different_codes() {
    let mut f = Fixture::new();
    let bot = f.kernel.const_(f.p.code.syntax.bot, vec![]);
    let name = f.p.code.syntax.all;
    let q1 = f.ctor(name, &[bot]);
    let lhs = f.fcode(q1);
    let name = f.p.code.syntax.ex;
    let q2 = f.ctor(name, &[bot]);
    let rhs = f.fcode(q2);
    f.assert_ne_expr(lhs, rhs, "code (all bot) vs code (ex bot)");
}

/// The three binary connectives are the other copy-paste risk.
#[test]
fn the_three_binary_connectives_get_different_codes() {
    let mut f = Fixture::new();
    let bot = f.kernel.const_(f.p.code.syntax.bot, vec![]);
    let mut codes = Vec::new();
    for name in [
        f.p.code.syntax.and_,
        f.p.code.syntax.or_,
        f.p.code.syntax.imp,
    ] {
        let q = f.ctor(name, &[bot, bot]);
        codes.push(f.fcode(q));
    }
    f.assert_ne_expr(
        codes[0],
        codes[1],
        "code (and_ bot bot) vs code (or_ bot bot)",
    );
    f.assert_ne_expr(
        codes[1],
        codes[2],
        "code (or_ bot bot) vs code (imp bot bot)",
    );
    f.assert_ne_expr(
        codes[0],
        codes[2],
        "code (and_ bot bot) vs code (imp bot bot)",
    );
}

/// `FO.Term.code_injective`'s inferred type is
/// `Π t u, Eq Nat (code t) (code u) -> Eq FO.Term t u`.
///
/// The negative control is the CONVERSE, `Π t u, Eq FO.Term t u ->
/// Eq Nat (code t) (code u)` — true, but congruence rather than injectivity,
/// and the statement a proof term built the wrong way round would have.
#[test]
fn term_code_injective_states_injectivity_not_congruence() {
    let mut f = Fixture::new();
    let t_id = 1_646_001_u64;
    let u_id = 1_646_002_u64;
    let t = f.kernel.fvar(t_id);
    let u = f.kernel.fvar(u_id);
    let logic = f.c.logic;
    let nat_ty = f.c.nat_ty;
    let term_ty = f.term_ty;

    let ct = f.tcode(t);
    let cu = f.tcode(u);
    let codes_eq = geq(&mut f.kernel, logic, nat_ty, ct, cu);
    let terms_eq = geq(&mut f.kernel, logic, term_ty, t, u);

    let want = {
        let inner = arrow(&mut f.kernel, codes_eq, terms_eq);
        pis(&mut f.kernel, &[(t_id, term_ty), (u_id, term_ty)], inner)
    };
    let converse = {
        let inner = arrow(&mut f.kernel, terms_eq, codes_eq);
        pis(&mut f.kernel, &[(t_id, term_ty), (u_id, term_ty)], inner)
    };

    let c = f.kernel.const_(f.p.term_code_injective, vec![]);
    let got = f.kernel.infer(c).expect("a declared theorem has a type");
    f.assert_eq_expr(got, want, "FO.Term.code_injective's type");
    f.assert_ne_expr(got, converse, "FO.Term.code_injective vs its converse");
}

/// The same, for `FO.Formula.code_injective`.
#[test]
fn formula_code_injective_states_injectivity_not_congruence() {
    let mut f = Fixture::new();
    let p_id = 1_646_011_u64;
    let q_id = 1_646_012_u64;
    let p = f.kernel.fvar(p_id);
    let q = f.kernel.fvar(q_id);
    let logic = f.c.logic;
    let nat_ty = f.c.nat_ty;
    let formula_ty = f.formula_ty;

    let cp = f.fcode(p);
    let cq = f.fcode(q);
    let codes_eq = geq(&mut f.kernel, logic, nat_ty, cp, cq);
    let formulas_eq = geq(&mut f.kernel, logic, formula_ty, p, q);

    let want = {
        let inner = arrow(&mut f.kernel, codes_eq, formulas_eq);
        pis(
            &mut f.kernel,
            &[(p_id, formula_ty), (q_id, formula_ty)],
            inner,
        )
    };
    let converse = {
        let inner = arrow(&mut f.kernel, formulas_eq, codes_eq);
        pis(
            &mut f.kernel,
            &[(p_id, formula_ty), (q_id, formula_ty)],
            inner,
        )
    };

    let c = f.kernel.const_(f.p.formula_code_injective, vec![]);
    let got = f.kernel.infer(c).expect("a declared theorem has a type");
    f.assert_eq_expr(got, want, "FO.Formula.code_injective's type");
    f.assert_ne_expr(got, converse, "FO.Formula.code_injective vs its converse");
}

#[test]
fn every_declaration_of_this_slice_is_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;
    for (name, label) in [
        (p.term_code, "FO.Term.code"),
        (p.formula_code, "FO.Formula.code"),
        (p.term_code_injective, "FO.Term.code_injective"),
        (p.formula_code_injective, "FO.Formula.code_injective"),
    ] {
        f.assert_axiom_free(name, label);
    }
}
