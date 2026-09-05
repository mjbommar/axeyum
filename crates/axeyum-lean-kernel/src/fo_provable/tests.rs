//! Tests for `fo_provable.rs`.
//!
//! `FO.Context.shift` and `FO.ctxSat` are `Definition`s and get evaluation
//! tests; `FO.Provable` is an inductive relation, so the checks on it are the
//! three example derivations (admitted and axiom-free) plus structural guards
//! on the two rules whose *shape* is what makes them sound — `all_intro`'s
//! eigenvariable condition and `ex_elim`'s two shifts.

use super::*;
use crate::Kernel;

struct Fixture {
    kernel: Kernel,
    p: FoProvablePrelude,
}

impl Fixture {
    fn new() -> Self {
        let mut kernel = Kernel::new();
        let p = build_fo_provable_prelude(&mut kernel).expect("FO provable prelude must build");
        Self { kernel, p }
    }

    fn syn(&mut self) -> SyntaxNames {
        let syntax = self.p.semantics.syntax;
        syntax.names(&mut self.kernel)
    }

    fn calc(&mut self) -> CalcNames {
        let p = self.p;
        p.calc(&mut self.kernel)
    }

    fn logic(&self) -> crate::LogicPrelude {
        self.p.semantics.syntax.nat.logic
    }

    fn nil(&mut self) -> ExprId {
        self.kernel.const_(self.p.nil, vec![])
    }

    fn cons(&mut self, head: ExprId, tail: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.cons, vec![]);
        apply_all(&mut self.kernel, c, &[head, tail])
    }

    fn shift_ctx(&mut self, g: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.context_shift, vec![]);
        self.kernel.app(c, g)
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
            "{what}: expected these to differ, but both are {}",
            self.kernel.render_lean(got)
        );
    }
}

/// Every declared name is in the environment, INCLUDING all sixteen rules —
/// the rule count is read from the array, not written as a literal, so a rule
/// added or removed cannot silently escape this control.
#[test]
fn fo_provable_prelude_declares_every_name() {
    let f = Fixture::new();
    let p = f.p;
    let env = f.kernel.environment();
    for (name, label) in [
        (p.context, "FO.Context"),
        (p.nil, "FO.Context.nil"),
        (p.cons, "FO.Context.cons"),
        (p.context_rec, "FO.Context.rec"),
        (p.context_shift, "FO.Context.shift"),
        (p.ctx_sat, "FO.ctxSat"),
        (p.provable, "FO.Provable"),
        (p.provable_rec, "FO.Provable.rec"),
        (p.provable_imp_self, "FO.provable_imp_self"),
        (p.provable_all_imp_self, "FO.provable_all_imp_self"),
        (p.provable_all_imp_ex, "FO.provable_all_imp_ex"),
    ] {
        assert!(env.get(name).is_some(), "{label} must be declared");
    }
    for (i, &rule_name) in p.rules.iter().enumerate() {
        assert!(
            env.get(rule_name).is_some(),
            "FO.Provable rule #{i} must be declared"
        );
    }
}

/// `FO.Context.shift nil` reduces to `nil` — the reduction
/// `FO.provable_all_imp_self`'s admission depends on — and
/// `FO.Context.shift (cons a nil)` reduces to `cons (Formula.shift a) nil`,
/// which is the other half: `shift` is not the identity.
#[test]
fn context_shift_computes_at_nil_and_at_a_cons() {
    let mut f = Fixture::new();
    let syn = f.syn();

    let nil = f.nil();
    let got = f.shift_ctx(nil);
    let want = f.nil();
    f.assert_eq_expr(got, want, "Context.shift nil");

    // a := rel1 0 (var i), which Formula.shift moves to rel1 0 (var (i+1)).
    let atom_at = |f: &mut Fixture, i: u32| -> ExprId {
        let mut idx = f.kernel.const_(syn.nat_zero, vec![]);
        let succ = f.kernel.const_(syn.nat_succ, vec![]);
        for _ in 0..i {
            idx = f.kernel.app(succ, idx);
        }
        let var = f.kernel.const_(syn.var, vec![]);
        let v = f.kernel.app(var, idx);
        let zero = f.kernel.const_(syn.nat_zero, vec![]);
        let rel1 = f.kernel.const_(syn.rel1, vec![]);
        apply_all(&mut f.kernel, rel1, &[zero, v])
    };

    let a0 = atom_at(&mut f, 0);
    let nil = f.nil();
    let g = f.cons(a0, nil);
    let got = f.shift_ctx(g);

    let a1 = atom_at(&mut f, 1);
    let nil = f.nil();
    let want = f.cons(a1, nil);
    f.assert_eq_expr(got, want, "Context.shift (cons (rel1 0 (var 0)) nil)");

    // …and NOT the identity on that entry.
    let a0 = atom_at(&mut f, 0);
    let nil = f.nil();
    let unchanged = f.cons(a0, nil);
    f.assert_ne_expr(got, unchanged, "Context.shift must move a free index");
}

/// `FO.ctxSat` computes: `True` at `nil`, and a conjunction whose left half is
/// `FO.sat` of the head at `cons`.
#[test]
fn ctx_sat_computes_at_nil_and_at_a_cons() {
    let mut f = Fixture::new();
    let syn = f.syn();
    let semantics = f.p.semantics;
    let logic = f.logic();

    let nat_ty = f.kernel.const_(semantics.syntax.nat.nat, vec![]);
    let structure = f.kernel.const_(semantics.nat_structure, vec![]);
    let v = {
        let id = 1_637_900_u64;
        let n = f.kernel.fvar(id);
        lam_fv(&mut f.kernel, id, nat_ty, n)
    };

    let ctx_sat_name = f.p.ctx_sat;
    let ctx_sat_app = |f: &mut Fixture, g: ExprId| -> ExprId {
        let c = f.kernel.const_(ctx_sat_name, vec![]);
        apply_all(&mut f.kernel, c, &[nat_ty, structure, g, v])
    };

    let nil = f.nil();
    let got = ctx_sat_app(&mut f, nil);
    let want = f.kernel.const_(logic.true_, vec![]);
    f.assert_eq_expr(got, want, "ctxSat nil must be True");

    let atom = {
        let zero = f.kernel.const_(syn.nat_zero, vec![]);
        let f0 = f.kernel.const_(syn.f0, vec![]);
        let constant = f.kernel.app(f0, zero);
        let one = {
            let z = f.kernel.const_(syn.nat_zero, vec![]);
            let succ = f.kernel.const_(syn.nat_succ, vec![]);
            f.kernel.app(succ, z)
        };
        let rel2 = f.kernel.const_(syn.rel2, vec![]);
        apply_all(&mut f.kernel, rel2, &[one, constant, constant])
    };
    let nil = f.nil();
    let g = f.cons(atom, nil);
    let got = ctx_sat_app(&mut f, g);

    let want = {
        let sat_const = f.kernel.const_(semantics.sat, vec![]);
        let head = apply_all(&mut f.kernel, sat_const, &[nat_ty, structure, atom, v]);
        let true_ = f.kernel.const_(logic.true_, vec![]);
        let and_const = f.kernel.const_(logic.and, vec![]);
        apply_all(&mut f.kernel, and_const, &[head, true_])
    };
    f.assert_eq_expr(got, want, "ctxSat (cons a nil) must be And (sat a v) True");
}

/// The three example derivations are present and axiom-free. The
/// `Environment::contains` half is load-bearing: `axiom_footprint` of an
/// undeclared name is also empty.
#[test]
fn the_example_derivations_are_axiom_free() {
    let mut f = Fixture::new();
    for (name, label) in [
        (f.p.provable_imp_self, "FO.provable_imp_self"),
        (f.p.provable_all_imp_self, "FO.provable_all_imp_self"),
        (f.p.provable_all_imp_ex, "FO.provable_all_imp_ex"),
    ] {
        assert!(
            f.kernel.environment().contains(name),
            "{label} must be in the environment before its footprint means anything"
        );
        let footprint = f.kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} must be axiom-free; it depends on {footprint:?}"
        );
    }
}

/// `FO.provable_all_imp_ex`'s stated type really is
/// `Provable nil (imp (all (rel1 0 (var 0))) (ex (rel1 0 (var 0))))` —
/// rebuilt here from the constructors rather than read off the declaration, so
/// a derivation that landed at some other (also-derivable) statement fails.
#[test]
fn the_first_order_derivation_has_the_statement_it_claims() {
    let mut f = Fixture::new();
    let syn = f.syn();
    let c = f.calc();

    let p = {
        let zero = f.kernel.const_(syn.nat_zero, vec![]);
        let var = f.kernel.const_(syn.var, vec![]);
        let v0 = f.kernel.app(var, zero);
        let zero2 = f.kernel.const_(syn.nat_zero, vec![]);
        let rel1 = f.kernel.const_(syn.rel1, vec![]);
        apply_all(&mut f.kernel, rel1, &[zero2, v0])
    };
    let universal = {
        let head = f.kernel.const_(c.all, vec![]);
        f.kernel.app(head, p)
    };
    let existential = {
        let head = f.kernel.const_(c.ex, vec![]);
        f.kernel.app(head, p)
    };
    let implication = {
        let head = f.kernel.const_(c.imp, vec![]);
        apply_all(&mut f.kernel, head, &[universal, existential])
    };
    let nil = f.nil();
    let want = provable_app(&mut f.kernel, &c, nil, implication);

    let decl_const = f.kernel.const_(f.p.provable_all_imp_ex, vec![]);
    let got = f.kernel.infer(decl_const).expect("must infer");
    f.assert_eq_expr(got, want, "FO.provable_all_imp_ex's statement");
}

/// The `∀`-introduction rule's premise is over the SHIFTED context, and that is
/// checked structurally rather than trusted: `all_intro`'s inferred type must
/// equal the rule as documented, and must NOT equal the rule with the shift
/// removed.
///
/// This is the guard the first mutation in this lane's table targets — an
/// `all_intro` whose premise reads `Provable g p` instead of
/// `Provable (Context.shift g) p` is unsound (it derives `∀y. p(y)` from
/// `p(x)`), and it is exactly the edit this test is built to kill.
#[test]
fn all_intro_quantifies_over_the_shifted_context() {
    let mut f = Fixture::new();
    let c = f.calc();

    let all_intro = f.kernel.const_(f.p.rules[rule::ALL_INTRO], vec![]);
    let got = f.kernel.infer(all_intro).expect("must infer");

    let g_id = 1_637_910_u64;
    let p_id = 1_637_911_u64;
    let g = f.kernel.fvar(g_id);
    let p = f.kernel.fvar(p_id);

    let build = |f: &mut Fixture, shifted_premise: bool| -> ExprId {
        let premise_ctx = if shifted_premise {
            ctx_shift_app(&mut f.kernel, &c, g)
        } else {
            g
        };
        let hyp = provable_app(&mut f.kernel, &c, premise_ctx, p);
        let quantified = {
            let head = f.kernel.const_(c.all, vec![]);
            f.kernel.app(head, p)
        };
        let concl = provable_app(&mut f.kernel, &c, g, quantified);
        let body = arrow(&mut f.kernel, hyp, concl);
        pis(
            &mut f.kernel,
            &[(g_id, c.context_ty), (p_id, c.formula_ty)],
            body,
        )
    };

    let want = build(&mut f, true);
    f.assert_eq_expr(got, want, "all_intro's type");

    let unsound = build(&mut f, false);
    f.assert_ne_expr(
        got,
        unsound,
        "all_intro's premise must NOT be over the unshifted context",
    );
}

/// The same structural guard on `ex_elim`: its minor premise must shift BOTH
/// the context and the conclusion. Each half is checked against the variant
/// with that half removed.
#[test]
fn ex_elim_shifts_both_the_context_and_the_conclusion() {
    let mut f = Fixture::new();
    let c = f.calc();

    let ex_elim = f.kernel.const_(f.p.rules[rule::EX_ELIM], vec![]);
    let got = f.kernel.infer(ex_elim).expect("must infer");

    let g_id = 1_637_920_u64;
    let p_id = 1_637_921_u64;
    let q_id = 1_637_922_u64;
    let g = f.kernel.fvar(g_id);
    let p = f.kernel.fvar(p_id);
    let q = f.kernel.fvar(q_id);

    let build = |f: &mut Fixture, shift_ctx: bool, shift_goal: bool| -> ExprId {
        let quantified = {
            let head = f.kernel.const_(c.ex, vec![]);
            f.kernel.app(head, p)
        };
        let h1 = provable_app(&mut f.kernel, &c, g, quantified);
        let ctx_inner = if shift_ctx {
            ctx_shift_app(&mut f.kernel, &c, g)
        } else {
            g
        };
        let extended = cons_app(&mut f.kernel, &c, p, ctx_inner);
        let goal = if shift_goal {
            f_shift_app(&mut f.kernel, &c, q)
        } else {
            q
        };
        let h2 = provable_app(&mut f.kernel, &c, extended, goal);
        let concl = provable_app(&mut f.kernel, &c, g, q);
        let inner = arrow(&mut f.kernel, h2, concl);
        let body = arrow(&mut f.kernel, h1, inner);
        pis(
            &mut f.kernel,
            &[
                (g_id, c.context_ty),
                (p_id, c.formula_ty),
                (q_id, c.formula_ty),
            ],
            body,
        )
    };

    let want = build(&mut f, true, true);
    f.assert_eq_expr(got, want, "ex_elim's type");

    let no_ctx_shift = build(&mut f, false, true);
    f.assert_ne_expr(got, no_ctx_shift, "ex_elim must shift its minor's context");

    let no_goal_shift = build(&mut f, true, false);
    f.assert_ne_expr(got, no_goal_shift, "ex_elim must shift its minor's goal");
}
