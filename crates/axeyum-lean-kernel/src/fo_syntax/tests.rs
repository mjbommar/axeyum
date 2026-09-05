//! Evaluation tests for `fo_syntax.rs`'s definitions.
//!
//! Every declaration in the parent module is a `Definition`, so the kernel
//! admitting it proves only that it is well-formed — a substitution that
//! ignored its argument, or one that forgot to `lift` under a binder, would
//! type-check identically. Each test below therefore hand-computes the
//! expected value first (in the doc comment) and then asserts it by
//! `Kernel::def_eq`, at small, discriminating arguments.

use super::*;
use crate::Kernel;

/// A test-local mirror of the parent module's fvar-id discipline: the ids here
/// are only ever live inside one expression build, so a single high block is
/// enough.
const TEST_FV: u64 = 1_636_900_u64;

struct Fixture {
    kernel: Kernel,
    p: FoSyntaxPrelude,
}

impl Fixture {
    fn new() -> Self {
        let mut kernel = Kernel::new();
        let p = build_fo_syntax_prelude(&mut kernel).expect("FO syntax prelude must build");
        Self { kernel, p }
    }

    fn syn(&mut self) -> SyntaxNames {
        let p = self.p;
        p.names(&mut self.kernel)
    }

    /// The unary numeral `Nat.succ^n Nat.zero`. Kept tiny — this file never
    /// needs more than `6`.
    fn num(&mut self, n: u32) -> ExprId {
        let mut e = self.kernel.const_(self.p.nat.zero, vec![]);
        let succ = self.kernel.const_(self.p.nat.succ, vec![]);
        for _ in 0..n {
            e = self.kernel.app(succ, e);
        }
        e
    }

    fn var(&mut self, i: u32) -> ExprId {
        let idx = self.num(i);
        let c = self.kernel.const_(self.p.var, vec![]);
        self.kernel.app(c, idx)
    }

    fn f0(&mut self, k: u32) -> ExprId {
        let idx = self.num(k);
        let c = self.kernel.const_(self.p.f0, vec![]);
        self.kernel.app(c, idx)
    }

    fn f1(&mut self, k: u32, t: ExprId) -> ExprId {
        let idx = self.num(k);
        let c = self.kernel.const_(self.p.f1, vec![]);
        apply_all(&mut self.kernel, c, &[idx, t])
    }

    fn f2(&mut self, k: u32, a: ExprId, b: ExprId) -> ExprId {
        let idx = self.num(k);
        let c = self.kernel.const_(self.p.f2, vec![]);
        apply_all(&mut self.kernel, c, &[idx, a, b])
    }

    fn rel1(&mut self, k: u32, t: ExprId) -> ExprId {
        let idx = self.num(k);
        let c = self.kernel.const_(self.p.rel1, vec![]);
        apply_all(&mut self.kernel, c, &[idx, t])
    }

    fn rel2(&mut self, k: u32, a: ExprId, b: ExprId) -> ExprId {
        let idx = self.num(k);
        let c = self.kernel.const_(self.p.rel2, vec![]);
        apply_all(&mut self.kernel, c, &[idx, a, b])
    }

    fn eqf(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.eqf, vec![]);
        apply_all(&mut self.kernel, c, &[a, b])
    }

    fn all(&mut self, body: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.all, vec![]);
        self.kernel.app(c, body)
    }

    fn ex(&mut self, body: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.ex, vec![]);
        self.kernel.app(c, body)
    }

    fn imp(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.imp, vec![]);
        apply_all(&mut self.kernel, c, &[a, b])
    }

    fn subst_id(&mut self) -> ExprId {
        self.kernel.const_(self.p.subst_id, vec![])
    }

    fn subst_shift(&mut self) -> ExprId {
        self.kernel.const_(self.p.subst_shift, vec![])
    }

    /// `FO.Subst.cons t s`.
    fn subst_cons(&mut self, t: ExprId, s: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.subst_cons, vec![]);
        apply_all(&mut self.kernel, c, &[t, s])
    }

    /// `FO.Term.subst t s`.
    fn tsubst(&mut self, t: ExprId, s: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.term_subst, vec![]);
        apply_all(&mut self.kernel, c, &[t, s])
    }

    /// `FO.Formula.subst p s`.
    fn fsubst(&mut self, f: ExprId, s: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.formula_subst, vec![]);
        apply_all(&mut self.kernel, c, &[f, s])
    }

    /// `FO.Term.shift t`.
    fn tshift(&mut self, t: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.term_shift, vec![]);
        self.kernel.app(c, t)
    }

    /// `FO.Formula.shift p`.
    fn fshift(&mut self, f: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.formula_shift, vec![]);
        self.kernel.app(c, f)
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

/// Every declared name is actually in the environment. A missing name and a
/// name whose declaration failed to admit are indistinguishable downstream, so
/// this is the positive control the rest of the file rests on.
#[test]
fn fo_syntax_prelude_declares_every_name() {
    let f = Fixture::new();
    let p = f.p;
    let env = f.kernel.environment();
    for (name, label) in [
        (p.term, "FO.Term"),
        (p.var, "FO.Term.var"),
        (p.f0, "FO.Term.f0"),
        (p.f1, "FO.Term.f1"),
        (p.f2, "FO.Term.f2"),
        (p.term_rec, "FO.Term.rec"),
        (p.formula, "FO.Formula"),
        (p.bot, "FO.Formula.bot"),
        (p.eqf, "FO.Formula.eqf"),
        (p.rel1, "FO.Formula.rel1"),
        (p.rel2, "FO.Formula.rel2"),
        (p.and_, "FO.Formula.and_"),
        (p.or_, "FO.Formula.or_"),
        (p.imp, "FO.Formula.imp"),
        (p.all, "FO.Formula.all"),
        (p.ex, "FO.Formula.ex"),
        (p.formula_rec, "FO.Formula.rec"),
        (p.term_subst, "FO.Term.subst"),
        (p.subst_id, "FO.Subst.id"),
        (p.subst_shift, "FO.Subst.shift"),
        (p.term_shift, "FO.Term.shift"),
        (p.subst_cons, "FO.Subst.cons"),
        (p.subst_lift, "FO.Subst.lift"),
        (p.formula_subst, "FO.Formula.subst"),
        (p.formula_shift, "FO.Formula.shift"),
    ] {
        assert!(env.get(name).is_some(), "{label} must be declared");
    }
}

/// `FO.Term.subst` and `FO.Formula.subst` have the types the module docs
/// claim, checked by inference against a separately rebuilt expected type
/// rather than assumed from how they were constructed.
#[test]
fn substitution_definitions_have_their_stated_types() {
    let mut f = Fixture::new();
    let syn = f.syn();

    let sub_ty = subst_ty(&mut f.kernel, &syn);

    let term_subst_const = f.kernel.const_(f.p.term_subst, vec![]);
    let inferred = f.kernel.infer(term_subst_const).expect("must infer");
    let cod = arrow(&mut f.kernel, sub_ty, syn.term_ty);
    let expected = arrow(&mut f.kernel, syn.term_ty, cod);
    f.assert_eq_expr(inferred, expected, "FO.Term.subst type");

    let formula_subst_const = f.kernel.const_(f.p.formula_subst, vec![]);
    let inferred = f.kernel.infer(formula_subst_const).expect("must infer");
    let cod = arrow(&mut f.kernel, sub_ty, syn.formula_ty);
    let expected = arrow(&mut f.kernel, syn.formula_ty, cod);
    f.assert_eq_expr(inferred, expected, "FO.Formula.subst type");
}

/// `FO.Subst.cons t s` computes: `0 ↦ t`, `succ k ↦ s k`. Hand-computed
/// against the `Nat.rec` in the definition:
/// - `cons (f0 7) id Nat.zero      = f0 7`
/// - `cons (f0 7) id (Nat.succ 2)  = id 2 = var 2`
///
/// Both halves are needed: a `cons` that returned its head unconditionally
/// would pass the first and fail the second, and one that ignored its head
/// would pass the second and fail the first.
#[test]
fn subst_cons_computes_at_zero_and_at_a_successor() {
    let mut f = Fixture::new();
    let head = f.f0(7);
    let id = f.subst_id();
    let s = f.subst_cons(head, id);

    let zero = f.num(0);
    let at_zero = f.kernel.app(s, zero);
    f.assert_eq_expr(at_zero, head, "cons t s 0 must be t");

    let three = f.num(3);
    let at_three = f.kernel.app(s, three);
    let want = f.var(3);
    f.assert_eq_expr(at_three, want, "cons t s (succ k) must be s k");
}

/// `FO.Term.subst` consults the substitution **only** at `var`, and rebuilds
/// every other constructor while pushing it inward. Hand-computed with
/// `s := cons (f0 7) id`:
/// - `(var 0)[s]         = f0 7`            — the head is used
/// - `(var 3)[s]         = var 2`           — the tail is used, shifted down
/// - `(f0 3)[s]          = f0 3`            — a constant symbol is untouched
/// - `(f1 1 (var 0))[s]  = f1 1 (f0 7)`     — pushed under a unary symbol
/// - `(f2 2 (var 0) (var 3))[s] = f2 2 (f0 7) (var 2)`
///
/// The last case is the discriminating one: the two arguments get *different*
/// answers, so a minor premise that applied one induction hypothesis twice
/// fails loudly.
#[test]
fn term_subst_reaches_variables_and_rebuilds_symbols() {
    let mut f = Fixture::new();
    let head = f.f0(7);
    let id = f.subst_id();
    let s = f.subst_cons(head, id);

    let v0 = f.var(0);
    let got = f.tsubst(v0, s);
    f.assert_eq_expr(got, head, "(var 0)[cons (f0 7) id]");

    let v3 = f.var(3);
    let got = f.tsubst(v3, s);
    let want = f.var(2);
    f.assert_eq_expr(got, want, "(var 3)[cons (f0 7) id]");

    let c3 = f.f0(3);
    let got = f.tsubst(c3, s);
    let want = f.f0(3);
    f.assert_eq_expr(got, want, "(f0 3)[s] must be f0 3");

    let v0 = f.var(0);
    let unary = f.f1(1, v0);
    let got = f.tsubst(unary, s);
    let head2 = f.f0(7);
    let want = f.f1(1, head2);
    f.assert_eq_expr(got, want, "(f1 1 (var 0))[s]");

    let v0 = f.var(0);
    let v3 = f.var(3);
    let binary = f.f2(2, v0, v3);
    let got = f.tsubst(binary, s);
    let head3 = f.f0(7);
    let v2 = f.var(2);
    let want = f.f2(2, head3, v2);
    f.assert_eq_expr(got, want, "(f2 2 (var 0) (var 3))[s]");
}

/// `FO.Term.shift` raises every free index by one and leaves symbols alone:
/// `shift (f2 0 (var 0) (f1 1 (var 4))) = f2 0 (var 1) (f1 1 (var 5))`.
#[test]
fn term_shift_raises_every_index_by_one() {
    let mut f = Fixture::new();
    let v0 = f.var(0);
    let v4 = f.var(4);
    let inner = f.f1(1, v4);
    let t = f.f2(0, v0, inner);
    let got = f.tshift(t);

    let v1 = f.var(1);
    let v5 = f.var(5);
    let inner = f.f1(1, v5);
    let want = f.f2(0, v1, inner);
    f.assert_eq_expr(got, want, "FO.Term.shift");
}

/// **The capture-avoidance test, and the one a missing `FO.Subst.lift` fails.**
///
/// With `s := cons (var 5) id`, hand-computed:
///
/// ```text
/// (all (rel1 0 (var 1)))[s]
///   = all ((rel1 0 (var 1))[lift s])          -- the binder case lifts
///   = all (rel1 0 (lift s 1))
///   = all (rel1 0 (shiftTerm (s 0)))          -- lift s (succ k) = shift (s k)
///   = all (rel1 0 (shiftTerm (var 5)))
///   = all (rel1 0 (var 6))
/// ```
///
/// A binder case that passed `s` straight through would produce
/// `all (rel1 0 (var 5))` — the substituted term captured by the new binder —
/// and a `lift` that forgot to shift would produce `all (rel1 0 (var 5))` too.
/// Both are checked against here.
#[test]
fn formula_subst_lifts_under_a_binder() {
    let mut f = Fixture::new();
    let v5 = f.var(5);
    let id = f.subst_id();
    let s = f.subst_cons(v5, id);

    let v1 = f.var(1);
    let body = f.rel1(0, v1);
    let quantified = f.all(body);
    let got = f.fsubst(quantified, s);

    let v6 = f.var(6);
    let body = f.rel1(0, v6);
    let want = f.all(body);
    f.assert_eq_expr(got, want, "(all (rel1 0 (var 1)))[cons (var 5) id]");

    // The un-lifted answer, which a `lift`-free binder case would produce.
    let v5b = f.var(5);
    let body = f.rel1(0, v5b);
    let captured = f.all(body);
    f.assert_ne_expr(
        got,
        captured,
        "the substituted term must not be captured by the `all` binder",
    );
}

/// The bound index itself is left alone: `(all (rel1 0 (var 0)))[s] =
/// all (rel1 0 (var 0))` for any `s`, because `lift s 0 = var 0`. This is the
/// other half of capture avoidance, and the half a `lift` defined as
/// `cons (s 0) …` instead of `cons (var 0) …` would break.
#[test]
fn formula_subst_leaves_the_bound_index_alone() {
    let mut f = Fixture::new();
    let v5 = f.var(5);
    let id = f.subst_id();
    let s = f.subst_cons(v5, id);

    let v0 = f.var(0);
    let body = f.rel1(0, v0);
    let quantified = f.all(body);
    let got = f.fsubst(quantified, s);

    let v0 = f.var(0);
    let body = f.rel1(0, v0);
    let want = f.all(body);
    f.assert_eq_expr(got, want, "the bound index 0 must survive substitution");
}

/// `all` and `ex` are not interchangeable, and `FO.Formula.subst` keeps them
/// apart. The same body under the two quantifiers substitutes to two terms
/// that are **not** definitionally equal — the check a copy-paste between the
/// two quantifier minors would fail.
#[test]
fn formula_subst_keeps_all_and_ex_apart() {
    let mut f = Fixture::new();
    let v5 = f.var(5);
    let id = f.subst_id();
    let s = f.subst_cons(v5, id);

    let v1 = f.var(1);
    let body = f.rel1(0, v1);
    let universal = f.all(body);
    let v1 = f.var(1);
    let body = f.rel1(0, v1);
    let existential = f.ex(body);

    let got_all = f.fsubst(universal, s);
    let got_ex = f.fsubst(existential, s);
    f.assert_ne_expr(got_all, got_ex, "all and ex must substitute differently");

    // …and each still lands on its own quantifier.
    let v6 = f.var(6);
    let body = f.rel1(0, v6);
    let want_ex = f.ex(body);
    f.assert_eq_expr(got_ex, want_ex, "(ex (rel1 0 (var 1)))[cons (var 5) id]");
}

/// Substitution pushes through the propositional connectives and the two
/// atomic forms unchanged, with the relation/function symbol indices
/// preserved. Hand-computed with `s := cons (f0 7) id`:
/// `(imp (eqf (var 0) (var 3)) (rel2 4 (var 0) (f0 1)))[s]
///    = imp (eqf (f0 7) (var 2)) (rel2 4 (f0 7) (f0 1))`.
#[test]
fn formula_subst_pushes_through_connectives_and_atoms() {
    let mut f = Fixture::new();
    let head = f.f0(7);
    let id = f.subst_id();
    let s = f.subst_cons(head, id);

    let v0 = f.var(0);
    let v3 = f.var(3);
    let atom_eq = f.eqf(v0, v3);
    let v0 = f.var(0);
    let c1 = f.f0(1);
    let atom_rel = f.rel2(4, v0, c1);
    let phi = f.imp(atom_eq, atom_rel);
    let got = f.fsubst(phi, s);

    let h1 = f.f0(7);
    let v2 = f.var(2);
    let atom_eq = f.eqf(h1, v2);
    let h2 = f.f0(7);
    let c1 = f.f0(1);
    let atom_rel = f.rel2(4, h2, c1);
    let want = f.imp(atom_eq, atom_rel);
    f.assert_eq_expr(got, want, "substitution through imp/eqf/rel2");
}

/// `FO.Formula.shift` raises the free indices of a formula but stops at a
/// binder: `shift (and-free) …` is checked on a quantified formula, where the
/// bound index must survive and the free one must move.
///
/// Hand-computed: `shiftF (all (rel2 0 (var 0) (var 1)))`
/// `= all ((rel2 0 (var 0) (var 1))[lift Subst.shift])`
/// `= all (rel2 0 (lift shift 0) (lift shift 1))`
/// `= all (rel2 0 (var 0) (shiftTerm (shift 0)))`
/// `= all (rel2 0 (var 0) (shiftTerm (var 1)))`
/// `= all (rel2 0 (var 0) (var 2))`.
#[test]
fn formula_shift_moves_free_indices_but_not_bound_ones() {
    let mut f = Fixture::new();
    let v0 = f.var(0);
    let v1 = f.var(1);
    let body = f.rel2(0, v0, v1);
    let phi = f.all(body);
    let got = f.fshift(phi);

    let v0 = f.var(0);
    let v2 = f.var(2);
    let body = f.rel2(0, v0, v2);
    let want = f.all(body);
    f.assert_eq_expr(got, want, "FO.Formula.shift under a binder");
}

/// `FO.Subst.id` really is the identity on a formula with a binder in it —
/// the composite check that `lift Subst.id` behaves as `Subst.id` at every
/// index. Hand-computed: `lift id 0 = var 0`, `lift id (succ k) =
/// shiftTerm (id k) = shiftTerm (var k) = var (succ k)`, so
/// `(all (rel2 0 (var 0) (var 1)))[id] = all (rel2 0 (var 0) (var 1))`.
#[test]
fn identity_substitution_is_the_identity_under_a_binder() {
    let mut f = Fixture::new();
    let v0 = f.var(0);
    let v1 = f.var(1);
    let body = f.rel2(0, v0, v1);
    let phi = f.all(body);
    let id = f.subst_id();
    let got = f.fsubst(phi, id);

    let v0 = f.var(0);
    let v1 = f.var(1);
    let body = f.rel2(0, v0, v1);
    let want = f.all(body);
    f.assert_eq_expr(got, want, "identity substitution under a binder");
}

/// A negative control of the same kind as the positives above: `FO.Subst.shift`
/// is *not* the identity, so the previous test is not passing because
/// `Formula.subst` ignores its substitution argument. Same formula, same
/// route, different substitution, different answer.
#[test]
fn shift_substitution_is_not_the_identity() {
    let mut f = Fixture::new();
    let v0 = f.var(0);
    let v1 = f.var(1);
    let body = f.rel2(0, v0, v1);
    let phi = f.all(body);
    let sh = f.subst_shift();
    let got = f.fsubst(phi, sh);

    let v0 = f.var(0);
    let v1 = f.var(1);
    let body = f.rel2(0, v0, v1);
    let unchanged = f.all(body);
    f.assert_ne_expr(got, unchanged, "Subst.shift must change the formula");
}

/// The fvar-id block this test module reserves is distinct from the parent
/// module's, which is what keeps a test-built expression from colliding with
/// a definition-built one inside the same kernel.
#[test]
fn test_fvar_block_is_disjoint_from_the_definition_block() {
    assert!(TEST_FV > 1_636_500_u64);
}
