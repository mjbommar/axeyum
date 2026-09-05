//! Evaluation tests for `fo_semantics.rs`.
//!
//! `FO.Term.eval`, `FO.sat`, `FO.Val.cons`, the five `FO.Structure`
//! projections and `FO.natStructure` are all `Definition`s: the kernel
//! admitting them says nothing about what they compute. Each test below
//! hand-computes its expected value against the module's own clause table and
//! then asserts it by `Kernel::def_eq`, at small, discriminating arguments.
//!
//! The two `Theorem`s get the other treatment: `Environment::contains` first
//! (a missing name and an axiom-free one both report an empty footprint), then
//! `Kernel::axiom_footprint` asserted empty.

use super::*;
use crate::Kernel;

struct Fixture {
    kernel: Kernel,
    p: FoSemanticsPrelude,
}

impl Fixture {
    fn new() -> Self {
        let mut kernel = Kernel::new();
        let p = build_fo_semantics_prelude(&mut kernel).expect("FO semantics prelude must build");
        Self { kernel, p }
    }

    fn syn(&mut self) -> SyntaxNames {
        let syntax = self.p.syntax;
        syntax.names(&mut self.kernel)
    }

    fn nat_ty(&mut self) -> ExprId {
        self.kernel.const_(self.p.syntax.nat.nat, vec![])
    }

    fn num(&mut self, n: u32) -> ExprId {
        let mut e = self.kernel.const_(self.p.syntax.nat.zero, vec![]);
        let succ = self.kernel.const_(self.p.syntax.nat.succ, vec![]);
        for _ in 0..n {
            e = self.kernel.app(succ, e);
        }
        e
    }

    fn var(&mut self, i: u32) -> ExprId {
        let idx = self.num(i);
        let c = self.kernel.const_(self.p.syntax.var, vec![]);
        self.kernel.app(c, idx)
    }

    fn f0(&mut self, k: u32) -> ExprId {
        let idx = self.num(k);
        let c = self.kernel.const_(self.p.syntax.f0, vec![]);
        self.kernel.app(c, idx)
    }

    fn f1(&mut self, k: u32, t: ExprId) -> ExprId {
        let idx = self.num(k);
        let c = self.kernel.const_(self.p.syntax.f1, vec![]);
        apply_all(&mut self.kernel, c, &[idx, t])
    }

    fn f2(&mut self, k: u32, a: ExprId, b: ExprId) -> ExprId {
        let idx = self.num(k);
        let c = self.kernel.const_(self.p.syntax.f2, vec![]);
        apply_all(&mut self.kernel, c, &[idx, a, b])
    }

    fn rel2f(&mut self, k: u32, a: ExprId, b: ExprId) -> ExprId {
        let idx = self.num(k);
        let c = self.kernel.const_(self.p.syntax.rel2, vec![]);
        apply_all(&mut self.kernel, c, &[idx, a, b])
    }

    fn nat_structure(&mut self) -> ExprId {
        self.kernel.const_(self.p.nat_structure, vec![])
    }

    /// The identity valuation `fun n : Nat => n`.
    fn valuation_identity(&mut self) -> ExprId {
        let nat_ty = self.nat_ty();
        let id = 1_636_950_u64;
        let n = self.kernel.fvar(id);
        lam_fv(&mut self.kernel, id, nat_ty, n)
    }

    /// `FO.Term.eval Nat FO.natStructure t v`.
    fn eval(&mut self, t: ExprId, v: ExprId) -> ExprId {
        let nat_ty = self.nat_ty();
        let s = self.nat_structure();
        let c = self.kernel.const_(self.p.term_eval, vec![]);
        apply_all(&mut self.kernel, c, &[nat_ty, s, t, v])
    }

    /// `FO.sat Nat FO.natStructure phi v`.
    fn sat(&mut self, phi: ExprId, v: ExprId) -> ExprId {
        let nat_ty = self.nat_ty();
        let s = self.nat_structure();
        let c = self.kernel.const_(self.p.sat, vec![]);
        apply_all(&mut self.kernel, c, &[nat_ty, s, phi, v])
    }

    /// `Nat.add x y`.
    fn add(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.syntax.nat.add, vec![]);
        apply_all(&mut self.kernel, c, &[x, y])
    }

    /// `Nat.lt x y`.
    fn lt(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let c = self.kernel.const_(self.p.syntax.nat.lt, vec![]);
        apply_all(&mut self.kernel, c, &[x, y])
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

/// Every declared name is in the environment — the positive control the rest of
/// the file rests on.
#[test]
fn fo_semantics_prelude_declares_every_name() {
    let f = Fixture::new();
    let p = f.p;
    let env = f.kernel.environment();
    for (name, label) in [
        (p.structure, "FO.Structure"),
        (p.structure_mk, "FO.Structure.mk"),
        (p.structure_rec, "FO.Structure.rec"),
        (p.fn0, "FO.Structure.fn0"),
        (p.fn1, "FO.Structure.fn1"),
        (p.fn2, "FO.Structure.fn2"),
        (p.rel1, "FO.Structure.rel1"),
        (p.rel2, "FO.Structure.rel2"),
        (p.val_cons, "FO.Val.cons"),
        (p.term_eval, "FO.Term.eval"),
        (p.sat, "FO.sat"),
        (p.nat_structure, "FO.natStructure"),
        (p.nat_sat_lt_irrefl, "FO.nat_sat_lt_irrefl"),
        (p.nat_sat_no_greatest, "FO.nat_sat_no_greatest"),
    ] {
        assert!(env.get(name).is_some(), "{label} must be declared");
    }
}

/// `FO.Val.cons` computes: `0 ↦ a`, `succ k ↦ v k`. Hand-computed with
/// `a := 7` and `v := fun n => n`:
/// - `Val.cons Nat 7 v 0 = 7`
/// - `Val.cons Nat 7 v 3 = v 2 = 2`
///
/// Both halves are needed: a `cons` returning its head unconditionally passes
/// the first and fails the second.
#[test]
fn val_cons_computes_at_zero_and_at_a_successor() {
    let mut f = Fixture::new();
    let nat_ty = f.nat_ty();
    let seven = f.num(7);
    let v = f.valuation_identity();
    let c = f.kernel.const_(f.p.val_cons, vec![]);
    let extended = apply_all(&mut f.kernel, c, &[nat_ty, seven, v]);

    let zero = f.num(0);
    let at_zero = f.kernel.app(extended, zero);
    let want = f.num(7);
    f.assert_eq_expr(at_zero, want, "Val.cons a v 0 must be a");

    let three = f.num(3);
    let at_three = f.kernel.app(extended, three);
    let want = f.num(2);
    f.assert_eq_expr(at_three, want, "Val.cons a v (succ k) must be v k");
}

/// **The `funext`-free load-bearer, measured rather than asserted.** The module
/// docs claim `fun m => FO.Val.cons M a v (Nat.succ m)` is *definitionally*
/// the valuation `v` — ι-reduction under the binder plus the kernel's η rule.
/// Everything `fo_substitution.rs` saves rests on that claim, so it is checked
/// here directly, at a symbolic `a` and a symbolic `v` (free variables, not
/// literals — a check at a literal valuation would pass for the wrong reason).
#[test]
fn shifting_past_the_new_slot_is_definitionally_the_old_valuation() {
    let mut f = Fixture::new();
    let nat_ty = f.nat_ty();
    let val_ty = arrow(&mut f.kernel, nat_ty, nat_ty);

    let a_id = 1_636_960_u64;
    let v_id = 1_636_961_u64;
    let m_id = 1_636_962_u64;
    let a = f.kernel.fvar(a_id);
    let v = f.kernel.fvar(v_id);
    let m = f.kernel.fvar(m_id);

    let succ = f.kernel.const_(f.p.syntax.nat.succ, vec![]);
    let sm = f.kernel.app(succ, m);
    let c = f.kernel.const_(f.p.val_cons, vec![]);
    let body = apply_all(&mut f.kernel, c, &[nat_ty, a, v, sm]);
    let shifted = lam_fv(&mut f.kernel, m_id, nat_ty, body);

    let _ = val_ty;
    f.assert_eq_expr(
        shifted,
        v,
        "fun m => Val.cons a v (succ m) must be definitionally v",
    );
}

/// The five `FO.Structure` projections select the field they name, and they
/// select *different* fields. Hand-computed against `FO.natStructure`'s symbol
/// table:
/// - `fn0 3 = 3`
/// - `fn1 1 4 = Nat.add 4 1 = 5`
/// - `fn2 0 2 3 = Nat.add (Nat.add 2 3) 0 = 5`
/// - `fn2 1 2 3 = Nat.add (Nat.add 2 3) 1 = 6`  (index-dependent, so a `sat`
///   that dropped the symbol index would fail here)
#[test]
fn structure_projections_select_the_field_they_name() {
    let mut f = Fixture::new();
    let nat_ty = f.nat_ty();
    let s = f.nat_structure();

    let (fn0, fn1, fn2) = (f.p.fn0, f.p.fn1, f.p.fn2);
    let proj = |f: &mut Fixture, name: NameId, args: &[ExprId]| -> ExprId {
        let c = f.kernel.const_(name, vec![]);
        let head = apply_all(&mut f.kernel, c, &[nat_ty, s]);
        apply_all(&mut f.kernel, head, args)
    };

    let three = f.num(3);
    let got = proj(&mut f, fn0, &[three]);
    let want = f.num(3);
    f.assert_eq_expr(got, want, "fn0 3");

    let one = f.num(1);
    let four = f.num(4);
    let got = proj(&mut f, fn1, &[one, four]);
    let want = f.num(5);
    f.assert_eq_expr(got, want, "fn1 1 4");

    let zero = f.num(0);
    let two = f.num(2);
    let three = f.num(3);
    let got = proj(&mut f, fn2, &[zero, two, three]);
    let want = f.num(5);
    f.assert_eq_expr(got, want, "fn2 0 2 3");

    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);
    let got = proj(&mut f, fn2, &[one, two, three]);
    let want = f.num(6);
    f.assert_eq_expr(got, want, "fn2 1 2 3 -- the family is index-dependent");
}

/// `FO.Term.eval` at `FO.natStructure`. Hand-computed:
/// - `eval (f0 0) v = 0`                      — the constant symbol `0`
/// - `eval (f1 1 (f0 0)) v = Nat.add 0 1 = 1` — `f1 1` is successor
/// - `eval (f2 0 (f0 2) (f0 3)) v = 5`        — `f2 0` is `+`
/// - `eval (var 1) (fun n => n) = 1`          — the valuation is consulted
///
/// The last two together are discriminating: they are the same shape with a
/// different constructor, and they give different answers.
#[test]
fn term_eval_computes_in_the_nat_structure() {
    let mut f = Fixture::new();
    let v = f.valuation_identity();

    let t = f.f0(0);
    let got = f.eval(t, v);
    let want = f.num(0);
    f.assert_eq_expr(got, want, "eval (f0 0)");

    let inner = f.f0(0);
    let t = f.f1(1, inner);
    let got = f.eval(t, v);
    let want = f.num(1);
    f.assert_eq_expr(got, want, "eval (f1 1 (f0 0)) -- f1 1 is succ");

    let a = f.f0(2);
    let b = f.f0(3);
    let t = f.f2(0, a, b);
    let got = f.eval(t, v);
    let want = f.num(5);
    f.assert_eq_expr(got, want, "eval (f2 0 (f0 2) (f0 3)) -- f2 0 is +");

    let t = f.var(1);
    let got = f.eval(t, v);
    let want = f.num(1);
    f.assert_eq_expr(got, want, "eval (var 1) at the identity valuation");
}

/// `FO.Term.eval` really consumes its valuation: the SAME term `var 0` at two
/// different valuations gives two different answers. Without this, every test
/// above would pass for an `eval` that ignored `v` entirely.
#[test]
fn term_eval_consumes_its_valuation() {
    let mut f = Fixture::new();
    let nat_ty = f.nat_ty();

    let mk_const = |f: &mut Fixture, k: u32| -> ExprId {
        let id = 1_636_970_u64 + u64::from(k);
        let body = f.num(k);
        lam_fv(&mut f.kernel, id, nat_ty, body)
    };

    let t = f.var(0);
    let v = mk_const(&mut f, 0);
    let got = f.eval(t, v);
    let want = f.num(0);
    f.assert_eq_expr(got, want, "eval (var 0) at (fun _ => 0)");

    let t = f.var(0);
    let v = mk_const(&mut f, 4);
    let got = f.eval(t, v);
    let want = f.num(4);
    f.assert_eq_expr(got, want, "eval (var 0) at (fun _ => 4)");
}

/// `FO.sat` of an atomic formula reduces to the structure's relation at the
/// evaluated arguments. Hand-computed: `sat (rel2 0 (f0 1) (f0 2)) v` is
/// `rel2 0 1 2 = Nat.lt (Nat.add 1 0) 2`, which is `Nat.lt 1 2` after ι on
/// `Nat.add _ Nat.zero`.
#[test]
fn sat_of_an_atom_is_the_structures_relation() {
    let mut f = Fixture::new();
    let v = f.valuation_identity();
    let a = f.f0(1);
    let b = f.f0(2);
    let phi = f.rel2f(0, a, b);
    let got = f.sat(phi, v);

    let one = f.num(1);
    let two = f.num(2);
    let want = f.lt(one, two);
    f.assert_eq_expr(got, want, "sat (rel2 0 (f0 1) (f0 2))");

    // The same atom at a different relation index is a different proposition,
    // which is what pins that `sat` passes the symbol index through.
    let a = f.f0(1);
    let b = f.f0(2);
    let phi = f.rel2f(1, a, b);
    let got_at_one = f.sat(phi, v);
    let one = f.num(1);
    let two = f.num(2);
    let want = f.lt(one, two);
    f.assert_ne_expr(got_at_one, want, "rel2 1 must not collapse to rel2 0");
}

/// **The valuation-plumbing test.** `sat` of the two-binder sentence
/// `all (ex (rel2 0 (var 1) (var 0)))` must reduce to
///
/// ```text
/// Π (x : Nat), Exists Nat (fun y => Nat.lt (Nat.add x 0) y)
/// ```
///
/// i.e. `∀ x ∃ y, x < y`. The de Bruijn reading is what is being checked: under
/// the two binders, index `1` is the `all`-bound `x` and index `0` is the
/// `ex`-bound `y`, so the atom's LEFT argument must be `x` and its RIGHT one
/// `y`. The swapped reading — `fun y => Nat.lt (Nat.add y 0) x`, which is what
/// an `ex` clause reading the wrong valuation slot produces — is asserted
/// *different*, so this test fails in both directions.
#[test]
fn sat_of_a_two_binder_sentence_reads_the_right_valuation_slots() {
    let mut f = Fixture::new();
    let nat_ty = f.nat_ty();
    let syn = f.syn();
    let sentence = nat_no_greatest_sentence(&mut f.kernel, &syn);
    let v = f.valuation_identity();
    let got = f.sat(sentence, v);

    let x_id = 1_636_980_u64;
    let y_id = 1_636_981_u64;
    let x = f.kernel.fvar(x_id);
    let y = f.kernel.fvar(y_id);

    let logic = f.p.syntax.nat.logic;
    let zero_lvl = f.kernel.level_zero();
    let one_lvl = f.kernel.level_succ(zero_lvl);

    // Π (x : Nat), Exists Nat (fun y => Nat.lt (Nat.add x 0) y)
    let want = {
        let zero = f.num(0);
        let x_plus_zero = f.add(x, zero);
        let atom = f.lt(x_plus_zero, y);
        let predicate = lam_fv(&mut f.kernel, y_id, nat_ty, atom);
        let exists_const = f.kernel.const_(logic.exists_, vec![one_lvl]);
        let body = apply_all(&mut f.kernel, exists_const, &[nat_ty, predicate]);
        pi_fv(&mut f.kernel, x_id, nat_ty, body)
    };
    f.assert_eq_expr(got, want, "sat of `all (ex (rel2 0 (var 1) (var 0)))`");

    // The swapped reading, which must NOT be what `sat` produces.
    let swapped = {
        let zero = f.num(0);
        let y_plus_zero = f.add(y, zero);
        let atom = f.lt(y_plus_zero, x);
        let predicate = lam_fv(&mut f.kernel, y_id, nat_ty, atom);
        let exists_const = f.kernel.const_(logic.exists_, vec![one_lvl]);
        let body = apply_all(&mut f.kernel, exists_const, &[nat_ty, predicate]);
        pi_fv(&mut f.kernel, x_id, nat_ty, body)
    };
    f.assert_ne_expr(
        got,
        swapped,
        "the two de Bruijn indices must not be read in the wrong order",
    );
}

/// `sat` of the `all` sentence reduces to a `Pi` over the carrier with the
/// valuation extended by the bound element. Hand-computed:
/// `sat (all (imp (rel2 0 (var 0) (var 0)) bot)) v`
/// `= Π (x : Nat), Nat.lt (Nat.add x 0) x -> False`.
#[test]
fn sat_of_the_irreflexivity_sentence_reduces_as_documented() {
    let mut f = Fixture::new();
    let nat_ty = f.nat_ty();
    let syn = f.syn();
    let sentence = nat_irrefl_sentence(&mut f.kernel, &syn);
    let v = f.valuation_identity();
    let got = f.sat(sentence, v);

    let x_id = 1_636_990_u64;
    let x = f.kernel.fvar(x_id);
    let logic = f.p.syntax.nat.logic;
    let want = {
        let zero = f.num(0);
        let x_plus_zero = f.add(x, zero);
        let atom = f.lt(x_plus_zero, x);
        let false_ = f.kernel.const_(logic.false_, vec![]);
        let body = arrow(&mut f.kernel, atom, false_);
        pi_fv(&mut f.kernel, x_id, nat_ty, body)
    };
    f.assert_eq_expr(got, want, "sat of `all (imp (rel2 0 (var 0) (var 0)) bot)`");
}

/// Both satisfaction theorems are present **and** axiom-free. The
/// `Environment::contains` half is not decoration: `axiom_footprint` of a name
/// that was never declared is also empty, so without it this test would pass
/// for a theorem that failed to admit.
#[test]
fn the_nat_satisfaction_theorems_are_axiom_free() {
    let f = Fixture::new();
    for (name, label) in [
        (f.p.nat_sat_lt_irrefl, "FO.nat_sat_lt_irrefl"),
        (f.p.nat_sat_no_greatest, "FO.nat_sat_no_greatest"),
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
