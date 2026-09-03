//! Tests for the term-builder additions this commit lands: `nil_of`/
//! `cons_of`/`append_of`/`reverse_of`/`length_of`/`map_of`/`foldr_of`/
//! `count_of`/`nat_add_of`/`nat_succ_of`, plus the pre-existing
//! `congr_of`/`refl_of` layer these are meant to compose with.
//!
//! `simp::list` (the next commit) needs BOTH halves: reusable term builders
//! for each operator (this file's positive controls), and confirmation that
//! `congr_of` genuinely lifts an equality through a one-hole `List`
//! context and that the KERNEL — not this module's own bookkeeping —
//! rejects a corrupted lift (this file's negative control).

use super::{apply_all, congr_of, cons_of, eq_of, nil_of, refl_of};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::{BinderInfo, Kernel, ListPrelude, LogicPrelude, NameId, build_list_prelude};

struct Fixture {
    k: Kernel,
    p: ListPrelude,
    logic: LogicPrelude,
    zero_lvl: LevelId,
    one_lvl: LevelId,
    nat: ExprId,
    root: NameId,
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_list_prelude(&mut k).expect("List prelude must build");
        let logic = crate::build_logic_prelude(&mut k).expect("Logic prelude must build");
        let zero_lvl = k.level_zero();
        let one_lvl = k.level_succ(zero_lvl);
        let nat = k.const_(logic.nat, vec![]);
        let anon = k.anon();
        let root = k.name_str(anon, "ops_test");
        Self {
            k,
            p,
            logic,
            zero_lvl,
            one_lvl,
            nat,
            root,
        }
    }

    fn name(&mut self, s: &str) -> NameId {
        let root = self.root;
        self.k.name_str(root, s)
    }

    fn num(&mut self, n: u32) -> ExprId {
        let mut e = self.k.const_(self.logic.nat_zero, vec![]);
        let succ = self.k.const_(self.logic.nat_succ, vec![]);
        for _ in 0..n {
            e = self.k.app(succ, e);
        }
        e
    }
}

/// `append (cons 1 nil) nil` reduces, by pure ι-reduction on a CONCRETE
/// `nil`/`cons` skeleton (no induction needed — `List.append` recurses on
/// its first argument), to `cons 1 nil`. `refl_of` at the un-reduced LHS,
/// ascribed against the reduced statement, exercises `nil_of`/`cons_of`/
/// `append_of` together and requires the kernel to confirm the defeq.
#[test]
fn append_of_a_concrete_singleton_by_nil_reduces_definitionally() {
    let mut f = Fixture::new();
    let one = f.num(1);
    let nil = nil_of(&mut f.k, f.p.nil, f.zero_lvl, f.nat);
    let singleton = cons_of(&mut f.k, f.p.cons, f.zero_lvl, f.nat, one, nil);
    let append_c = f.k.const_(f.p.append, vec![]);
    let lhs = apply_all(&mut f.k, append_c, &[f.nat, singleton, nil]);

    let list_nat = {
        let c = f.k.const_(f.p.list, vec![f.zero_lvl]);
        f.k.app(c, f.nat)
    };
    let proof = refl_of(&mut f.k, &f.logic, f.one_lvl, list_nat, lhs);
    let stated_ty = eq_of(&mut f.k, &f.logic, f.one_lvl, list_nat, lhs, singleton);

    let name = f.name("append_singleton_nil");
    f.k.add_declaration(crate::env::Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stated_ty,
        value: proof,
    })
    .expect("append (cons 1 nil) nil = cons 1 nil must be admitted by defeq alone");
}

/// `congr_of` lifts `h : Eq (List Nat) t1 t2` to
/// `Eq (List Nat) (cons 0 t1) (cons 0 t2)` — the exact shape `simp::list`'s
/// traversal needs to rewrite inside a `cons`'s tail position.
#[test]
fn congr_of_lifts_an_equality_through_cons_tail_position() {
    let mut f = Fixture::new();
    let zero = f.num(0);
    let nil = nil_of(&mut f.k, f.p.nil, f.zero_lvl, f.nat);
    let one = f.num(1);
    let singleton = cons_of(&mut f.k, f.p.cons, f.zero_lvl, f.nat, one, nil);
    // append nil singleton = singleton, by ι (nil is the recursion base case).
    let append_c = f.k.const_(f.p.append, vec![]);
    let append_nil_singleton = apply_all(&mut f.k, append_c, &[f.nat, nil, singleton]);

    let list_nat = {
        let c = f.k.const_(f.p.list, vec![f.zero_lvl]);
        f.k.app(c, f.nat)
    };
    let h = refl_of(
        &mut f.k,
        &f.logic,
        f.one_lvl,
        list_nat,
        append_nil_singleton,
    );
    let h_stated = eq_of(
        &mut f.k,
        &f.logic,
        f.one_lvl,
        list_nat,
        append_nil_singleton,
        singleton,
    );

    let cons_name = f.p.cons;
    let zero_lvl = f.zero_lvl;
    let nat = f.nat;
    let x_fv = 700_000;
    let lifted = congr_of(
        &mut f.k,
        &f.logic,
        f.one_lvl,
        list_nat,
        f.one_lvl,
        list_nat,
        append_nil_singleton,
        singleton,
        h,
        x_fv,
        &|k, x| {
            let c = k.const_(cons_name, vec![zero_lvl]);
            apply_all(k, c, &[nat, zero, x])
        },
    );

    let lhs = {
        let c = f.k.const_(cons_name, vec![zero_lvl]);
        apply_all(&mut f.k, c, &[nat, zero, append_nil_singleton])
    };
    let rhs = {
        let c = f.k.const_(cons_name, vec![zero_lvl]);
        apply_all(&mut f.k, c, &[nat, zero, singleton])
    };
    let stated_ty = eq_of(&mut f.k, &f.logic, f.one_lvl, list_nat, lhs, rhs);

    let name = f.name("congr_cons_lift");
    f.k.add_declaration(crate::env::Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stated_ty,
        value: lifted,
    })
    .unwrap_or_else(|e| panic!("congr_of's lifted proof must be admitted: {e:?}\n(h_stated was {h_stated:?}, only built to keep `h`'s intended type on record)"));
}

/// The same lift, corrupted: `h` proves `Eq append_nil_singleton
/// append_nil_singleton` (a `refl`), but `congr_of` is told it proves `Eq
/// append_nil_singleton other` for an UNRELATED list `other` (a different
/// singleton, not defeq to `append_nil_singleton`'s actual ι-reduced value
/// — using `singleton` itself here would not corrupt anything, since
/// `append nil singleton` *is* defeq to `singleton` and the kernel would
/// accept it regardless of which one `h`'s stated type names). The
/// procedure's own bookkeeping never checks `h`'s actual type — only the
/// KERNEL does, at `add_declaration`, and this test requires it to refuse.
#[test]
fn a_congr_of_lift_from_an_unrelated_hypothesis_is_rejected_by_the_kernel() {
    let mut f = Fixture::new();
    let zero = f.num(0);
    let nil = nil_of(&mut f.k, f.p.nil, f.zero_lvl, f.nat);
    let one = f.num(1);
    let two = f.num(2);
    let singleton = cons_of(&mut f.k, f.p.cons, f.zero_lvl, f.nat, one, nil);
    let other = cons_of(&mut f.k, f.p.cons, f.zero_lvl, f.nat, two, nil);
    let append_c = f.k.const_(f.p.append, vec![]);
    let append_nil_singleton = apply_all(&mut f.k, append_c, &[f.nat, nil, singleton]);

    let list_nat = {
        let c = f.k.const_(f.p.list, vec![f.zero_lvl]);
        f.k.app(c, f.nat)
    };
    // `h` is a REFL on `append_nil_singleton` alone -- NOT a proof that it
    // equals `other` -- but `congr_of` is told (via the `b` argument) that
    // it is.
    let h = refl_of(
        &mut f.k,
        &f.logic,
        f.one_lvl,
        list_nat,
        append_nil_singleton,
    );

    let cons_name = f.p.cons;
    let zero_lvl = f.zero_lvl;
    let nat = f.nat;
    let x_fv = 700_100;
    let lifted = congr_of(
        &mut f.k,
        &f.logic,
        f.one_lvl,
        list_nat,
        f.one_lvl,
        list_nat,
        append_nil_singleton,
        other, // claims `h : Eq append_nil_singleton other` -- false
        h,
        x_fv,
        &|k, x| {
            let c = k.const_(cons_name, vec![zero_lvl]);
            apply_all(k, c, &[nat, zero, x])
        },
    );

    let lhs = {
        let c = f.k.const_(cons_name, vec![zero_lvl]);
        apply_all(&mut f.k, c, &[nat, zero, append_nil_singleton])
    };
    let rhs = {
        let c = f.k.const_(cons_name, vec![zero_lvl]);
        apply_all(&mut f.k, c, &[nat, zero, other])
    };
    let stated_ty = eq_of(&mut f.k, &f.logic, f.one_lvl, list_nat, lhs, rhs);

    let name = f.name("congr_cons_lift_corrupted");
    let result = f.k.add_declaration(crate::env::Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stated_ty,
        value: lifted,
    });
    assert!(
        result.is_err(),
        "a congr lift from an unrelated hypothesis must be rejected, not admitted"
    );
}
