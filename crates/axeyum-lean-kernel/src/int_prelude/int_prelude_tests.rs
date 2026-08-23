//! Proof-term tests for the integer prelude (ADR-0042, the integer-arithmetic /
//! Diophantine reconstruction foundation).
//!
//! These tests build proof terms over the discretely-ordered commutative ring
//! `ℤ` — now *constructed* over the axiom-free `Nat` development — and
//! `infer`-check them. A test passes only if the trusted type-checker genuinely
//! accepts the proof. The headline test exercises the integer-specific
//! **discreteness** law: given `0 < x` and `x < 1`,
//! `no_int_between x (And.intro _ _ h0 h1) : False`.
//!
//! Three assertions carry the construction's weight, and each rules out a
//! different way it could be hollow:
//!
//! - [`the_operations_compute_their_normal_forms`] — the operations are the
//!   right ones. Type-checking `add_comm` does not pin `Int.add` down; a wrong
//!   `add` would satisfy a wrong-but-provable commutativity.
//! - [`derived_laws_have_no_axiom_footprint`] — the derived laws did not
//!   quietly reach for one of the laws still asserted. Only the footprint
//!   catches that; the proof would type-check either way.
//! - [`the_only_trusted_declarations_are_the_asserted_laws`] — nothing was
//!   admitted without a checked body behind the construction's back, including
//!   no `Quotient` primitive.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use crate::ExprId;
use crate::env::Declaration;
use crate::{IntPrelude, Kernel, build_int_prelude};

/// A fixture: a kernel with the integer prelude plus an abstract point `x : Z`;
/// hypotheses are added per-test.
struct Fixture {
    k: Kernel,
    p: IntPrelude,
    x: crate::NameId,
}

fn fixture() -> Fixture {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let anon = k.anon();
    // x : Z.
    let x = k.name_str(anon, "x");
    let z_ty = k.const_(p.z, vec![]);
    k.add_declaration(Declaration::Axiom {
        name: x,
        uparams: vec![],
        ty: z_ty,
    })
    .unwrap();
    Fixture { k, p, x }
}

impl Fixture {
    fn x_const(&mut self) -> crate::ExprId {
        self.k.const_(self.x, vec![])
    }
    /// `lt x y` as a Prop term.
    fn lt(&mut self, x: crate::ExprId, y: crate::ExprId) -> crate::ExprId {
        let ltc = self.k.const_(self.p.lt, vec![]);
        let e = self.k.app(ltc, x);
        self.k.app(e, y)
    }
    fn zero(&mut self) -> crate::ExprId {
        self.k.const_(self.p.zero, vec![])
    }
    fn one(&mut self) -> crate::ExprId {
        self.k.const_(self.p.one, vec![])
    }
    fn false_(&mut self) -> crate::ExprId {
        self.k.const_(self.p.logic.false_, vec![])
    }
    /// `And p q` as a Prop term (two explicit Prop arguments).
    fn and(&mut self, p: crate::ExprId, q: crate::ExprId) -> crate::ExprId {
        let andc = self.k.const_(self.p.logic.and, vec![]);
        let e = self.k.app(andc, p);
        self.k.app(e, q)
    }
    /// `Not r` as a Prop term.
    fn not(&mut self, r: crate::ExprId) -> crate::ExprId {
        let notc = self.k.const_(self.p.logic.not, vec![]);
        self.k.app(notc, r)
    }
    /// Declare a hypothesis axiom `name : ty` and return its const term.
    fn hyp(&mut self, name: &str, ty: crate::ExprId) -> (crate::NameId, crate::ExprId) {
        let anon = self.k.anon();
        let nm = self.k.name_str(anon, name);
        self.k
            .add_declaration(Declaration::Axiom {
                name: nm,
                uparams: vec![],
                ty,
            })
            .unwrap();
        let c = self.k.const_(nm, vec![]);
        (nm, c)
    }
}

/// The prelude admits: every axiom type-checked through the trusted gate and is
/// present in the environment as an `Axiom`. A green build of `build_int_prelude`
/// already *is* the well-formedness proof; this asserts the environment shape.
#[test]
fn int_prelude_admits_all_declarations() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    // The carrier is an inductive with two constructors and a recursor; the
    // operations are checked definitions. None of these is asserted.
    for name in [p.z, p.of_nat, p.neg_succ, p.rec] {
        assert!(
            k.environment().contains(name),
            "int prelude should declare {}",
            k.display_name(name)
        );
        assert!(
            !matches!(
                k.environment().get(name).unwrap(),
                Declaration::Axiom { .. }
            ),
            "{} must not be an Axiom — the carrier is constructed",
            k.display_name(name)
        );
    }
    for name in [
        p.add,
        p.mul,
        p.neg,
        p.zero,
        p.one,
        p.le,
        p.lt,
        p.neg_of_nat,
        p.sub_nat_nat,
        p.ediv,
        p.emod,
        p.dvd,
        p.mod_eq,
    ] {
        assert!(
            matches!(
                k.environment().get(name).unwrap(),
                Declaration::Definition { .. }
            ),
            "{} should be a checked Definition",
            k.display_name(name)
        );
    }
    for name in derived_laws(&p).into_iter().chain(derived_lemmas(&p)) {
        assert!(
            matches!(
                k.environment().get(name).unwrap(),
                Declaration::Theorem { .. }
            ),
            "{} should be a checked Theorem",
            k.display_name(name)
        );
    }
    for name in asserted_laws(&p) {
        assert!(
            matches!(
                k.environment().get(name).unwrap(),
                Declaration::Axiom { .. }
            ),
            "{} is not derived yet, so it should still be an Axiom",
            k.display_name(name)
        );
    }
    // The logical prelude is embedded and present.
    assert!(k.environment().contains(p.logic.false_));
    assert!(k.environment().contains(p.logic.not));
    assert!(k.environment().contains(p.logic.and));
    assert!(k.environment().contains(p.logic.and_intro));
}

/// The integer laws this development **derives** from the axiom-free `Nat`
/// prelude. Each must be a `Theorem` with an empty axiom footprint.
fn derived_laws(p: &IntPrelude) -> [crate::NameId; 51] {
    [
        p.euclidean_decomposition,
        p.of_nat_nat_abs_of_nonneg,
        p.euclid_of_nat,
        p.euclid_neg_succ,
        p.ediv_add_emod,
        p.emod_nonneg,
        p.emod_lt_of_pos,
        p.ediv_emod_unique,
        p.dvd_refl,
        p.dvd_trans,
        p.dvd_add,
        p.dvd_mul_right,
        p.dvd_mul_left,
        p.emod_eq_zero_iff_dvd,
        p.mod_eq_refl,
        p.mod_eq_symm,
        p.mod_eq_trans,
        p.mod_eq_iff_dvd,
        p.mod_eq_add_right,
        p.mod_eq_add_left,
        p.mul_neg,
        p.mul_sub,
        p.le_refl,
        p.le_trans,
        p.lt_irrefl,
        p.lt_trans,
        p.lt_of_lt_of_le,
        p.lt_of_le_of_lt,
        p.le_of_lt,
        p.le_total,
        p.zero_lt_one,
        p.no_int_between,
        p.lt_of_le_of_ne,
        p.add_zero,
        p.add_comm,
        p.add_assoc,
        p.add_neg,
        p.add_neg_cancel_right,
        p.add_le_add,
        p.add_lt_add_of_le_of_lt,
        p.mul_zero,
        p.mul_one,
        p.one_mul,
        p.neg_one_mul,
        p.mul_comm,
        p.mul_assoc,
        p.left_distrib,
        p.mul_nonneg,
        p.sq_nonneg,
        p.mul_le_mul_of_nonneg_left,
        p.eq_em,
    ]
}

/// The `subNatNat` borrow sub-development, and the sign/difference lemmas built
/// on it. These are not laws of `ℤ` a reader would quote, but they are the
/// working parts of five of the laws above, and a footprint that leaked into one
/// of them would leak into the law. They are checked to exactly the same
/// standard.
fn derived_lemmas(p: &IntPrelude) -> [crate::NameId; 26] {
    [
        p.sub_nat_nat_succ_succ,
        p.sub_nat_nat_add_add,
        p.sub_nat_nat_add_add_left,
        p.sub_nat_nat_zero,
        p.zero_sub_nat_nat,
        p.sub_nat_nat_add_left,
        p.sub_nat_nat_add_right,
        p.sub_nat_nat_elim,
        p.of_nat_add_sub_nat_nat,
        p.sub_nat_nat_add_of_nat,
        p.sub_nat_nat_add_neg_succ,
        p.neg_succ_add_sub_nat_nat,
        p.of_nat_add_neg_of_nat,
        p.neg_of_nat_add_of_nat,
        p.neg_of_nat_add_neg_of_nat,
        p.neg_of_nat_add_sub_nat_nat,
        p.mul_of_nat_neg_of_nat,
        p.mul_neg_of_nat_of_nat,
        p.mul_neg_succ_neg_of_nat,
        p.mul_neg_of_nat_neg_succ,
        p.of_nat_mul_sub_nat_nat,
        p.neg_succ_mul_sub_nat_nat,
        p.le_of_nat_add,
        p.le_dest,
        p.lt_of_nat_add,
        p.lt_dest,
    ]
}

/// The integer laws still **asserted**. This list was the lane's standing debt;
/// it is expected to shrink and must never grow.
///
/// It is now **empty**: `Int.euclidean_decomposition` was the last member, and
/// it is a theorem as of 2026-08-16. An entry reappearing here is a regression —
/// something previously proved has become an assumption.
fn asserted_laws(_p: &IntPrelude) -> [crate::NameId; 0] {
    []
}

/// Every derived law's trusted closure is **empty** — not merely "smaller".
/// A theorem that silently reached for one of the remaining assumptions would
/// still type-check; only the footprint catches it.
#[test]
fn derived_laws_have_no_axiom_footprint() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    for name in derived_laws(&p).into_iter().chain(derived_lemmas(&p)) {
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{} should rest on no axiom, but rests on {:?}",
            k.display_name(name),
            footprint
                .iter()
                .map(|a| k.display_name(*a).to_string())
                .collect::<Vec<_>>()
        );
    }
}

/// The environment carries exactly the asserted laws and nothing else that was
/// admitted without a proof: no axioms crept in, and no `Quotient` primitive
/// was admitted (the reason `Int` is a normalized inductive rather than a
/// setoid quotient of `ℕ × ℕ`).
#[test]
fn the_only_trusted_declarations_are_the_asserted_laws() {
    use std::collections::BTreeSet;
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let expected: BTreeSet<_> = asserted_laws(&p).into_iter().collect();
    let mut found = BTreeSet::new();
    for (_, declaration) in k.environment().iter() {
        match declaration {
            Declaration::Axiom { name, .. } => {
                found.insert(*name);
            }
            Declaration::Opaque { name, .. } | Declaration::Quotient { name, .. } => {
                panic!(
                    "{} was admitted without a checked proof body",
                    k.display_name(*name)
                );
            }
            _ => {}
        }
    }
    let unexpected: Vec<_> = found
        .difference(&expected)
        .map(|n| k.display_name(*n).to_string())
        .collect();
    assert!(unexpected.is_empty(), "unexpected axioms: {unexpected:?}");
    let missing: Vec<_> = expected
        .difference(&found)
        .map(|n| k.display_name(*n).to_string())
        .collect();
    assert!(missing.is_empty(), "asserted law not declared: {missing:?}");
}

/// Every axiom's *type* itself infers to a `Sort` — i.e. the whole axiom set is
/// well-formed (the trusted admission gate already enforced this, but we
/// re-check the types infer with no error).
#[test]
fn every_axiom_type_infers_to_a_sort() {
    use crate::expr::ExprNode;
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    for name in [
        p.le_refl,
        p.le_trans,
        p.lt_irrefl,
        p.lt_trans,
        p.lt_of_lt_of_le,
        p.lt_of_le_of_lt,
        p.le_of_lt,
        p.add_le_add,
        p.add_comm,
        p.add_assoc,
        p.add_zero,
        p.add_neg,
        p.add_neg_cancel_right,
        p.add_lt_add_of_le_of_lt,
        p.mul_le_mul_of_nonneg_left,
        p.zero_lt_one,
        p.mul_comm,
        p.mul_assoc,
        p.mul_one,
        p.one_mul,
        p.neg_one_mul,
        p.mul_zero,
        p.left_distrib,
        p.mul_nonneg,
        p.no_int_between,
        p.le_total,
        p.lt_of_le_of_ne,
        p.euclidean_decomposition,
        p.eq_em,
    ] {
        let ty = k.environment().get(name).unwrap().ty();
        let inferred = k.infer(ty).unwrap();
        assert!(
            matches!(k.expr_node(inferred), ExprNode::Sort(_)),
            "axiom {} type should infer to a Sort",
            k.display_name(name)
        );
    }
}

/// **`no_int_between` applied**: `no_int_between x : Not (And (lt zero x)
/// (lt x one))`. We build a fresh `x : Z` const, apply `no_int_between` to it,
/// `infer`, and `def_eq`-check the inferred type against the expected
/// `Not (And (lt zero x) (lt x one))`. (Mirrors `arith_prelude`'s
/// `lt_irrefl_applied_checks`.)
#[test]
fn no_int_between_applied_checks() {
    let mut f = fixture();
    let x = f.x_const();

    // proof := no_int_between x.
    let nib = f.k.const_(f.p.no_int_between, vec![]);
    let proof = f.k.app(nib, x);
    let inferred = f.k.infer(proof).unwrap();

    // Expected: Not (And (lt zero x) (lt x one)).
    let zero = f.zero();
    let x2 = f.x_const();
    let lt_0x = f.lt(zero, x2);
    let x3 = f.x_const();
    let one = f.one();
    let lt_x1 = f.lt(x3, one);
    let conj = f.and(lt_0x, lt_x1);
    let expected = f.not(conj);
    assert!(
        f.k.def_eq(inferred, expected),
        "no_int_between x : Not (And (lt zero x) (lt x one))"
    );
}

/// **discreteness refutation** — the integer-specific content: given
/// `h0 : lt zero x` and `h1 : lt x one`, the term
/// `no_int_between x (And.intro (lt zero x) (lt x one) h0 h1)` infers to `False`.
/// The conjunction is built with the logic prelude's `And.intro`, which takes the
/// two Prop arguments explicitly (`And.intro P Q hp hq : And P Q`), and
/// `no_int_between x : Not (And …)` unfolds to `And … → False`, so the whole term
/// is `False`.
#[test]
fn discreteness_refutes_zero_lt_x_lt_one() {
    let mut f = fixture();

    // Hypotheses h0 : lt zero x, h1 : lt x one.
    let zero = f.zero();
    let x = f.x_const();
    let lt_0x = f.lt(zero, x);
    let x2 = f.x_const();
    let one = f.one();
    let lt_x1 = f.lt(x2, one);
    let (_, h0) = f.hyp("h0", lt_0x);
    let (_, h1) = f.hyp("h1", lt_x1);

    // and_proof := And.intro (lt zero x) (lt x one) h0 h1 : And (lt zero x)(lt x one).
    let zero2 = f.zero();
    let x3 = f.x_const();
    let p_prop = f.lt(zero2, x3); // lt zero x
    let x4 = f.x_const();
    let one2 = f.one();
    let q_prop = f.lt(x4, one2); // lt x one
    let and_proof = {
        let intro = f.k.const_(f.p.logic.and_intro, vec![]);
        let e = f.k.app(intro, p_prop);
        let e = f.k.app(e, q_prop);
        let e = f.k.app(e, h0);
        f.k.app(e, h1)
    };

    // proof := no_int_between x and_proof : False.
    let x5 = f.x_const();
    let proof = {
        let nib = f.k.const_(f.p.no_int_between, vec![]);
        let e = f.k.app(nib, x5); // no_int_between x : Not (And …)
        f.k.app(e, and_proof) // applied to (And …) ⇒ False
    };
    let inferred = f.k.infer(proof).unwrap();
    let false_ = f.false_();
    assert!(
        f.k.def_eq(inferred, false_),
        "no_int_between x (And.intro … h0 h1) : False"
    );
}

/// ADR-0104's trusted theorem has the exact quotient/remainder proposition:
/// applying it to `x`, modulus `1`, and `zero_lt_one` produces
/// `Exists q r, x = 1*q+r ∧ 0≤r ∧ r<1`.
#[test]
fn euclidean_decomposition_applied_checks_exact_type() {
    use crate::BinderInfo;

    let mut f = fixture();
    let x = f.x_const();
    let one = f.one();
    let theorem = f.k.const_(f.p.euclidean_decomposition, vec![]);
    let proof = f.k.app(theorem, x);
    let proof = f.k.app(proof, one);
    let positive = f.k.const_(f.p.zero_lt_one, vec![]);
    let proof = f.k.app(proof, positive);
    let inferred = f.k.infer(proof).unwrap();

    let q_id = 20_000;
    let r_id = 20_001;
    let q = f.k.fvar(q_id);
    let r = f.k.fvar(r_id);
    let mul = f.k.const_(f.p.mul, vec![]);
    let one = f.one();
    let one_q = f.k.app(mul, one);
    let one_q = f.k.app(one_q, q);
    let add = f.k.const_(f.p.add, vec![]);
    let sum = f.k.app(add, one_q);
    let sum = f.k.app(sum, r);
    let zero_level = f.k.level_zero();
    let one_level = f.k.level_succ(zero_level);
    let eq = f.k.const_(f.p.logic.eq, vec![one_level]);
    let z_ty = f.k.const_(f.p.z, vec![]);
    let recomposition = f.k.app(eq, z_ty);
    let x = f.x_const();
    let recomposition = f.k.app(recomposition, x);
    let recomposition = f.k.app(recomposition, sum);
    let le = f.k.const_(f.p.le, vec![]);
    let zero = f.zero();
    let nonnegative = f.k.app(le, zero);
    let nonnegative = f.k.app(nonnegative, r);
    let r_again = f.k.fvar(r_id);
    let one = f.one();
    let below_one = f.lt(r_again, one);
    let bounds = f.and(nonnegative, below_one);
    let facts = f.and(recomposition, bounds);

    let anon = f.k.anon();
    let r_body = f.k.abstract_fvars(facts, &[r_id]);
    let z_ty = f.k.const_(f.p.z, vec![]);
    let r_pred = f.k.lam(anon, z_ty, r_body, BinderInfo::Default);
    let exists = f.k.const_(f.p.logic.exists_, vec![one_level]);
    let z_ty = f.k.const_(f.p.z, vec![]);
    let exists_r = f.k.app(exists, z_ty);
    let exists_r = f.k.app(exists_r, r_pred);
    let q_body = f.k.abstract_fvars(exists_r, &[q_id]);
    let z_ty = f.k.const_(f.p.z, vec![]);
    let q_pred = f.k.lam(anon, z_ty, q_body, BinderInfo::Default);
    let exists = f.k.const_(f.p.logic.exists_, vec![one_level]);
    let z_ty = f.k.const_(f.p.z, vec![]);
    let expected = f.k.app(exists, z_ty);
    let expected = f.k.app(expected, q_pred);

    assert!(
        f.k.def_eq(inferred, expected),
        "euclidean_decomposition x one zero_lt_one has the exact residue type"
    );
}

/// ADR-0106 exposes decidability only for integer equality, not unrestricted
/// propositional excluded middle.
#[test]
fn integer_equality_decidability_applied_checks_exact_type() {
    let mut f = fixture();
    let x = f.x_const();
    let zero = f.zero();
    let theorem = f.k.const_(f.p.eq_em, vec![]);
    let proof = f.k.app(theorem, x);
    let proof = f.k.app(proof, zero);
    let inferred = f.k.infer(proof).unwrap();

    let zero_level = f.k.level_zero();
    let one_level = f.k.level_succ(zero_level);
    let eq = f.k.const_(f.p.logic.eq, vec![one_level]);
    let z_ty = f.k.const_(f.p.z, vec![]);
    let equality = f.k.app(eq, z_ty);
    let x = f.x_const();
    let equality = f.k.app(equality, x);
    let zero = f.zero();
    let equality = f.k.app(equality, zero);
    let not = f.k.const_(f.p.logic.not, vec![]);
    let not_equality = f.k.app(not, equality);
    let or = f.k.const_(f.p.logic.or, vec![]);
    let expected = f.k.app(or, equality);
    let expected = f.k.app(expected, not_equality);
    assert!(
        f.k.def_eq(inferred, expected),
        "eq_em x zero has exactly Eq-or-Not-Eq type"
    );
}

/// Determinism: building the prelude twice yields identical `IntPrelude` (same
/// dense ids), since interning is insertion-ordered.
#[test]
fn build_is_deterministic() {
    let mut k1 = Kernel::new();
    let p1 = build_int_prelude(&mut k1).expect("Int prelude must build");
    let mut k2 = Kernel::new();
    let p2 = build_int_prelude(&mut k2).expect("Int prelude must build");
    assert_eq!(p1, p2, "IntPrelude ids are deterministic");
}

/// `Int.ofNat n` for `n ≥ 0` and `Int.negSucc (-n-1)` for `n < 0` — the unique
/// normal form of the integer `n`.
fn numeral(k: &mut Kernel, p: &IntPrelude, n: i32) -> crate::ExprId {
    let magnitude = if n >= 0 {
        u32::try_from(n).expect("non-negative")
    } else {
        u32::try_from(-n - 1).expect("negative")
    };
    let mut nat = k.const_(p.nat.zero, vec![]);
    for _ in 0..magnitude {
        let succ = k.const_(p.nat.succ, vec![]);
        nat = k.app(succ, nat);
    }
    let ctor = if n >= 0 { p.of_nat } else { p.neg_succ };
    let c = k.const_(ctor, vec![]);
    k.app(c, nat)
}

/// The raw `Nat` numeral `n` (a `zero`/`succ` chain), unwrapped by `Int.ofNat`
/// — for building `Nat.le`/`Nat.lt` witnesses directly.
fn numeral_nat(k: &mut Kernel, p: &IntPrelude, n: u32) -> crate::ExprId {
    let mut nat = k.const_(p.nat.zero, vec![]);
    for _ in 0..n {
        let succ = k.const_(p.nat.succ, vec![]);
        nat = k.app(succ, nat);
    }
    nat
}

/// The construction **computes**. Type-checking the ring laws does not pin the
/// operations down — a wrong `Int.add` would still satisfy a wrong-but-provable
/// `add_comm` — so every case of every operation is evaluated against its
/// normal form here, including the borrow cases where `subNatNat` has to decide
/// which constructor the answer lands in.
#[test]
fn the_operations_compute_their_normal_forms() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let binary = [
        (p.add, 2, 3, 5),
        (p.add, 2, -1, 1),
        (p.add, 1, -3, -2),
        (p.add, -1, 2, 1),
        (p.add, -2, -3, -5),
        (p.add, 3, -3, 0),
        (p.add, -3, 3, 0),
        (p.add, 0, 0, 0),
        (p.add, 0, -4, -4),
        (p.mul, 2, 3, 6),
        (p.mul, 2, -3, -6),
        (p.mul, -2, 3, -6),
        (p.mul, -2, -3, 6),
        (p.mul, 0, -3, 0),
        (p.mul, -3, 0, 0),
        (p.mul, 1, -4, -4),
    ];
    for (operation, left, right, expected) in binary {
        let a = numeral(&mut k, &p, left);
        let b = numeral(&mut k, &p, right);
        let f = k.const_(operation, vec![]);
        let applied = k.app(f, a);
        let applied = k.app(applied, b);
        let want = numeral(&mut k, &p, expected);
        assert!(
            k.def_eq(applied, want),
            "{} {left} {right} should be {expected}",
            k.display_name(operation)
        );
    }

    for (input, expected) in [(0, 0), (3, -3), (-3, 3), (1, -1), (-1, 1)] {
        let a = numeral(&mut k, &p, input);
        let f = k.const_(p.neg, vec![]);
        let applied = k.app(f, a);
        let want = numeral(&mut k, &p, expected);
        assert!(k.def_eq(applied, want), "neg {input} should be {expected}");
    }

    // The two constants are the normal forms they claim to be.
    let zero = k.const_(p.zero, vec![]);
    let want = numeral(&mut k, &p, 0);
    assert!(k.def_eq(zero, want), "Int.zero is Int.ofNat 0");
    let one = k.const_(p.one, vec![]);
    let want = numeral(&mut k, &p, 1);
    assert!(k.def_eq(one, want), "Int.one is Int.ofNat 1");
}

/// `Int.ediv`/`Int.emod` compute the exact values Lean 4 core's `Int.ediv`/
/// `Int.emod` document for themselves (`Init.Data.Int.DivMod.Basic`), across
/// every sign combination and the division-by-zero corner — the totality
/// convention this development chose to match, not a case it happened to get
/// right. Both are checked `Declaration::Definition`s with an empty axiom
/// footprint: nothing here was assumed.
#[test]
fn ediv_emod_compute_their_normal_forms() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    assert!(
        k.axiom_footprint(p.ediv).is_empty(),
        "Int.ediv must rest on no axiom"
    );
    assert!(
        k.axiom_footprint(p.emod).is_empty(),
        "Int.emod must rest on no axiom"
    );

    let ediv_cases = [
        (7, 0, 0),
        (0, 7, 0),
        (12, 6, 2),
        (12, -6, -2),
        (-12, 6, -2),
        (-12, -6, 2),
        (12, 7, 1),
        (12, -7, -1),
        (-12, 7, -2),
        (-12, -7, 2),
    ];
    for (left, right, expected) in ediv_cases {
        let a = numeral(&mut k, &p, left);
        let b = numeral(&mut k, &p, right);
        let f = k.const_(p.ediv, vec![]);
        let applied = k.app(f, a);
        let applied = k.app(applied, b);
        let want = numeral(&mut k, &p, expected);
        assert!(
            k.def_eq(applied, want),
            "ediv {left} {right} should be {expected}"
        );
    }

    let emod_cases = [
        (7, 0, 7),
        (0, 7, 0),
        (12, 6, 0),
        (12, -6, 0),
        (-12, 6, 0),
        (-12, -6, 0),
        (12, 7, 5),
        (12, -7, 5),
        (-12, 7, 2),
        (-12, -7, 2),
    ];
    for (left, right, expected) in emod_cases {
        let a = numeral(&mut k, &p, left);
        let b = numeral(&mut k, &p, right);
        let f = k.const_(p.emod, vec![]);
        let applied = k.app(f, a);
        let applied = k.app(applied, b);
        let want = numeral(&mut k, &p, expected);
        assert!(
            k.def_eq(applied, want),
            "emod {left} {right} should be {expected}"
        );
        // The E-rounding invariant: the remainder is always non-negative.
        assert!(expected >= 0, "emod {left} {right} should be non-negative");
    }
}

/// `Int.ediv_add_emod` — the division algorithm as an equation
/// (`b*(a/b)+a%b=a`) — genuinely computes, across every sign combination and
/// the division-by-zero corner, and is a `Theorem` with an empty axiom
/// footprint: the equation was DERIVED from `Nat.div_mod_exec`, not assumed.
#[test]
fn ediv_add_emod_computes_at_concrete_values() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        k.axiom_footprint(p.ediv_add_emod).is_empty(),
        "Int.ediv_add_emod must rest on no axiom"
    );

    let cases = [
        (7, 0),
        (0, 7),
        (12, 6),
        (12, -6),
        (-12, 6),
        (-12, -6),
        (12, 7),
        (12, -7),
        (-12, 7),
        (-12, -7),
    ];
    for (left, right) in cases {
        let a = numeral(&mut k, &p, left);
        let b = numeral(&mut k, &p, right);
        let theorem = k.const_(p.ediv_add_emod, vec![]);
        let applied = k.app(theorem, a);
        let proof = k.app(applied, b);
        let inferred = k
            .infer(proof)
            .unwrap_or_else(|e| panic!("ediv_add_emod {left} {right} should type-check: {e:?}"));

        // The stated equation, built directly: `Eq Int (b*(a/b)+a%b) a`.
        let a = numeral(&mut k, &p, left);
        let b = numeral(&mut k, &p, right);
        let ediv = k.const_(p.ediv, vec![]);
        let ediv_ab_f = k.app(ediv, a);
        let ediv_ab = k.app(ediv_ab_f, b);
        let mul = k.const_(p.mul, vec![]);
        let scaled_f = k.app(mul, b);
        let scaled = k.app(scaled_f, ediv_ab);
        let emod = k.const_(p.emod, vec![]);
        let emod_ab_f = k.app(emod, a);
        let emod_ab = k.app(emod_ab_f, b);
        let add = k.const_(p.add, vec![]);
        let sum_f = k.app(add, scaled);
        let sum = k.app(sum_f, emod_ab);
        let zero_level = k.level_zero();
        let one_level = k.level_succ(zero_level);
        let eq = k.const_(p.logic.eq, vec![one_level]);
        let z_ty = k.const_(p.z, vec![]);
        let eq_ty = k.app(eq, z_ty);
        let eq_ty_sum = k.app(eq_ty, sum);
        let expected = k.app(eq_ty_sum, a);

        assert!(
            k.def_eq(inferred, expected),
            "ediv_add_emod {left} {right}: inferred type does not match the stated equation"
        );

        // And it genuinely computes: the reconstruction reduces to `left`.
        let want = numeral(&mut k, &p, left);
        assert!(
            k.def_eq(sum, want),
            "ediv_add_emod {left} {right}: b*(a/b)+a%b should reduce to {left}"
        );
    }
}

/// `Int.ediv_emod_unique` applied at a genuine positive divisor and a genuine
/// valid decomposition (`13 = 4*3+1`, remainder `1` in `[0,4)`) type-checks
/// end to end: every one of the six hypothesis proofs is a real `Nat.le`/
/// `Nat.lt` witness at concrete numerals, not just an abstract variable. The
/// two decompositions supplied are identical, so the conclusion is trivial
/// (`3=3 ∧ 1=1`), but reaching it exercises the divisor-pinning
/// (`Int.lt_dest`) and the `Int.le_total` split on real literals rather than
/// free variables.
#[test]
fn ediv_emod_unique_applies_at_a_concrete_decomposition() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        k.axiom_footprint(p.ediv_emod_unique).is_empty(),
        "Int.ediv_emod_unique must rest on no axiom"
    );

    let a = numeral(&mut k, &p, 13);
    let b = numeral(&mut k, &p, 4);
    let q = numeral(&mut k, &p, 3);
    let r = numeral(&mut k, &p, 1);

    let zero_level = k.level_zero();
    let one_level = k.level_succ(zero_level);
    let z_ty = k.const_(p.z, vec![]);

    // 0 < 4 : Nat.le 1 4, from `le_succ_succ 0 3 (zero_le 3)`.
    let pos_proof = {
        let base = {
            let n3 = numeral_nat(&mut k, &p, 3);
            let f = k.const_(p.nat.zero_le, vec![]);
            k.app(f, n3)
        };
        let n0 = numeral_nat(&mut k, &p, 0);
        let n3 = numeral_nat(&mut k, &p, 3);
        let f = k.const_(p.nat.le_succ_succ, vec![]);
        let f = k.app(f, n0);
        let f = k.app(f, n3);
        k.app(f, base)
    };

    // 13 = 4*3+1, by computation alone.
    let eq_proof = {
        let refl = k.const_(p.logic.eq_refl, vec![one_level]);
        let refl = k.app(refl, z_ty);
        k.app(refl, a)
    };

    // 0 ≤ 1 : Nat.le 0 1.
    let lower_proof = {
        let n1 = numeral_nat(&mut k, &p, 1);
        let f = k.const_(p.nat.zero_le, vec![]);
        k.app(f, n1)
    };

    // 1 < 4 : Nat.le 2 4, from two `le_succ_succ` steps off `zero_le 2`.
    let upper_proof = {
        let n2 = numeral_nat(&mut k, &p, 2);
        let base = {
            let f = k.const_(p.nat.zero_le, vec![]);
            k.app(f, n2)
        };
        let n0 = numeral_nat(&mut k, &p, 0);
        let step1 = {
            let f = k.const_(p.nat.le_succ_succ, vec![]);
            let f = k.app(f, n0);
            let f = k.app(f, n2);
            k.app(f, base)
        };
        let n1 = numeral_nat(&mut k, &p, 1);
        let n3 = numeral_nat(&mut k, &p, 3);
        let f = k.const_(p.nat.le_succ_succ, vec![]);
        let f = k.app(f, n1);
        let f = k.app(f, n3);
        k.app(f, step1)
    };

    let theorem = k.const_(p.ediv_emod_unique, vec![]);
    let mut proof = theorem;
    for arg in [a, b, q, r, q, r] {
        proof = k.app(proof, arg);
    }
    for arg in [
        pos_proof,
        eq_proof,
        lower_proof,
        upper_proof,
        eq_proof,
        lower_proof,
        upper_proof,
    ] {
        proof = k.app(proof, arg);
    }
    let inferred = k
        .infer(proof)
        .unwrap_or_else(|e| panic!("ediv_emod_unique 13 4 3 1 3 1 should type-check: {e:?}"));

    let eq = k.const_(p.logic.eq, vec![one_level]);
    let eq_q = k.app(eq, z_ty);
    let eq_q = k.app(eq_q, q);
    let eq_q = k.app(eq_q, q);
    let eq_r = k.const_(p.logic.eq, vec![one_level]);
    let z_ty = k.const_(p.z, vec![]);
    let eq_r = k.app(eq_r, z_ty);
    let eq_r = k.app(eq_r, r);
    let eq_r = k.app(eq_r, r);
    let and = k.const_(p.logic.and, vec![]);
    let expected = k.app(and, eq_q);
    let expected = k.app(expected, eq_r);

    assert!(
        k.def_eq(inferred, expected),
        "ediv_emod_unique's conclusion should be exactly q1=q2 ∧ r1=r2"
    );
}

/// `Int.emod_eq_zero_iff_dvd`'s `mp` direction, applied at a genuine multiple
/// (`12 = 4*3`): feeding it the (computed) proof that `12 % 4 = 0` produces a
/// real divisibility witness of type `Int.dvd 4 12`.
#[test]
fn emod_eq_zero_iff_dvd_mp_produces_a_real_witness() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    assert!(
        k.axiom_footprint(p.emod_eq_zero_iff_dvd).is_empty(),
        "Int.emod_eq_zero_iff_dvd must rest on no axiom"
    );

    let a = numeral(&mut k, &p, 12);
    let b = numeral(&mut k, &p, 4);

    // 0 < 4 : Nat.le 1 4.
    let pos_proof = {
        let n3 = numeral_nat(&mut k, &p, 3);
        let base = {
            let f = k.const_(p.nat.zero_le, vec![]);
            k.app(f, n3)
        };
        let n0 = numeral_nat(&mut k, &p, 0);
        let f = k.const_(p.nat.le_succ_succ, vec![]);
        let f = k.app(f, n0);
        let f = k.app(f, n3);
        k.app(f, base)
    };

    let theorem = k.const_(p.emod_eq_zero_iff_dvd, vec![]);
    let mut iff_proof = theorem;
    for arg in [a, b, pos_proof] {
        iff_proof = k.app(iff_proof, arg);
    }

    // 12 % 4 = 0, purely by computation.
    let zero_level = k.level_zero();
    let one_level = k.level_succ(zero_level);
    let z_ty = k.const_(p.z, vec![]);
    let emod = k.const_(p.emod, vec![]);
    let emod_ab = k.app(emod, a);
    let emod_ab = k.app(emod_ab, b);
    let refl = k.const_(p.logic.eq_refl, vec![one_level]);
    let refl = k.app(refl, z_ty);
    let zero_remainder_proof = k.app(refl, emod_ab);

    let mp = k.const_(p.logic.iff_mp, vec![]);
    let zero_eq_ty = {
        let eq = k.const_(p.logic.eq, vec![one_level]);
        let eq_ty = k.app(eq, z_ty);
        let eq_ty = k.app(eq_ty, emod_ab);
        let zero = k.const_(p.zero, vec![]);
        k.app(eq_ty, zero)
    };
    let dvd_ba = {
        let dvd = k.const_(p.dvd, vec![]);
        let dvd_ba = k.app(dvd, b);
        k.app(dvd_ba, a)
    };
    let mp = k.app(mp, zero_eq_ty);
    let mp = k.app(mp, dvd_ba);
    let mp = k.app(mp, iff_proof);
    let witness = k.app(mp, zero_remainder_proof);
    let inferred = k
        .infer(witness)
        .unwrap_or_else(|e| panic!("emod_eq_zero_iff_dvd mp at 12 4 should type-check: {e:?}"));

    assert!(
        k.def_eq(inferred, dvd_ba),
        "the witness's type should be exactly Int.dvd 4 12"
    );
}

/// The order relations decide the mixed-sign cases outright: a negative integer
/// is below every non-negative one, and never the reverse. (The same-sign cases
/// delegate to `Nat.le`/`Nat.lt`, which the `Nat` prelude's own suite covers.)
#[test]
fn the_order_relations_decide_mixed_signs() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let true_ = k.const_(p.logic.true_, vec![]);
    let false_ = k.const_(p.logic.false_, vec![]);

    for relation in [p.le, p.lt] {
        for (left, right) in [(-1, 0), (-4, 2), (-1, 7)] {
            let a = numeral(&mut k, &p, left);
            let b = numeral(&mut k, &p, right);
            let f = k.const_(relation, vec![]);
            let applied = k.app(f, a);
            let applied = k.app(applied, b);
            assert!(
                k.def_eq(applied, true_),
                "{} {left} {right} should hold outright",
                k.display_name(relation)
            );
            // …and the reverse orientation is refuted outright.
            let a = numeral(&mut k, &p, right);
            let b = numeral(&mut k, &p, left);
            let f = k.const_(relation, vec![]);
            let applied = k.app(f, a);
            let applied = k.app(applied, b);
            assert!(
                k.def_eq(applied, false_),
                "{} {right} {left} should be refuted outright",
                k.display_name(relation)
            );
        }
    }
}

/// The `Nat` development the construction rests on is itself axiom-free, and
/// building `Int` on top of it introduces no trusted declaration of its own
/// beyond the still-asserted laws. This is the property that makes a derived
/// integer fact's empty footprint mean something.
#[test]
fn the_nat_foundation_stays_axiom_free() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    for name in [
        p.nat.add_comm,
        p.nat.mul_comm,
        p.nat.le_trans,
        p.nat.sub_self,
        p.nat.mul_one,
        p.nat.le_total,
    ] {
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{} must stay axiom-free",
            k.display_name(name)
        );
    }
}

/// `Int.euclid_of_nat` is a **theorem** with an empty axiom footprint — the
/// non-negative branch of the Euclidean decomposition, derived from the
/// axiom-free `Nat` division development rather than assumed.
///
/// This is the ledger-grade claim about the branch: not that it exists, but
/// that it rests on nothing. `Int.euclidean_decomposition` is deliberately NOT
/// asserted to be gone here — it is still an axiom, and the test that it has
/// become a theorem belongs with the commit that discharges it.
#[test]
fn euclid_of_nat_is_derived_and_axiom_free() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let declaration = k
        .environment()
        .get(p.euclid_of_nat)
        .expect("Int.euclid_of_nat must be declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "Int.euclid_of_nat must be a Theorem, not an assumption"
    );

    let footprint = k.axiom_footprint(p.euclid_of_nat);
    assert!(
        footprint.is_empty(),
        "Int.euclid_of_nat rests on trusted declarations: {:?}",
        footprint
            .iter()
            .map(|&n| k.display_name(n).to_string())
            .collect::<Vec<_>>()
    );
}

/// `Int.natAbs` computes on both constructors by `rfl`, and the round-trip
/// lemma is a theorem with an empty axiom footprint.
///
/// The `rfl` checks matter: `natAbs` is the first piece of the ℚ groundwork, and
/// its two computation rules being definitional is what lets every later
/// statement about a normalised rational avoid a rewrite.
#[test]
fn nat_abs_computes_and_round_trips() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    // natAbs (ofNat 3) ≡ 3 and natAbs (negSucc 2) ≡ 3, by conversion alone.
    let three = {
        let mut n = k.const_(p.nat.zero, vec![]);
        for _ in 0..3 {
            let succ = k.const_(p.nat.succ, vec![]);
            n = k.app(succ, n);
        }
        n
    };
    let two = {
        let mut n = k.const_(p.nat.zero, vec![]);
        for _ in 0..2 {
            let succ = k.const_(p.nat.succ, vec![]);
            n = k.app(succ, n);
        }
        n
    };
    let nat_abs = k.const_(p.nat_abs, vec![]);
    for magnitude in [
        {
            let ctor = k.const_(p.of_nat, vec![]);
            k.app(ctor, three)
        },
        {
            let ctor = k.const_(p.neg_succ, vec![]);
            k.app(ctor, two)
        },
    ] {
        let applied = k.app(nat_abs, magnitude);
        assert!(k.def_eq(applied, three), "natAbs did not compute to 3");
    }

    let declaration = k
        .environment()
        .get(p.of_nat_nat_abs_of_nonneg)
        .expect("of_nat_nat_abs_of_nonneg must be declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "of_nat_nat_abs_of_nonneg must be a Theorem"
    );
    assert!(
        k.axiom_footprint(p.of_nat_nat_abs_of_nonneg).is_empty(),
        "the round-trip lemma rests on a trusted declaration"
    );
}

/// A concrete rational is constructible, and a non-normalised one is not.
///
/// `Rat.mk` carries two proof fields, and this test discharges both the way a
/// smart constructor will: positivity from `le_succ_succ`, and reducedness by
/// `rfl` — which works only because **`Nat.gcd` computes in this kernel**.
/// Measured here before relying on it: `gcd 1 2` is definitionally `1`, even
/// though `gcd` is defined by well-founded recursion and `WellFounded.fix` does
/// not generally reduce by iota.
///
/// The rejection half is the point. `2/4` differs from `1/2` only in that its
/// `reduced` field is false, so if the kernel accepted it the structure would be
/// carrying a proof obligation it does not enforce.
#[test]
fn rat_admits_a_normalised_pair_and_rejects_an_unreduced_one() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.nat.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.nat.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };
    let nat_ty = k.const_(p.nat.nat, vec![]);

    // `gcd` really does reduce; the `rfl` below depends on it.
    let one = numeral(&mut k, 1);
    let two = numeral(&mut k, 2);
    let gcd = k.const_(p.nat.gcd, vec![]);
    let computed = {
        let at_one = k.app(gcd, one);
        k.app(at_one, two)
    };
    assert!(
        k.def_eq(computed, one),
        "gcd 1 2 must reduce to 1 for a rational's `reduced` field to be rfl"
    );

    // 1/2 : num = ofNat 1, den = 2, 1 <= 2, gcd (natAbs 1) 2 = 1.
    let build = |k: &mut Kernel, numerator: usize, denominator: usize| {
        let zero = k.const_(p.nat.zero, vec![]);
        let num = {
            let ctor = k.const_(p.of_nat, vec![]);
            let magnitude = numeral(k, numerator);
            k.app(ctor, magnitude)
        };
        let den = numeral(k, denominator);
        // 1 <= den, for den = succ (succ .. zero): le_succ_succ zero (den-1) (zero_le _)
        let predecessor = numeral(k, denominator - 1);
        let positive = {
            let base = {
                let lemma = k.const_(p.nat.zero_le, vec![]);
                k.app(lemma, predecessor)
            };
            let lemma = k.const_(p.nat.le_succ_succ, vec![]);
            let at_zero = k.app(lemma, zero);
            let at_pred = k.app(at_zero, predecessor);
            k.app(at_pred, base)
        };
        // rfl : gcd (natAbs num) den = 1, by computation.
        let unit = numeral(k, 1);
        let reduced = {
            let level = {
                let zero = k.level_zero();
                k.level_succ(zero)
            };
            let refl = k.const_(p.logic.eq_refl, vec![level]);
            let at_ty = k.app(refl, nat_ty);
            k.app(at_ty, unit)
        };
        let ctor = k.const_(p.rat_mk, vec![]);
        let at_num = k.app(ctor, num);
        let at_den = k.app(at_num, den);
        let at_pos = k.app(at_den, positive);
        k.app(at_pos, reduced)
    };

    let half = build(&mut k, 1, 2);
    let inferred = k.infer(half).expect("1/2 must be a well-formed Rat");
    let rendered = k.render_lean(inferred);
    assert!(rendered.contains("Rat"), "unexpected type: {rendered}");

    // 2/4 is not reduced: gcd 2 4 computes to 2, so the `rfl` cannot check.
    let unreduced = build(&mut k, 2, 4);
    assert!(
        k.infer(unreduced).is_err(),
        "Rat accepted 2/4, whose `reduced` field is false"
    );
}

/// `Rat.normalize` actually normalises: `2/4` and `1/2` are the *same* rational.
///
/// This is the strongest statement available about a smart constructor, and it
/// needs no lemma — `Nat.gcd`, `Nat.div` and `Int.rec` all compute, so the two
/// terms are definitionally equal and `def_eq` decides it.
///
/// The discrimination half matters just as much: `1/2` and `1/3` must NOT be
/// equal, or the check above would be vacuous.
#[test]
fn rat_normalize_reduces_two_quarters_to_one_half() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.nat.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.nat.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };
    let zero = k.const_(p.nat.zero, vec![]);
    let one_le = |k: &mut Kernel, n: usize| {
        let predecessor = numeral(k, n - 1);
        let base = {
            let lemma = k.const_(p.nat.zero_le, vec![]);
            k.app(lemma, predecessor)
        };
        let lemma = k.const_(p.nat.le_succ_succ, vec![]);
        let at_zero = k.app(lemma, zero);
        let at_pred = k.app(at_zero, predecessor);
        k.app(at_pred, base)
    };
    let normalize_at = |k: &mut Kernel, numerator: usize, denominator: usize| {
        let num = {
            let ctor = k.const_(p.of_nat, vec![]);
            let magnitude = numeral(k, numerator);
            k.app(ctor, magnitude)
        };
        let den = numeral(k, denominator);
        let positive = one_le(k, denominator);
        let normalize = k.const_(p.rat_normalize, vec![]);
        let at_num = k.app(normalize, num);
        let at_den = k.app(at_num, den);
        k.app(at_den, positive)
    };

    let two_quarters = normalize_at(&mut k, 2, 4);
    let one_half = normalize_at(&mut k, 1, 2);
    assert!(
        k.def_eq(two_quarters, one_half),
        "normalize did not reduce 2/4 to 1/2"
    );

    // Non-vacuity: distinct rationals stay distinct.
    let one_third = normalize_at(&mut k, 1, 3);
    assert!(
        !k.def_eq(one_half, one_third),
        "1/2 and 1/3 compared equal — the check above would be meaningless"
    );

    // And a negative numerator normalises through the `negSucc` branch.
    let minus_two_quarters = {
        let num = {
            let ctor = k.const_(p.neg_succ, vec![]);
            let one = numeral(&mut k, 1);
            k.app(ctor, one)
        };
        let den = numeral(&mut k, 4);
        let positive = one_le(&mut k, 4);
        let normalize = k.const_(p.rat_normalize, vec![]);
        let at_num = k.app(normalize, num);
        let at_den = k.app(at_num, den);
        k.app(at_den, positive)
    };
    let inferred = k
        .infer(minus_two_quarters)
        .expect("normalize must accept a negSucc numerator");
    let rendered = k.render_lean(inferred);
    assert!(rendered.contains("Rat"), "unexpected type: {rendered}");
}

/// `Rat.mul` renormalises: `2/3 · 3/2` is `1/1`, not `6/6`.
///
/// This is why multiplication cannot just multiply the stored pairs — the
/// product of two *reduced* fractions need not be reduced, and `Rat`'s
/// `reduced` field would then be unprovable. Routing through `Rat.normalize`
/// fixes that, and because every operation computes, the claim is settled by
/// `def_eq` with no lemma.
#[test]
fn rat_mul_renormalises_two_thirds_times_three_halves_to_one() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.nat.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.nat.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };
    let zero = k.const_(p.nat.zero, vec![]);
    let rational = |k: &mut Kernel, numerator: usize, denominator: usize| {
        let num = {
            let ctor = k.const_(p.of_nat, vec![]);
            let magnitude = numeral(k, numerator);
            k.app(ctor, magnitude)
        };
        let den = numeral(k, denominator);
        let positive = {
            let predecessor = numeral(k, denominator - 1);
            let base = {
                let lemma = k.const_(p.nat.zero_le, vec![]);
                k.app(lemma, predecessor)
            };
            let lemma = k.const_(p.nat.le_succ_succ, vec![]);
            let at_zero = k.app(lemma, zero);
            let at_pred = k.app(at_zero, predecessor);
            k.app(at_pred, base)
        };
        let normalize = k.const_(p.rat_normalize, vec![]);
        let at_num = k.app(normalize, num);
        let at_den = k.app(at_num, den);
        k.app(at_den, positive)
    };
    let times = |k: &mut Kernel, a: ExprId, b: ExprId| {
        let mul = k.const_(p.rat_mul, vec![]);
        let at_a = k.app(mul, a);
        k.app(at_a, b)
    };

    let two_thirds = rational(&mut k, 2, 3);
    let three_halves = rational(&mut k, 3, 2);
    let product = times(&mut k, two_thirds, three_halves);
    let one = rational(&mut k, 1, 1);
    assert!(
        k.def_eq(product, one),
        "2/3 * 3/2 did not renormalise to 1/1"
    );

    // Non-vacuity, and a product that genuinely stays a fraction.
    let one_half = rational(&mut k, 1, 2);
    let one_third = rational(&mut k, 1, 3);
    let sixth = times(&mut k, one_half, one_third);
    let one_sixth = rational(&mut k, 1, 6);
    assert!(k.def_eq(sixth, one_sixth), "1/2 * 1/3 is not 1/6");
    assert!(
        !k.def_eq(sixth, one_half),
        "1/6 and 1/2 compared equal — the checks above would be meaningless"
    );
}

/// `Rat.add` renormalises and `Rat.neg` is an involution.
///
/// `1/6 + 1/3` reaches `9/18` over the common denominator before reduction, so
/// addition has the same obligation multiplication does. Negation is the
/// opposite case — it rebuilds the pair directly, because `Int.nat_abs_neg`
/// says the magnitude the `reduced` field speaks of is unchanged.
#[test]
fn rat_add_renormalises_and_neg_is_an_involution() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let numeral = |k: &mut Kernel, n: usize| {
        let mut value = k.const_(p.nat.zero, vec![]);
        for _ in 0..n {
            let succ = k.const_(p.nat.succ, vec![]);
            value = k.app(succ, value);
        }
        value
    };
    let zero = k.const_(p.nat.zero, vec![]);
    let rational = |k: &mut Kernel, numerator: usize, denominator: usize| {
        let num = {
            let ctor = k.const_(p.of_nat, vec![]);
            let magnitude = numeral(k, numerator);
            k.app(ctor, magnitude)
        };
        let den = numeral(k, denominator);
        let positive = {
            let predecessor = numeral(k, denominator - 1);
            let base = {
                let lemma = k.const_(p.nat.zero_le, vec![]);
                k.app(lemma, predecessor)
            };
            let lemma = k.const_(p.nat.le_succ_succ, vec![]);
            let at_zero = k.app(lemma, zero);
            let at_pred = k.app(at_zero, predecessor);
            k.app(at_pred, base)
        };
        let normalize = k.const_(p.rat_normalize, vec![]);
        let at_num = k.app(normalize, num);
        let at_den = k.app(at_num, den);
        k.app(at_den, positive)
    };
    let plus = |k: &mut Kernel, a: ExprId, b: ExprId| {
        let add = k.const_(p.rat_add, vec![]);
        let at_a = k.app(add, a);
        k.app(at_a, b)
    };
    let negate = |k: &mut Kernel, a: ExprId| {
        let neg = k.const_(p.rat_neg, vec![]);
        k.app(neg, a)
    };

    // 1/6 + 1/3 = 9/18 = 1/2
    let sixth = rational(&mut k, 1, 6);
    let third = rational(&mut k, 1, 3);
    let sum = plus(&mut k, sixth, third);
    let half = rational(&mut k, 1, 2);
    assert!(k.def_eq(sum, half), "1/6 + 1/3 did not renormalise to 1/2");
    assert!(
        !k.def_eq(sum, third),
        "1/2 and 1/3 compared equal — the check above would be meaningless"
    );

    // neg is an involution, and moves the value.
    let negated = negate(&mut k, half);
    let twice = negate(&mut k, negated);
    assert!(k.def_eq(twice, half), "neg is not an involution on 1/2");
    assert!(!k.def_eq(negated, half), "neg left 1/2 unchanged");

    // x + (-x) = 0
    let cancelled = plus(&mut k, half, negated);
    let origin = rational(&mut k, 0, 1);
    assert!(k.def_eq(cancelled, origin), "1/2 + (-1/2) is not 0");
}
