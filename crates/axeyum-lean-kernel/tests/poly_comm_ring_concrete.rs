//! ADR-1618: `AlgS.Poly.commRing` instantiated at the concrete carriers.
//!
//! `AlgS.Poly.commRing : AlgS.CommRing -> AlgS.CommRing` is stated over an
//! abstract commutative ring, at the `AlgS` build position where no `Nat`
//! arithmetic exists. This suite feeds it the three concrete `AlgS.CommRing`
//! values the tree already has and makes the **trusted gate** check the
//! resulting 23-field record at each of them:
//!
//! | value | source |
//! |---|---|
//! | `AlgS.CommRing.ofAlg Alg.Rat.commRing` | ℚ, through the `Alg -> AlgS` projection (`Alg.Rat.commRing` is an `Eq`-flavored record, so it must be projected first) |
//! | `CReal.commRingS` | ℝ, ADR-1588's payoff |
//! | `Complex.commRingS` | ℂ |
//!
//! So this is where "a polynomial ring over an abstract commutative ring"
//! becomes **ℚ[X], ℝ[X] and ℂ[X], each a machine-checked commutative ring**.
//! Nothing here is a prelude declaration: the three instances are admitted
//! into a test-local kernel, which is enough to establish that the abstract
//! construction type-checks at the concrete carriers. Landing them as named
//! prelude declarations is a separate (small) step — ADR-1618 sizes it.
//!
//! It is deliberately an INTEGRATION test rather than a unit test in
//! `polynomial_setoid.rs`: `AlgS.Poly.*` is declared long before `Rat`,
//! `CReal` and `Complex` exist, so no unit fixture at that build position can
//! reach them.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, NameId, ReducibilityHint, build_complex_prelude,
    build_nat_prelude,
};

/// Intern `AlgS.<seg1>.<seg2>…` and assert the name is ALREADY in the
/// environment. Interning is idempotent, so this returns the existing
/// `NameId` — and the assertion is the coverage control: a typo'd path would
/// silently mint a fresh unused name instead of failing.
fn resolve(k: &mut Kernel, path: &[&str]) -> NameId {
    let mut name = k.anon();
    for seg in path {
        name = k.name_str(name, *seg);
    }
    assert!(
        k.environment().get(name).is_some(),
        "path {path:?} must already be declared -- an absent name here means \
         the path is wrong, not that the declaration is missing"
    );
    name
}

struct Fixture {
    /// `AlgS.CommRing`, the record type.
    comm_ring_ty: ExprId,
    /// `AlgS.Poly.commRing`.
    poly_comm_ring: NameId,
    /// The three concrete `AlgS.CommRing` VALUES, with labels.
    concrete: Vec<(&'static str, ExprId)>,
    /// `Alg.Rat.commRing` — an `Alg.CommRing`, NOT an `AlgS.CommRing`. Used
    /// as the negative control's argument.
    alg_rat_comm_ring: ExprId,
}

fn build(k: &mut Kernel) -> Fixture {
    let complex = build_complex_prelude(k).expect("the Complex prelude must build");

    let comm_ring_name = resolve(k, &["AlgS", "CommRing"]);
    let poly_comm_ring = resolve(k, &["AlgS", "Poly", "commRing"]);
    let ofalg = resolve(k, &["AlgS", "CommRing", "ofAlg"]);
    let alg_rat_cr = resolve(k, &["Alg", "Rat", "commRing"]);
    let creal_crs = resolve(k, &["CReal", "commRingS"]);
    // The `Complex` name comes from the prelude struct, not from a path, so
    // the two routes cross-check each other.
    let complex_crs = complex.comm_ring_s;
    assert_eq!(
        complex_crs,
        resolve(k, &["Complex", "commRingS"]),
        "the ComplexPrelude field and the interned path must be the same name"
    );

    let comm_ring_ty = k.const_(comm_ring_name, vec![]);
    let alg_rat_comm_ring = k.const_(alg_rat_cr, vec![]);
    let rat_s = {
        let f = k.const_(ofalg, vec![]);
        k.app(f, alg_rat_comm_ring)
    };
    let creal_s = k.const_(creal_crs, vec![]);
    let complex_s = k.const_(complex_crs, vec![]);

    Fixture {
        comm_ring_ty,
        poly_comm_ring,
        concrete: vec![("Q[X]", rat_s), ("R[X]", creal_s), ("C[X]", complex_s)],
        alg_rat_comm_ring,
    }
}

/// `AlgS.Poly.commRing R` for a concrete `R`.
fn poly_ring_over(k: &mut Kernel, f: &Fixture, r: ExprId) -> ExprId {
    let c = k.const_(f.poly_comm_ring, vec![]);
    k.app(c, r)
}

/// **ℚ[X], ℝ[X] and ℂ[X] are commutative rings, checked by the kernel.**
///
/// Each is admitted as a `Definition` whose declared type is `AlgS.CommRing`,
/// so `Kernel::add_declaration` re-checked every one of the record's 23
/// fields at that concrete carrier — including the four ADR-1609 left open
/// (`mulOneL`, `mulOneR`, `mulComm`, `mulAssoc`).
#[test]
fn the_abstract_polynomial_ring_instantiates_at_q_r_and_c() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    for (label, r) in f.concrete.clone() {
        let value = poly_ring_over(&mut k, &f, r);
        let name = {
            let root = k.anon();
            let ns = k.name_str(root, "PolyCommRingConcreteTest");
            k.name_str(ns, label)
        };
        let admitted = k.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty: f.comm_ring_ty,
            value,
            hint: ReducibilityHint::Regular(1),
        });
        assert!(
            admitted.is_ok(),
            "{label} must admit as an AlgS.CommRing value: {admitted:?}"
        );
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label}'s axiom footprint must be empty, got {} entries",
            footprint.len()
        );
    }
}

/// **Evaluation test: ℚ[X] really is the polynomial ring over ℚ.** Its
/// `carrier` selector reduces to `Nat -> Rat` and its `mul` selector to
/// `AlgS.Poly.mul` at the same coefficient ring. The negative twin pairs
/// `mul` against `AlgS.Poly.add`, which a mis-ordered field list would
/// satisfy.
#[test]
fn the_rational_polynomial_ring_carries_coefficient_functions_and_convolution() {
    let mut k = Kernel::new();
    let f = build(&mut k);
    let (_, rat_s) = f.concrete[0];
    let ring = poly_ring_over(&mut k, &f, rat_s);

    let rat_ty = {
        let n = resolve(&mut k, &["Rat"]);
        k.const_(n, vec![])
    };
    let nat_ty = {
        // The `Nat` type's name comes from the prelude, not from a path: its
        // rendered root (`AxNat`) is not the name it is interned under.
        let natp = build_nat_prelude(&mut k).expect("Nat prelude is already built");
        k.const_(natp.nat, vec![])
    };
    let coeff_fn = {
        let anon = k.anon();
        let binder = k.name_str(anon, "n");
        // Non-dependent, so the body needs no `bvar`.
        k.pi(binder, nat_ty, rat_ty, BinderInfo::Default)
    };

    // The record's own field projections, reached by name.
    let field = |k: &mut Kernel, label: &str, inst: ExprId| -> ExprId {
        let n = resolve(k, &["AlgS", "CommRing", label]);
        let c = k.const_(n, vec![]);
        k.app(c, inst)
    };

    let carrier = field(&mut k, "carrier", ring);
    assert!(
        k.def_eq(carrier, coeff_fn),
        "Q[X]'s carrier must reduce to `Nat -> Rat`"
    );

    let poly_mul = resolve(&mut k, &["AlgS", "Poly", "mul"]);
    let poly_add = resolve(&mut k, &["AlgS", "Poly", "add"]);
    let want_mul = {
        let c = k.const_(poly_mul, vec![]);
        k.app(c, rat_s)
    };
    let want_add = {
        let c = k.const_(poly_add, vec![]);
        k.app(c, rat_s)
    };
    let got_mul = field(&mut k, "mul", ring);
    assert!(
        k.def_eq(got_mul, want_mul),
        "Q[X]'s `mul` field must reduce to AlgS.Poly.mul at the same ring"
    );
    assert!(
        !k.def_eq(got_mul, want_add),
        "Q[X]'s `mul` field must NOT be AlgS.Poly.add"
    );
}

/// **Negative control.** `AlgS.Poly.commRing` takes an `AlgS.CommRing`, whose
/// law fields are stated over a carried `equiv`; `Alg.Rat.commRing` is the
/// `Eq`-flavored record with the SAME field names. Feeding the latter must be
/// REFUSED — one argument apart from the positive twin above, which is
/// re-run here so the refusal is evidence about the record and not about the
/// declaration machinery.
#[test]
fn the_eq_flavored_rational_ring_is_refused_where_the_setoid_one_is_required() {
    let mut k = Kernel::new();
    let f = build(&mut k);

    // Positive twin: the `ofAlg`-projected value admits.
    let (_, rat_s) = f.concrete[0];
    let good = poly_ring_over(&mut k, &f, rat_s);
    let good_name = {
        let root = k.anon();
        k.name_str(root, "polyCommRingOverProjectedRat")
    };
    assert!(
        k.add_declaration(Declaration::Definition {
            name: good_name,
            uparams: vec![],
            ty: f.comm_ring_ty,
            value: good,
            hint: ReducibilityHint::Regular(1),
        })
        .is_ok(),
        "the projected `AlgS.CommRing.ofAlg Alg.Rat.commRing` must admit"
    );

    // The mutant: the unprojected `Alg.CommRing` value.
    let bad = poly_ring_over(&mut k, &f, f.alg_rat_comm_ring);
    let bad_name = {
        let root = k.anon();
        k.name_str(root, "polyCommRingOverUnprojectedRat")
    };
    assert!(
        k.add_declaration(Declaration::Definition {
            name: bad_name,
            uparams: vec![],
            ty: f.comm_ring_ty,
            value: bad,
            hint: ReducibilityHint::Regular(1),
        })
        .is_err(),
        "`Alg.CommRing` and `AlgS.CommRing` are different records -- feeding \
         the Eq-flavored one to AlgS.Poly.commRing must be REFUSED"
    );
}
