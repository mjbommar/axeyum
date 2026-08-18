//! Tests for the real (setoid) prelude.

use super::{CRealPrelude, build_creal_prelude};
use crate::{Declaration, Kernel};

/// A built `CReal` kernel, as a **clone of one template**.
///
/// The full development is now 65 declarations over the constructed ℚ and takes
/// tens of seconds to type-check; seventeen tests each building it from scratch
/// dominated this crate's test time. The argument for cloning is
/// [`prelude_cache`](crate::prelude_cache)'s, verbatim: prelude construction is
/// a deterministic function of the empty kernel, so the template equals what a
/// fresh build would produce, and every declaration in it entered through
/// `Kernel::add_declaration` under the full type checker exactly once.
/// `creal_prelude_builds` deliberately does **not** use this — it is the test
/// that exercises the real build.
fn built() -> (Kernel, CRealPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, CRealPrelude)> = OnceLock::new();
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        let mut kernel = Kernel::new();
        let prelude = build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        (kernel, prelude)
    });
    (kernel.clone(), *prelude)
}

/// The build itself, with the kernel's rejection **rendered**. A `Debug` of
/// `KernelError` says nothing about what was refused; this says which two types
/// failed to match.
#[test]
fn creal_prelude_builds() {
    let mut kernel = Kernel::new();
    match build_creal_prelude(&mut kernel) {
        Ok(_) => {}
        Err(error) => {
            let nat = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
            let mut dev = crate::NatDev::new(&mut kernel, nat);
            let explained = crate::NatOps::explain(&mut dev, &error);
            panic!("the kernel refused a real proof: {explained}");
        }
    }
}

/// **ADR-0468's headline claim, measured.** A Bishop setoid over `ℚ` costs zero
/// trusted declarations: no `Quot.sound`, no `funext`, no `propext`, no
/// classical axiom, nothing.
#[test]
fn the_constructed_reals_add_no_trusted_declaration() {
    let (kernel, _) = built();
    let trusted: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Quotient { name, .. } => Some(kernel.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    assert!(
        trusted.is_empty(),
        "the real construction must assume nothing, found: {trusted:?}"
    );
}

/// Every declaration is the kind it claims to be and has an empty axiom
/// footprint, read out of the kernel rather than off the diff.
#[test]
fn every_creal_declaration_is_checked_and_axiom_free() {
    let (kernel, p) = built();
    let expected: [(&str, crate::NameId, &str); 65] = [
        ("Within", p.within, "def"),
        ("Regular", p.regular_pred, "inductive-or-def"),
        ("CReal", p.creal, "inductive"),
        ("CReal.mk", p.mk, "ctor"),
        ("CReal.rec", p.rec, "recursor"),
        ("CReal.seq", p.seq, "def"),
        ("CReal.regular", p.regular, "theorem"),
        ("CReal.Equiv", p.equiv, "def"),
        ("Equiv.refl", p.equiv_refl, "theorem"),
        ("Equiv.symm", p.equiv_symm, "theorem"),
        ("Equiv.trans", p.equiv_trans, "theorem"),
        ("CReal.ofRat", p.of_rat, "def"),
        ("Equiv.not_zero_one", p.not_zero_one, "theorem"),
        ("CReal.zero", p.zero, "def"),
        ("CReal.one", p.one, "def"),
        ("Equiv.of_pointwise", p.equiv_of_pointwise, "theorem"),
        ("CReal.neg", p.neg, "def"),
        ("CReal.neg_congr", p.neg_congr, "theorem"),
        ("CReal.add", p.add, "def"),
        ("CReal.add_congr", p.add_congr, "theorem"),
        ("CReal.add_comm", p.add_comm, "theorem"),
        ("CReal.add_neg", p.add_neg, "theorem"),
        ("CReal.add_zero", p.add_zero, "theorem"),
        ("CReal.add_assoc", p.add_assoc, "theorem"),
        ("CReal.le", p.le, "def"),
        ("CReal.le_refl", p.le_refl, "theorem"),
        ("CReal.le_trans", p.le_trans, "theorem"),
        ("CReal.add_le_add", p.add_le_add, "theorem"),
        ("CReal.le_of_equiv", p.le_of_equiv, "theorem"),
        ("CReal.equiv_of_le_le", p.equiv_of_le_le, "theorem"),
        ("CReal.not_le_one_zero", p.not_le_one_zero, "theorem"),
        ("CReal.le_add_of_nonneg", p.le_add_of_nonneg, "theorem"),
        ("CReal.lt", p.lt, "def"),
        ("CReal.lt_irrefl", p.lt_irrefl, "theorem"),
        ("CReal.lt_trans", p.lt_trans, "theorem"),
        ("CReal.lt_of_lt_of_le", p.lt_of_lt_of_le, "theorem"),
        ("CReal.lt_of_le_of_lt", p.lt_of_le_of_lt, "theorem"),
        ("CReal.le_of_lt", p.le_of_lt, "theorem"),
        ("CReal.zero_lt_one", p.zero_lt_one, "theorem"),
        (
            "CReal.add_lt_add_of_le_of_lt",
            p.add_lt_add_of_le_of_lt,
            "theorem",
        ),
        ("CReal.le_congr", p.le_congr, "theorem"),
        ("CReal.lt_congr", p.lt_congr, "theorem"),
        ("CReal.bound", p.bound, "def"),
        ("CReal.bound_within", p.bound_within, "theorem"),
        ("CReal.mulShift", p.mul_shift, "def"),
        ("CReal.mul", p.mul, "def"),
        ("CReal.ofRat_mul", p.of_rat_mul, "theorem"),
        ("CReal.mul_comm", p.mul_comm, "theorem"),
        ("CReal.mul_one", p.mul_one, "theorem"),
        ("CReal.mul_zero", p.mul_zero, "theorem"),
        ("CReal.mul_nonneg", p.mul_nonneg, "theorem"),
        ("CReal.sq_nonneg", p.sq_nonneg, "theorem"),
        (
            "CReal.not_equiv_mul_one_one_zero",
            p.not_equiv_mul_one_one_zero,
            "theorem",
        ),
        ("CReal.Equiv.of_bounded", p.equiv_of_bounded, "theorem"),
        ("CReal.mul_congr", p.mul_congr, "theorem"),
        ("CReal.left_distrib", p.left_distrib, "theorem"),
        ("CReal.mul_assoc", p.mul_assoc, "theorem"),
        (
            "CReal.mul_le_mul_of_nonneg_left",
            p.mul_le_mul_of_nonneg_left,
            "theorem",
        ),
        ("CReal.Apart", p.apart, "def"),
        ("CReal.apart_symm", p.apart_symm, "theorem"),
        ("CReal.apart_irrefl", p.apart_irrefl, "theorem"),
        ("CReal.apart_congr", p.apart_congr, "theorem"),
        ("CReal.not_equiv_of_apart", p.not_equiv_of_apart, "theorem"),
        ("CReal.apart_zero_one", p.apart_zero_one, "theorem"),
        ("CReal.no_total_inverse", p.no_total_inverse, "theorem"),
    ];
    for (label, name, kind) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} was interned but never declared"));
        match kind {
            "theorem" => assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "{label} must be a checked Theorem"
            ),
            "def" => assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "{label} must be a Definition"
            ),
            _ => {}
        }
        assert!(
            !matches!(
                declaration,
                Declaration::Axiom { .. } | Declaration::Opaque { .. }
            ),
            "{label} is asserted, not derived"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "{label} rests on {footprint:?}");
    }
}

/// The three setoid laws say what ADR-0468 says they say. An empty footprint on
/// a theorem stating something weaker is this repository's standing failure
/// mode, so the rendered types are asserted verbatim.
#[test]
fn the_setoid_laws_have_the_statements_adr_0468_specifies() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.equiv_refl),
        "((x0 : CReal) -> CReal.Equiv x0 x0)"
    );
    assert_eq!(
        rendered(&mut kernel, p.equiv_symm),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Equiv x0 x1) -> CReal.Equiv x1 x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.equiv_trans),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.Equiv x0 x1) -> \
         ((x4 : CReal.Equiv x1 x2) -> CReal.Equiv x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_zero_one),
        "Not (CReal.Equiv (CReal.ofRat Rat.zero) (CReal.ofRat Rat.one))"
    );
    // The two of the 22 that hold in `Equiv` form. Asserting these verbatim is
    // what stops "N laws hold" drifting into "N laws are named".
    assert_eq!(
        rendered(&mut kernel, p.add_comm),
        "((x0 : CReal) -> ((x1 : CReal) -> \
         CReal.Equiv (CReal.add x0 x1) (CReal.add x1 x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_neg),
        "((x0 : CReal) -> \
         CReal.Equiv (CReal.add x0 (CReal.neg x0)) CReal.zero)"
    );
    // The two that are NOT pointwise, and are the reason `Equiv` had to be an
    // equivalence relation before any of this was worth stating.
    assert_eq!(
        rendered(&mut kernel, p.add_zero),
        "((x0 : CReal) -> CReal.Equiv (CReal.add x0 CReal.zero) x0)"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_assoc),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> \
         CReal.Equiv (CReal.add (CReal.add x0 x1) x2) \
         (CReal.add x0 (CReal.add x1 x2)))))"
    );
    // The three order laws. Unlike the additive ones these are the `Real`
    // package's statements VERBATIM — none of them mentions `Eq`, so there is
    // no equality to replace by `Equiv` (ADR-0468, Measurement 2).
    assert_eq!(
        rendered(&mut kernel, p.le_refl),
        "((x0 : CReal) -> CReal.le x0 x0)"
    );
    assert_eq!(
        rendered(&mut kernel, p.le_trans),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.le x0 x1) -> \
         ((x4 : CReal.le x1 x2) -> CReal.le x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_le_add),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.le x0 x1) -> ((x5 : CReal.le x2 x3) -> \
         CReal.le (CReal.add x0 x2) (CReal.add x1 x3)))))))"
    );
    // The order is the order OF this setoid, not an unexamined relation that
    // happens to satisfy three laws.
    assert_eq!(
        rendered(&mut kernel, p.le_of_equiv),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Equiv x0 x1) -> CReal.le x0 x1)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.equiv_of_le_le),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.le x0 x1) -> \
         ((x3 : CReal.le x1 x0) -> CReal.Equiv x0 x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_le_one_zero),
        "Not (CReal.le CReal.one CReal.zero)"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         CReal.Equiv (CReal.add x0 x2) (CReal.add x1 x3)))))))"
    );
    // The seven strict-order laws, also VERBATIM: like the three `le` laws,
    // none of them mentions `Eq`, so the `Real` package's statement is the
    // statement proved here — no `Equiv` restatement, nothing weakened.
    assert_eq!(
        rendered(&mut kernel, p.lt_irrefl),
        "((x0 : CReal) -> Not (CReal.lt x0 x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_trans),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.lt x0 x1) -> \
         ((x4 : CReal.lt x1 x2) -> CReal.lt x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_of_lt_of_le),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.lt x0 x1) -> \
         ((x4 : CReal.le x1 x2) -> CReal.lt x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_of_le_of_lt),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.le x0 x1) -> \
         ((x4 : CReal.lt x1 x2) -> CReal.lt x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.le_of_lt),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.lt x0 x1) -> CReal.le x0 x1)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.zero_lt_one),
        "CReal.lt CReal.zero CReal.one"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_lt_add_of_le_of_lt),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.le x0 x1) -> ((x5 : CReal.lt x2 x3) -> \
         CReal.lt (CReal.add x0 x2) (CReal.add x1 x3)))))))"
    );
    // The two relation congruences of the setoid telescope's equality slot.
    assert_eq!(
        rendered(&mut kernel, p.le_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         ((x6 : CReal.le x0 x2) -> CReal.le x1 x3)))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         ((x6 : CReal.lt x0 x2) -> CReal.lt x1 x3)))))))"
    );
    // The five product laws. Two of the 22 in `Equiv` form, three verbatim —
    // and `mul_nonneg`/`sq_nonneg` are the `Real` package's statements
    // unchanged, so a weakened restatement would show up here as a diff.
    assert_eq!(
        rendered(&mut kernel, p.mul_comm),
        "((x0 : CReal) -> ((x1 : CReal) -> \
         CReal.Equiv (CReal.mul x0 x1) (CReal.mul x1 x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_one),
        "((x0 : CReal) -> CReal.Equiv (CReal.mul x0 CReal.one) x0)"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_zero),
        "((x0 : CReal) -> CReal.Equiv (CReal.mul x0 CReal.zero) CReal.zero)"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_nonneg),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.le CReal.zero x0) -> \
         ((x3 : CReal.le CReal.zero x1) -> CReal.le CReal.zero (CReal.mul x0 x1)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.sq_nonneg),
        "((x0 : CReal) -> CReal.le CReal.zero (CReal.mul x0 x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_assoc),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> \
         CReal.Equiv (CReal.mul (CReal.mul x0 x1) x2) \
         (CReal.mul x0 (CReal.mul x1 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.left_distrib),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> \
         CReal.Equiv (CReal.mul x0 (CReal.add x1 x2)) \
         (CReal.add (CReal.mul x0 x1) (CReal.mul x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_le_mul_of_nonneg_left),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> \
         ((x3 : CReal.le CReal.zero x0) -> ((x4 : CReal.le x1 x2) -> \
         CReal.le (CReal.mul x0 x1) (CReal.mul x0 x2))))))"
    );
    // The fifth congruence obligation — not one of the 22, and the R4
    // prerequisite ADR-0468 calls the setoid's real tax.
    assert_eq!(
        rendered(&mut kernel, p.mul_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         CReal.Equiv (CReal.mul x0 x2) (CReal.mul x1 x3)))))))"
    );
    // The two witnesses that stop the five above being satisfiable by a
    // degenerate product. `ofRat_mul` pins the OPERATION on the embedded `ℚ`;
    // `not_equiv_mul_one_one_zero` exhibits a separated pair by computation.
    assert_eq!(
        rendered(&mut kernel, p.of_rat_mul),
        "((x0 : Rat) -> ((x1 : Rat) -> \
         CReal.Equiv (CReal.mul (CReal.ofRat x0) (CReal.ofRat x1)) \
         (CReal.ofRat (Rat.mul x0 x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_equiv_mul_one_one_zero),
        "Not (CReal.Equiv (CReal.mul CReal.one CReal.one) CReal.zero)"
    );
    // The canonical bound is a bound on EVERY sample, not just the zeroth —
    // which is the whole reason `CReal.mul`'s index can be a fixed function of
    // the two factors.
    assert_eq!(
        rendered(&mut kernel, p.bound_within),
        "((x0 : CReal) -> ((x1 : AxNat) -> \
         CReal.Within (CReal.seq x0 x1) \
         (Rat.natDivSucc (AxNat.succ (CReal.bound x0)) AxNat.zero)))"
    );
}

/// **The product is not the degenerate one**, and the check is by computation.
///
/// `CReal.mul_zero`, `CReal.mul_comm` and `CReal.sq_nonneg` all hold — with
/// empty axiom footprints — of `fun _ _ => CReal.zero`. So does every
/// footprint check that only asks whether they were *derived*. This asks the
/// kernel for a closed instance instead: `1 · 1` is `Equiv`-equal to `1`, and
/// `Equiv 1 0` is refuted.
#[test]
fn the_product_is_not_the_constant_zero() {
    let (kernel, p) = built();
    // PRESENCE FIRST. `Kernel::axiom_footprint` of a name that was interned but
    // never declared is the empty vector, which is indistinguishable from
    // "declared and axiom-free" — the failure mode this repository keeps
    // rediscovering. Assert the declaration exists and is a Theorem before
    // reading anything off it.
    assert!(
        matches!(
            kernel.environment().get(p.not_equiv_mul_one_one_zero),
            Some(Declaration::Theorem { .. })
        ),
        "CReal.not_equiv_mul_one_one_zero must be a checked theorem: without it \
         nothing separates any product from zero, and mul_zero / mul_comm / \
         sq_nonneg all still hold of `fun _ _ => zero`"
    );
    assert!(
        matches!(
            kernel.environment().get(p.of_rat_mul),
            Some(Declaration::Theorem { .. })
        ),
        "CReal.ofRat_mul must be a checked theorem: without it nothing pins \
         CReal.mul to Rat.mul anywhere at all"
    );
    let footprint = kernel.axiom_footprint(p.not_equiv_mul_one_one_zero);
    assert!(
        footprint.is_empty(),
        "the product's discrimination witness rests on {:?}",
        footprint
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect::<Vec<_>>()
    );
}

/// The negative control for the product witness: the **same script**, pointed
/// at a claim that is false.
///
/// `Not (Equiv (mul one one) one)` is false — `mul_one` proves the positive
/// form — and it differs from the proved witness in one constant. The kernel
/// must refuse it, which is what says the witness is checking the pair it
/// names rather than any pair.
#[test]
fn the_product_discrimination_route_cannot_refute_mul_one_one_one() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_eq_rewrite, rmul, rone};

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);

    let cone = d.kernel().const_(p.one, vec![]);
    let product = d.const_app(p.mul, &[cone, cone]);
    let claim = super::equiv(&mut d, p, product, cone);
    let stmt = d.not(claim);

    let unit = rone(&mut d, rat);
    let homomorphism = d.lemma(p.of_rat_mul, &[unit, unit]);
    let square = rmul(&mut d, unit, unit);
    let collapse = d.lemma(rat.mul_one, &[unit]);
    let at_one = rat_eq_rewrite(&mut d, square, unit, collapse, homomorphism, &|d, t| {
        let embedded = d.const_app(p.of_rat, &[t]);
        super::equiv(d, p, product, embedded)
    });
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let reversed = d.lemma(p.equiv_symm, &[product, cone, h]);
    let chained = d.lemma(p.equiv_trans, &[cone, product, cone, reversed, at_one]);
    let absurd = d.lemma(p.not_zero_one, &[chained]);
    let value = d.lam_fv(h_fv, claim, absurd);
    let name = d.kernel().name_str(anon, "Check.not_mul_one_one_one");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stmt,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `Not (CReal.Equiv (mul one one) one)`, which \
         contradicts CReal.mul_one — the product witness proves nothing"
    );
}

/// **`CReal.lt` is the strict order ADR-0468 asks for, not a negation.**
///
/// The definition is asserted verbatim because the two rejected shapes differ
/// from it only in the body: `Not (le y x)` would render as a `Not`, and
/// `∃ n : Nat, …` would quantify over `Nat`. This quantifies over a **rational
/// gap**, which is what makes `le_of_lt` constructive and `lt_trans` carry its
/// witness through untouched.
#[test]
fn lt_quantifies_over_a_positive_rational_gap() {
    let (kernel, p) = built();
    let value = match kernel.environment().get(p.lt).expect("CReal.lt declared") {
        Declaration::Definition { value, .. } => *value,
        other => panic!("{other:?} is not a definition"),
    };
    let rendered = kernel
        .render_lean(value)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        rendered,
        "fun (x0 : CReal) => fun (x1 : CReal) => Exists.{1} Rat \
         (fun (x2 : Rat) => And (Rat.lt Rat.zero x2) \
         (CReal.le (CReal.add x0 (CReal.ofRat x2)) x1))"
    );
}

/// **`CReal.lt` is neither empty nor total**, and both halves are needed.
///
/// Six of the seven strict-order laws *consume* a `lt`, so all six hold —
/// footprint-free — of the empty relation. `zero_lt_one` is the only one that
/// produces an inhabitant, and `lt_irrefl` is the only one that refuses a pair.
/// Together they are the discrimination witness the axiom footprint cannot see.
#[test]
fn the_strict_order_discriminates() {
    let (kernel, p) = built();
    for (label, name) in [
        ("CReal.zero_lt_one", p.zero_lt_one),
        ("CReal.lt_irrefl", p.lt_irrefl),
    ] {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} must be declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "{label} must be a checked Theorem — an axiom would witness nothing"
        );
        assert!(
            kernel.axiom_footprint(name).is_empty(),
            "{label} must be axiom-free"
        );
    }
}

/// The negative control for `zero_lt_one`: the **same script**, with the two
/// constants swapped.
///
/// `lt one zero` is false, and the script that proves `lt zero one` reaches it
/// through `Rat.zero_add` on the sampled sum `0 + 1`. Pointed at `one + 1` that
/// rewrite does not apply, and the kernel must **refuse** — which is what says
/// the strict order is reading which sequence is being sampled rather than
/// merely assembling a bound.
#[test]
fn the_zero_lt_one_route_cannot_prove_one_lt_zero() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rchain, rcongr, rone, rsymm, rzero};

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);
    let nat = d.nat_ty();

    let zero_rat = rzero(&mut d, rat);
    let one_rat = rone(&mut d, rat);
    // The two changed tokens: the claim is `lt one zero`, not `lt zero one`.
    let zero_real = d.kernel().const_(p.zero, vec![]);
    let one_real = d.kernel().const_(p.one, vec![]);

    let bounded = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sum = radd(&mut d, one_rat, one_rat);
        let quantity = rsub(&mut d, rat, sum, zero_rat);
        let bound = super::div_succ(&mut d, p, 2, n);
        let unpad = d.lemma(rat.zero_add, &[one_rat]);
        let step = rcongr(&mut d, sum, one_rat, unpad, &|d, t| {
            rsub(d, rat, t, zero_rat)
        });
        let degenerate = rsub(&mut d, rat, one_rat, zero_rat);
        let collapse = d.lemma(rat.sub_self, &[one_rat]);
        let (_, to_zero) = rchain(
            &mut d,
            quantity,
            &[(degenerate, step), (zero_rat, collapse)],
        );
        let back = rsymm(&mut d, quantity, zero_rat, to_zero);
        let two = d.num(2);
        let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
        let at_index = rat_eq_rewrite(&mut d, zero_rat, quantity, back, nonneg, &|d, t| {
            crate::rat_prelude::ops::rle(d, rat, t, bound)
        });
        d.lam_fv(n_fv, nat, at_index)
    };
    let positive = crate::rat_prelude::ops::rlt(&mut d, rat, zero_rat, one_rat);
    let embedded = super::embed(&mut d, p, one_rat);
    let shifted = super::cadd(&mut d, p, one_real, embedded);
    let reached = super::cle(&mut d, p, shifted, zero_real);
    let strict = d.lemma(rat.zero_lt_one, &[]);
    let pair = super::and_intro(&mut d, p, positive, reached, strict, bounded);
    let value = super::gap_intro(&mut d, p, one_real, zero_real, one_rat, pair);
    let ty = super::clt(&mut d, p, one_real, zero_real);
    let name = d.kernel().name_str(anon, "Check.one_lt_zero");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `CReal.lt CReal.one CReal.zero`, which contradicts \
         CReal.lt_irrefl through lt_trans — the strict order proves nothing"
    );
}

/// **The carrier is inhabited.** Everything above is a statement about the
/// inhabitants of `CReal`; if `CReal.Regular` had no solutions the carrier
/// would be empty, `refl`/`symm`/`trans` would all hold vacuously, and the
/// axiom footprints would still be empty. `CReal.ofRat` is a *checked*
/// definition, so the kernel accepted a regularity proof for a concrete
/// sequence.
#[test]
fn the_carrier_is_inhabited() {
    let (kernel, p) = built();
    let declaration = kernel
        .environment()
        .get(p.of_rat)
        .expect("CReal.ofRat must be declared");
    assert!(
        matches!(declaration, Declaration::Definition { .. }),
        "CReal.ofRat must be a Definition — an axiom would not witness anything"
    );
}

/// **`CReal.Equiv` discriminates.** An equivalence relation that relates
/// everything is an equivalence relation, and worthless; this exhibits two
/// `CReal`s it separates.
#[test]
fn equiv_is_not_the_total_relation() {
    let (kernel, p) = built();
    assert!(
        matches!(
            kernel.environment().get(p.not_zero_one),
            Some(Declaration::Theorem { .. })
        ),
        "the discrimination witness must be a checked Theorem"
    );
}

/// The negative control for [`equiv_is_not_the_total_relation`]: the same proof
/// route, pointed at a pair `Equiv` does **not** separate.
///
/// `Equiv.not_zero_one` works because `−1/2 ≤ −1` reduces to `Nat.le 1 0`. If
/// the kernel's reduction were not actually deciding that, the identical script
/// with `ofRat 0` on **both** sides would also go through — and it would prove
/// `Not (Equiv x x)`, contradicting `Equiv.refl`. It must be **refused**.
#[test]
fn the_discrimination_route_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::rzero;

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);

    let zero_rat = rzero(&mut d, rat);
    let left = d.const_app(p.of_rat, &[zero_rat]);
    let claim = super::equiv(&mut d, p, left, left);
    let stmt = d.not(claim);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let index = d.num(3);
    let instance = d.apply(h, &[index]);
    let a = super::sample(&mut d, p, left, index);
    let difference = rsub(&mut d, rat, a, a);
    let bound = super::div_succ(&mut d, p, 2, index);
    let (lower, _upper) = super::halves(&mut d, p, difference, bound, instance);
    let zero_nat = d.zero();
    let absurd = d.lemma(rat.int.nat.not_succ_le_zero, &[zero_nat, lower]);
    let value = d.lam_fv(h_fv, claim, absurd);
    let name = d.kernel().name_str(anon, "Check.not_zero_zero");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stmt,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `Not (CReal.Equiv (ofRat 0) (ofRat 0))`, which \
         contradicts CReal.Equiv.refl — the discrimination witness proves nothing"
    );
}

/// The negative control for `add_zero`: the **same script**, pointed at a law
/// that is false.
///
/// `add_zero` is the first law whose two sides are not equal at any index, so
/// what carries it is regularity plus a bound comparison — and a bound
/// comparison is exactly the kind of argument that would still go through if
/// the kernel were not actually looking at which sequence is being sampled.
/// `Equiv (add x one) x` is false, differs from the proved statement in one
/// constant, and must be **refused**.
#[test]
fn the_add_zero_route_cannot_prove_add_one() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rsymm, rzero};

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);
    let carrier = super::creal_ty(&mut d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    // The one changed token: `CReal.one` where the proved law has `CReal.zero`.
    let one_real = d.kernel().const_(p.one, vec![]);
    let left = d.const_app(p.add, &[x, one_real]);
    let body = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let index = super::shift(&mut d, n);
        let deep = super::sample(&mut d, p, x, index);
        let shallow = super::sample(&mut d, p, x, n);
        let difference = rsub(&mut d, rat, deep, shallow);
        let bound = super::modulus(&mut d, p, index, n);
        let goal_bound = super::div_succ(&mut d, p, 2, n);
        let source = d.lemma(p.regular, &[x, index, n]);
        let order = super::shifted_bound_le(&mut d, p, n);
        let widened = super::weaken(&mut d, p, difference, bound, goal_bound, source, order);
        let zero_rat = rzero(&mut d, rat);
        let padded = radd(&mut d, deep, zero_rat);
        let collapse = d.lemma(rat.add_zero, &[deep]);
        let restore = rsymm(&mut d, padded, deep, collapse);
        let at_index = rat_eq_rewrite(&mut d, deep, padded, restore, widened, &|d, t| {
            let quantity = rsub(d, rat, t, shallow);
            super::within(d, p, quantity, goal_bound)
        });
        d.lam_fv(n_fv, nat, at_index)
    };
    let value = d.lam_fv(x_fv, carrier, body);
    let ty = {
        let conclusion = super::equiv(&mut d, p, left, x);
        d.pi_fv(x_fv, carrier, conclusion)
    };
    let name = d.kernel().name_str(anon, "Check.add_one");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `Equiv (add x one) x`, so the add_zero route is not \
         checking which sequence the shifted index samples"
    );
}

/// **`CReal.le` discriminates.** `le_refl`, `le_trans` and `add_le_add` all
/// hold — footprint-free — of the relation that relates every pair, so an
/// order that separates nothing would satisfy every law proved about it. This
/// is the negative control for `CReal.not_le_one_zero`: the identical script,
/// pointed at `le zero one`, which is TRUE and must therefore be refused as a
/// `Not`.
#[test]
fn the_order_discrimination_route_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);
    let nat_p = rat.int.nat;

    // The two constants, swapped: `le zero one` holds, so `Not` of it does not.
    let one_real = d.kernel().const_(p.one, vec![]);
    let zero_real = d.kernel().const_(p.zero, vec![]);
    let claim = d.const_app(p.le, &[zero_real, one_real]);
    let stmt = d.not(claim);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let index = d.num(3);
    let instance = d.apply(h, &[index]);
    let one_nat = d.num(1);
    let zero_nat = d.zero();
    let stripped = d.lemma(nat_p.le_of_succ_le_succ, &[one_nat, zero_nat, instance]);
    let absurd = d.lemma(nat_p.not_succ_le_zero, &[zero_nat, stripped]);
    let value = d.lam_fv(h_fv, claim, absurd);
    let name = d.kernel().name_str(anon, "Check.not_le_zero_one");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stmt,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `Not (CReal.le CReal.zero CReal.one)`, which is false — \
         the order discrimination witness proves nothing"
    );
}

/// **The headline count, read out of the kernel.**
///
/// `CRealPrelude::ordered_ring_laws` is the 22 in the `Real` package's own
/// declaration order — the same order `RatPrelude::ring_laws` uses — and every
/// entry must be a checked `Theorem` with an empty axiom footprint. A dropped,
/// duplicated or demoted law fails here rather than shrinking a sentence in a
/// document nobody re-derives.
#[test]
fn all_twenty_two_ordered_ring_laws_are_checked_theorems_over_creal() {
    let (kernel, p) = built();
    let laws = p.ordered_ring_laws();
    assert_eq!(laws.len(), 22);
    let mut names: Vec<String> = laws
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    names.sort();
    names.dedup();
    assert_eq!(
        names.len(),
        22,
        "the ordered-ring law list must have 22 DISTINCT entries; a repeated \
         name would inflate the count without proving anything"
    );
    for (index, law) in p.ordered_ring_laws().into_iter().enumerate() {
        let rendered = kernel.display_name(law).to_string();
        let declaration = kernel
            .environment()
            .get(law)
            .unwrap_or_else(|| panic!("ring law #{index} ({rendered}) is not declared at all"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "ring law #{index} ({rendered}) must be a checked Theorem"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(law)
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect();
        assert!(
            footprint.is_empty(),
            "ring law #{index} ({rendered}) rests on {footprint:?}"
        );
    }
}

/// The `CReal` and `Rat` law lists are the **same 22 laws in the same order**,
/// name for name under their own namespaces.
///
/// Without this the two lists could drift — `CReal` could quietly omit
/// `mul_assoc` and add a second `mul_comm` — and both would still be "22
/// checked theorems". `build_rat_model_of_arith` pairs `RatPrelude::ring_laws`
/// positionally with the `Real` package, so this is what says `CReal`'s list is
/// the same interface and not merely the same length.
#[test]
fn the_creal_law_list_matches_the_rat_law_list_position_by_position() {
    let (kernel, p) = built();
    let real: Vec<String> = p
        .ordered_ring_laws()
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    let rational: Vec<String> = p
        .rat
        .ring_laws()
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    let strip = |full: &str| -> String { full.split('.').skip(1).collect::<Vec<_>>().join(".") };
    let real_tails: Vec<String> = real.iter().map(|name| strip(name)).collect();
    let rational_tails: Vec<String> = rational.iter().map(|name| strip(name)).collect();
    assert_eq!(
        real_tails, rational_tails,
        "CReal's ordered-ring law list must be the SAME 22 laws in the SAME \
         order as Rat's, or the two are not the same interface"
    );
}

/// The apartness laws say what Bishop says they say, rendered verbatim.
///
/// The statements are the point here, not the footprints: `Apart` defined as
/// `Not ∘ Equiv` would satisfy symmetry, irreflexivity and the congruence with
/// an empty footprint apiece, and it is exactly the relation the inverse cannot
/// be defined over. So the *definition* is asserted too, through
/// `CReal.apart_zero_one` — which is `zero_lt_one` under `Or.inl` and could not
/// be proved for a relation that separates nothing.
#[test]
fn the_apartness_laws_have_the_statements_bishop_specifies() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.apart_symm),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Apart x0 x1) -> CReal.Apart x1 x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.apart_irrefl),
        "((x0 : CReal) -> Not (CReal.Apart x0 x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.apart_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         ((x6 : CReal.Apart x0 x2) -> CReal.Apart x1 x3)))))))"
    );
    // ONE-WAY. The converse is Markov's principle; nothing here proves it and
    // nothing here assumes it.
    assert_eq!(
        rendered(&mut kernel, p.not_equiv_of_apart),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Apart x0 x1) -> \
         Not (CReal.Equiv x0 x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.apart_zero_one),
        "CReal.Apart CReal.zero CReal.one"
    );
}

/// **The missing structure is a theorem.** `CReal.no_total_inverse` refutes
/// every total multiplicative inverse at once, so "the inverse is partial"
/// is a proved obstruction rather than a scoping note — the standard
/// `Complex.no_compatible_order` set.
#[test]
fn no_function_on_all_of_creal_is_a_multiplicative_inverse() {
    let (mut kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.no_total_inverse)
        .expect("CReal.no_total_inverse must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };
    let rendered = kernel
        .render_lean(ty)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        rendered,
        "((x0 : ((x0 : CReal) -> CReal)) -> \
         Not (((x1 : CReal) -> CReal.Equiv (CReal.mul x1 (x0 x1)) CReal.one)))"
    );
    let footprint: Vec<String> = kernel
        .axiom_footprint(p.no_total_inverse)
        .into_iter()
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    assert!(
        footprint.is_empty(),
        "the refutation of a total inverse rests on {footprint:?}"
    );
}

/// The negative control for [`no_function_on_all_of_creal_is_a_multiplicative_inverse`]:
/// the **identical script**, with `CReal.one` replaced by `CReal.zero` in the
/// statement, is REFUSED.
///
/// `∀ f, ¬ ∀ x, x · f x ≈ 0` is false — `f := fun _ => zero` satisfies the
/// inner law by `mul_zero` — so a script that proved it would prove anything.
/// The refusal is what says `no_total_inverse` closes on the *content* of
/// `Equiv.not_zero_one` and not on a shape that would go through for any
/// right-hand side.
#[test]
fn the_no_total_inverse_route_cannot_refute_a_universally_zero_product() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let function_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    // The one changed token: the target of the inner law is `zero`, not `one`.
    let target = d.kernel().const_(p.zero, vec![]);
    let law = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let applied = d.apply(f, &[x]);
        let product = d.const_app(p.mul, &[x, applied]);
        let claim = d.const_app(p.equiv, &[product, target]);
        d.pi_fv(x_fv, carrier, claim)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero = d.kernel().const_(p.zero, vec![]);
    let reciprocal = d.apply(f, &[zero]);
    let product = d.const_app(p.mul, &[zero, reciprocal]);
    let flipped = d.const_app(p.mul, &[reciprocal, zero]);
    let commuted = d.lemma(p.mul_comm, &[zero, reciprocal]);
    let vanishes = d.lemma(p.mul_zero, &[reciprocal]);
    let collapses = d.lemma(p.equiv_trans, &[product, flipped, zero, commuted, vanishes]);
    let restored = d.lemma(p.equiv_symm, &[product, zero, collapses]);
    let at_zero = d.apply(h, &[zero]);
    let degenerate = d.lemma(p.equiv_trans, &[zero, product, target, restored, at_zero]);
    let refuted = d.lemma(p.not_zero_one, &[]);
    let contradiction = d.apply(refuted, &[degenerate]);

    let value = {
        let with_h = d.lam_fv(h_fv, law, contradiction);
        d.lam_fv(f_fv, function_ty, with_h)
    };
    let ty = {
        let negated = d.not(law);
        d.pi_fv(f_fv, function_ty, negated)
    };
    let name = d.kernel().name_str(anon, "Check.no_total_annihilator");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted a refutation of `∀ x, x · f x ≈ 0`, which is FALSE \
         (take f := fun _ => zero). The no_total_inverse script would then close \
         for any right-hand side, and its content would be nil."
    );
}
