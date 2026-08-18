//! Tests for the real (setoid) prelude.

use super::{CRealPrelude, build_creal_prelude};
use crate::{Declaration, Kernel};

fn built() -> (Kernel, CRealPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_creal_prelude(&mut kernel).expect("CReal prelude must build");
    (kernel, prelude)
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
    let expected: [(&str, crate::NameId, &str); 31] = [
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
