//! Tests for the complex prelude.
//!
//! Every assertion here is read **out of the kernel** — the environment, the
//! declaration kinds, `Kernel::axiom_footprint` — and never out of source text
//! or a doc comment.

use super::{ComplexPrelude, build_complex_prelude};
use crate::{Declaration, Kernel};

/// A built `Complex` kernel, as a **clone of one template**.
///
/// The argument is `creal_tests`' verbatim: prelude construction is a
/// deterministic function of the empty kernel, so the template equals what a
/// fresh build would produce, and every declaration in it entered through
/// `Kernel::add_declaration` under the full type checker exactly once.
/// `complex_prelude_builds` deliberately does **not** use this — it is the test
/// that exercises the real build.
fn built() -> (Kernel, ComplexPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, ComplexPrelude)> = OnceLock::new();
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        let mut kernel = Kernel::new();
        let prelude = build_complex_prelude(&mut kernel).expect("Complex prelude must build");
        (kernel, prelude)
    });
    (kernel.clone(), *prelude)
}

/// The build itself, with the kernel's rejection **rendered**: a `Debug` of
/// `KernelError` says nothing about what was refused.
#[test]
fn complex_prelude_builds() {
    let mut kernel = Kernel::new();
    match build_complex_prelude(&mut kernel) {
        Ok(_) => {}
        Err(error) => {
            let nat = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
            let mut dev = crate::NatDev::new(&mut kernel, nat);
            let explained = crate::NatOps::explain(&mut dev, &error);
            panic!("the kernel refused a complex proof: {explained}");
        }
    }
}

/// Building twice is a no-op, not a duplicate-declaration error.
#[test]
fn complex_prelude_is_idempotent() {
    let (mut kernel, first) = built();
    let before = kernel.environment().iter().count();
    let second = build_complex_prelude(&mut kernel).expect("rebuild must succeed");
    assert_eq!(first, second, "a rebuild must return the same handles");
    assert_eq!(
        before,
        kernel.environment().iter().count(),
        "a rebuild must not add declarations"
    );
}

/// **The headline claim, measured.** ℂ over the constructed ℝ costs zero
/// trusted declarations: no `Quot.sound`, no `funext`, no `propext`, no
/// classical axiom, nothing.
///
/// `Declaration::Axiom` alone is *not* the trusted surface — `Opaque` has no
/// proof body and `Quotient` admits `Quot.sound` — so all three kinds are
/// enumerated.
#[test]
fn the_constructed_complexes_add_no_trusted_declaration() {
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
        "the complex development must assume nothing, found: {trusted:?}"
    );
}

/// The named surface of [`ComplexPrelude`], declaration by declaration: each is
/// present, each is a **checked** `Definition`/`Theorem`/`Inductive` and never
/// an `Axiom` or `Opaque`, and each has an **empty** axiom footprint.
#[test]
fn every_named_complex_declaration_is_checked_and_footprint_free() {
    let (kernel, p) = built();
    let named = [
        ("Complex", p.complex),
        ("Complex.mk", p.mk),
        ("Complex.rec", p.rec),
        ("Complex.re", p.re),
        ("Complex.im", p.im),
        ("Complex.re_congr", p.re_congr),
        ("Complex.im_congr", p.im_congr),
        ("Complex.Equiv", p.equiv),
        ("Complex.Equiv.refl", p.equiv_refl),
        ("Complex.Equiv.symm", p.equiv_symm),
        ("Complex.Equiv.trans", p.equiv_trans),
        ("Complex.ofReal", p.of_real),
        ("Complex.I", p.i),
        ("Complex.zero", p.zero),
        ("Complex.one", p.one),
        ("Complex.add", p.add),
        ("Complex.neg", p.neg),
        ("Complex.mul", p.mul),
        ("Complex.add_congr", p.add_congr),
        ("Complex.neg_congr", p.neg_congr),
        ("Complex.mul_congr", p.mul_congr),
        ("Complex.conj_congr", p.conj_congr),
        ("Complex.add_comm", p.add_comm),
        ("Complex.add_assoc", p.add_assoc),
        ("Complex.add_zero", p.add_zero),
        ("Complex.add_neg", p.add_neg),
        ("Complex.mul_comm", p.mul_comm),
        ("Complex.mul_assoc", p.mul_assoc),
        ("Complex.mul_one", p.mul_one),
        ("Complex.mul_zero", p.mul_zero),
        ("Complex.left_distrib", p.left_distrib),
        ("Complex.ofReal_add", p.of_real_add),
        ("Complex.ofReal_mul", p.of_real_mul),
        ("Complex.I_sq", p.i_sq),
        ("Complex.Equiv.not_zero_one", p.not_zero_one),
        ("Complex.Equiv.not_zero_I", p.not_zero_i),
        ("Complex.re_add_im", p.re_add_im),
        ("Complex.conj", p.conj),
        ("Complex.conj_conj", p.conj_conj),
        ("Complex.conj_add", p.conj_add),
        ("Complex.conj_mul", p.conj_mul),
        ("Complex.conj_sub", p.conj_sub),
        ("Complex.conj_ofReal", p.conj_of_real),
        ("Complex.conj_I", p.conj_i),
        ("Complex.eq_conj_iff_real", p.eq_conj_iff_real),
        ("Complex.normSq", p.norm_sq),
        ("Complex.mul_conj", p.mul_conj),
        ("Complex.normSq_nonneg", p.norm_sq_nonneg),
        ("Complex.normSq_conj", p.norm_sq_conj),
        ("Complex.normSq_mul", p.norm_sq_mul),
        (
            "Complex.normSq_eq_zero_of_eq_zero",
            p.norm_sq_eq_zero_of_eq_zero,
        ),
        (
            "Complex.eq_zero_of_normSq_eq_zero",
            p.eq_zero_of_norm_sq_eq_zero,
        ),
        ("Complex.normSq_eq_zero_iff", p.norm_sq_eq_zero_iff),
        ("Complex.normSq_add", p.norm_sq_add),
        ("Complex.no_compatible_order", p.no_compatible_order),
        ("Complex.inv", p.inv),
        ("Complex.mul_inv_cancel", p.mul_inv_cancel),
        ("Complex.inv_congr", p.inv_congr),
        ("Complex.div", p.div),
        ("Complex.div_self", p.div_self),
        ("Complex.Apart", p.apart),
        ("Complex.apart_irrefl", p.apart_irrefl),
        ("Complex.apart_symm", p.apart_symm),
        ("Complex.apart_of_normSq_pos", p.apart_of_normsq_pos),
        ("Complex.mul_apart_zero", p.mul_apart_zero),
        (
            "Complex.mul_eq_zero_not_both_apart_zero",
            p.mul_eq_zero_not_both_apart_zero,
        ),
    ];
    for (label, name) in named {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} must be declared"));
        assert!(
            !matches!(
                declaration,
                Declaration::Axiom { .. } | Declaration::Opaque { .. }
            ),
            "{label} must be checked, not assumed"
        );
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} must have an empty axiom footprint, found {:?}",
            footprint
                .iter()
                .map(|n| kernel.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}

/// **9 of 9**, read out of the kernel through
/// [`ComplexPrelude::ring_laws`] and nowhere else: nine *distinct*
/// declarations, every one a checked `Theorem` with an empty footprint.
///
/// A dropped or duplicated law fails here rather than shrinking a sentence in a
/// document.
#[test]
fn the_nine_ring_laws_are_distinct_checked_theorems() {
    let (kernel, p) = built();
    let laws = p.ring_laws();
    let mut seen: Vec<_> = laws.to_vec();
    seen.sort_unstable();
    seen.dedup();
    assert_eq!(seen.len(), 9, "the nine ring laws must be distinct");
    for name in laws {
        let declaration = kernel
            .environment()
            .get(name)
            .expect("a ring law must be declared");
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "{} must be a Theorem",
            kernel.display_name(name)
        );
        assert!(
            kernel.axiom_footprint(name).is_empty(),
            "{} must have an empty axiom footprint",
            kernel.display_name(name)
        );
    }
}

/// **No order is invented.** `Complex.le` and `Complex.lt` must not exist:
/// [`ComplexPrelude::no_compatible_order`] proves that any such pair satisfying
/// seven of the `Real` package's order laws is contradictory, so declaring one
/// here would be declaring something the same module refutes.
///
/// `inv`/`div` are deliberately **not** in this list: `Complex.inv` and
/// `Complex.div` exist and need no order on `Complex` at all, since the
/// separating witness is `CReal.PosBound (normSq z) k`, phrased over the
/// already-ordered `CReal.le` rather than any order on `Complex` itself.
/// `abs` is what an order on `Complex` would actually be needed for.
#[test]
fn no_order_relation_is_declared_on_complex() {
    let (kernel, p) = built();
    for forbidden in ["le", "lt", "abs"] {
        let mut probe = kernel.clone();
        let name = probe.name_str(p.complex, forbidden);
        assert!(
            probe.environment().get(name).is_none(),
            "Complex.{forbidden} must not be declared"
        );
    }
}

/// The three witnesses that stop the laws above being true of a degenerate
/// structure, and each of them fails for a *different* degenerate candidate.
///
/// - `Equiv.not_zero_one` refuses the total relation on the real component;
/// - `Equiv.not_zero_I` refuses one that ignores the imaginary component —
///   `not_zero_one` alone would not notice;
/// - `ofReal_mul` and `I_sq` together pin the product: `mul_comm`, `mul_zero`
///   and `left_distrib` all hold, footprint-free, of `fun _ _ => zero`.
#[test]
fn the_discrimination_witnesses_are_theorems() {
    let (kernel, p) = built();
    for (label, name) in [
        ("Complex.Equiv.not_zero_one", p.not_zero_one),
        ("Complex.Equiv.not_zero_I", p.not_zero_i),
        ("Complex.ofReal_mul", p.of_real_mul),
        ("Complex.I_sq", p.i_sq),
    ] {
        assert!(
            matches!(
                kernel.environment().get(name),
                Some(Declaration::Theorem { .. })
            ),
            "{label} must be a checked Theorem"
        );
    }
}

/// The ring calculus is a **decision** procedure, not a search: an identity
/// that is not a consequence of the commutative-ring laws is refused loudly at
/// build time rather than handed to the kernel as a term it will reject a
/// thousand nodes deep.
///
/// `x + x` and `x` have different normal forms — coefficients are deliberately
/// not collected, so the two multisets differ by one monomial.
#[test]
#[should_panic(expected = "different normal forms")]
fn the_ring_calculus_refuses_a_false_identity() {
    use crate::int_prelude::ops::IntDev;

    let mut kernel = Kernel::new();
    let p = crate::creal::build_creal_prelude(&mut kernel).expect("CReal must build");
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let x = super::ring::cone(&mut d, p);
    let atom = super::ring::RExpr::Atom(x);
    let doubled = super::ring::RExpr::add(atom.clone(), atom.clone());
    let _ = super::ring::ring_proof(&mut d, p, &doubled, &atom);
}

/// ...and it **accepts** the identity one monomial away from that one, with the
/// emitted term type-checked by the kernel rather than merely built. So the
/// test above is measuring the normal-form comparison, not a build that could
/// not run at all.
#[test]
fn the_ring_calculus_proves_a_true_identity() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let mut kernel = Kernel::new();
    let p = crate::creal::build_creal_prelude(&mut kernel).expect("CReal must build");
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let x = super::ring::cone(&mut d, p);
    let atom = super::ring::RExpr::Atom(x);
    // `(x + (−x)) + x` and `x`: a cancellation and a reordering.
    let expression = super::ring::RExpr::add(
        super::ring::RExpr::add(atom.clone(), super::ring::RExpr::neg(atom.clone())),
        atom.clone(),
    );
    let proof = super::ring::ring_proof(&mut d, p, &expression, &atom);
    let source = super::ring::render(&mut d, p, &expression);
    let expected = super::ring::ceq(&mut d, p, source, x);
    let inferred = d
        .kernel()
        .infer(proof)
        .expect("the calculus must emit a well-typed proof");
    assert!(
        d.kernel().def_eq(inferred, expected),
        "the calculus must prove exactly the stated identity"
    );
}
