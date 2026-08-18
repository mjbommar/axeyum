//! Tests for the rational prelude.

use super::{RatPrelude, build_rat_prelude};
use crate::{Declaration, Kernel};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("Rat prelude must build");
    (kernel, prelude)
}

#[test]
fn rat_prelude_is_axiom_free() {
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
        "the rational prelude must assume nothing, found: {trusted:?}"
    );
}

#[test]
fn every_named_declaration_exists() {
    let (kernel, p) = built();
    let expected = [
        ("zero", p.zero),
        ("one", p.one),
        ("le", p.le),
        ("lt", p.lt),
        ("inv", p.inv),
        ("sub", p.sub),
        ("div", p.div),
        ("mk_congr", p.mk_congr),
        ("eta", p.eta),
        ("ext", p.ext),
        ("le_total", p.le_total),
        ("lt_of_not_le", p.lt_of_not_le),
        ("normalize_add_normalize", p.normalize_add_normalize),
        ("normalize_mul_normalize", p.normalize_mul_normalize),
        ("mul_neg", p.mul_neg),
        ("neg_mul", p.neg_mul),
        ("mul_le_mul_of_nonneg_right", p.mul_le_mul_of_nonneg_right),
        ("mul_sub_mul", p.mul_sub_mul),
        ("bounds_mul", p.bounds_mul),
        ("neg_mul_le_of_bounds", p.neg_mul_le_of_bounds),
        ("natDivSucc_mul", p.nat_div_succ_mul),
        ("natDivSucc_le_one", p.nat_div_succ_le_one),
        ("natDivSucc_le_scaled", p.nat_div_succ_le_scaled),
        ("nat_index_compose", p.nat_index_compose),
        ("int_le_natAbs", p.int_le_nat_abs),
        ("int_neg_natAbs_le", p.int_neg_nat_abs_le),
        ("bounds_num", p.bounds_num),
    ];
    for (label, name) in expected {
        assert!(
            kernel.environment().get(name).is_some(),
            "Rat.{label} was interned but never declared"
        );
    }
}

/// The build itself, with the kernel's rejection **rendered** rather than
/// printed as opaque `ExprId`s. A `Debug` of `KernelError` says nothing about
/// what was refused; this says which two types failed to match.
#[test]
fn rat_prelude_builds() {
    let mut kernel = Kernel::new();
    match build_rat_prelude(&mut kernel) {
        Ok(_) => {}
        Err(error) => {
            let nat = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
            let mut dev = crate::NatDev::new(&mut kernel, nat);
            let explained = crate::NatOps::explain(&mut dev, &error);
            panic!("the kernel refused a rational proof: {explained}");
        }
    }
}

/// Every one of the 22 ordered-commutative-ring laws is a **checked theorem**
/// with an empty axiom footprint — not an axiom, not an opaque, not missing.
///
/// This fails if a law is dropped, demoted to an axiom, or quietly loses its
/// proof: it reads the kernel's own environment and footprint rather than
/// trusting that `build_rat_prelude` returned `Ok`.
#[test]
fn every_ordered_ring_law_is_a_checked_theorem() {
    let (kernel, p) = built();
    for (index, law) in p.ring_laws().into_iter().enumerate() {
        let rendered = kernel.display_name(law).to_string();
        let declaration = kernel
            .environment()
            .get(law)
            .unwrap_or_else(|| panic!("ring law #{index} ({rendered}) is not declared at all"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "ring law #{index} ({rendered}) must be a checked Theorem, found a different kind"
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

/// Dropping any single law is caught: the list this asserts against is
/// `RatPrelude::ring_laws`, which `build_rat_model_of_arith` pairs positionally
/// with the `Real` package, so a shortened or reordered list is a build failure
/// there rather than a silently weaker claim here.
#[test]
fn the_ring_law_list_has_exactly_twenty_two_distinct_entries() {
    let (kernel, p) = built();
    let mut names: Vec<String> = p
        .ring_laws()
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    assert_eq!(names.len(), 22);
    names.sort();
    names.dedup();
    assert_eq!(names.len(), 22, "the ring-law list repeats an entry");
}

/// ℚ is a model of the whole `Real` axiom package: every one of the 30
/// declarations is either an interpreted symbol or a law with a
/// kernel-checked, axiom-free witness.
#[test]
fn rationals_model_the_real_axioms() {
    let mut kernel = Kernel::new();
    let model = crate::build_rat_model_of_arith(&mut kernel).expect("ℚ must model the Real axioms");
    assert_eq!(model.laws.len(), 22);
    assert_eq!(model.symbols.len(), 8);
    for law in &model.laws {
        let footprint: Vec<String> = kernel
            .axiom_footprint(law.witness)
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect();
        let rendered = kernel.display_name(law.real).to_string();
        assert!(
            footprint.is_empty(),
            "the ℚ witness for {rendered} rests on {footprint:?}"
        );
    }
    // Completeness: no `Real` declaration escapes the interpretation.
    let interpreted: std::collections::HashSet<_> = model
        .symbols
        .iter()
        .map(|(real, _)| *real)
        .chain(model.laws.iter().map(|law| law.real))
        .collect();
    let missed: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. } => Some(*name),
            _ => None,
        })
        .filter(|name| !interpreted.contains(name))
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    assert!(
        missed.is_empty(),
        "these Real declarations have no ℚ interpretation: {missed:?}"
    );
}

// --- the Archimedean property (ADR-0468 phase R1) ---------------------------

/// Every declaration the Archimedean development adds is a **checked** theorem
/// (or definition) with an empty axiom footprint — read out of the kernel, not
/// off the diff.
#[test]
fn the_archimedean_development_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("natDivSucc", p.nat_div_succ, false),
        ("int_le_or_lt", p.int_le_or_lt, true),
        ("le_or_lt", p.le_or_lt, true),
        ("int_pos_of_pos", p.int_pos_of_pos, true),
        ("int_one_le_of_pos", p.int_one_le_of_pos, true),
        ("natDivSucc_lt_of_pos", p.nat_div_succ_lt_of_pos, true),
        ("le_of_le_add_natDivSucc", p.le_of_le_add_nat_div_succ, true),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// The Archimedean statement is the one ADR-0468 asks for, **verbatim**.
///
/// A footprint of `[]` on a theorem that says something weaker than intended is
/// the failure mode this repository keeps hitting, so this asserts the rendered
/// type rather than the declaration's existence: the hypothesis has to be
/// universally quantified over the index (`∀ j`, not one fixed `j`), the bound
/// has to be `Rat.natDivSucc k j` under that quantifier, and the conclusion has
/// to be the *unweakened* `Rat.le a b`.
#[test]
fn the_archimedean_statement_is_the_one_adr_0468_needs() {
    let (kernel, p) = built();
    let rendered = match kernel
        .environment()
        .get(p.le_of_le_add_nat_div_succ)
        .expect("the Archimedean property must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("the Archimedean property must be a Theorem, found {other:?}"),
    };
    let text = kernel.render_lean(rendered);
    let normalised: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
    assert_eq!(
        normalised,
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : AxNat) -> \
         ((x3 : ((x3 : AxNat) -> Rat.le x0 (Rat.add x1 (Rat.natDivSucc x2 x3)))) -> \
         Rat.le x0 x1))))",
        "the Archimedean statement drifted from ADR-0468's"
    );
}

/// `Rat.natDivSucc k j` really is the rational `k/(j+1)` **in lowest terms**,
/// checked by the kernel's own reduction (`Eq.refl` only typechecks if the two
/// sides are definitionally equal).
///
/// This is the guard that stops the Archimedean property being vacuous. A
/// `natDivSucc` that collapsed to `0` — or that never renormalised — would leave
/// every theorem above provable and every one of them worthless, and neither an
/// empty footprint nor the rendered statement would notice. `6/(1+1)` is chosen
/// because it exercises the `gcd` reduction: the answer is `3/1`, not `6/2`.
///
/// **Measured 2026-08-18, so the redundancy is stated rather than assumed.**
/// Mutating the development to `k/(j+2)` — consistently, in both the definition
/// and the witness proof — does not reach this test: the *kernel* refuses the
/// witness lemma first, because `Int.lt (ofNat (k·q)) (ofNat (k·q+2))` is no
/// longer `Nat.le_refl`, and all ten tests in this module die on the build. So
/// today `Rat.natDivSucc`'s meaning is pinned by the proofs that consume it, and
/// this test is defence for the refactor that re-proves the witness lemma some
/// other way and no longer pins it. Its own discriminating power is measured by
/// [`nat_div_succ_reduction_check_can_fail`], which requires the kernel to
/// **reject** a wrong numerator through the same `Eq.refl` route.
#[test]
fn nat_div_succ_computes_the_reduced_fraction() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    // `Rat.num (Rat.natDivSucc 6 1) = Int.ofNat 3` and `Rat.den … = 1`.
    let cases: [(&str, u32, u32, u32, u32); 3] = [
        ("six_halves", 6, 1, 3, 1),
        ("one_quarter", 1, 3, 1, 4),
        ("four_sixths", 4, 5, 2, 3),
    ];
    for (label, k, j, expected_num, expected_den) in cases {
        let numerator_arg = d.num(k);
        let index = d.num(j);
        let value = d.const_app(p.nat_div_succ, &[numerator_arg, index]);

        let actual_num = super::ops::num(&mut d, value);
        let wanted = d.num(expected_num);
        let wanted_num = d.of_nat(wanted);
        let num_stmt = d.ieq(actual_num, wanted_num);
        let num_proof = d.irefl(actual_num);
        let num_name = d.kernel().name_str(anon, format!("Check.num_{label}"));
        d.declare_theorem(num_name, num_stmt, num_proof)
            .unwrap_or_else(|e| {
                panic!("Rat.natDivSucc {k} {j} did not reduce to numerator {expected_num}: {e:?}")
            });

        let actual_den = super::ops::den(&mut d, value);
        let wanted_den = d.num(expected_den);
        let den_stmt = NatOps::eq(&mut d, actual_den, wanted_den);
        let den_proof = NatOps::refl(&mut d, actual_den);
        let den_name = d.kernel().name_str(anon, format!("Check.den_{label}"));
        d.declare_theorem(den_name, den_stmt, den_proof)
            .unwrap_or_else(|e| {
                panic!("Rat.natDivSucc {k} {j} did not reduce to denominator {expected_den}: {e:?}")
            });
    }
}

/// The negative control for
/// [`nat_div_succ_computes_the_reduced_fraction`]: the same `Eq.refl` route,
/// pointed at a value `Rat.natDivSucc` does **not** take.
///
/// Without this, a kernel whose conversion checker accepted anything would make
/// the test above pass while measuring nothing. `6/(1+1)` is `3/1`, so asking it
/// to be `6/1` must be **refused**.
#[test]
fn nat_div_succ_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let six = d.num(6);
    let one = d.num(1);
    let value = d.const_app(p.nat_div_succ, &[six, one]);
    let actual_num = super::ops::num(&mut d, value);
    let wrong = d.num(6);
    let wrong_num = d.of_nat(wrong);
    let stmt = d.ieq(actual_num, wrong_num);
    let proof = d.irefl(actual_num);
    let name = d.kernel().name_str(anon, "Check.wrong_numerator");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.num (Rat.natDivSucc 6 1) = Int.ofNat 6`, \
         so the reduction check above proves nothing"
    );
}

/// The two `natDivSucc` lemmas `CReal.mul` will need, stated verbatim — and the
/// proof that the first genuinely **subsumes** `natDivSucc_halve` rather than
/// merely resembling it.
///
/// `natDivSucc_halve` is the `c = 1` instance *definitionally*: `Nat.add x
/// (succ y)` reduces to `succ (Nat.add x y)`, so `(1+1)·m + 1` is `succ (2·m)`
/// and `natDivSucc_scale 1` type-checks at `natDivSucc_halve`'s statement. The
/// kernel is asked to confirm that, because "the general lemma covers the
/// special case" is exactly the kind of claim that is usually asserted in a doc
/// comment and never checked.
#[test]
fn nat_div_succ_scale_subsumes_halve_and_is_monotone_in_the_numerator() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let render = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        render(&mut kernel, p.nat_div_succ_scale),
        "((x0 : AxNat) -> ((x1 : AxNat) -> Eq.{1} Rat \
         (Rat.natDivSucc (AxNat.succ x0) (AxNat.add (AxNat.mul (AxNat.succ x0) x1) x0)) \
         (Rat.natDivSucc (AxNat.succ AxNat.zero) x1)))"
    );
    assert_eq!(
        render(&mut kernel, p.nat_div_succ_le_add_left),
        "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> \
         Rat.le (Rat.natDivSucc x0 x2) (Rat.natDivSucc (AxNat.add x0 x1) x2))))"
    );

    // `natDivSucc_scale 1 m : natDivSucc 2 (2·m + 1) = natDivSucc 1 m`, which is
    // `natDivSucc_halve`'s statement. Admitting it proves the subsumption.
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let one_nat = d.num(1);
    let two_nat = d.num(2);
    let doubled = NatOps::mul(&mut d, two_nat, m);
    let shifted = d.succ(doubled);
    let left = d.const_app(p.nat_div_succ, &[two_nat, shifted]);
    let right = d.const_app(p.nat_div_succ, &[one_nat, m]);
    let stmt = crate::rat_prelude::ops::req(&mut d, left, right);
    let instance = d.lemma(p.nat_div_succ_scale, &[one_nat, m]);
    let nat = d.nat_ty();
    let ty = d.pi_fv(m_fv, nat, stmt);
    let value = d.lam_fv(m_fv, nat, instance);
    let name = d.kernel().name_str(anon, "Check.halve_from_scale");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "natDivSucc_scale at c = 1 must BE natDivSucc_halve — it did not \
         type-check, so the generalisation does not subsume the special case: \
         {admitted:?}"
    );
}

/// The multiplicative toolkit says what `CReal.mul` needs it to say.
///
/// Rendered verbatim, because an empty axiom footprint on a *weaker* statement
/// is this repository's standing failure mode and the product estimate is
/// exactly where a silently weakened bound would not be noticed: every one of
/// these is consumed inside a proof whose conclusion is checked only for
/// well-typedness.
#[test]
fn the_product_toolkit_has_the_statements_creal_mul_needs() {
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
        rendered(&mut kernel, p.mul_sub_mul),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Rat) -> \
         Eq.{1} Rat (Rat.sub (Rat.mul x0 x1) (Rat.mul x2 x3)) \
         (Rat.add (Rat.mul x0 (Rat.sub x1 x3)) (Rat.mul (Rat.sub x0 x2) x3))))))"
    );
    // `bounds_mul` must bound the product by the product of the two bounds —
    // NOT by one of them, and not one-sidedly.
    assert_eq!(
        rendered(&mut kernel, p.bounds_mul),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Rat) -> \
         ((x4 : Rat.le Rat.zero x1) -> ((x5 : Rat.le (Rat.neg x1) x0) -> \
         ((x6 : Rat.le x0 x1) -> ((x7 : Rat.le (Rat.neg x3) x2) -> \
         ((x8 : Rat.le x2 x3) -> \
         And (Rat.le (Rat.neg (Rat.mul x1 x3)) (Rat.mul x0 x2)) \
         (Rat.le (Rat.mul x0 x2) (Rat.mul x1 x3)))))))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.nat_div_succ_mul),
        "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> \
         Eq.{1} Rat (Rat.mul (Rat.natDivSucc x0 AxNat.zero) (Rat.natDivSucc x1 x2)) \
         (Rat.natDivSucc (AxNat.mul x0 x1) x2))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.nat_div_succ_le_one),
        "((x0 : AxNat) -> Rat.le (Rat.natDivSucc (AxNat.succ AxNat.zero) x0) \
         (Rat.natDivSucc (AxNat.succ AxNat.zero) AxNat.zero))"
    );
    // The two that make nested sampling indices reducible. `nat_index_compose`
    // must say the COMPOSED index is a product index in `n` — a statement that
    // merely related the two shifts would be true and useless.
    assert_eq!(
        rendered(&mut kernel, p.nat_index_compose),
        "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> \
         Eq.{1} AxNat \
         (AxNat.add (AxNat.mul (AxNat.succ x0) \
         (AxNat.add (AxNat.mul (AxNat.succ x1) x2) x1)) x0) \
         (AxNat.add (AxNat.mul (AxNat.succ \
         (AxNat.add (AxNat.mul (AxNat.succ x0) x1) x0)) x2) \
         (AxNat.add (AxNat.mul (AxNat.succ x0) x1) x0)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.nat_div_succ_le_scaled),
        "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> \
         Rat.le (Rat.natDivSucc x0 \
         (AxNat.add (AxNat.mul (AxNat.succ x1) x2) x1)) \
         (Rat.natDivSucc x0 x2))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.bounds_num),
        "((x0 : Rat) -> \
         And (Rat.le (Rat.neg (Rat.natDivSucc (Int.natAbs (Rat.num x0)) AxNat.zero)) x0) \
         (Rat.le x0 (Rat.natDivSucc (Int.natAbs (Rat.num x0)) AxNat.zero)))"
    );
}

/// Every new multiplicative lemma is a **checked theorem** with an empty axiom
/// footprint.
#[test]
fn the_product_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let laws = [
        p.mul_neg,
        p.neg_mul,
        p.mul_le_mul_of_nonneg_right,
        p.mul_sub_mul,
        p.bounds_mul,
        p.neg_mul_le_of_bounds,
        p.nat_div_succ_mul,
        p.nat_div_succ_le_one,
        p.nat_div_succ_le_scaled,
        p.nat_index_compose,
        p.int_le_nat_abs,
        p.int_neg_nat_abs_le,
        p.bounds_num,
    ];
    for law in laws {
        let label = kernel.display_name(law).to_string();
        let declaration = kernel
            .environment()
            .get(law)
            .unwrap_or_else(|| panic!("{label} is not declared at all"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "{label} must be a checked Theorem"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(law)
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect();
        assert!(footprint.is_empty(), "{label} rests on {footprint:?}");
    }
}
