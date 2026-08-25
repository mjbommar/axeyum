//! Tests for the rational prelude.

use super::{RatPrelude, build_rat_prelude};
use crate::expr::ExprId;
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
        ("le_antisymm", p.le_antisymm),
        ("lt_trichotomy", p.lt_trichotomy),
        ("mul_eq_zero", p.mul_eq_zero),
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
        ("mul_inv_cancel", p.mul_inv_cancel),
        ("mul_inv_cancel_of_neg", p.mul_inv_cancel_of_neg),
        ("mul_inv_cancel_of_ne_zero", p.mul_inv_cancel_of_ne_zero),
        ("inv_pos", p.inv_pos),
        ("one_ne_zero", p.one_ne_zero),
        ("IsField", p.is_field),
        ("rat_isField", p.rat_is_field),
        ("mul_left_cancel_of_ne_zero", p.mul_left_cancel_of_ne_zero),
        ("sub_mul", p.sub_mul),
        ("mul_inv_sub_one", p.mul_inv_sub_one),
        ("inv_sub_inv", p.inv_sub_inv),
        ("inv_le_of_pos_le", p.inv_le_of_pos_le),
        ("mul_pos", p.mul_pos),
        ("natDivSucc_pos", p.nat_div_succ_pos),
        ("inv_natDivSucc", p.inv_nat_div_succ),
        ("natDivSucc_antitone", p.nat_div_succ_antitone),
        ("nat_index_symm", p.nat_index_symm),
        ("max", p.max),
        ("min", p.min),
        ("max_cases", p.max_cases),
        ("min_cases", p.min_cases),
        ("le_max_left", p.le_max_left),
        ("le_max_right", p.le_max_right),
        ("max_le", p.max_le),
        ("min_le_left", p.min_le_left),
        ("min_le_right", p.min_le_right),
        ("le_min", p.le_min),
        ("le_of_sub_le", p.le_of_sub_le),
        ("sub_le_of_le", p.sub_le_of_le),
        ("sub_max_le", p.sub_max_le),
        ("sub_min_le", p.sub_min_le),
        ("zero_le_max_neg", p.zero_le_max_neg),
        ("abs", p.abs),
        ("abs_nonneg", p.abs_nonneg),
        ("le_abs_self", p.le_abs_self),
        ("neg_le_abs", p.neg_le_abs),
        ("abs_zero", p.abs_zero),
        ("abs_neg", p.abs_neg),
        ("abs_add", p.abs_add),
        ("abs_mul", p.abs_mul),
        ("abs_le_of_le_of_neg_le", p.abs_le_of_le_of_neg_le),
        ("le_of_abs_le", p.le_of_abs_le),
        ("neg_le_of_abs_le", p.neg_le_of_abs_le),
        ("abs_sub_comm", p.abs_sub_comm),
        ("ble", p.ble),
        ("ble_eq_true_of_le", p.ble_eq_true_of_le),
        ("le_of_ble_eq_true", p.le_of_ble_eq_true),
        ("ble_refl", p.ble_refl),
        ("ble_trans", p.ble_trans),
        ("ble_total", p.ble_total),
        ("det2", p.det2),
        ("det2_swap_rows", p.det2_swap_rows),
        ("det2_id", p.det2_id),
        ("det2_scale_row", p.det2_scale_row),
        ("det2_row_add", p.det2_row_add),
        ("det2_mul", p.det2_mul),
        ("mul_adj2_top_left", p.mul_adj2_top_left),
        ("mul_adj2_top_right", p.mul_adj2_top_right),
        ("mul_adj2_bottom_left", p.mul_adj2_bottom_left),
        ("mul_adj2_bottom_right", p.mul_adj2_bottom_right),
        ("inv2_top_left", p.inv2_top_left),
        ("inv2_top_right", p.inv2_top_right),
        ("inv2_bottom_left", p.inv2_bottom_left),
        ("inv2_bottom_right", p.inv2_bottom_right),
        ("cramer_two_unique_x", p.cramer_two_unique_x),
        ("cramer_two_unique_y", p.cramer_two_unique_y),
        ("ofInt", p.of_int),
        ("ofInt_add", p.of_int_add),
        ("ofInt_mul", p.of_int_mul),
        ("ofInt_neg", p.of_int_neg),
        ("det2_fib", p.det2_fib),
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

/// `Rat.le` is not just total (`le_total`) but **antisymmetric**
/// (`le_antisymm`) and its strict companion is **trichotomous**
/// (`lt_trichotomy`) — none of which is one of the 22, and the last two did
/// not exist before this development. `le_antisymm` is built directly on
/// `int_prelude`'s own `Int.le_antisymm`. Every declaration involved is a
/// **checked** theorem with an empty axiom footprint — read out of the
/// kernel, not off the diff.
#[test]
fn the_order_is_antisymmetric_and_trichotomous_and_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("le_antisymm", p.le_antisymm),
        ("lt_trichotomy", p.lt_trichotomy),
    ];
    for (label, name) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "Rat.{label} must be a checked Theorem, found a different kind"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// The statements are the unweakened ones, rendered verbatim: `le_antisymm`'s
/// conclusion is the bare equality (not, say, `le a b` again), and
/// `lt_trichotomy`'s disjunction is right-associated with `lt a b` first,
/// `a = b` in the middle and `lt b a` last — not some other bracketing that
/// would still have an empty footprint while proving something weaker or
/// differently-shaped than trichotomy.
#[test]
fn the_order_completeness_statements_are_the_unweakened_ones() {
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
        rendered(&mut kernel, p.le_antisymm),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat.le x0 x1) -> \
         ((x3 : Rat.le x1 x0) -> Eq.{1} Rat x0 x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_trichotomy),
        "((x0 : Rat) -> ((x1 : Rat) -> \
         Or (Rat.lt x0 x1) (Or (Eq.{1} Rat x0 x1) (Rat.lt x1 x0))))"
    );
}

/// `Rat.mul_eq_zero` is a **checked** theorem with an empty axiom footprint.
///
/// It is not a cross-multiplication fact like the order laws above — `Rat.mul`
/// normalises, so it earns its own check rather than riding along with
/// [`the_order_is_antisymmetric_and_trichotomous_and_axiom_free`].
#[test]
fn mul_eq_zero_is_axiom_free() {
    let (kernel, p) = built();
    let declaration = kernel
        .environment()
        .get(p.mul_eq_zero)
        .expect("Rat.mul_eq_zero was interned but never declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "Rat.mul_eq_zero must be a checked Theorem, found a different kind"
    );
    let footprint: Vec<String> = kernel
        .axiom_footprint(p.mul_eq_zero)
        .into_iter()
        .map(|entry| kernel.display_name(entry).to_string())
        .collect();
    assert!(
        footprint.is_empty(),
        "Rat.mul_eq_zero rests on {footprint:?}"
    );
}

/// `Rat.right_distrib` is a **checked** theorem with an empty axiom
/// footprint, read out of the kernel, not off the diff.
#[test]
fn right_distrib_is_axiom_free() {
    let (kernel, p) = built();
    let declaration = kernel
        .environment()
        .get(p.right_distrib)
        .expect("Rat.right_distrib was interned but never declared");
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "Rat.right_distrib must be a checked Theorem, found a different kind"
    );
    let footprint: Vec<String> = kernel
        .axiom_footprint(p.right_distrib)
        .into_iter()
        .map(|entry| kernel.display_name(entry).to_string())
        .collect();
    assert!(
        footprint.is_empty(),
        "Rat.right_distrib rests on {footprint:?}"
    );
}

/// `Rat.det2` and its theorems — the 2×2 linear algebra `matrix` adds,
/// including the `ℤ→ℚ` cast `Rat.ofInt` and the Fibonacci–determinant bridge
/// `Rat.det2_fib` — are each a **checked** declaration with an empty axiom
/// footprint, read out of the kernel rather than off the diff. `det2` and
/// `ofInt` are `Definition`s (their defining equations hold by unfolding, so
/// neither needs an equation lemma); everything else here is a `Theorem`.
#[test]
fn matrix_laws_are_axiom_free() {
    let (kernel, p) = built();

    let declaration = kernel
        .environment()
        .get(p.det2)
        .expect("Rat.det2 was interned but never declared");
    assert!(
        matches!(declaration, Declaration::Definition { .. }),
        "Rat.det2 must be a Definition, found a different kind"
    );

    let declaration = kernel
        .environment()
        .get(p.of_int)
        .expect("Rat.ofInt was interned but never declared");
    assert!(
        matches!(declaration, Declaration::Definition { .. }),
        "Rat.ofInt must be a Definition, found a different kind"
    );

    let expected = [
        ("det2_swap_rows", p.det2_swap_rows),
        ("det2_id", p.det2_id),
        ("det2_scale_row", p.det2_scale_row),
        ("det2_row_add", p.det2_row_add),
        ("det2_mul", p.det2_mul),
        ("mul_adj2_top_left", p.mul_adj2_top_left),
        ("mul_adj2_top_right", p.mul_adj2_top_right),
        ("mul_adj2_bottom_left", p.mul_adj2_bottom_left),
        ("mul_adj2_bottom_right", p.mul_adj2_bottom_right),
        ("inv2_top_left", p.inv2_top_left),
        ("inv2_top_right", p.inv2_top_right),
        ("inv2_bottom_left", p.inv2_bottom_left),
        ("inv2_bottom_right", p.inv2_bottom_right),
        ("cramer_two_unique_x", p.cramer_two_unique_x),
        ("cramer_two_unique_y", p.cramer_two_unique_y),
        ("ofInt_add", p.of_int_add),
        ("ofInt_mul", p.of_int_mul),
        ("ofInt_neg", p.of_int_neg),
        ("det2_fib", p.det2_fib),
    ];
    for (label, name) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "Rat.{label} must be a checked Theorem, found a different kind"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `Rat.det2_fib`'s statement, asserted verbatim — an empty axiom footprint
/// on a theorem *named* `det2_fib` says nothing about which statement it
/// proves; this checks it is genuinely Cassini's identity read through
/// `det2`, cast into `ℚ` by `ofInt`, and not some vacuous or mismatched
/// restatement.
#[test]
fn det2_fib_is_cassini_through_det2() {
    let (kernel, p) = built();
    let ty = match kernel.environment().get(p.det2_fib).expect("declared") {
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
        "((x0 : AxNat) -> Eq.{1} Rat (Rat.det2 \
         (Rat.ofInt (Int.ofNat (AxNat.fib (AxNat.succ (AxNat.succ x0))))) \
         (Rat.ofInt (Int.ofNat (AxNat.fib (AxNat.succ x0)))) \
         (Rat.ofInt (Int.ofNat (AxNat.fib (AxNat.succ x0)))) \
         (Rat.ofInt (Int.ofNat (AxNat.fib x0)))) \
         (Rat.ofInt (Int.pow (Int.neg Int.one) (AxNat.succ x0))))"
    );
}

/// `Rat.inv2_top_left`'s statement, asserted verbatim — the same discipline
/// [`the_rationals_are_a_field_and_the_inverse_is_positive`] applies to
/// `mul_inv_cancel`: an empty axiom footprint on a theorem *named*
/// `inv2_top_left` says nothing about which statement it proves.
#[test]
fn inv2_top_left_is_the_stated_entry_of_a_inverse_a() {
    let (kernel, p) = built();
    let ty = match kernel.environment().get(p.inv2_top_left).expect("declared") {
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
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Rat) -> \
         ((x4 : Not (Eq.{1} Rat (Rat.det2 x0 x1 x2 x3) Rat.zero)) -> \
         Eq.{1} Rat (Rat.add (Rat.mul (Rat.mul (Rat.inv (Rat.det2 x0 x1 x2 x3)) x3) x0) \
         (Rat.mul (Rat.mul (Rat.inv (Rat.det2 x0 x1 x2 x3)) (Rat.neg x1)) x2)) Rat.one)))))"
    );
}

/// `Rat.cramer_two_unique_x`'s statement, asserted verbatim — same discipline
/// as [`inv2_top_left_is_the_stated_entry_of_a_inverse_a`]: an empty axiom
/// footprint on a theorem named `cramer_two_unique_x` says nothing about
/// which statement it proves, and this is the FORWARD direction only (a
/// solution must have this form), never a bare existence claim.
#[test]
fn cramer_two_unique_x_is_the_stated_forward_direction() {
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.cramer_two_unique_x)
        .expect("declared")
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
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Rat) -> ((x4 : Rat) -> \
         ((x5 : Rat) -> ((x6 : Rat) -> ((x7 : Rat) -> \
         ((x8 : Eq.{1} Rat (Rat.add (Rat.mul x0 x4) (Rat.mul x1 x5)) x6) -> \
         ((x9 : Eq.{1} Rat (Rat.add (Rat.mul x2 x4) (Rat.mul x3 x5)) x7) -> \
         ((x10 : Not (Eq.{1} Rat (Rat.det2 x0 x1 x2 x3) Rat.zero)) -> \
         Eq.{1} Rat x4 (Rat.div (Rat.det2 x6 x1 x7 x3) (Rat.det2 x0 x1 x2 x3)))))))))))))"
    );
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
        "these AxReal declarations have no ℚ interpretation: {missed:?}"
    );
}

// --- the Archimedean property (ADR-0512 phase R1) ---------------------------

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
        ("natDivSucc_antitone", p.nat_div_succ_antitone, true),
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

/// `Rat.natDivSucc_antitone` is antitonicity **exactly as briefed**: the
/// hypothesis is `Nat.le j j'` (not a fixed pair, not `Nat.lt`), and the
/// conclusion swaps `j`/`j'` on `Rat.natDivSucc 1 _` — the wider index gives
/// the smaller bound — rather than leaving the direction to an empty
/// footprint's word.
#[test]
fn nat_div_succ_antitone_is_the_statement_briefed() {
    let (kernel, p) = built();
    let rendered = match kernel
        .environment()
        .get(p.nat_div_succ_antitone)
        .expect("Rat.natDivSucc_antitone must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("Rat.natDivSucc_antitone must be a Theorem, found {other:?}"),
    };
    let text = kernel.render_lean(rendered);
    let normalised: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
    assert_eq!(
        normalised,
        "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat.le x0 x1) -> \
         Rat.le (Rat.natDivSucc (AxNat.succ AxNat.zero) x1) \
         (Rat.natDivSucc (AxNat.succ AxNat.zero) x0))))",
        "Rat.natDivSucc_antitone's statement drifted from the briefed one"
    );
}

/// The Archimedean statement is the one ADR-0512 asks for, **verbatim**.
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
        "the Archimedean statement drifted from ADR-0512's"
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

/// **`Rat.IsField`, and every leaf is asserted verbatim** — the curriculum
/// target (`fields.md`): a bundled `Prop` predicate in the
/// `nat_prelude::group::Nat.IsGroupOn` house style, with `Rat.rat_isField` the
/// worked instance and `Rat.mul_left_cancel_of_ne_zero` the consequence a
/// field gives that a ring does not.
#[test]
fn the_rationals_satisfy_is_field_and_cancel() {
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
        rendered(&mut kernel, p.one_ne_zero),
        "Not (Eq.{1} Rat Rat.one Rat.zero)"
    );
    assert_eq!(
        rendered(&mut kernel, p.is_field),
        "((x0 : ((x0 : Rat) -> ((x1 : Rat) -> Rat))) -> ((x1 : ((x1 : Rat) -> \
         ((x2 : Rat) -> Rat))) -> ((x2 : ((x2 : Rat) -> Rat)) -> ((x3 : ((x3 : \
         Rat) -> Rat)) -> ((x4 : Rat) -> ((x5 : Rat) -> Prop))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.rat_is_field),
        "Rat.IsField Rat.add Rat.mul Rat.neg Rat.inv Rat.zero Rat.one"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_left_cancel_of_ne_zero),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Not (Eq.{1} Rat x0 \
         Rat.zero)) -> ((x4 : Eq.{1} Rat (Rat.mul x0 x1) (Rat.mul x0 x2)) -> \
         Eq.{1} Rat x1 x2)))))"
    );

    for (label, name, expect_definition) in [
        ("one_ne_zero", p.one_ne_zero, false),
        ("IsField", p.is_field, true),
        ("rat_isField", p.rat_is_field, false),
        (
            "mul_left_cancel_of_ne_zero",
            p.mul_left_cancel_of_ne_zero,
            false,
        ),
    ] {
        let decl = kernel.environment().get(name);
        if expect_definition {
            assert!(
                matches!(decl, Some(Declaration::Definition { .. })),
                "Rat.{label} must be a checked Definition"
            );
        } else {
            assert!(
                matches!(decl, Some(Declaration::Theorem { .. })),
                "Rat.{label} must be a checked Theorem"
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

/// **The field laws compute at an explicit rational, and the kernel refuses
/// the unrestricted `x·x⁻¹ = 1` when it is asked to reuse the real proof
/// without the `x ≠ 0` hypothesis.**
///
/// `Rat.inv`'s totality (`inv 0 = 0`) is exactly what makes `mul_inv_cancel`
/// need a hypothesis at all; the negative control here is the mistake that
/// hypothesis exists to rule out.
#[test]
fn field_laws_compute_at_one_half_and_reject_the_unrestricted_inverse() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_eq_rewrite, req, rlt, rmul, rone, rrefl, rzero};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    // `1/2`, as `Rat.natDivSucc 1 1`, and its positivity (`1 ≤ 1`).
    let one_nat = d.num(1);
    let half = d.const_app(p.nat_div_succ, &[one_nat, one_nat]);
    let one_le_one = d.lemma(p.int.nat.le_refl, &[one_nat]);
    let half_pos = d.lemma(p.nat_div_succ_pos, &[one_nat, one_nat, one_le_one]); // 0 < 1/2

    // `1/2 ≠ 0`, by the same rewrite-to-`lt_irrefl` route as `Rat.one_ne_zero`.
    let zero = rzero(&mut d, p);
    let half_eq_zero = req(&mut d, half, zero);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let rewritten = rat_eq_rewrite(&mut d, half, zero, h, half_pos, &|d, t| rlt(d, p, zero, t));
    let refuted = d.lemma(p.lt_irrefl, &[zero]);
    let false_proof = d.apply(refuted, &[rewritten]);
    let half_ne_zero = d.lam_fv(h_fv, half_eq_zero, false_proof);

    // Computation: `(1/2)⁻¹` REDUCES to `2/1` — `Eq.refl` alone must check.
    let two_nat = d.num(2);
    let zero_nat = d.zero();
    let doubled = d.const_app(p.nat_div_succ, &[two_nat, zero_nat]); // 2/1
    let reciprocal = d.const_app(p.inv, &[half]);
    let inv_computes = req(&mut d, reciprocal, doubled);
    let inv_proof = rrefl(&mut d, doubled);
    let inv_name = d.kernel().name_str(anon, "Check.half_inv_computes");
    let inv_accepted = d.kernel().add_declaration(Declaration::Theorem {
        name: inv_name,
        uparams: vec![],
        ty: inv_computes,
        value: inv_proof,
    });
    assert!(
        inv_accepted.is_ok(),
        "`(1/2)⁻¹` must REDUCE to `2/1`: {inv_accepted:?}"
    );

    // The field law itself, applied at this concrete `1/2`: `(1/2)·(1/2)⁻¹ = 1`.
    let one = rone(&mut d, p);
    let product = rmul(&mut d, half, reciprocal);
    let law_claim = req(&mut d, product, one);
    let law_proof = d.lemma(p.mul_inv_cancel_of_ne_zero, &[half, half_ne_zero]);
    let law_name = d.kernel().name_str(anon, "Check.half_mul_inv_cancel");
    let law_accepted = d.kernel().add_declaration(Declaration::Theorem {
        name: law_name,
        uparams: vec![],
        ty: law_claim,
        value: law_proof,
    });
    assert!(
        law_accepted.is_ok(),
        "the field law must apply at `1/2`: {law_accepted:?}"
    );

    // NEGATIVE CONTROL: `∀ x, mul x (inv x) = one`, UNRESTRICTED — false at
    // `x = 0` (`Rat.inv Rat.zero = Rat.zero`, so the claim there is `0 = 1`).
    // Reuse `Rat.mul_inv_cancel_of_ne_zero`'s own constant, applied to just
    // `x` (no `x ≠ 0` proof supplied) — its type is `Not (x=0) -> …`, not the
    // bare `Eq` the unrestricted statement needs, so the kernel must refuse.
    let carrier = crate::rat_prelude::ops::rat_ty(&mut d);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let one2 = rone(&mut d, p);
    let ix = d.const_app(p.inv, &[x]);
    let bad_product = rmul(&mut d, x, ix);
    let bad_concl = req(&mut d, bad_product, one2);
    let bad_ty = d.pi_fv(x_fv, carrier, bad_concl);

    let real_const = d.kernel().const_(p.mul_inv_cancel_of_ne_zero, vec![]);
    let bad_body = d.apply(real_const, &[x]); // : Not (x=0) -> mul x (inv x) = one
    let bad_value = d.lam_fv(x_fv, carrier, bad_body);
    let bad_name = d.kernel().name_str(anon, "Check.unrestricted_inv_cancel");
    let bad_accepted = d.kernel().add_declaration(Declaration::Theorem {
        name: bad_name,
        uparams: vec![],
        ty: bad_ty,
        value: bad_value,
    });
    assert!(
        bad_accepted.is_err(),
        "the kernel accepted `∀ x, x·x⁻¹ = 1` UNRESTRICTED — the `x ≠ 0` \
         hypothesis was refused as if it were vacuous: {bad_accepted:?}"
    );
}

/// **ℚ is a field, and the statement is asserted verbatim.**
///
/// `Rat.inv` was a definition with no law about it for the whole life of this
/// prelude; an empty footprint on a theorem *named* `mul_inv_cancel` says
/// nothing, so the rendered type is the assertion. `Rat.div` is `a · b⁻¹`, so
/// this is also the first law division has.
#[test]
fn the_rationals_are_a_field_and_the_inverse_is_positive() {
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
        rendered(&mut kernel, p.mul_inv_cancel),
        "((x0 : Rat) -> ((x1 : Rat.lt Rat.zero x0) -> \
         Eq.{1} Rat (Rat.mul x0 (Rat.inv x0)) Rat.one))"
    );
    assert_eq!(
        rendered(&mut kernel, p.inv_pos),
        "((x0 : Rat) -> ((x1 : Rat.lt Rat.zero x0) -> Rat.lt Rat.zero (Rat.inv x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_inv_cancel_of_neg),
        "((x0 : Rat) -> ((x1 : Rat.lt x0 Rat.zero) -> \
         Eq.{1} Rat (Rat.mul x0 (Rat.inv x0)) Rat.one))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_inv_cancel_of_ne_zero),
        "((x0 : Rat) -> ((x1 : Not (Eq.{1} Rat x0 Rat.zero)) -> \
         Eq.{1} Rat (Rat.mul x0 (Rat.inv x0)) Rat.one))"
    );
    for (label, name) in [
        ("mul_inv_cancel", p.mul_inv_cancel),
        ("inv_pos", p.inv_pos),
        ("mul_inv_cancel_of_neg", p.mul_inv_cancel_of_neg),
        ("mul_inv_cancel_of_ne_zero", p.mul_inv_cancel_of_ne_zero),
    ] {
        assert!(
            matches!(
                kernel.environment().get(name),
                Some(Declaration::Theorem { .. })
            ),
            "Rat.{label} must be a checked Theorem"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// **`Rat.inv` is the reciprocal, by computation.** `(2/1)⁻¹` reduces to `1/2`,
/// so `Eq.refl` proves it and the kernel checks the reduction.
///
/// `mul_inv_cancel` alone does not pin the operation as tightly as it looks:
/// its hypothesis is `0 < q`, so it says nothing at all about `inv` on the
/// non-positive rationals, and a "reciprocal" that agreed with the real one
/// only on the positives would satisfy it. This is the point check that fails
/// for the identity, for the constant, and for the negated reciprocal — the
/// paired negative control below runs the identity and is REFUSED.
#[test]
fn the_inverse_computes_the_reciprocal() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let two = d.num(2);
    let one = d.num(1);
    let zero = d.zero();
    // `2/1` and `1/2`, as `Rat.natDivSucc k j = k/(j+1)`.
    let doubled = d.const_app(p.nat_div_succ, &[two, zero]);
    let halved = d.const_app(p.nat_div_succ, &[one, one]);
    let reciprocal = d.const_app(p.inv, &[doubled]);
    let claim = crate::rat_prelude::ops::req(&mut d, reciprocal, halved);
    let proof = crate::rat_prelude::ops::rrefl(&mut d, halved);
    let name = d.kernel().name_str(anon, "Check.inv_two");
    let accepted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: claim,
        value: proof,
    });
    assert!(
        accepted.is_ok(),
        "`Rat.inv (2/1)` must REDUCE to `1/2`; the kernel refused the reflexivity \
         proof, so the definition does not compute the reciprocal: {accepted:?}"
    );
}

/// The negative control: the identical `Eq.refl` script pointed at
/// `(2/1)⁻¹ = 2/1` is REFUSED, so the check above is a check.
#[test]
fn the_inverse_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let two = d.num(2);
    let zero = d.zero();
    let doubled = d.const_app(p.nat_div_succ, &[two, zero]);
    let reciprocal = d.const_app(p.inv, &[doubled]);
    // The one changed token: the claimed value is `2/1`, not `1/2`.
    let claim = crate::rat_prelude::ops::req(&mut d, reciprocal, doubled);
    let proof = crate::rat_prelude::ops::rrefl(&mut d, doubled);
    let name = d.kernel().name_str(anon, "Check.inv_two_is_two");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: claim,
        value: proof,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `(2/1)⁻¹ = 2/1`, so `Rat.inv` does not compute a \
         reciprocal and the reduction check above proves nothing"
    );
}

/// **The two lemmas `CReal.inv`'s index arithmetic is written in**, asserted
/// verbatim rather than by footprint.
///
/// `inv_natDivSucc` is the only lemma in this development that computes the
/// *value* of an inverse; `nat_index_symm` says Bishop's sampling index is
/// symmetric in its shift and its argument, which is what lets a bound read at
/// a product index come back to the **shift** without `Rat.natDivSucc` ever
/// having to be antitone in its index.
#[test]
fn the_inverse_index_toolkit_has_the_statements_creal_inv_needs() {
    let (mut kernel, p) = built();
    let render = |kernel: &mut Kernel, name: crate::NameId| -> String {
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
        render(&mut kernel, p.inv_nat_div_succ),
        "((x0 : AxNat) -> Eq.{1} Rat \
         (Rat.inv (Rat.natDivSucc (AxNat.succ AxNat.zero) x0)) \
         (Rat.natDivSucc (AxNat.succ x0) AxNat.zero))"
    );
    assert_eq!(
        render(&mut kernel, p.nat_index_symm),
        "((x0 : AxNat) -> ((x1 : AxNat) -> Eq.{1} AxNat \
         (AxNat.add (AxNat.mul (AxNat.succ x0) x1) x0) \
         (AxNat.add (AxNat.mul (AxNat.succ x1) x0) x1)))"
    );
    for (label, name) in [
        ("inv_natDivSucc", p.inv_nat_div_succ),
        ("nat_index_symm", p.nat_index_symm),
    ] {
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// The negative control for
/// [`the_inverse_index_toolkit_has_the_statements_creal_inv_needs`]: the
/// **same proof term**, pointed at a statement one token away, is REFUSED.
///
/// `(1/(m+1))⁻¹ = m/1` is false at every `m ≥ 1` — at `m = 1` it claims
/// `(1/2)⁻¹ = 1` — and `nat_index_symm` with one argument left unswapped is
/// false at every `a ≠ b`. If either mutation were accepted, the statement
/// tests above would be pinning a shape rather than a fact.
#[test]
fn the_inverse_index_toolkit_cannot_prove_the_off_by_one_statements() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat_ty = d.nat_ty();

    // (1/(m+1))⁻¹ = m/1 — the numerator is `m`, not `m+1`.
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let one_nat = d.num(1);
    let zero_nat = d.num(0);
    let modulus = d.const_app(p.nat_div_succ, &[one_nat, m]);
    let reciprocal = d.const_app(p.inv, &[modulus]);
    let short = d.const_app(p.nat_div_succ, &[m, zero_nat]);
    let claim = crate::rat_prelude::ops::req(&mut d, reciprocal, short);
    let ty = d.pi_fv(m_fv, nat_ty, claim);
    let value = {
        let instance = d.lemma(p.inv_nat_div_succ, &[m]);
        d.lam_fv(m_fv, nat_ty, instance)
    };
    let name = d.kernel().name_str(anon, "Check.inv_off_by_one");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `(1/(m+1))⁻¹ = m/1`, which is FALSE at m = 1"
    );

    // (a+1)·b + a = (b+1)·a + a — the trailing summand is not swapped.
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let sa = d.succ(a);
    let sb = d.succ(b);
    let start = {
        let scaled = NatOps::mul(&mut d, sa, b);
        NatOps::add(&mut d, scaled, a)
    };
    let unswapped = {
        let scaled = NatOps::mul(&mut d, sb, a);
        NatOps::add(&mut d, scaled, a)
    };
    let claim = d.eq(start, unswapped);
    let ty = {
        let inner = d.pi_fv(b_fv, nat_ty, claim);
        d.pi_fv(a_fv, nat_ty, inner)
    };
    let value = {
        let instance = d.lemma(p.nat_index_symm, &[a, b]);
        let inner = d.lam_fv(b_fv, nat_ty, instance);
        d.lam_fv(a_fv, nat_ty, inner)
    };
    let name = d.kernel().name_str(anon, "Check.index_half_swapped");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `(a+1)·b + a = (b+1)·a + a`, which is FALSE at a = 0, b = 1"
    );
}

/// **The rational lattice computes**, and it is the *representation* that
/// decides.
///
/// The lattice laws are all one-sided consequences of `max_cases`, and every
/// one of them would hold, footprint-free, of a `max` that always returned its
/// first argument. This does not: it reduces `Rat.max` and `Rat.min` at four
/// concrete pairs by `Eq.refl` — including a pair whose gap lands in the
/// `Int.negSucc` branch, which is the branch no law exercises directly.
#[test]
fn the_rational_lattice_computes_on_both_branches() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // (label, a, b, negate_a, expected)
    let cases: [(&str, u32, u32, bool, bool); 4] = [
        // 3 vs 1 — the gap is `ofNat 2`, so `max = b`… no: `max a b` returns
        // `b` when `a ≤ b`, and `3 ≤ 1` is false, so the gap is `negSucc` and
        // `max` returns `a`.
        ("three_one", 3, 1, false, true),
        ("one_three", 1, 3, false, false),
        // −1 vs 1 — the `negSucc` sample on the ARGUMENT rather than the gap.
        ("neg_one_one", 1, 1, true, false),
        ("two_two", 2, 2, false, false),
    ];
    for (label, av, bv, negate_a, max_is_a) in cases {
        let raw_a = literal(&mut d, av);
        let a = if negate_a {
            crate::rat_prelude::ops::rneg(&mut d, raw_a)
        } else {
            raw_a
        };
        let b = literal(&mut d, bv);
        let joined = d.const_app(p.max, &[a, b]);
        let met = d.const_app(p.min, &[a, b]);
        let (max_expected, min_expected) = if max_is_a { (a, b) } else { (b, a) };

        let stmt = crate::rat_prelude::ops::req(&mut d, joined, max_expected);
        let proof = crate::rat_prelude::ops::rrefl(&mut d, joined);
        let name = d.kernel().name_str(anon, format!("Check.max_{label}"));
        d.declare_theorem(name, stmt, proof)
            .unwrap_or_else(|e| panic!("Rat.max did not reduce for {label}: {e:?}"));

        let stmt = crate::rat_prelude::ops::req(&mut d, met, min_expected);
        let proof = crate::rat_prelude::ops::rrefl(&mut d, met);
        let name = d.kernel().name_str(anon, format!("Check.min_{label}"));
        d.declare_theorem(name, stmt, proof)
            .unwrap_or_else(|e| panic!("Rat.min did not reduce for {label}: {e:?}"));
    }
}

/// The negative control for [`the_rational_lattice_computes_on_both_branches`]:
/// the same `Eq.refl` route, pointed at the **other** argument.
///
/// `max 3 1` is `3`; asking it to be `1` must be REFUSED, or the reductions
/// above measure nothing.
#[test]
fn the_rational_lattice_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let zero_index = d.num(0);
    let three = d.num(3);
    let one = d.num(1);
    let a = d.const_app(p.nat_div_succ, &[three, zero_index]);
    let b = d.const_app(p.nat_div_succ, &[one, zero_index]);

    let joined = d.const_app(p.max, &[a, b]);
    let stmt = crate::rat_prelude::ops::req(&mut d, joined, b);
    let proof = crate::rat_prelude::ops::rrefl(&mut d, joined);
    let name = d.kernel().name_str(anon, "Check.max_is_the_smaller");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.max 3 1 = 1`, so the lattice reduction check \
         proves nothing"
    );

    let met = d.const_app(p.min, &[a, b]);
    let stmt = crate::rat_prelude::ops::req(&mut d, met, a);
    let proof = crate::rat_prelude::ops::rrefl(&mut d, met);
    let name = d.kernel().name_str(anon, "Check.min_is_the_larger");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.min 3 1 = 3`"
    );
}

/// The lattice's **case-analysis principle** and its one-Lipschitz estimate,
/// stated verbatim.
///
/// `max_cases` is the whole module: six of the nine lattice theorems are one
/// application of it. Its statement is asserted here because an `Or`-shaped
/// weakening of it (`Or (le a b) (le b a) → …`) would still let every law
/// through while quietly assuming a decision procedure at the use site.
#[test]
fn the_lattice_case_principle_has_the_statement_adr_0490_specifies() {
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
        rendered(&mut kernel, p.max),
        "((x0 : Rat) -> ((x1 : Rat) -> Rat))"
    );
    assert_eq!(
        rendered(&mut kernel, p.max_cases),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : ((x2 : Rat) -> Prop)) -> \
         ((x3 : ((x3 : Rat.le x0 x1) -> x2 x1)) -> \
         ((x4 : ((x4 : Rat.le x1 x0) -> x2 x0)) -> x2 (Rat.max x0 x1))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.min_cases),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : ((x2 : Rat) -> Prop)) -> \
         ((x3 : ((x3 : Rat.le x0 x1) -> x2 x0)) -> \
         ((x4 : ((x4 : Rat.le x1 x0) -> x2 x1)) -> x2 (Rat.min x0 x1))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.sub_max_le),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat) -> ((x3 : Rat) -> ((x4 : Rat) -> \
         ((x5 : Rat.le (Rat.sub x0 x2) x4) -> ((x6 : Rat.le (Rat.sub x1 x3) x4) -> \
         Rat.le (Rat.sub (Rat.max x0 x1) (Rat.max x2 x3)) x4)))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.zero_le_max_neg),
        "((x0 : Rat) -> Rat.le Rat.zero (Rat.max x0 (Rat.neg x0)))"
    );
}

/// Every lattice declaration is a **checked** definition or theorem with an
/// empty axiom footprint, read out of the kernel.
#[test]
fn the_rational_lattice_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("max", p.max),
        ("min", p.min),
        ("max_cases", p.max_cases),
        ("min_cases", p.min_cases),
        ("le_max_left", p.le_max_left),
        ("le_max_right", p.le_max_right),
        ("max_le", p.max_le),
        ("min_le_left", p.min_le_left),
        ("min_le_right", p.min_le_right),
        ("le_min", p.le_min),
        ("le_of_sub_le", p.le_of_sub_le),
        ("sub_le_of_le", p.sub_le_of_le),
        ("sub_max_le", p.sub_max_le),
        ("sub_min_le", p.sub_min_le),
        ("zero_le_max_neg", p.zero_le_max_neg),
    ];
    for (label, name) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        assert!(
            !matches!(
                declaration,
                Declaration::Axiom { .. } | Declaration::Opaque { .. }
            ),
            "Rat.{label} is asserted, not derived"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

// --- `Rat.abs` and the triangle inequality -----------------------------

/// Every declaration [`super::abs::declare_abs`] adds — `Rat.abs` itself and
/// the eleven theorems built on it (the triangle-inequality group, plus
/// `abs_mul`, the `abs_le` introduction/elimination trio, and
/// `abs_sub_comm`) — is a **checked** definition or theorem with an empty
/// axiom footprint, read out of the kernel, not off the diff.
#[test]
fn the_absolute_value_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("abs", p.abs, false),
        ("abs_nonneg", p.abs_nonneg, true),
        ("le_abs_self", p.le_abs_self, true),
        ("neg_le_abs", p.neg_le_abs, true),
        ("abs_zero", p.abs_zero, true),
        ("abs_neg", p.abs_neg, true),
        ("abs_add", p.abs_add, true),
        ("abs_mul", p.abs_mul, true),
        ("abs_le_of_le_of_neg_le", p.abs_le_of_le_of_neg_le, true),
        ("le_of_abs_le", p.le_of_abs_le, true),
        ("neg_le_of_abs_le", p.neg_le_of_abs_le, true),
        ("abs_sub_comm", p.abs_sub_comm, true),
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

/// `Rat.abs_add` is the **unweakened** triangle inequality — `|a+b| ≤ |a| +
/// |b|` verbatim, not, say, an equality or a one-sided estimate that would
/// still have an empty footprint while proving something weaker.
#[test]
fn abs_add_is_the_triangle_inequality_unweakened() {
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
        rendered(&mut kernel, p.abs_add),
        "((x0 : Rat) -> ((x1 : Rat) -> Rat.le (Rat.abs (Rat.add x0 x1)) \
         (Rat.add (Rat.abs x0) (Rat.abs x1))))"
    );
}

/// **`Rat.abs` computes**, on both a positive and a negative literal, by
/// `Eq.refl` — not by trusting the spec theorems to be about the definition
/// this file actually declared. `|3| = 3` exercises the branch where `max`
/// returns its first argument outright; `|−3| = 3` additionally exercises
/// `Rat.neg` reducing twice (`neg (neg 3)` inside the gap computation).
#[test]
fn rat_abs_computes_on_both_signs() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // |3| = 3.
    {
        let three = literal(&mut d, 3);
        let magnitude = d.const_app(p.abs, &[three]);
        let stmt = crate::rat_prelude::ops::req(&mut d, magnitude, three);
        let proof = crate::rat_prelude::ops::rrefl(&mut d, magnitude);
        let name = d.kernel().name_str(anon, "Check.abs_three");
        d.declare_theorem(name, stmt, proof)
            .unwrap_or_else(|e| panic!("Rat.abs did not reduce on |3|: {e:?}"));
    }

    // |−3| = 3.
    {
        let three = literal(&mut d, 3);
        let negated = crate::rat_prelude::ops::rneg(&mut d, three);
        let magnitude = d.const_app(p.abs, &[negated]);
        let three_again = literal(&mut d, 3);
        let stmt = crate::rat_prelude::ops::req(&mut d, magnitude, three_again);
        let proof = crate::rat_prelude::ops::rrefl(&mut d, magnitude);
        let name = d.kernel().name_str(anon, "Check.abs_neg_three");
        d.declare_theorem(name, stmt, proof)
            .unwrap_or_else(|e| panic!("Rat.abs did not reduce on |-3|: {e:?}"));
    }
}

/// The negative control for [`rat_abs_computes_on_both_signs`]: `|3| = 1`
/// must be REFUSED, or the reduction checks above measure nothing.
#[test]
fn rat_abs_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let index = d.num(0);
    let three_num = d.num(3);
    let one_num = d.num(1);
    let three = d.const_app(p.nat_div_succ, &[three_num, index]);
    let one = d.const_app(p.nat_div_succ, &[one_num, index]);

    let magnitude = d.const_app(p.abs, &[three]);
    let stmt = crate::rat_prelude::ops::req(&mut d, magnitude, one);
    let proof = crate::rat_prelude::ops::rrefl(&mut d, magnitude);
    let name = d.kernel().name_str(anon, "Check.abs_three_is_not_one");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.abs 3 = 1`, so the abs reduction check proves nothing"
    );
}

// --- `Rat.ble`, the decidable `≤` -------------------------------------------

/// Every declaration `decide::declare_decide` adds — `Rat.ble` itself and the
/// five theorems built on it — is a **checked** definition or theorem with an
/// empty axiom footprint, read out of the kernel, not off the diff.
#[test]
fn the_boolean_decision_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("ble", p.ble, false),
        ("ble_eq_true_of_le", p.ble_eq_true_of_le, true),
        ("le_of_ble_eq_true", p.le_of_ble_eq_true, true),
        ("ble_refl", p.ble_refl, true),
        ("ble_trans", p.ble_trans, true),
        ("ble_total", p.ble_total, true),
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

/// **`Rat.ble` computes**, and it is the *representation* that decides — the
/// same standard [`the_rational_lattice_computes_on_both_branches`] holds
/// `Rat.max`/`Rat.min` to. Checked at a pair whose gap lands in the
/// `Int.ofNat` branch (`1 ≤ 3`, and the reflexive `2 ≤ 2`) and one whose gap
/// lands in `Int.negSucc` (`3 ≤ 1` is `false`), by `Eq.refl` — not by trusting
/// the spec theorems to be about the definition this file actually declared.
#[test]
fn rat_ble_computes_on_both_branches() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // (label, a, b, ble a b expected)
    let cases: [(&str, u32, u32, bool); 3] = [
        ("one_le_three", 1, 3, true),
        ("three_le_one", 3, 1, false),
        ("two_le_two", 2, 2, true),
    ];
    for (label, av, bv, expected) in cases {
        let a = literal(&mut d, av);
        let b = literal(&mut d, bv);
        let ble_ab = d.const_app(p.ble, &[a, b]);
        let expected_value = if expected {
            d.bool_true()
        } else {
            d.bool_false()
        };
        let stmt = d.bool_eq(ble_ab, expected_value);
        let proof = d.bool_refl(expected_value);
        let name = d.kernel().name_str(anon, format!("Check.ble_{label}"));
        d.declare_theorem(name, stmt, proof)
            .unwrap_or_else(|e| panic!("Rat.ble did not reduce for {label}: {e:?}"));
    }
}

/// The negative control for [`rat_ble_computes_on_both_branches`]: the same
/// `Eq.refl` route, pointed at the **wrong** `Bool`.
///
/// `Rat.ble 3 1` is `false`; asking it to be `true` must be REFUSED, or the
/// computation check above measures nothing.
#[test]
fn rat_ble_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let zero_index = d.num(0);
    let three = d.num(3);
    let one = d.num(1);
    let a = d.const_app(p.nat_div_succ, &[three, zero_index]);
    let b = d.const_app(p.nat_div_succ, &[one, zero_index]);

    let ble_ab = d.const_app(p.ble, &[a, b]);
    let true_ = d.bool_true();
    let stmt = d.bool_eq(ble_ab, true_);
    let proof = d.bool_refl(true_);
    let name = d
        .kernel()
        .name_str(anon, "Check.ble_three_le_one_is_not_true");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.ble 3 1 = true`, so the computation check \
         proves nothing"
    );
}

/// `Rat.ble_refl`/`Rat.ble_trans`/`Rat.ble_total` each **use** the spec rather
/// than restating it: dropping `ble_eq_true_of_le` or `le_of_ble_eq_true`
/// would make every one of these fail to build, which is what makes them a
/// meaningful check on the spec rather than three more axiom-free theorems
/// that happen to sit beside it.
#[test]
fn ble_refl_trans_total_are_built_on_the_spec() {
    let (kernel, p) = built();
    for (label, name) in [
        ("ble_refl", p.ble_refl),
        ("ble_trans", p.ble_trans),
        ("ble_total", p.ble_total),
    ] {
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

// --- `Rat.sumRange` and its algebra (`rat_prelude::sum`) -------------------

/// Every declaration `sum::declare_sum` adds — `Rat.sumRange` itself and the
/// ten theorems built on it (counted from the list below, not carried over
/// from an earlier count) — is a **checked** definition or theorem with an
/// empty axiom footprint, read out of the kernel, not off the diff.
#[test]
fn the_finite_sum_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("sumRange", p.sum_range, false),
        ("sumRange_zero", p.sum_range_zero, true),
        ("sumRange_succ", p.sum_range_succ, true),
        ("sumRange_congr", p.sum_range_congr, true),
        ("sumRange_add", p.sum_range_add, true),
        ("mul_sumRange", p.mul_sum_range, true),
        ("sumRange_le", p.sum_range_le, true),
        ("sumRange_nonneg", p.sum_range_nonneg, true),
        ("sumRange_congr_lt", p.sum_range_congr_lt, true),
        ("sumRange_eq_zero_of_lt", p.sum_range_eq_zero_of_lt, true),
        ("sumRange_swap", p.sum_range_swap, true),
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

/// `Rat.sumRange_zero`/`Rat.sumRange_succ` close by `Eq.refl` alone — checked
/// directly here, independent of [`super::sum`]'s own construction, over a
/// **symbolic** `f`/`n` (an opaque bound variable, not a concrete literal):
/// with a concrete `f` every subterm is ground and can fully compute, which
/// would hide whether the equation holds definitionally or only because
/// everything reduced to the same value regardless of shape (see
/// [`sum_range_succ_wrong_order_is_rejected`] for exactly that trap).
#[test]
fn sum_range_defining_equations_close_by_refl_alone() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, req, rrefl, rsum_range};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = crate::rat_prelude::ops::rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // sumRange_zero : Eq Rat (sumRange f zero) zero, by Eq.refl.
    {
        let zero_n = d.zero();
        let lhs = rsum_range(&mut d, p, f, zero_n);
        let zero_r = crate::rat_prelude::ops::rzero(&mut d, p);
        let stmt = req(&mut d, lhs, zero_r);
        let zero_r2 = crate::rat_prelude::ops::rzero(&mut d, p);
        let proof = rrefl(&mut d, zero_r2);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        let name = d.kernel().name_str(anon, "Check.sum_range_zero_refl");
        d.declare_theorem(name, ty, value).unwrap_or_else(|e| {
            panic!(
                "sumRange_zero did not close by refl alone: {}",
                d.explain(&e)
            )
        });
    }

    // sumRange_succ : Eq Rat (sumRange f (succ n)) (sumRange f n + f n), by
    // Eq.refl — the addend order the definition actually produces.
    {
        let sn = d.succ(n);
        let lhs = rsum_range(&mut d, p, f, sn);
        let prior = rsum_range(&mut d, p, f, n);
        let fn_applied = d.apply(f, &[n]);
        let rhs = radd(&mut d, prior, fn_applied);
        let stmt = req(&mut d, lhs, rhs);
        let proof = rrefl(&mut d, rhs);
        let ty = {
            let inner = d.pi_fv(n_fv, nat, stmt);
            d.pi_fv(f_fv, fn_ty, inner)
        };
        let value = {
            let inner = d.lam_fv(n_fv, nat, proof);
            d.lam_fv(f_fv, fn_ty, inner)
        };
        let name = d.kernel().name_str(anon, "Check.sum_range_succ_refl");
        d.declare_theorem(name, ty, value).unwrap_or_else(|e| {
            panic!(
                "sumRange_succ did not close by refl alone: {}",
                d.explain(&e)
            )
        });
    }
}

/// The negative control for
/// [`sum_range_defining_equations_close_by_refl_alone`]: swapping the
/// addends in `sumRange_succ`'s RHS (`f n + sumRange f n` instead of
/// `sumRange f n + f n`) over the same symbolic `f`/`n` must be **REJECTED**
/// by `Eq.refl` — `Rat.add` is not definitionally commutative
/// (`Rat.add_comm` is a proved LAW, not a reduction rule, and for a
/// symbolic/opaque `f`/`n` neither addend reduces any further), so if this
/// succeeded the computation check above would prove nothing.
#[test]
fn sum_range_succ_wrong_order_is_rejected() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, req, rrefl, rsum_range};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = crate::rat_prelude::ops::rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let sn = d.succ(n);
    let lhs = rsum_range(&mut d, p, f, sn);
    let prior = rsum_range(&mut d, p, f, n);
    let fn_applied = d.apply(f, &[n]);
    let wrong_rhs = radd(&mut d, fn_applied, prior); // swapped
    let stmt = req(&mut d, lhs, wrong_rhs);
    let proof = rrefl(&mut d, wrong_rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, inner)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, inner)
    };
    let name = d
        .kernel()
        .name_str(anon, "Check.sum_range_succ_wrong_order");
    assert!(
        d.declare_theorem(name, ty, value).is_err(),
        "the kernel accepted the swapped-order sumRange_succ equation by \
         Eq.refl, so the computation check above proves nothing"
    );
}

// --- finite probability distributions (`rat_prelude::probability`) --------

/// Every declaration `probability::declare_probability` adds —
/// `Rat.IsDistribution` itself and the two theorems built on it — is a
/// **checked** definition or theorem with an empty axiom footprint, read out
/// of the kernel, not off the diff.
#[test]
fn the_probability_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("IsDistribution", p.is_distribution, false),
        ("prob_le_one", p.prob_le_one, true),
        ("prob_complement", p.prob_complement, true),
        ("expectation", p.expectation, false),
        ("expectation_add", p.expectation_add, true),
        ("expectation_smul", p.expectation_smul, true),
        ("expectation_const", p.expectation_const, true),
        ("uniform", p.uniform, false),
        ("uniform_is_distribution", p.uniform_is_distribution, true),
        ("expectation_nonneg", p.expectation_nonneg, true),
        ("expectation_le", p.expectation_le, true),
        ("markov_inequality", p.markov_inequality, true),
        (
            "expectation_indicator_le_one",
            p.expectation_indicator_le_one,
            true,
        ),
        ("variance", p.variance, false),
        ("variance_nonneg", p.variance_nonneg, true),
        ("variance_eq", p.variance_eq, true),
        ("variance_smul", p.variance_smul, true),
        ("covariance", p.covariance, false),
        ("variance_add_eq", p.variance_add_eq, true),
        (
            "variance_add_of_uncorrelated",
            p.variance_add_of_uncorrelated,
            true,
        ),
        ("indicator", p.indicator, false),
        ("indicator_nonneg", p.indicator_nonneg, true),
        ("indicator_le", p.indicator_le, true),
        ("variance_indicator", p.variance_indicator, true),
        (
            "variance_indicator_le_quarter",
            p.variance_indicator_le_quarter,
            true,
        ),
        ("markov_constructed", p.markov_constructed, true),
        ("chebyshev_inequality", p.chebyshev_inequality, true),
        ("covariance_comm", p.covariance_comm, true),
        ("covariance_add_right", p.covariance_add_right, true),
        ("covariance_smul_left", p.covariance_smul_left, true),
        ("sumVars", p.sum_vars, false),
        ("expectation_sumVars", p.expectation_sum_vars, true),
        ("covariance_sumVars_left", p.covariance_sum_vars_left, true),
        ("PairwiseUncorrelated", p.pairwise_uncorrelated, false),
        ("variance_sumVars", p.variance_sum_vars, true),
        ("variance_scaled_mean", p.variance_scaled_mean, true),
        (
            "chebyshev_sampleMean_uncorrelated",
            p.chebyshev_sample_mean_uncorrelated,
            true,
        ),
        (
            "variance_sampleMean_uncorrelated",
            p.variance_sample_mean_uncorrelated,
            true,
        ),
        (
            "weak_law_of_large_numbers",
            p.weak_law_of_large_numbers,
            true,
        ),
        (
            "bernoulli_law_of_large_numbers",
            p.bernoulli_law_of_large_numbers,
            true,
        ),
        (
            "variance_scaled_add_nonneg",
            p.variance_scaled_add_nonneg,
            true,
        ),
        (
            "covariance_sq_le_variance_mul_of_pos",
            p.covariance_sq_le_variance_mul_of_pos,
            true,
        ),
        (
            "covariance_sq_le_variance_mul_of_zero_zero",
            p.covariance_sq_le_variance_mul_of_zero_zero,
            true,
        ),
        (
            "covariance_sq_le_variance_mul",
            p.covariance_sq_le_variance_mul,
            true,
        ),
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

/// A CONCRETE Bernoulli instance, checked by `Eq.refl` alone against the
/// DEFINITIONS themselves — not against [`RatPrelude::variance_indicator`]'s
/// proof, which could be internally consistent yet prove a statement off by
/// a factor this check would catch. A fair coin: `a := 1`, `X k := k`, `p :=
/// const 1/2`, `n := 2` (`X 0 = 0 < 1`, `X 1 = 1 ≤ 1`, so the indicator
/// selects exactly outcome `1`). Hand computation: `E[𝟙] = 0·(1/2) +
/// 1·(1/2) = 1/2`; `Var[𝟙] = E[𝟙²] − E[𝟙]² = E[𝟙] − E[𝟙]² = 1/2 − 1/4 =
/// 1/4` (using `𝟙² = 𝟙`, [`indicator_sq_eq_self`](super::probability)).
#[test]
fn bernoulli_variance_at_one_half_reduces_to_one_quarter() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();

    let literal = |d: &mut IntDev<'_>, num: u32, idx: u32| -> ExprId {
        let numerator = d.num(num);
        let index = d.num(idx);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let a = literal(&mut d, 1, 0); // 1
    let half = literal(&mut d, 1, 1); // 1/2
    let quarter = literal(&mut d, 1, 3); // 1/4

    let x = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_nat = d.num(0);
        let val = d.const_app(p.nat_div_succ, &[k, zero_nat]);
        d.lam_fv(k_fv, nat, val)
    };
    let ind = d.const_app(p.indicator, &[a, x]);

    let pf = {
        let k_fv = d.fresh_fvar();
        d.lam_fv(k_fv, nat, half)
    };
    let n = d.num(2);

    let mu = d.const_app(p.expectation, &[ind, pf, n]);
    let mu_stmt = req(&mut d, mu, half);
    let mu_proof = rrefl(&mut d, mu);
    let mu_name = d
        .kernel()
        .name_str(anon, "Check.bernoulli_half_expectation");
    d.declare_theorem(mu_name, mu_stmt, mu_proof)
        .unwrap_or_else(|e| panic!("expectation did not reduce to 1/2: {e:?}"));

    let variance = d.const_app(p.variance, &[ind, pf, n]);
    let var_stmt = req(&mut d, variance, quarter);
    let var_proof = rrefl(&mut d, variance);
    let var_name = d.kernel().name_str(anon, "Check.bernoulli_half_variance");
    d.declare_theorem(var_name, var_stmt, var_proof)
        .unwrap_or_else(|e| panic!("variance did not reduce to 1/4: {e:?}"));
}

/// The negative control for
/// [`bernoulli_variance_at_one_half_reduces_to_one_quarter`]: the SAME
/// variance is NOT `1/2` (the mean itself — the off-by-`p`-instead-of-
/// `p(1-p)` bug a wrong `variance` definition could have). Must be REFUSED,
/// or the positive check above proves nothing.
#[test]
fn bernoulli_variance_at_one_half_is_not_one_half() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();

    let literal = |d: &mut IntDev<'_>, num: u32, idx: u32| -> ExprId {
        let numerator = d.num(num);
        let index = d.num(idx);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let a = literal(&mut d, 1, 0);
    let half = literal(&mut d, 1, 1);

    let x = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zero_nat = d.num(0);
        let val = d.const_app(p.nat_div_succ, &[k, zero_nat]);
        d.lam_fv(k_fv, nat, val)
    };
    let ind = d.const_app(p.indicator, &[a, x]);

    let pf = {
        let k_fv = d.fresh_fvar();
        d.lam_fv(k_fv, nat, half)
    };
    let n = d.num(2);

    let variance = d.const_app(p.variance, &[ind, pf, n]);
    let stmt = req(&mut d, variance, half);
    let proof = rrefl(&mut d, half);
    let name = d
        .kernel()
        .name_str(anon, "Check.bernoulli_variance_is_not_the_mean");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted Var[fair coin] = 1/2 (the MEAN, not p(1-p)=1/4), \
         so the reduction check above proves nothing"
    );
}

/// The quarter bound is TIGHT at `q = 1/2` — the fair coin is the unique
/// maximiser of `q(1-q)`: `4·(1/2)·(1/2) = 1` exactly, checked as an
/// EQUALITY by `Eq.refl` alone (not merely that
/// [`RatPrelude::variance_indicator_le_quarter`] admits `≤`, which would
/// also accept a bound that is off by a wide margin).
#[test]
fn quarter_bound_is_tight_at_one_half() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{radd, req, rmul, rone, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, num: u32, idx: u32| -> ExprId {
        let numerator = d.num(num);
        let index = d.num(idx);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };
    let half = literal(&mut d, 1, 1);
    let one_r = rone(&mut d, p);
    let two_r = radd(&mut d, one_r, one_r);
    let three_r = radd(&mut d, two_r, one_r);
    let four_r = radd(&mut d, three_r, one_r);

    let half_sq = rmul(&mut d, half, half);
    let four_half = rmul(&mut d, four_r, half);
    let four_half_sq = rmul(&mut d, four_r, half_sq);
    let bound_expr = rsub(&mut d, p, four_half, four_half_sq);

    let stmt = req(&mut d, bound_expr, one_r);
    let proof = rrefl(&mut d, bound_expr);
    let name = d
        .kernel()
        .name_str(anon, "Check.quarter_bound_tight_at_half");
    d.declare_theorem(name, stmt, proof)
        .unwrap_or_else(|e| panic!("4*(1/2)*(1/2) did not reduce to 1: {e:?}"));
}

/// `Rat.chebyshev_sampleMean_uncorrelated`'s rendered type, verbatim — this
/// IS the weak law of large numbers in its standard finite-sample
/// Chebyshev-bound shape (a bound on the ε²-weighted probability mass where
/// the sample mean of `m` pairwise-uncorrelated variables deviates from its
/// expectation by at least `ε`), and this pin exists so a future edit that
/// weakens it (drops the `IsDistribution` hypothesis, drops
/// `PairwiseUncorrelated`, or changes which quantity the bound is against)
/// is caught by a rendered-type diff rather than an unread doc comment. See
/// [`RatPrelude::chebyshev_sample_mean_uncorrelated`]'s own doc for the full
/// reading.
#[test]
fn chebyshev_sample_mean_uncorrelated_is_the_weak_law_of_large_numbers() {
    let (kernel, p) = built();
    let rendered = match kernel
        .environment()
        .get(p.chebyshev_sample_mean_uncorrelated)
        .expect("Rat.chebyshev_sampleMean_uncorrelated must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("Rat.chebyshev_sampleMean_uncorrelated must be a Theorem, found {other:?}"),
    };
    let text = kernel.render_lean(rendered);
    let normalised: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
    assert_eq!(
        normalised,
        "((x0 : ((x0 : AxNat) -> ((x1 : AxNat) -> Rat))) -> ((x1 : Rat) -> \
         ((x2 : ((x2 : AxNat) -> Rat)) -> ((x3 : AxNat) -> ((x4 : AxNat) -> \
         ((x5 : Rat.IsDistribution x2 x3) -> ((x6 : Rat.PairwiseUncorrelated x0 x4 x2 x3) -> \
         ((x7 : Rat.lt Rat.zero x1) -> Rat.le (Rat.mul (Rat.mul x1 x1) \
         (Rat.expectation (Rat.indicator (Rat.mul x1 x1) (fun (x8 : AxNat) => Rat.mul \
         (Rat.sub ((fun (x9 : AxNat) => Rat.mul (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) \
         (Rat.sumVars x0 x4 x9)) x8) (Rat.expectation (fun (x9 : AxNat) => Rat.mul \
         (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) (Rat.sumVars x0 x4 x9)) x2 x3)) \
         (Rat.sub ((fun (x9 : AxNat) => Rat.mul (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) \
         (Rat.sumVars x0 x4 x9)) x8) (Rat.expectation (fun (x9 : AxNat) => Rat.mul \
         (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) (Rat.sumVars x0 x4 x9)) x2 x3)))) x2 x3)) \
         (Rat.mul (Rat.mul (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) \
         (Rat.inv (Rat.natDivSucc x4 AxNat.zero))) (Rat.sumRange (fun (x8 : AxNat) => \
         Rat.variance (x0 x8) x2 x3) x4))))))))))",
        "Rat.chebyshev_sampleMean_uncorrelated's statement drifted from the weak-law reading"
    );
}

/// `Rat.weak_law_of_large_numbers` is a RENAMING, not a new result — its
/// rendered type must be BYTE-IDENTICAL to
/// [`RatPrelude::chebyshev_sample_mean_uncorrelated`]'s, checked directly
/// rather than trusted from the doc comment or the commit message.
#[test]
fn weak_law_of_large_numbers_is_byte_identical_to_the_theorem_it_renames() {
    let (kernel, p) = built();
    let cheb_ty = match kernel
        .environment()
        .get(p.chebyshev_sample_mean_uncorrelated)
        .expect("Rat.chebyshev_sampleMean_uncorrelated must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("Rat.chebyshev_sampleMean_uncorrelated must be a Theorem, found {other:?}"),
    };
    let wlln_ty = match kernel
        .environment()
        .get(p.weak_law_of_large_numbers)
        .expect("Rat.weak_law_of_large_numbers must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("Rat.weak_law_of_large_numbers must be a Theorem, found {other:?}"),
    };
    assert_eq!(
        kernel.render_lean(cheb_ty),
        kernel.render_lean(wlln_ty),
        "Rat.weak_law_of_large_numbers must be the SAME statement as \
         Rat.chebyshev_sampleMean_uncorrelated, byte for byte — it is a \
         renaming for discoverability, not a new theorem"
    );
}

/// `Rat.variance_sampleMean_uncorrelated`'s rendered type, verbatim — the
/// quantitative heart of the weak law named on its own: `Var[sample mean] =
/// (1/m)² · Σ_{j<m} Var[X_j]` under `IsDistribution` and
/// `PairwiseUncorrelated`, composing
/// [`RatPrelude::variance_scaled_mean`] and [`RatPrelude::variance_sumVars`].
#[test]
fn variance_sample_mean_uncorrelated_is_the_statement_briefed() {
    let (kernel, p) = built();
    let rendered = match kernel
        .environment()
        .get(p.variance_sample_mean_uncorrelated)
        .expect("Rat.variance_sampleMean_uncorrelated must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("Rat.variance_sampleMean_uncorrelated must be a Theorem, found {other:?}"),
    };
    let text = kernel.render_lean(rendered);
    let normalised: String = text.split_whitespace().collect::<Vec<_>>().join(" ");
    assert_eq!(
        normalised,
        "((x0 : ((x0 : AxNat) -> ((x1 : AxNat) -> Rat))) -> \
         ((x1 : ((x1 : AxNat) -> Rat)) -> ((x2 : AxNat) -> \
         ((x3 : Rat.IsDistribution x1 x2) -> ((x4 : AxNat) -> \
         ((x5 : Rat.PairwiseUncorrelated x0 x4 x1 x2) -> \
         Eq.{1} Rat (Rat.variance (fun (x6 : AxNat) => Rat.mul \
         (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) (Rat.sumVars x0 x4 x6)) x1 x2) \
         (Rat.mul (Rat.mul (Rat.inv (Rat.natDivSucc x4 AxNat.zero)) \
         (Rat.inv (Rat.natDivSucc x4 AxNat.zero))) (Rat.sumRange (fun (x6 : AxNat) => \
         Rat.variance (x0 x6) x1 x2) x4))))))))",
        "Rat.variance_sampleMean_uncorrelated's statement drifted from the briefed one"
    );
}

/// `Rat.expectation X p n` closes by `Eq.refl` alone against `sumRange (fun k
/// => X k * p k) n`, over a **symbolic** `X`/`p`/`n` — the same convention
/// [`sum_range_defining_equations_close_by_refl_alone`] follows, so this
/// checks the definition itself rather than a fully-computed instance.
#[test]
fn expectation_defining_equation_closes_by_refl_alone() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl, rsum_range};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let summand = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let pk = d.apply(pf, &[k]);
        let body = rmul(&mut d, xk, pk);
        d.lam_fv(k_fv, nat, body)
    };
    let lhs = d.const_app(p.expectation, &[x, pf, n]);
    let rhs = rsum_range(&mut d, p, summand, n);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, inner);
        d.pi_fv(x_fv, fn_ty, with_pf)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let name = d.kernel().name_str(anon, "Check.expectation_defn_refl");
    d.declare_theorem(name, ty, value).unwrap_or_else(|e| {
        panic!(
            "Rat.expectation did not reduce to its defining sum by refl alone: {}",
            d.explain(&e)
        )
    });
}

/// The negative control for
/// [`expectation_defining_equation_closes_by_refl_alone`]: the same route
/// pointed at the summand with the multiplication **swapped**
/// (`p k * X k` instead of `X k * p k`), over the same symbolic `X`/`p`/`n`.
/// `Rat.mul` is not definitionally commutative (`Rat.mul_comm` is a proved
/// law, not a reduction rule), so this must be **REJECTED** — otherwise the
/// computation check above proves nothing.
#[test]
fn expectation_wrong_multiplication_order_is_rejected() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl, rsum_range};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let swapped_summand = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let pk = d.apply(pf, &[k]);
        let body = rmul(&mut d, pk, xk); // swapped
        d.lam_fv(k_fv, nat, body)
    };
    let lhs = d.const_app(p.expectation, &[x, pf, n]);
    let rhs = rsum_range(&mut d, p, swapped_summand, n);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, inner);
        d.pi_fv(x_fv, fn_ty, with_pf)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let name = d
        .kernel()
        .name_str(anon, "Check.expectation_swapped_mul_order");
    assert!(
        d.declare_theorem(name, ty, value).is_err(),
        "the kernel accepted Rat.expectation's summand with the multiplication \
         swapped, so the computation check above proves nothing"
    );
}

/// `Rat.variance X p n` closes by `Eq.refl` alone against `expectation (fun k
/// => sub (X k) (expectation X p n) * sub (X k) (expectation X p n)) p n`,
/// over a **symbolic** `X`/`p`/`n` — the same convention
/// [`expectation_defining_equation_closes_by_refl_alone`] follows.
#[test]
fn variance_defining_equation_closes_by_refl_alone() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let mu = d.const_app(p.expectation, &[x, pf, n]);
    let summand = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let gap = rsub(&mut d, p, xk, mu);
        let body = rmul(&mut d, gap, gap);
        d.lam_fv(k_fv, nat, body)
    };
    let lhs = d.const_app(p.variance, &[x, pf, n]);
    let rhs = d.const_app(p.expectation, &[summand, pf, n]);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, inner);
        d.pi_fv(x_fv, fn_ty, with_pf)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let name = d.kernel().name_str(anon, "Check.variance_defn_refl");
    d.declare_theorem(name, ty, value).unwrap_or_else(|e| {
        panic!(
            "Rat.variance did not reduce to its defining expectation by refl alone: {}",
            d.explain(&e)
        )
    });
}

/// The negative control for
/// [`variance_defining_equation_closes_by_refl_alone`]: the same route with
/// the subtraction **swapped** (`sub (expectation X p n) (X k)` instead of
/// `sub (X k) (expectation X p n)`) inside the squared summand. `Rat.sub` is
/// not definitionally anti-commutative (`(a-b)² = (b-a)²` is a proved
/// identity, not a reduction rule), so this must be **REJECTED** — otherwise
/// the computation check above proves nothing.
#[test]
fn variance_swapped_subtraction_order_is_rejected() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let mu = d.const_app(p.expectation, &[x, pf, n]);
    let swapped_summand = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let gap = rsub(&mut d, p, mu, xk); // swapped
        let body = rmul(&mut d, gap, gap);
        d.lam_fv(k_fv, nat, body)
    };
    let lhs = d.const_app(p.variance, &[x, pf, n]);
    let rhs = d.const_app(p.expectation, &[swapped_summand, pf, n]);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, inner);
        d.pi_fv(x_fv, fn_ty, with_pf)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        d.lam_fv(x_fv, fn_ty, with_pf)
    };
    let name = d
        .kernel()
        .name_str(anon, "Check.variance_swapped_sub_order");
    assert!(
        d.declare_theorem(name, ty, value).is_err(),
        "the kernel accepted Rat.variance's summand with the subtraction \
         swapped, so the computation check above proves nothing"
    );
}

/// `Rat.covariance X Y p n` closes by `Eq.refl` alone against `sub
/// (expectation (fun k => X k * Y k) p n) (mul (expectation X p n)
/// (expectation Y p n))`, over **symbolic** `X`/`Y`/`p`/`n` — the same
/// convention [`variance_defining_equation_closes_by_refl_alone`] follows.
#[test]
fn covariance_defining_equation_closes_by_refl_alone() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let xy = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let yk = d.apply(y, &[k]);
        let body = rmul(&mut d, xk, yk);
        d.lam_fv(k_fv, nat, body)
    };
    let e_xy = d.const_app(p.expectation, &[xy, pf, n]);
    let ex = d.const_app(p.expectation, &[x, pf, n]);
    let ey = d.const_app(p.expectation, &[y, pf, n]);
    let exey = rmul(&mut d, ex, ey);

    let lhs = d.const_app(p.covariance, &[x, y, pf, n]);
    let rhs = rsub(&mut d, p, e_xy, exey);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, inner);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let name = d.kernel().name_str(anon, "Check.covariance_defn_refl");
    d.declare_theorem(name, ty, value).unwrap_or_else(|e| {
        panic!(
            "Rat.covariance did not reduce to its defining sub-of-expectations \
             by refl alone: {}",
            d.explain(&e)
        )
    });
}

/// The negative control for
/// [`covariance_defining_equation_closes_by_refl_alone`]: the same route with
/// the subtraction **swapped** (`sub (mul (expectation X p n) (expectation Y
/// p n)) (expectation (fun k => X k * Y k) p n)` instead of the defined
/// order). `Rat.sub` is not definitionally anti-commutative, so this must be
/// **REJECTED** — otherwise the computation check above proves nothing.
#[test]
fn covariance_swapped_subtraction_order_is_rejected() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let fn_ty = d.arrow(nat, carrier);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let pf_fv = d.fresh_fvar();
    let pf = d.kernel().fvar(pf_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let xy = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let xk = d.apply(x, &[k]);
        let yk = d.apply(y, &[k]);
        let body = rmul(&mut d, xk, yk);
        d.lam_fv(k_fv, nat, body)
    };
    let e_xy = d.const_app(p.expectation, &[xy, pf, n]);
    let ex = d.const_app(p.expectation, &[x, pf, n]);
    let ey = d.const_app(p.expectation, &[y, pf, n]);
    let exey = rmul(&mut d, ex, ey);

    let lhs = d.const_app(p.covariance, &[x, y, pf, n]);
    let swapped_rhs = rsub(&mut d, p, exey, e_xy); // swapped
    let stmt = req(&mut d, lhs, swapped_rhs);
    let proof = rrefl(&mut d, swapped_rhs);
    let ty = {
        let inner = d.pi_fv(n_fv, nat, stmt);
        let with_pf = d.pi_fv(pf_fv, fn_ty, inner);
        let with_y = d.pi_fv(y_fv, fn_ty, with_pf);
        d.pi_fv(x_fv, fn_ty, with_y)
    };
    let value = {
        let inner = d.lam_fv(n_fv, nat, proof);
        let with_pf = d.lam_fv(pf_fv, fn_ty, inner);
        let with_y = d.lam_fv(y_fv, fn_ty, with_pf);
        d.lam_fv(x_fv, fn_ty, with_y)
    };
    let name = d
        .kernel()
        .name_str(anon, "Check.covariance_swapped_sub_order");
    assert!(
        d.declare_theorem(name, ty, value).is_err(),
        "the kernel accepted Rat.covariance with the subtraction swapped, \
         so the computation check above proves nothing"
    );
}

// --- the constructed indicator (`rat_prelude::probability`) ----------------

/// Every declaration `probability::declare_probability` adds in its
/// indicator section — `Rat.indicator` itself and the six theorems built on
/// it — is a **checked** definition or theorem with an empty axiom footprint,
/// read out of the kernel, not off the diff.
#[test]
fn the_indicator_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("indicator", p.indicator, false),
        ("indicator_nonneg", p.indicator_nonneg, true),
        ("indicator_le", p.indicator_le, true),
        ("variance_indicator", p.variance_indicator, true),
        (
            "variance_indicator_le_quarter",
            p.variance_indicator_le_quarter,
            true,
        ),
        ("markov_constructed", p.markov_constructed, true),
        ("chebyshev_inequality", p.chebyshev_inequality, true),
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

/// `Rat.indicator` **computes**, on both branches of the `Rat.ble` it
/// dispatches on — the same standard [`rat_ble_computes_on_both_branches`]
/// holds `Rat.ble` itself to, checked by `Eq.refl` alone rather than by
/// trusting [`declare_indicator_nonneg`]/[`declare_indicator_le`] to be
/// about the definition this file actually declared.
#[test]
fn rat_indicator_computes_on_both_branches() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rone, rrefl, rzero};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };
    let const_x = |d: &mut IntDev<'_>, value: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, value)
    };

    // (label, a, X's constant value, ble a (X k) expected)
    let cases: [(&str, u32, u32, bool); 2] =
        [("selected", 3, 5, true), ("not_selected", 7, 5, false)];
    for (label, av, xv, expected) in cases {
        let a = literal(&mut d, av);
        let x_val = literal(&mut d, xv);
        let x = const_x(&mut d, x_val);
        let k = d.num(0);
        let indicator_val = d.const_app(p.indicator, &[a, x, k]);
        let expected_value = if expected {
            rone(&mut d, p)
        } else {
            rzero(&mut d, p)
        };
        let stmt = req(&mut d, indicator_val, expected_value);
        let proof = rrefl(&mut d, indicator_val);
        let name = d
            .kernel()
            .name_str(anon, format!("Check.indicator_{label}"));
        d.declare_theorem(name, stmt, proof)
            .unwrap_or_else(|e| panic!("Rat.indicator did not reduce for {label}: {e:?}"));
    }
}

/// The negative control for [`rat_indicator_computes_on_both_branches`]:
/// `Rat.indicator 7 (fun _ => 5) 0` returning `Rat.one` on the **false**
/// branch (`Rat.ble 7 5 = false`). `Rat.indicator`'s whole point is
/// discharging `markov_inequality`'s pointwise hypothesis
/// ([`declare_indicator_le`]); a definition that quietly returned `1` when
/// `Rat.ble` is `false` would make that hypothesis false for any `a > X k`.
/// This must be REFUSED, or the computation check above proves nothing.
#[test]
fn rat_indicator_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rone, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };
    let a = literal(&mut d, 7);
    let x_val = literal(&mut d, 5);
    let x = {
        let k_fv = d.fresh_fvar();
        let nat = d.nat_ty();
        d.lam_fv(k_fv, nat, x_val)
    };
    let k = d.num(0);
    let indicator_val = d.const_app(p.indicator, &[a, x, k]);
    let one = rone(&mut d, p);
    let stmt = req(&mut d, indicator_val, one);
    let proof = rrefl(&mut d, one);
    let name = d
        .kernel()
        .name_str(anon, "Check.indicator_false_branch_is_not_one");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.indicator 7 (fun _ => 5) 0 = 1`, so the \
         computation check above proves nothing"
    );
}

#[test]
fn sum_vars_succ_closes_by_refl_alone() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, rat_ty, req, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let nat_fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, nat_fn_ty);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    // sumVars X (succ m) k = sumVars X m k + X m k, by Eq.refl — the addend
    // order sumRange's own succ ι-reduction actually produces.
    let sm = d.succ(m);
    let lhs = d.const_app(p.sum_vars, &[x, sm, k]);
    let sv_m_k = d.const_app(p.sum_vars, &[x, m, k]);
    let x_m = d.apply(x, &[m]);
    let x_m_k = d.apply(x_m, &[k]);
    let rhs = radd(&mut d, sv_m_k, x_m_k);
    let stmt = req(&mut d, lhs, rhs);
    let proof = rrefl(&mut d, rhs);
    let ty = {
        let inner = d.pi_fv(k_fv, nat, stmt);
        let with_m = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(x_fv, x_ty, with_m)
    };
    let value = {
        let inner = d.lam_fv(k_fv, nat, proof);
        let with_m = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(x_fv, x_ty, with_m)
    };
    let name = d.kernel().name_str(anon, "Check.sum_vars_succ_refl");
    d.declare_theorem(name, ty, value).unwrap_or_else(|e| {
        panic!(
            "Rat.sumVars did not reduce to sumVars X m k + X m k at succ m \
             by refl alone: {}",
            d.explain(&e)
        )
    });
}

#[test]
fn sum_vars_succ_wrong_order_is_rejected() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, rat_ty, req, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let nat_fn_ty = d.arrow(nat, carrier);
    let x_ty = d.arrow(nat, nat_fn_ty);

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let sm = d.succ(m);
    let lhs = d.const_app(p.sum_vars, &[x, sm, k]);
    let sv_m_k = d.const_app(p.sum_vars, &[x, m, k]);
    let x_m = d.apply(x, &[m]);
    let x_m_k = d.apply(x_m, &[k]);
    let wrong_rhs = radd(&mut d, x_m_k, sv_m_k); // swapped
    let stmt = req(&mut d, lhs, wrong_rhs);
    let proof = rrefl(&mut d, wrong_rhs);
    let ty = {
        let inner = d.pi_fv(k_fv, nat, stmt);
        let with_m = d.pi_fv(m_fv, nat, inner);
        d.pi_fv(x_fv, x_ty, with_m)
    };
    let value = {
        let inner = d.lam_fv(k_fv, nat, proof);
        let with_m = d.lam_fv(m_fv, nat, inner);
        d.lam_fv(x_fv, x_ty, with_m)
    };
    let name = d.kernel().name_str(anon, "Check.sum_vars_succ_wrong_order");
    assert!(
        d.declare_theorem(name, ty, value).is_err(),
        "the kernel accepted the swapped-order sumVars succ equation by \
         Eq.refl, so the computation check above proves nothing"
    );
}

// --- `Rat.sumRange` diagonal/rectangle reindexing (`rat_prelude::diagonal`) -

/// Every declaration `diagonal::declare_diagonal` adds — the three theorems
/// built on `Rat.sumRange` (counted from the list below, not carried over
/// from an earlier count) — is a **checked** theorem with an empty axiom
/// footprint, read out of the kernel, not off the diff.
#[test]
fn the_diagonal_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("sumRange_split", p.sum_range_split),
        ("sumRange_diagonal", p.sum_range_diagonal),
        (
            "sumRange_rect_eq_diag_add_corner",
            p.sum_range_rect_eq_diag_add_corner,
        ),
    ];
    for (label, name) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "Rat.{label} must be a checked Theorem, found a different kind"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `Rat.sumRange_diagonal` at a concrete instance: `F i j := 1` (constant),
/// `n = 3`. Both the antidiagonal grouping (`Σ_{k<3} Σ_{i≤k} F i (k−i)`) and
/// the row grouping (`Σ_{i<3} Σ_{j<3−i} F i j`) COUNT the same 6-point
/// triangle `{(i,j) : i+j<3}` — `(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)` — and
/// both must independently reduce to `6`, so this is a genuine reindexing
/// check over `Rat` values, not just an admission. A constant summand (not
/// `add i j`, unlike `Nat`'s own version of this test) keeps the concrete
/// arithmetic to `Rat.add`/normalize alone, without also needing a `Nat →
/// Rat` conversion for the summand itself.
#[test]
fn sum_range_diagonal_computes_at_a_concrete_instance_over_rat() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rsum_range};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // F := fun i j => 1 (constant Rat one).
    let one = literal(&mut d, 1);
    let ff = {
        let i_fv = d.fresh_fvar();
        let j_fv = d.fresh_fvar();
        let inner = d.lam_fv(j_fv, nat, one);
        d.lam_fv(i_fv, nat, inner)
    };
    let three = d.num(3);
    let six = literal(&mut d, 6);

    let proof = d.lemma(p.sum_range_diagonal, &[ff, three]);
    let inferred = d
        .kernel()
        .infer(proof)
        .unwrap_or_else(|e| panic!("sumRange_diagonal(F,3) should infer: {e:?}"));

    // The antidiagonal (triangle) sum, built independently of
    // `diagonal.rs`'s own helpers.
    let triangle = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ki = d.sub(k, i);
        let fiki = d.apply(ff, &[i, ki]);
        let diag_inner = d.lam_fv(i_fv, nat, fiki);
        let sk = d.succ(k);
        let diag_sum = rsum_range(&mut d, p, diag_inner, sk);
        let t_fn = d.lam_fv(k_fv, nat, diag_sum);
        rsum_range(&mut d, p, t_fn, three)
    };
    // The row-major sum, likewise independently built.
    let rows = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let fij = d.apply(ff, &[i, j]);
        let row_inner = d.lam_fv(j_fv, nat, fij);
        let ni = d.sub(three, i);
        let row_sum_i = rsum_range(&mut d, p, row_inner, ni);
        let row_fn = d.lam_fv(i_fv, nat, row_sum_i);
        rsum_range(&mut d, p, row_fn, three)
    };

    let expected = req(&mut d, triangle, rows);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "sumRange_diagonal(F,3) should state the antidiagonal sum equals the row-major sum"
    );
    assert!(
        d.kernel().def_eq(triangle, six),
        "the antidiagonal (triangle) sum of the constant 1 over {{(i,j):i+j<3}} \
         (6 points) must reduce to 6"
    );
    assert!(
        d.kernel().def_eq(rows, six),
        "the row-major sum of the constant 1 over {{(i,j):i+j<3}} (6 points) \
         must reduce to 6"
    );

    assert!(
        d.kernel().axiom_footprint(p.sum_range_diagonal).is_empty(),
        "sumRange_diagonal must rest on zero axioms"
    );
}

/// `Rat.sumRange_rect_eq_diag_add_corner` at a concrete instance: `F i j :=
/// 1`, `n = 2`. The rectangle `{i<2,j<2}` (4 points) splits into the
/// antidiagonal triangle `{i+j<2}` (3 points: `(0,0),(1,0),(0,1)`) and the
/// corner `{i<2,j<2,i+j≥2}` (the single point `(1,1)`) — `4 = 3 + 1`, checked
/// both as the theorem's own statement AND by independently reducing all
/// three sums.
#[test]
fn sum_range_rect_eq_diag_add_corner_computes_at_a_concrete_instance_over_rat() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{radd, req, rsum_range};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();

    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let one = literal(&mut d, 1);
    let ff = {
        let i_fv = d.fresh_fvar();
        let j_fv = d.fresh_fvar();
        let inner = d.lam_fv(j_fv, nat, one);
        d.lam_fv(i_fv, nat, inner)
    };
    let two = d.num(2);

    let proof = d.lemma(p.sum_range_rect_eq_diag_add_corner, &[ff, two]);
    let inferred = d
        .kernel()
        .infer(proof)
        .unwrap_or_else(|e| panic!("sumRange_rect_eq_diag_add_corner(F,2) should infer: {e:?}"));

    // The rectangle {(i,j): i<2, j<2} -- 4 points -- built independently.
    let rectangle = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let fij = d.apply(ff, &[i, j]);
        let row_inner = d.lam_fv(j_fv, nat, fij);
        let row_sum_i = rsum_range(&mut d, p, row_inner, two);
        let rect_row = d.lam_fv(i_fv, nat, row_sum_i);
        rsum_range(&mut d, p, rect_row, two)
    };
    // The antidiagonal triangle {(i,j): i+j<2} -- 3 points -- built
    // independently.
    let triangle = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ki = d.sub(k, i);
        let fiki = d.apply(ff, &[i, ki]);
        let diag_inner = d.lam_fv(i_fv, nat, fiki);
        let sk = d.succ(k);
        let diag_sum = rsum_range(&mut d, p, diag_inner, sk);
        let t_fn = d.lam_fv(k_fv, nat, diag_sum);
        rsum_range(&mut d, p, t_fn, two)
    };
    // The corner {(i,j): i<2, j<2, i+j>=2} -- the single point (1,1) --
    // built independently.
    let corner = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let k_fv = d.fresh_fvar();
        let sub_2i = d.sub(two, i);
        let shifted_idx = {
            let k = d.kernel().fvar(k_fv);
            d.add(sub_2i, k)
        };
        let fi_shifted = d.apply(ff, &[i, shifted_idx]);
        let corner_inner = d.lam_fv(k_fv, nat, fi_shifted);
        let corner_sum_i = rsum_range(&mut d, p, corner_inner, i);
        let corner_row = d.lam_fv(i_fv, nat, corner_sum_i);
        rsum_range(&mut d, p, corner_row, two)
    };

    let rhs = radd(&mut d, triangle, corner);
    let expected = req(&mut d, rectangle, rhs);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "sumRange_rect_eq_diag_add_corner(F,2) should state rectangle = triangle + corner"
    );

    let four = literal(&mut d, 4);
    let three = literal(&mut d, 3);
    assert!(
        d.kernel().def_eq(rectangle, four),
        "the rectangle sum of the constant 1 over {{i<2,j<2}} (4 points) must reduce to 4"
    );
    assert!(
        d.kernel().def_eq(triangle, three),
        "the triangle sum of the constant 1 over {{i+j<2}} (3 points) must reduce to 3"
    );
    assert!(
        d.kernel().def_eq(corner, one),
        "the corner sum of the constant 1 over {{i<2,j<2,i+j>=2}} (1 point) must reduce to 1"
    );

    assert!(
        d.kernel()
            .axiom_footprint(p.sum_range_rect_eq_diag_add_corner)
            .is_empty(),
        "sumRange_rect_eq_diag_add_corner must rest on zero axioms"
    );
}

// --- polynomials (`rat_prelude::polynomial`) --------------------------------

/// Every declaration `polynomial::declare_polynomial` adds — `Rat.pow`,
/// `Rat.polyEval`, and the six theorems built on them — is a **checked**
/// definition or theorem with an empty axiom footprint, read out of the
/// kernel, not off the diff. (`built()` already implies the kernel accepted
/// every one of these proofs — a failed `add_declaration` would have made
/// `build_rat_prelude` return `Err` and this helper's own `.expect` panic —
/// so this test's job is the *kind*/footprint check, not re-proving
/// acceptance.)
#[test]
fn the_polynomial_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("pow", p.pow, false),
        ("pow_zero", p.pow_zero, true),
        ("pow_succ", p.pow_succ, true),
        ("polyEval", p.poly_eval, false),
        ("polyEval_zero", p.poly_eval_zero, true),
        ("polyEval_succ", p.poly_eval_succ, true),
        ("polyEval_add", p.poly_eval_add, true),
        ("polyEval_smul", p.poly_eval_smul, true),
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

/// `Rat.pow` **computes**: `2^3 = 8`, by `Eq.refl` on concrete literals —
/// not by trusting `pow_succ`/`pow_zero` (proved symbolically, over opaque
/// `a`/`m`) to be about the definition this file actually declared.
#[test]
fn rat_pow_computes_on_a_concrete_literal() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rpow, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let two = literal(&mut d, 2);
    let three_n = d.num(3);
    let power = rpow(&mut d, p, two, three_n);
    let eight = literal(&mut d, 8);
    let stmt = req(&mut d, power, eight);
    let proof = rrefl(&mut d, power);
    let name = d.kernel().name_str(anon, "Check.pow_two_cubed");
    d.declare_theorem(name, stmt, proof)
        .unwrap_or_else(|e| panic!("Rat.pow did not reduce on 2^3: {}", d.explain(&e)));
}

/// The negative control for [`rat_pow_computes_on_a_concrete_literal`]:
/// `2^3 = 9` must be REFUSED, or the reduction check above measures nothing.
#[test]
fn rat_pow_reduction_check_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{req, rpow, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let two = literal(&mut d, 2);
    let three_n = d.num(3);
    let power = rpow(&mut d, p, two, three_n);
    let nine = literal(&mut d, 9);
    let stmt = req(&mut d, power, nine);
    let proof = rrefl(&mut d, power);
    let name = d.kernel().name_str(anon, "Check.pow_two_cubed_is_not_nine");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `Rat.pow 2 3 = 9`, so the pow reduction check proves nothing"
    );
}

/// **The mandatory concrete computation test.** `Rat.polyEval` evaluates the
/// linear polynomial `p(i) = 1 + 2i` (as the coefficient function `c 0 = 1`,
/// `c (succ _) = 2`, degree bound `n = 2`) at `x = 3`: `p(3) = 1·1 + 2·3 =
/// 7`, checked by `Eq.refl` alone — not by trusting `polyEval_zero`/
/// `polyEval_succ` (proved symbolically) to be about the definition this
/// file actually declared.
#[test]
fn rat_poly_eval_computes_a_concrete_polynomial() {
    use crate::BinderInfo;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_ty, req, rpoly_eval, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // c := fun i => Nat.rec (motive := fun _ => Rat) 1 (fun _ _ => 2) i,
    // i.e. c 0 = 1, c (succ _) = 2 — enough to fix c at the two indices
    // (0, 1) that a degree bound of 2 ever inspects.
    let coeffs = {
        let one_r = literal(&mut d, 1);
        let two_r = literal(&mut d, 2);
        let anon_binder = d.anon_name();
        let one_level = d.level_one();
        let motive = d
            .kernel()
            .lam(anon_binder, nat, carrier, BinderInfo::Default);
        let minor_succ = {
            let j_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let inner = d.lam_fv(ih_fv, carrier, two_r);
            d.lam_fv(j_fv, nat, inner)
        };
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let rec_name = d.prelude().rec;
        let rec = d.kernel().const_(rec_name, vec![one_level]);
        let body = d.apply(rec, &[motive, one_r, minor_succ, i]);
        d.lam_fv(i_fv, nat, body)
    };

    let n = d.num(2);
    let x = literal(&mut d, 3);
    let evaluated = rpoly_eval(&mut d, p, coeffs, n, x);
    let seven = literal(&mut d, 7);
    let stmt = req(&mut d, evaluated, seven);
    let proof = rrefl(&mut d, evaluated);
    let name = d.kernel().name_str(anon, "Check.poly_eval_linear_at_three");
    d.declare_theorem(name, stmt, proof).unwrap_or_else(|e| {
        panic!(
            "Rat.polyEval did not reduce to 7 on (1+2i) at x=3: {}",
            d.explain(&e)
        )
    });
}

/// The negative control for
/// [`rat_poly_eval_computes_a_concrete_polynomial`]: the same polynomial at
/// the same point evaluated against `8` instead of `7` must be REFUSED, or
/// the computation check above measures nothing.
#[test]
fn rat_poly_eval_computation_check_can_fail() {
    use crate::BinderInfo;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_ty, req, rpoly_eval, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    let coeffs = {
        let one_r = literal(&mut d, 1);
        let two_r = literal(&mut d, 2);
        let anon_binder = d.anon_name();
        let one_level = d.level_one();
        let motive = d
            .kernel()
            .lam(anon_binder, nat, carrier, BinderInfo::Default);
        let minor_succ = {
            let j_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let inner = d.lam_fv(ih_fv, carrier, two_r);
            d.lam_fv(j_fv, nat, inner)
        };
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let rec_name = d.prelude().rec;
        let rec = d.kernel().const_(rec_name, vec![one_level]);
        let body = d.apply(rec, &[motive, one_r, minor_succ, i]);
        d.lam_fv(i_fv, nat, body)
    };

    let n = d.num(2);
    let x = literal(&mut d, 3);
    let evaluated = rpoly_eval(&mut d, p, coeffs, n, x);
    let eight = literal(&mut d, 8);
    let stmt = req(&mut d, evaluated, eight);
    let proof = rrefl(&mut d, evaluated);
    let name = d
        .kernel()
        .name_str(anon, "Check.poly_eval_linear_at_three_is_not_eight");
    assert!(
        d.declare_theorem(name, stmt, proof).is_err(),
        "the kernel accepted `polyEval (1+2i) 2 3 = 8`, so the polyEval computation \
         check proves nothing"
    );
}

/// `polyEval_mul` (the finite Cauchy product) is NOT attempted in this
/// prelude, and this test is the kernel-confirmed reason why: the natural
/// candidate statement `polyEval (conv a b) (m+n-1) x = polyEval a m x *
/// polyEval b n x`, with `conv a b k := sumRange (fun i => a i * b (k-i))
/// (k+1)` the plain (untruncated) antidiagonal formula, is FALSE for
/// `a`/`b` that are not required to vanish beyond their own bound.
///
/// Take `a 0 = 1`, `a (succ _) = 5` (so `m = 2` means "`a`'s declared
/// coefficients are `1, 5`"), and `b 0 = 3`, `b (succ _) = 100` (`n = 1`
/// means "`b`'s declared coefficient is `3`"; `b 1 = 100` is `b`'s value
/// PAST its declared bound — `polyEval b 1 x` never looks at it, but nothing
/// stops it being nonzero). The truncated rectangle product's `x^1`
/// coefficient is `a 1 * b 0 = 5*3 = 15`. But `conv a b 1` — the coefficient
/// `polyEval_mul` would need to equal `15` — is `a 0 * b 1 + a 1 * b 0 =
/// 1*100 + 5*3 = 115`: `conv` sums the FULL antidiagonal `{(i,j) : i+j=1}`,
/// which includes `(0,1)`, a point OUTSIDE the `m×n` rectangle `{i<2,j<1}`
/// (since `j=1 ≥ n=1`). `conv`'s own formula is correct (it is exactly the
/// infinite-power-series Cauchy product, confirmed positively below); the
/// gap is that it is not, by itself, the TRUNCATED product `polyEval_mul`
/// would need — that needs either an extra hypothesis (`a`/`b` vanish beyond
/// `m`/`n`) or a `conv` bounded by BOTH `m` and `n` (not the same-bound `n×n`
/// square `rat_prelude/diagonal.rs` supplies), neither built here.
#[test]
fn naive_conv_disagrees_with_the_truncated_rectangle_product() {
    use crate::BinderInfo;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_ty, req, rmul, rrefl, rsum_range};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let carrier = rat_ty(&mut d);
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };

    // A step function `Nat -> Rat`, `f 0 = at_zero`, `f (succ _) = beyond`,
    // via `Nat.rec` -- exactly `rat_poly_eval_computes_a_concrete_polynomial`'s
    // own `coeffs` builder, reused for both `a` and `b`.
    let step = |d: &mut IntDev<'_>, at_zero: ExprId, beyond: ExprId| -> ExprId {
        let anon_binder = d.anon_name();
        let one_level = d.level_one();
        let motive = d
            .kernel()
            .lam(anon_binder, nat, carrier, BinderInfo::Default);
        let minor_succ = {
            let j_fv = d.fresh_fvar();
            let ih_fv = d.fresh_fvar();
            let inner = d.lam_fv(ih_fv, carrier, beyond);
            d.lam_fv(j_fv, nat, inner)
        };
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let rec_name = d.prelude().rec;
        let rec = d.kernel().const_(rec_name, vec![one_level]);
        let body = d.apply(rec, &[motive, at_zero, minor_succ, i]);
        d.lam_fv(i_fv, nat, body)
    };

    let one_r = literal(&mut d, 1);
    let five_r = literal(&mut d, 5);
    let a = step(&mut d, one_r, five_r); // a 0 = 1, a 1 = 5

    let three_r = literal(&mut d, 3);
    let hundred_r = literal(&mut d, 100);
    let b = step(&mut d, three_r, hundred_r); // b 0 = 3, b 1 = 100 (junk beyond n=1)

    // conv a b k := sumRange (fun i => a i * b (k-i)) (k+1), built inline
    // (not a named `Rat.conv` -- this test does not commit to that shape
    // being the right one, per the module doc above).
    let conv = |d: &mut IntDev<'_>, a: ExprId, b: ExprId, k: ExprId| -> ExprId {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ai = d.apply(a, &[i]);
        let ki = d.sub(k, i);
        let bki = d.apply(b, &[ki]);
        let term = rmul(d, ai, bki);
        let inner = d.lam_fv(i_fv, nat, term);
        let sk = d.succ(k);
        rsum_range(d, p, inner, sk)
    };

    // Positive control: conv's OWN antidiagonal formula computes correctly
    // (the "re-verify i<=k, so no truncation fires" check the task asked
    // for, at a third concrete instance beyond k=0,1,2 symbolic hand-check).
    let zero_n = d.zero();
    let conv_0 = conv(&mut d, a, b, zero_n);
    let expected_0 = literal(&mut d, 3); // a0*b0 = 1*3
    let stmt0 = req(&mut d, conv_0, expected_0);
    let proof0 = rrefl(&mut d, conv_0);
    let name0 = d.kernel().name_str(anon, "Check.conv_k0_is_three");
    d.declare_theorem(name0, stmt0, proof0)
        .unwrap_or_else(|e| panic!("conv(a,b,0) did not reduce to 3: {}", d.explain(&e)));

    let one_n = d.num(1);
    let conv_1 = conv(&mut d, a, b, one_n);
    let expected_1 = literal(&mut d, 115); // a0*b1 + a1*b0 = 100 + 15
    let stmt1 = req(&mut d, conv_1, expected_1);
    let proof1 = rrefl(&mut d, conv_1);
    let name1 = d.kernel().name_str(anon, "Check.conv_k1_is_115");
    d.declare_theorem(name1, stmt1, proof1)
        .unwrap_or_else(|e| panic!("conv(a,b,1) did not reduce to 115: {}", d.explain(&e)));

    // Negative control -- THE FINDING: conv(a,b,1) is NOT the truncated
    // rectangle coefficient a1*b0 = 15. If it were, `polyEval_mul`'s naive
    // statement (no vanishing-beyond-bound hypotheses on a/b) would be
    // provable as stated; it is not.
    let conv_1_again = conv(&mut d, a, b, one_n);
    let fifteen = literal(&mut d, 15);
    let wrong_stmt = req(&mut d, conv_1_again, fifteen);
    let wrong_proof = rrefl(&mut d, conv_1_again);
    let wrong_name = d.kernel().name_str(anon, "Check.conv_k1_is_not_fifteen");
    assert!(
        d.declare_theorem(wrong_name, wrong_stmt, wrong_proof)
            .is_err(),
        "the kernel accepted conv(a,b,1) = 15 (the truncated rectangle \
         coefficient a1*b0), but conv(a,b,1) = 115 (a0*b1+a1*b0) since conv \
         sums the FULL antidiagonal including the out-of-rectangle point \
         (0,1) -- so the naive polyEval_mul statement is not merely \
         unattempted here, it is false as stated without extra hypotheses"
    );
}

/// `dotN_cauchy_schwarz`'s statement rendered verbatim — SQUARED, the
/// unweakened form: `(dotN u v n) * (dotN u v n) <= (dotN u u n) * (dotN v v
/// n)`, not `|dotN u v n| <= sqrt(...)` (ℚ has no square root). The same
/// pinning discipline
/// [`the_order_completeness_statements_are_the_unweakened_ones`] uses for
/// `le_antisymm`/`lt_trichotomy`.
#[test]
fn the_cauchy_schwarz_statement_is_squared() {
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
        rendered(&mut kernel, p.dot_n_cauchy_schwarz),
        "((x0 : ((x0 : AxNat) -> Rat)) -> ((x1 : ((x1 : AxNat) -> Rat)) -> ((x2 : AxNat) -> \
         Rat.le (Rat.mul (Rat.dotN x0 x1 x2) (Rat.dotN x0 x1 x2)) \
         (Rat.mul (Rat.dotN x0 x0 x2) (Rat.dotN x1 x1 x2)))))"
    );
}

// --- `Rat.dotN`: the n-dimensional dot product (`rat_prelude::vector`) ----

/// Every declaration `vector::declare_vector` adds — `Rat.dotN` itself and
/// the six theorems built on it — is a **checked** definition or theorem
/// with an empty axiom footprint, read out of the kernel, not off the diff.
#[test]
fn the_vector_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("dotN", p.dot_n, false),
        ("dotN_zero", p.dot_n_zero, true),
        ("dotN_succ", p.dot_n_succ, true),
        ("dotN_comm", p.dot_n_comm, true),
        ("dotN_add_left", p.dot_n_add_left, true),
        ("dotN_smul_left", p.dot_n_smul_left, true),
        ("dotN_self_nonneg", p.dot_n_self_nonneg, true),
        ("dotN_two", p.dot_n_two, true),
        ("dotN_cauchy_schwarz", p.dot_n_cauchy_schwarz, true),
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
