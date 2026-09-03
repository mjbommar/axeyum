//! Tests for the complex prelude.
//!
//! Every assertion here is read **out of the kernel** — the environment, the
//! declaration kinds, `Kernel::axiom_footprint` — and never out of source text
//! or a doc comment.

use super::{ComplexPrelude, build_complex_prelude};
use crate::{Declaration, Kernel, on_a_deep_stack};

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
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude = build_complex_prelude(&mut kernel).expect("Complex prelude must build");
            (kernel, prelude)
        })
    });
    (kernel.clone(), *prelude)
}

/// The build itself, with the kernel's rejection **rendered**: a `Debug` of
/// `KernelError` says nothing about what was refused.
#[test]
fn complex_prelude_builds() {
    on_a_deep_stack(|| {
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
    });
}

/// Building twice is a no-op, not a duplicate-declaration error.
///
/// The rebuild itself is cheap (an already-`complex`-declared kernel hits
/// `build_complex_prelude`'s early "already registered" return before any
/// type-checking runs) — but it is wrapped in [`on_a_deep_stack`] anyway
/// rather than carved out of `scripts/check-deep-stack-call-sites.py`'s
/// static analysis, which cannot see that "the kernel `built()` handed back
/// is already fully built" and flags this call the same as a fresh one. An
/// exception list is one more thing to keep correct by hand; a redundant
/// thread spawn is not.
#[test]
fn complex_prelude_is_idempotent() {
    on_a_deep_stack(|| {
        let (mut kernel, first) = built();
        let before = kernel.environment().iter().count();
        let second = build_complex_prelude(&mut kernel).expect("rebuild must succeed");
        assert_eq!(first, second, "a rebuild must return the same handles");
        assert_eq!(
            before,
            kernel.environment().iter().count(),
            "a rebuild must not add declarations"
        );
    });
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
        ("Complex.commRingS", p.comm_ring_s),
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
        ("Complex.conj_zero", p.conj_zero),
        ("Complex.conj_one", p.conj_one),
        ("Complex.eq_conj_iff_real", p.eq_conj_iff_real),
        ("Complex.normSq", p.norm_sq),
        ("Complex.mul_conj", p.mul_conj),
        ("Complex.normSq_nonneg", p.norm_sq_nonneg),
        ("Complex.normSq_conj", p.norm_sq_conj),
        ("Complex.normSq_mul", p.norm_sq_mul),
        ("Complex.normSq_pow", p.norm_sq_pow),
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
        ("Complex.normSq_add_le", p.norm_sq_add_le),
        ("Complex.no_compatible_order", p.no_compatible_order),
        ("Complex.inv", p.inv),
        ("Complex.mul_inv_cancel", p.mul_inv_cancel),
        ("Complex.inv_congr", p.inv_congr),
        ("Complex.inv_mul", p.inv_mul),
        ("Complex.div", p.div),
        ("Complex.div_congr", p.div_congr),
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
        ("Complex.inv_mul_cancel", p.inv_mul_cancel),
        ("Complex.pos_bound_conj", p.pos_bound_conj),
        ("Complex.conj_inv", p.conj_inv),
        ("Complex.conj_div", p.conj_div),
        ("Complex.mul_div_assoc", p.mul_div_assoc),
        ("Complex.div_mul_cancel", p.div_mul_cancel),
        ("Complex.add_div", p.add_div),
        ("Complex.neg_div", p.neg_div),
        ("Complex.sub_div", p.sub_div),
        ("Complex.pow", p.pow),
        ("Complex.pow_zero", p.pow_zero),
        ("Complex.pow_succ", p.pow_succ),
        ("Complex.pow_add", p.pow_add),
        ("Complex.conj_pow", p.conj_pow),
        ("Complex.sumRange", p.sum_range),
        ("Complex.sumRange_zero", p.sum_range_zero),
        ("Complex.sumRange_succ", p.sum_range_succ),
        ("Complex.sumRange_congr", p.sum_range_congr),
        ("Complex.mul_sumRange", p.mul_sum_range),
        ("Complex.sumRange_mul", p.sum_range_mul),
        ("Complex.sumRange_mul_double", p.sum_range_mul_double),
        ("Complex.mul_sub_one_geom", p.mul_sub_one_geom),
        ("Complex.geom_series_div", p.geom_series_div),
        ("Complex.ofNat", p.of_nat),
        ("Complex.ofNat_zero", p.of_nat_zero),
        ("Complex.ofNat_succ", p.of_nat_succ),
        ("Complex.ofNat_add", p.of_nat_add),
        ("Complex.ofNat_mul", p.of_nat_mul),
        ("Complex.ofNat_eq_cast", p.of_nat_eq_cast),
        ("Complex.sumRange_add", p.sum_range_add),
        ("Complex.sumRange_shiftFront", p.sum_range_shift_front),
        ("Complex.sumRange_congr_lt", p.sum_range_congr_lt),
        ("Complex.sumRange_split", p.sum_range_split),
        ("Complex.sumRange_swap", p.sum_range_swap),
        ("Complex.sumRange_diagonal", p.sum_range_diagonal),
        (
            "Complex.sumRange_rect_eq_diag_add_corner",
            p.sum_range_rect_eq_diag_add_corner,
        ),
        (
            "Complex.sumRange_mul_eq_diag_add_corner",
            p.sum_range_mul_eq_diag_add_corner,
        ),
        ("Complex.add_pow", p.add_pow),
        ("Complex.IsRootOfUnity", p.is_root_of_unity),
        ("Complex.one_is_root_of_unity", p.one_is_root_of_unity),
        ("Complex.I_is_fourth_root", p.i_is_fourth_root),
        ("Complex.pow_mul", p.pow_mul),
        (
            "Complex.geom_sum_eq_zero_of_root_of_unity",
            p.geom_sum_eq_zero_of_root_of_unity,
        ),
        ("Complex.root_of_unity_mul", p.root_of_unity_mul),
        ("Complex.root_of_unity_pow", p.root_of_unity_pow),
        ("Complex.ptolemy_identity", p.ptolemy_identity),
        ("Complex.normSq_congr", p.norm_sq_congr),
        ("Complex.ptolemy_inequality_sq", p.ptolemy_inequality_sq),
        ("Complex.abs", p.abs),
        ("Complex.abs_nonneg", p.abs_nonneg),
        ("Complex.abs_congr", p.abs_congr),
        ("Complex.abs_one", p.abs_one),
        ("Complex.abs_mul", p.abs_mul),
        ("Complex.abs_add_le", p.abs_add_le),
        ("Complex.abs_neg", p.abs_neg),
        ("Complex.abs_le_add_abs_sub", p.abs_le_add_abs_sub),
        ("Complex.polyEval", p.poly.poly_eval),
        ("Complex.polyEval_zero", p.poly.poly_eval_zero),
        ("Complex.polyEval_succ", p.poly.poly_eval_succ),
        ("Complex.polyAdd", p.poly.poly_add),
        ("Complex.polyEval_polyAdd", p.poly.poly_eval_poly_add),
        ("Complex.polyScale", p.poly.poly_scale),
        ("Complex.polyEval_polyScale", p.poly.poly_eval_poly_scale),
        ("Complex.polyDegreeLt", p.poly.poly_degree_lt),
        (
            "Complex.polyDegreeLt_polyAdd",
            p.poly.poly_degree_lt_poly_add,
        ),
        (
            "Complex.polyDegreeLt_polyScale",
            p.poly.poly_degree_lt_poly_scale,
        ),
        ("Complex.polyMul", p.poly.poly_mul),
        (
            "Complex.polyDegreeLt_polyMul",
            p.poly.poly_degree_lt_poly_mul,
        ),
        ("Complex.polyEval_polyMul", p.poly.poly_eval_poly_mul),
        ("Complex.hornerFromTop", p.poly.horner_from_top),
        ("Complex.hornerFromTop_zero", p.poly.horner_from_top_zero),
        (
            "Complex.hornerFromTop_succ_zero",
            p.poly.horner_from_top_succ_zero,
        ),
        (
            "Complex.hornerFromTop_succ_succ",
            p.poly.horner_from_top_succ_succ,
        ),
        ("Complex.factorQuotient", p.poly.factor_quotient),
        (
            "Complex.factorQuotient_degreeLt",
            p.poly.factor_quotient_degree_lt,
        ),
        (
            "Complex.hornerFromTop_diag_eq_polyEval",
            p.poly.horner_from_top_diag_eq_poly_eval,
        ),
        (
            "Complex.factorQuotient_succ_eq",
            p.poly.factor_quotient_succ_eq,
        ),
    ];
    // COVERAGE, checked against the ENVIRONMENT rather than against `named`
    // itself.
    //
    // Without this, the loop below only ever inspects declarations someone
    // remembered to add to `named`, while the test's name promises *every*
    // named `Complex` declaration is checked. Mirrors
    // `every_creal_declaration_is_checked_and_axiom_free` (`creal_tests.rs`),
    // landed after exactly this gap was found there.
    //
    // Unlike the `Nat`/`CReal` sibling guards, `named` deliberately holds
    // every declaration kind (`Complex`/`Complex.mk`/`Complex.rec` are the
    // inductive/ctor/recursor, everything else a `Definition` or `Theorem`),
    // so the filter here is by namespace alone, not by declaration kind.
    let listed: std::collections::BTreeSet<crate::NameId> =
        named.iter().map(|(_, name)| *name).collect();
    let declared: Vec<crate::NameId> = kernel.environment().iter().map(|(name, _)| *name).collect();
    let unlisted: Vec<String> = declared
        .into_iter()
        .map(|name| (name, kernel.display_name(name).to_string()))
        .filter(|(name, shown)| shown.starts_with("Complex") && !listed.contains(name))
        .map(|(_, shown)| shown)
        .collect();
    assert!(
        unlisted.is_empty(),
        "these `Complex` declarations are live in the prelude but absent from \
         `named`, so nothing checks that they are derived and axiom-free: \
         {unlisted:?}. Add them here -- do not delete this assertion."
    );

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
///
/// `abs` is likewise **not** in this list, and for the same reason, not
/// because the reasoning above was wrong: `Complex.abs` exists
/// ([`ComplexPrelude::abs`]) and is `CReal`-valued, so every law it can even
/// state (`abs_nonneg`, a future triangle inequality) is phrased over
/// `CReal.le`, never over an order on `Complex` itself. Declaring `abs` did
/// not need — and did not add — an order on `Complex`.
#[test]
fn no_order_relation_is_declared_on_complex() {
    let (kernel, p) = built();
    for forbidden in ["le", "lt"] {
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
///
/// Runs its body on [`on_a_deep_stack`]'s thread, like every other fresh
/// `build_creal_prelude` call in this file — but it cannot use
/// `#[should_panic(expected = "...")]` on the outer test the way a same-thread
/// test would. Two independent problems, both measured on this toolchain:
///
/// - `on_a_deep_stack` re-panics via `JoinHandle::join().expect(..)`, and
///   `Result::expect`'s message is built from the `Err` payload's `Debug`
///   impl — for `Box<dyn Any + Send>` that is the fixed string `Any { .. }`,
///   never the original panic text.
/// - Even catching the panic *inside* the deep-stack thread and re-throwing
///   its own payload does not reliably preserve the message: the payload
///   downcasts to `String` at panic-HOOK time (before unwinding starts, via
///   `PanicHookInfo::payload_as_str`) but to neither `String` nor `&str` by
///   the time `catch_unwind` returns it a moment later — something on this
///   call's unwind path changes the boxed value's dynamic type between those
///   two observation points. `debug_probe_*`-shaped repros without the real
///   kernel state came back clean every time; only the genuine
///   `ring_proof` call under `on_a_deep_stack` showed the mismatch.
///
/// So the message is captured where it IS reliable — inside a panic hook,
/// before unwinding starts — and asserted on directly, rather than re-thrown
/// for `should_panic` to inspect on the far side of whatever changes it.
#[test]
fn the_ring_calculus_refuses_a_false_identity() {
    let (panicked, message) = crate::on_a_deep_stack(|| {
        use std::sync::{Arc, Mutex};

        let captured: Arc<Mutex<Option<String>>> = Arc::new(Mutex::new(None));
        let captured_hook = Arc::clone(&captured);
        let previous_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            #[allow(clippy::map_unwrap_or)]
            let message = info
                .payload_as_str()
                .map(str::to_string)
                .unwrap_or_else(|| info.to_string());
            *captured_hook.lock().unwrap() = Some(message);
        }));
        let result = std::panic::catch_unwind(the_ring_calculus_refuses_a_false_identity_body);
        std::panic::set_hook(previous_hook);
        (result.is_err(), captured.lock().unwrap().take())
    });
    assert!(
        panicked,
        "the ring calculus accepted `x + x = x`, a false identity"
    );
    let message = message.unwrap_or_default();
    assert!(
        message.contains("different normal forms"),
        "the ring calculus refused the identity for the wrong reason: {message}"
    );
}

fn the_ring_calculus_refuses_a_false_identity_body() {
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
    crate::on_a_deep_stack(the_ring_calculus_proves_a_true_identity_body);
}

fn the_ring_calculus_proves_a_true_identity_body() {
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

/// **The rectangle/triangle/corner decomposition says what it claims,
/// character for character** — the `Complex` counterpart of
/// `nat_prelude_tests::the_rectangle_decomposition_is_stated_exactly`. An
/// empty axiom footprint cannot carry this claim: a theorem that dropped the
/// corner term (i.e. the naive, FALSE finite Cauchy identity refuted in
/// `nat_prelude/rectangle.rs`'s module doc) has an identically empty
/// footprint too. What distinguishes them is the STATEMENT, so the statement
/// is what is pinned, for both the rectangle decomposition itself and the
/// headline Cauchy-product theorem that composes it with
/// `sumRange_mul_double`.
#[test]
fn the_rectangle_decomposition_is_stated_exactly() {
    let (kernel, p) = built();

    let rendered = |kernel: &Kernel, name: crate::NameId| -> String {
        match kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{} must be declared", kernel.display_name(name)))
        {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => {
                kernel.render_lean(*ty)
            }
            other => panic!("{other:?} is not a theorem or definition"),
        }
    };

    let rect = rendered(&kernel, p.sum_range_rect_eq_diag_add_corner);
    assert!(
        rect.contains("AxNat.add (AxNat.sub x1 x2) x3"),
        "the corner must be row i's width-i suffix reindexed from n-i, with ONE \
         truncated subtraction and no nesting: {rect}"
    );
    assert_eq!(
        rect, RECT_EQ_DIAG_ADD_CORNER_TYPE,
        "Complex.sumRange_rect_eq_diag_add_corner"
    );

    let cauchy = rendered(&kernel, p.sum_range_mul_eq_diag_add_corner);
    assert!(
        cauchy.contains("AxNat.add (AxNat.sub x2 x3) x4"),
        "the corner in the headline Cauchy-product theorem must carry the same \
         single-subtraction shift as the rectangle decomposition it composes: {cauchy}"
    );
    assert_eq!(
        cauchy, SUM_RANGE_MUL_EQ_DIAG_ADD_CORNER_TYPE,
        "Complex.sumRange_mul_eq_diag_add_corner"
    );
}

/// The pinned type of [`ComplexPrelude::sum_range_rect_eq_diag_add_corner`].
const RECT_EQ_DIAG_ADD_CORNER_TYPE: &str = "((x0 : ((x0 : AxNat) -> ((x1 : AxNat) -> Complex))) -> ((x1 : AxNat) -> Complex.Equiv (Complex.sumRange (fun (x2 : AxNat) => Complex.sumRange (fun (x3 : AxNat) => x0 x2 x3) x1) x1) (Complex.add (Complex.sumRange (fun (x2 : AxNat) => Complex.sumRange (fun (x3 : AxNat) => x0 x3 (AxNat.sub x2 x3)) (AxNat.succ x2)) x1) (Complex.sumRange (fun (x2 : AxNat) => Complex.sumRange (fun (x3 : AxNat) => (fun (x4 : AxNat) => x0 x2 x4) (AxNat.add (AxNat.sub x1 x2) x3)) x2) x1))))";

/// The pinned type of [`ComplexPrelude::sum_range_mul_eq_diag_add_corner`].
const SUM_RANGE_MUL_EQ_DIAG_ADD_CORNER_TYPE: &str = "((x0 : ((x0 : AxNat) -> Complex)) -> ((x1 : ((x1 : AxNat) -> Complex)) -> ((x2 : AxNat) -> Complex.Equiv (Complex.mul (Complex.sumRange x0 x2) (Complex.sumRange x1 x2)) (Complex.add (Complex.sumRange (fun (x3 : AxNat) => Complex.sumRange (fun (x4 : AxNat) => (fun (x5 : AxNat) => fun (x6 : AxNat) => Complex.mul (x0 x5) (x1 x6)) x4 (AxNat.sub x3 x4)) (AxNat.succ x3)) x2) (Complex.sumRange (fun (x3 : AxNat) => Complex.sumRange (fun (x4 : AxNat) => (fun (x5 : AxNat) => (fun (x6 : AxNat) => fun (x7 : AxNat) => Complex.mul (x0 x6) (x1 x7)) x3 x5) (AxNat.add (AxNat.sub x2 x3) x4)) x3) x2)))))";

/// **Concrete instantiation, checked by REDUCING, not merely type-checking.**
///
/// `ptolemy_identity` at `a = 1, b = I, c = −1, d = −I` — the fourth roots of
/// unity, all on the unit circle (concyclic), matching the module's own
/// `Complex.I_is_fourth_root` / `Complex.I_sq` witnesses. By hand: `L :=
/// (a−c)(b−d) = (1−(−1))·(I−(−I)) = 2·2I = 4I`; `X := (a−b)(c−d) =
/// (1−I)(−1+I) = 2I`; `Y := (b−c)(a−d) = (I+1)(1+I) = 2I`; `X+Y = 4I = L`.
///
/// That the UNIVERSAL theorem type-checks is already guaranteed by the ring
/// calculus refusing a false identity (`the_ring_calculus_refuses_a_false_identity`).
/// What this test adds: applying it at these four points, IN THIS ORDER,
/// must reduce (via the kernel's own `Pi`-application) to EXACTLY the
/// statement built independently here from raw `Complex.add`/`Complex.neg`/
/// `Complex.mul` applications — not via `complex_law`/`CExpr`, so this is a
/// genuine second construction path. An argument-position defect (a swapped
/// `a`/`b`/`c`/`d`, or a swapped `X`/`Y` pairing) would fail the `def_eq`
/// below even though the universal theorem type-checked perfectly.
#[test]
fn ptolemy_identity_reduces_at_the_fourth_roots_of_unity() {
    use crate::expr::ExprId;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let one = d.kernel().const_(p.one, vec![]);
    let i = d.kernel().const_(p.i, vec![]);
    let neg_one = d.const_app(p.neg, &[one]);
    let neg_i = d.const_app(p.neg, &[i]);

    let proof = d.lemma(p.ptolemy_identity, &[one, i, neg_one, neg_i]);
    let inferred = d
        .kernel()
        .infer(proof)
        .expect("ptolemy_identity at (1, I, -1, -I) must type-check");

    let sub = |d: &mut IntDev<'_>, x: ExprId, y: ExprId| -> ExprId {
        let ny = d.const_app(p.neg, &[y]);
        d.const_app(p.add, &[x, ny])
    };
    let a_minus_c = sub(&mut d, one, neg_one); // 1 - (-1)
    let b_minus_d = sub(&mut d, i, neg_i); // I - (-I)
    let lhs = d.const_app(p.mul, &[a_minus_c, b_minus_d]);

    let a_minus_b = sub(&mut d, one, i); // 1 - I
    let c_minus_d = sub(&mut d, neg_one, neg_i); // -1 - (-I)
    let x = d.const_app(p.mul, &[a_minus_b, c_minus_d]);

    let b_minus_c = sub(&mut d, i, neg_one); // I - (-1)
    let a_minus_d = sub(&mut d, one, neg_i); // 1 - (-I)
    let y = d.const_app(p.mul, &[b_minus_c, a_minus_d]);

    let rhs = d.const_app(p.add, &[x, y]);
    let expected = super::zeq(&mut d, p, lhs, rhs);

    assert!(
        d.kernel().def_eq(inferred, expected),
        "the instantiated identity must be EXACTLY \
         (1-(-1))(I-(-I)) ~ (1-I)(-1-(-I)) + (I-(-1))(1-(-I)); an \
         argument-position defect would fail this def_eq even though the \
         universal theorem type-checked"
    );
}

/// `Complex.ptolemy_inequality_sq` is built from `normSq` applied to the
/// SAME three products `ptolemy_identity` relates — not to some other
/// grouping — read out of the kernel's own rendering rather than trusted from
/// the source text that built it.
#[test]
fn ptolemy_inequality_sq_is_stated_over_the_ptolemy_products() {
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.ptolemy_inequality_sq)
        .expect("Complex.ptolemy_inequality_sq must be declared")
    {
        Declaration::Theorem { ty, .. } => kernel.render_lean(*ty),
        other => panic!("{other:?} is not a theorem"),
    };
    assert!(
        ty.contains("Complex.normSq"),
        "the statement must mention normSq: {ty}"
    );
    // Three multiplicative products, one normSq'd on the left of `CReal.le`
    // and two summed (each doubled) on the right -- L, X, X, Y, Y.
    assert_eq!(
        ty.matches("Complex.normSq (Complex.mul").count(),
        5,
        "L, X (twice, for the doubling) and Y (twice) must each appear as a \
         normSq of a Complex.mul: {ty}"
    );
    assert!(
        ty.contains("CReal.le"),
        "the conclusion must be a CReal.le, not an Equiv: {ty}"
    );
}

/// `Complex.conj_zero`/`Complex.conj_one` are already fully concrete (no
/// quantifier to instantiate): read their declared types straight out of the
/// kernel and check each `def_eq`s **exactly** the claimed statement, in the
/// claimed direction. A swapped `CExpr::Zero`/`CExpr::One` in either literal
/// would still type-check (the ring calculus proves either direction of a
/// true ring identity), so this must compare against a specific expected
/// term, not merely confirm the declaration exists.
#[test]
fn conj_zero_and_conj_one_are_exactly_stated() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let conj_zero = d.const_app(p.conj, &[zero_c]);
    let conj_one = d.const_app(p.conj, &[one_c]);

    let proof_zero = d.kernel().const_(p.conj_zero, vec![]);
    let inferred_zero = d
        .kernel()
        .infer(proof_zero)
        .expect("conj_zero must type-check");
    let expected_zero = super::zeq(&mut d, p, conj_zero, zero_c);
    assert!(
        d.kernel().def_eq(inferred_zero, expected_zero),
        "conj_zero must be EXACTLY Equiv (conj zero) zero, not the reverse \
         or some other pairing"
    );

    let proof_one = d.kernel().const_(p.conj_one, vec![]);
    let inferred_one = d
        .kernel()
        .infer(proof_one)
        .expect("conj_one must type-check");
    let expected_one = super::zeq(&mut d, p, conj_one, one_c);
    assert!(
        d.kernel().def_eq(inferred_one, expected_one),
        "conj_one must be EXACTLY Equiv (conj one) one, not the reverse or \
         some other pairing"
    );
}

/// `Complex.conj_pow` instantiated at the SAME negative-control witness
/// [`ptolemy_identity_reduces_at_the_fourth_roots_of_unity`]'s sibling test
/// uses, `z = I, n = 4`, chained against [`ComplexPrelude::i_is_fourth_root`]
/// and [`ComplexPrelude::conj_one`] to derive a genuinely new numeric fact
/// this lemma makes available and no prior declaration states on its own:
/// **`(−I)` is also a fourth root of unity**, `Equiv (pow (conj I) 4) one`.
///
/// This is not a restatement of `conj_pow`'s own type (which type-checking
/// alone already confirms) — it is an independent computation built by
/// composing `conj_pow` with two existing facts, and the final `def_eq`
/// check would fail if `conj_pow`'s conclusion had its two sides transposed,
/// even though the transposed statement is *also* a true theorem (`Equiv`
/// is symmetric) and would still have type-checked as a declaration.
#[test]
fn conj_pow_gives_conj_i_a_fourth_root_of_unity() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let four = d.num(4);
    let pow_i4 = d.const_app(p.pow, &[i_c, four]);
    let conj_i = d.const_app(p.conj, &[i_c]);
    let pow_conj_i_4 = d.const_app(p.pow, &[conj_i, four]);
    let conj_pow_i4 = d.const_app(p.conj, &[pow_i4]);
    let conj_one = d.const_app(p.conj, &[one_c]);

    // h_root : Equiv (pow I 4) one -- `I_is_fourth_root` unfolds by delta to
    // exactly this (IsRootOfUnity is a Definition, not a fresh Prop).
    let h_root = d.kernel().const_(p.i_is_fourth_root, vec![]);

    // h_congr : Equiv (conj (pow I 4)) (conj one), via `conj_congr`.
    let h_congr = d.lemma(p.conj_congr, &[pow_i4, one_c, h_root]);

    // h_conj_pow : Equiv (conj (pow I 4)) (pow (conj I) 4), via `conj_pow`.
    let h_conj_pow = d.lemma(p.conj_pow, &[i_c, four]);

    // h_conj_pow_symm : Equiv (pow (conj I) 4) (conj (pow I 4)).
    let h_conj_pow_symm = d.lemma(p.equiv_symm, &[conj_pow_i4, pow_conj_i_4, h_conj_pow]);

    // h_mid : Equiv (pow (conj I) 4) (conj one).
    let h_mid = d.lemma(
        p.equiv_trans,
        &[
            pow_conj_i_4,
            conj_pow_i4,
            conj_one,
            h_conj_pow_symm,
            h_congr,
        ],
    );

    // h_conj_one : Equiv (conj one) one.
    let h_conj_one = d.kernel().const_(p.conj_one, vec![]);

    // h_final : Equiv (pow (conj I) 4) one -- (-I)^4 ~ 1.
    let h_final = d.lemma(
        p.equiv_trans,
        &[pow_conj_i_4, conj_one, one_c, h_mid, h_conj_one],
    );

    let inferred = d
        .kernel()
        .infer(h_final)
        .expect("the composed (-I)^4 ~ 1 derivation must type-check");
    let expected = super::zeq(&mut d, p, pow_conj_i_4, one_c);
    assert!(
        d.kernel().def_eq(inferred, expected),
        "the derived fact must be EXACTLY Equiv (pow (conj I) 4) one"
    );
}

/// `Complex.conj_div` instantiated at `z = w = I`, chained against
/// [`ComplexPrelude::div_self`], [`ComplexPrelude::conj_congr`] and
/// [`ComplexPrelude::conj_one`] to derive a fact `conj_div`'s own type does
/// not state on its own: **dividing `conj I` by itself is also `Equiv` to
/// `one`** — `Equiv (div (conj I) (conj I) k (pos_bound_conj I k h)) one`,
/// for *any* modulus `k` and witness `h` the caller holds for `I` itself.
/// `k` and `h` stay universally quantified (the same genericity every
/// division law in this module already carries over its side condition);
/// `z` and `w` are pinned to the concrete numeral `I` this test exercises.
///
/// Built as a fully closed, abstracted proof term admitted through
/// `Kernel::add_declaration` — mirroring
/// `creal::creal_tests::the_inverses_domain_is_inhabited_and_the_inverse_is_not_the_zero_function`
/// — rather than `infer`/`def_eq` on an open term, because `k` and `h` are
/// free variables here rather than ground numerals. `add_declaration`
/// re-checks the closed value against the EXACT stated `ty`, which is
/// itself the direction check: had the derivation actually produced the
/// mathematically equivalent but syntactically reversed
/// `Equiv one (div (conj I) (conj I) k h2)`, the kernel would refuse it.
#[test]
fn conj_div_gives_the_conjugate_self_quotient_too() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let conj_i = d.const_app(p.conj, &[i_c]);

    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm_i = d.const_app(p.norm_sq, &[i_c]);
    let hypothesis = d.const_app(p.creal.pos_bound, &[norm_i, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // h2 : PosBound (normSq (conj I)) k, via `pos_bound_conj`.
    let h2 = d.lemma(p.pos_bound_conj, &[i_c, k, h]);

    let div_ii = d.const_app(p.div, &[i_c, i_c, k, h]);
    let conj_div_ii = d.const_app(p.conj, &[div_ii]);
    let div_conji_conji = d.const_app(p.div, &[conj_i, conj_i, k, h2]);

    // t_conj_div : Equiv (conj (div I I k h)) (div (conj I) (conj I) k h2).
    let t_conj_div = d.lemma(p.conj_div, &[i_c, i_c, k, h]);

    // t_div_self : Equiv (div I I k h) one.
    let t_div_self = d.lemma(p.div_self, &[i_c, k, h]);
    // t_congr : Equiv (conj (div I I k h)) (conj one).
    let t_congr = d.lemma(p.conj_congr, &[div_ii, one_c, t_div_self]);
    let conj_one_term = d.const_app(p.conj, &[one_c]);
    // t_conj_one : Equiv (conj one) one.
    let t_conj_one = d.kernel().const_(p.conj_one, vec![]);
    // t_left : Equiv (conj (div I I k h)) one.
    let t_left = d.lemma(
        p.equiv_trans,
        &[conj_div_ii, conj_one_term, one_c, t_congr, t_conj_one],
    );

    // t_symm : Equiv (div (conj I) (conj I) k h2) (conj (div I I k h)).
    let t_symm = d.lemma(p.equiv_symm, &[conj_div_ii, div_conji_conji, t_conj_div]);
    // t_final : Equiv (div (conj I) (conj I) k h2) one.
    let t_final = d.lemma(
        p.equiv_trans,
        &[div_conji_conji, conj_div_ii, one_c, t_symm, t_left],
    );

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, t_final);
        d.lam_fv(k_fv, nat, with_h)
    };
    let ty = {
        let conclusion = super::zeq(&mut d, p, div_conji_conji, one_c);
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        d.pi_fv(k_fv, nat, inner)
    };
    let name = d.kernel().name_str(anon, "Check.conj_div_self_quotient");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "conj_div + div_self + conj_one must derive \
         `Equiv (div (conj I) (conj I) k h2) one`: {admitted:?}"
    );
}

/// `Complex.div_congr` instantiated at `w = w' = I` and `z = I`,
/// `z' = conj (conj I)` (related by [`ComplexPrelude::conj_conj`]), chained
/// against [`ComplexPrelude::div_self`] to derive a fact neither lemma
/// states alone: **dividing `conj (conj I)` by `I` is also `Equiv` to
/// `one`** — `Equiv (div (conj (conj I)) I k h) one`, for any modulus `k`
/// and witness `h`. Reusing `I` for both `w` and `w'` (so the two `PosBound`
/// hypotheses coincide as one `h`) keeps the instantiation to a single
/// nontrivial numerator substitution rather than doubling the abstract
/// plumbing on the denominator side too.
#[test]
fn div_congr_transports_div_self_across_a_conjugate_involution() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let conj_i = d.const_app(p.conj, &[i_c]);
    let conj_conj_i = d.const_app(p.conj, &[conj_i]);

    // t_involution : Equiv (conj (conj I)) I.
    let t_involution = d.lemma(p.conj_conj, &[i_c]);
    // hz : Equiv I (conj (conj I)).
    let hz = d.lemma(p.equiv_symm, &[conj_conj_i, i_c, t_involution]);
    // hw : Equiv I I.
    let hw = d.lemma(p.equiv_refl, &[i_c]);

    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm_i = d.const_app(p.norm_sq, &[i_c]);
    let hypothesis = d.const_app(p.creal.pos_bound, &[norm_i, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let div_ii = d.const_app(p.div, &[i_c, i_c, k, h]);
    let div_ccii = d.const_app(p.div, &[conj_conj_i, i_c, k, h]);

    // t_div_congr : Equiv (div I I k h) (div (conj (conj I)) I k h).
    let t_div_congr = d.lemma(
        p.div_congr,
        &[i_c, conj_conj_i, i_c, i_c, k, k, h, h, hz, hw],
    );
    // t_div_self : Equiv (div I I k h) one.
    let t_div_self = d.lemma(p.div_self, &[i_c, k, h]);
    // t_symm : Equiv (div (conj (conj I)) I k h) (div I I k h).
    let t_symm = d.lemma(p.equiv_symm, &[div_ii, div_ccii, t_div_congr]);
    // t_final : Equiv (div (conj (conj I)) I k h) one.
    let t_final = d.lemma(
        p.equiv_trans,
        &[div_ccii, div_ii, one_c, t_symm, t_div_self],
    );

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, t_final);
        d.lam_fv(k_fv, nat, with_h)
    };
    let ty = {
        let conclusion = super::zeq(&mut d, p, div_ccii, one_c);
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        d.pi_fv(k_fv, nat, inner)
    };
    let name = d
        .kernel()
        .name_str(anon, "Check.div_congr_conjugate_involution");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "div_congr + conj_conj + div_self must derive \
         `Equiv (div (conj (conj I)) I k h) one`: {admitted:?}"
    );
}

/// `Complex.mul_div_assoc` instantiated at `z = I`, `w = one`, `w' = I`,
/// three arguments distinct enough from each other that a transposed side
/// of the stated `Equiv`, or a swapped `w`/`w'`, would be caught by
/// `add_declaration`'s own re-check against the exact stated `ty`. `k`/`h`
/// stay universally quantified, mirroring every division law in this module.
///
/// The declaration itself is already the symbolic check: `declare_mul_div_assoc`
/// builds its proof term entirely from `fresh_fvar` — `z`, `w`, `w'`, `k`, `h`
/// are never numerals — so its own admission during `build_complex_prelude`
/// (exercised by [`every_named_complex_declaration_is_checked_and_footprint_free`])
/// already confirms the term type-checks for genuinely free complex variables.
/// This test is the complementary concrete check the module's own convention
/// calls for.
#[test]
fn mul_div_assoc_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm_i = d.const_app(p.norm_sq, &[i_c]);
    let hypothesis = d.const_app(p.creal.pos_bound, &[norm_i, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // Equiv (div (mul I one) I k h) (mul I (div one I k h)).
    let proof = d.lemma(p.mul_div_assoc, &[i_c, one_c, i_c, k, h]);

    let mul_i_one = d.const_app(p.mul, &[i_c, one_c]);
    let div_lhs = d.const_app(p.div, &[mul_i_one, i_c, k, h]);
    let div_one_i = d.const_app(p.div, &[one_c, i_c, k, h]);
    let mul_i_div = d.const_app(p.mul, &[i_c, div_one_i]);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, proof);
        d.lam_fv(k_fv, nat, with_h)
    };
    let ty = {
        let conclusion = super::zeq(&mut d, p, div_lhs, mul_i_div);
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        d.pi_fv(k_fv, nat, inner)
    };
    let name = d.kernel().name_str(anon, "Check.mul_div_assoc_concrete");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "mul_div_assoc at (I, one, I, k, h) must give EXACTLY \
         Equiv (div (mul I one) I k h) (mul I (div one I k h)): {admitted:?}"
    );
}

/// `Complex.div_mul_cancel` instantiated at `z = I`, `w = one`: dividing
/// `I * one` by `one` must cancel back to exactly `I`, not `one` or some
/// other rearrangement — `add_declaration`'s re-check against the stated
/// `ty` is the direction check, the same reliance the module's other
/// concrete-instantiation tests document.
#[test]
fn div_mul_cancel_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm_one = d.const_app(p.norm_sq, &[one_c]);
    let hypothesis = d.const_app(p.creal.pos_bound, &[norm_one, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // Equiv (div (mul I one) one k h) I.
    let proof = d.lemma(p.div_mul_cancel, &[i_c, one_c, k, h]);

    let mul_i_one = d.const_app(p.mul, &[i_c, one_c]);
    let div_lhs = d.const_app(p.div, &[mul_i_one, one_c, k, h]);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, proof);
        d.lam_fv(k_fv, nat, with_h)
    };
    let ty = {
        let conclusion = super::zeq(&mut d, p, div_lhs, i_c);
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        d.pi_fv(k_fv, nat, inner)
    };
    let name = d.kernel().name_str(anon, "Check.div_mul_cancel_concrete");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "div_mul_cancel at (I, one, k, h) must give EXACTLY \
         Equiv (div (mul I one) one k h) I: {admitted:?}"
    );
}

/// `Complex.add_div` instantiated at `z = I`, `z' = one`, `w = I`: division
/// distributes the sum `I + one` across the shared divisor `I`.
#[test]
fn add_div_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm_i = d.const_app(p.norm_sq, &[i_c]);
    let hypothesis = d.const_app(p.creal.pos_bound, &[norm_i, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // Equiv (div (add I one) I k h) (add (div I I k h) (div one I k h)).
    let proof = d.lemma(p.add_div, &[i_c, one_c, i_c, k, h]);

    let add_i_one = d.const_app(p.add, &[i_c, one_c]);
    let div_lhs = d.const_app(p.div, &[add_i_one, i_c, k, h]);
    let div_i_i = d.const_app(p.div, &[i_c, i_c, k, h]);
    let div_one_i = d.const_app(p.div, &[one_c, i_c, k, h]);
    let add_divs = d.const_app(p.add, &[div_i_i, div_one_i]);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, proof);
        d.lam_fv(k_fv, nat, with_h)
    };
    let ty = {
        let conclusion = super::zeq(&mut d, p, div_lhs, add_divs);
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        d.pi_fv(k_fv, nat, inner)
    };
    let name = d.kernel().name_str(anon, "Check.add_div_concrete");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "add_div at (I, one, I, k, h) must give EXACTLY \
         Equiv (div (add I one) I k h) (add (div I I k h) (div one I k h)): {admitted:?}"
    );
}

/// `Complex.neg_div` instantiated at `z = I`, `w = one`: negation passes
/// through division of `-I` by `one`.
#[test]
fn neg_div_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm_one = d.const_app(p.norm_sq, &[one_c]);
    let hypothesis = d.const_app(p.creal.pos_bound, &[norm_one, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // Equiv (div (neg I) one k h) (neg (div I one k h)).
    let proof = d.lemma(p.neg_div, &[i_c, one_c, k, h]);

    let neg_i = d.const_app(p.neg, &[i_c]);
    let div_lhs = d.const_app(p.div, &[neg_i, one_c, k, h]);
    let div_i_one = d.const_app(p.div, &[i_c, one_c, k, h]);
    let neg_rhs = d.const_app(p.neg, &[div_i_one]);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, proof);
        d.lam_fv(k_fv, nat, with_h)
    };
    let ty = {
        let conclusion = super::zeq(&mut d, p, div_lhs, neg_rhs);
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        d.pi_fv(k_fv, nat, inner)
    };
    let name = d.kernel().name_str(anon, "Check.neg_div_concrete");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "neg_div at (I, one, k, h) must give EXACTLY \
         Equiv (div (neg I) one k h) (neg (div I one k h)): {admitted:?}"
    );
}

/// `Complex.sub_div` instantiated at `z = I`, `z2 = one`, `w = neg I` —
/// three PAIRWISE DISTINCT concrete values (unlike this module's earlier
/// concrete-instantiation tests, which only ever combined `I` and `one`),
/// so a transposed numerator, a swapped `div_z_w`/`div_z2_w`, or a missing
/// `neg` on the wrong side would all be caught by `add_declaration`'s own
/// re-check against the independently-built expected `ty`.
#[test]
fn sub_div_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let neg_i_c = d.const_app(p.neg, &[i_c]);

    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let norm_negi = d.const_app(p.norm_sq, &[neg_i_c]);
    let hypothesis = d.const_app(p.creal.pos_bound, &[norm_negi, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    // Equiv (div (add I (neg one)) (neg I) k h)
    //       (add (div I (neg I) k h) (neg (div one (neg I) k h))).
    let proof = d.lemma(p.sub_div, &[i_c, one_c, neg_i_c, k, h]);

    let neg_one = d.const_app(p.neg, &[one_c]);
    let add_i_negone = d.const_app(p.add, &[i_c, neg_one]);
    let div_lhs = d.const_app(p.div, &[add_i_negone, neg_i_c, k, h]);
    let div_i_negi = d.const_app(p.div, &[i_c, neg_i_c, k, h]);
    let div_one_negi = d.const_app(p.div, &[one_c, neg_i_c, k, h]);
    let neg_div_one_negi = d.const_app(p.neg, &[div_one_negi]);
    let add_rhs = d.const_app(p.add, &[div_i_negi, neg_div_one_negi]);

    let value = {
        let with_h = d.lam_fv(h_fv, hypothesis, proof);
        d.lam_fv(k_fv, nat, with_h)
    };
    let ty = {
        let conclusion = super::zeq(&mut d, p, div_lhs, add_rhs);
        let inner = d.pi_fv(h_fv, hypothesis, conclusion);
        d.pi_fv(k_fv, nat, inner)
    };
    let name = d.kernel().name_str(anon, "Check.sub_div_concrete");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "sub_div at (I, one, neg I, k, h) must give EXACTLY \
         Equiv (div (add I (neg one)) (neg I) k h) \
         (add (div I (neg I) k h) (neg (div one (neg I) k h))): {admitted:?}"
    );
}

/// `Complex.inv_mul` instantiated at `z = neg I`, `w = one` — two DISTINCT
/// concrete values, deliberately not the `z = I, w = one` combination this
/// module's earlier division-algebra tests already used, so a swapped
/// `inv_z`/`inv_w` on the right-hand side would be caught. The three moduli
/// `k1`/`k2`/`k3` and their witnesses stay free, mirroring every other
/// concrete-instantiation test in this module: this is a check on the
/// COMPLEX arguments, not on a constructed `PosBound` witness.
#[test]
fn inv_mul_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let neg_i_c = d.const_app(p.neg, &[i_c]);

    let nat = d.nat_ty();

    let k1_fv = d.fresh_fvar();
    let k1 = d.kernel().fvar(k1_fv);
    let norm_negi = d.const_app(p.norm_sq, &[neg_i_c]);
    let hyp1 = d.const_app(p.creal.pos_bound, &[norm_negi, k1]);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);

    let k2_fv = d.fresh_fvar();
    let k2 = d.kernel().fvar(k2_fv);
    let norm_one = d.const_app(p.norm_sq, &[one_c]);
    let hyp2 = d.const_app(p.creal.pos_bound, &[norm_one, k2]);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let prod = d.const_app(p.mul, &[neg_i_c, one_c]);
    let k3_fv = d.fresh_fvar();
    let k3 = d.kernel().fvar(k3_fv);
    let norm_prod = d.const_app(p.norm_sq, &[prod]);
    let hyp3 = d.const_app(p.creal.pos_bound, &[norm_prod, k3]);
    let h3_fv = d.fresh_fvar();
    let h3 = d.kernel().fvar(h3_fv);

    // Equiv (inv (mul (neg I) one) k3 h3) (mul (inv (neg I) k1 h1) (inv one k2 h2)).
    let proof = d.lemma(p.inv_mul, &[neg_i_c, one_c, k1, h1, k2, h2, k3, h3]);

    let inv_prod = d.const_app(p.inv, &[prod, k3, h3]);
    let inv_negi = d.const_app(p.inv, &[neg_i_c, k1, h1]);
    let inv_one = d.const_app(p.inv, &[one_c, k2, h2]);
    let mul_invs = d.const_app(p.mul, &[inv_negi, inv_one]);

    let value = {
        let with_h3 = d.lam_fv(h3_fv, hyp3, proof);
        let with_k3 = d.lam_fv(k3_fv, nat, with_h3);
        let with_h2 = d.lam_fv(h2_fv, hyp2, with_k3);
        let with_k2 = d.lam_fv(k2_fv, nat, with_h2);
        let with_h1 = d.lam_fv(h1_fv, hyp1, with_k2);
        d.lam_fv(k1_fv, nat, with_h1)
    };
    let ty = {
        let conclusion = super::zeq(&mut d, p, inv_prod, mul_invs);
        let inner = d.pi_fv(h3_fv, hyp3, conclusion);
        let with_k3 = d.pi_fv(k3_fv, nat, inner);
        let with_h2 = d.pi_fv(h2_fv, hyp2, with_k3);
        let with_k2 = d.pi_fv(k2_fv, nat, with_h2);
        let with_h1 = d.pi_fv(h1_fv, hyp1, with_k2);
        d.pi_fv(k1_fv, nat, with_h1)
    };
    let name = d.kernel().name_str(anon, "Check.inv_mul_concrete");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "inv_mul at (neg I, one, k1, h1, k2, h2, k3, h3) must give EXACTLY \
         Equiv (inv (mul (neg I) one) k3 h3) \
         (mul (inv (neg I) k1 h1) (inv one k2 h2)): {admitted:?}"
    );
}

/// `Complex.abs`'s declared TYPE is `Complex → CReal`, and its VALUE mentions
/// both `CReal.sqrt` and `Complex.normSq` — read out of the kernel's own
/// rendering, not trusted from the source text that built it.
#[test]
fn abs_is_creal_sqrt_of_norm_sq() {
    let (kernel, p) = built();
    let (ty, value) = match kernel
        .environment()
        .get(p.abs)
        .expect("Complex.abs must be declared")
    {
        Declaration::Definition { ty, value, .. } => {
            (kernel.render_lean(*ty), kernel.render_lean(*value))
        }
        other => panic!("{other:?} is not a definition"),
    };
    assert!(
        ty.contains("Complex") && ty.contains("CReal"),
        "Complex.abs must be typed Complex -> CReal: {ty}"
    );
    assert!(
        value.contains("CReal.sqrt"),
        "Complex.abs must be built from CReal.sqrt: {value}"
    );
    assert!(
        value.contains("Complex.normSq"),
        "Complex.abs must apply sqrt to normSq, not some other CReal: {value}"
    );
}

/// `Complex.abs_nonneg` is stated `CReal.le CReal.zero (abs z)` — zero on the
/// LEFT — not the reversed (and generally false) `CReal.le (abs z)
/// CReal.zero`.
#[test]
fn abs_nonneg_is_stated_zero_le_abs() {
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.abs_nonneg)
        .expect("Complex.abs_nonneg must be declared")
    {
        Declaration::Theorem { ty, .. } => kernel.render_lean(*ty),
        other => panic!("{other:?} is not a theorem"),
    };
    assert!(
        ty.contains("CReal.le CReal.zero"),
        "abs_nonneg must read `CReal.le CReal.zero ...`, zero first: {ty}"
    );
    assert!(
        ty.contains("Complex.abs"),
        "abs_nonneg's conclusion must mention Complex.abs: {ty}"
    );
}

/// A concrete instantiation of [`ComplexPrelude::abs_nonneg`] at `Complex.I`:
/// `0 ≤ abs I`, admitted as its own checked theorem.
#[test]
fn abs_nonneg_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let proof = d.lemma(p.abs_nonneg, &[i_c]);

    let abs_i = d.const_app(p.abs, &[i_c]);
    let zero_real = d.kernel().const_(p.creal.zero, vec![]);
    let ty = d.const_app(p.creal.le, &[zero_real, abs_i]);

    let name = d.kernel().name_str(anon, "Check.abs_nonneg_at_I");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: proof,
    });
    assert!(
        admitted.is_ok(),
        "abs_nonneg at I must give EXACTLY CReal.le CReal.zero (abs I): {admitted:?}"
    );
}

/// Negative control for [`abs_nonneg_concrete_instantiation`]: the SAME proof
/// term must be REFUSED against the REVERSED claim `abs I le 0`.
/// `CReal.le` is not symmetric, and this is generally false (`abs I` is not
/// known to be `~ 0`, and indeed is not) — a checker that accepted it would
/// be accepting an unrelated statement, not the one `abs_nonneg` proves.
#[test]
fn abs_nonneg_direction_is_load_bearing() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let proof = d.lemma(p.abs_nonneg, &[i_c]);

    let abs_i = d.const_app(p.abs, &[i_c]);
    let zero_real = d.kernel().const_(p.creal.zero, vec![]);
    let wrong_ty = d.const_app(p.creal.le, &[abs_i, zero_real]);

    let name = d.kernel().name_str(anon, "Check.abs_nonneg_reversed");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: wrong_ty,
        value: proof,
    });
    assert!(
        admitted.is_err(),
        "a proof of `0 le abs I` must NOT type-check against the REVERSED \
         claim `abs I le 0`: {admitted:?}"
    );
}

/// A concrete, NON-trivial instantiation of [`ComplexPrelude::abs_congr`]:
/// `conj (conj I) ~ I` ([`ComplexPrelude::conj_conj`]) transported across
/// `abs` gives `abs (conj (conj I)) ~ abs I`. Reflexivity at one fixed point
/// would exercise the mechanism vacuously (`Equiv.refl` proves `f x ~ f x`
/// for ANY `f`, congruent or not); `conj_conj` supplies two SYNTACTICALLY
/// different complex numbers connected by a genuine equivalence proof.
#[test]
fn abs_congr_concrete_instantiation() {
    use super::ring::ceq;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let conj_i = d.const_app(p.conj, &[i_c]);
    let conj_conj_i = d.const_app(p.conj, &[conj_i]);
    let h = d.lemma(p.conj_conj, &[i_c]);
    // h : Equiv (conj (conj I)) I

    let proof = d.lemma(p.abs_congr, &[conj_conj_i, i_c, h]);
    let abs_conj_conj_i = d.const_app(p.abs, &[conj_conj_i]);
    let abs_i = d.const_app(p.abs, &[i_c]);
    let ty = ceq(&mut d, p.creal, abs_conj_conj_i, abs_i);

    let name = d.kernel().name_str(anon, "Check.abs_congr_at_conj_conj_I");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: proof,
    });
    assert!(
        admitted.is_ok(),
        "abs_congr at conj_conj(I) must give EXACTLY CReal.Equiv \
         (abs (conj (conj I))) (abs I): {admitted:?}"
    );
}

/// Negative control for [`abs_congr_concrete_instantiation`]: the SAME proof
/// term must be REFUSED against `abs (conj (conj I)) ~ CReal.zero`.
///
/// **Not** used as the negative control here: pairing `abs I` with
/// `abs (conj I)`. That statement is ALSO kernel-checkable from this same
/// proof term (`conj` fixes `abs` too — `neg(one)*neg(one)` and `one*one`
/// land on the same normal form, a fact caught only by trying it), so it is
/// not a valid discriminator; see the module-level lesson about vacuous
/// negative controls this cost real time to find.
#[test]
fn abs_congr_argument_is_load_bearing() {
    use super::ring::ceq;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let conj_i = d.const_app(p.conj, &[i_c]);
    let conj_conj_i = d.const_app(p.conj, &[conj_i]);
    let h = d.lemma(p.conj_conj, &[i_c]);
    let proof = d.lemma(p.abs_congr, &[conj_conj_i, i_c, h]);

    let abs_conj_conj_i = d.const_app(p.abs, &[conj_conj_i]);
    let zero_real = d.kernel().const_(p.creal.zero, vec![]);
    let wrong_ty = ceq(&mut d, p.creal, abs_conj_conj_i, zero_real);

    let name = d.kernel().name_str(anon, "Check.abs_congr_wrong_target");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: wrong_ty,
        value: proof,
    });
    assert!(
        admitted.is_err(),
        "abs_congr's proof at conj_conj(I) must NOT type-check against \
         `abs (conj (conj I)) ~ CReal.zero`: {admitted:?}"
    );
}

/// A concrete instantiation of [`ComplexPrelude::abs_mul`] at `z := I`,
/// `w := one` -- two SYNTACTICALLY distinct complex numbers, not a
/// self-instantiation (`z = w` risks hiding a factor error the same way
/// `a = b` does elsewhere in this codebase's own retrospectives). Checked
/// against the INDEPENDENTLY reconstructed statement `abs (mul I one) ~
/// mul (abs I) (abs one)`, with a negative control against `CReal.zero`
/// rather than a swapped-factor target -- swapping factors would ALSO be
/// provable from this same proof term via `CReal.mul_comm`, which is
/// exactly the vacuous-negative-control trap `abs_congr_argument_is_load_bearing`'s
/// own doc names.
#[test]
fn abs_mul_concrete_instantiation() {
    use super::ring::ceq;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let proof = d.lemma(p.abs_mul, &[i_c, one_c]);

    let i_one = d.const_app(p.mul, &[i_c, one_c]);
    let abs_i_one = d.const_app(p.abs, &[i_one]);
    let abs_i = d.const_app(p.abs, &[i_c]);
    let abs_one = d.const_app(p.abs, &[one_c]);
    let rhs = d.const_app(p.creal.mul, &[abs_i, abs_one]);
    let ty = ceq(&mut d, p.creal, abs_i_one, rhs);

    let name = d.kernel().name_str(anon, "Check.abs_mul_at_I_one");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: proof,
    });
    assert!(
        admitted.is_ok(),
        "abs_mul at (I, one) must give EXACTLY CReal.Equiv (abs (mul I \
         one)) (mul (abs I) (abs one)): {admitted:?}"
    );
}

/// Negative control for [`abs_mul_concrete_instantiation`]: the SAME proof
/// term must be REFUSED against `abs (mul I one) ~ CReal.zero`.
#[test]
fn abs_mul_argument_is_load_bearing() {
    use super::ring::ceq;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let proof = d.lemma(p.abs_mul, &[i_c, one_c]);

    let i_one = d.const_app(p.mul, &[i_c, one_c]);
    let abs_i_one = d.const_app(p.abs, &[i_one]);
    let zero_real = d.kernel().const_(p.creal.zero, vec![]);
    let wrong_ty = ceq(&mut d, p.creal, abs_i_one, zero_real);

    let name = d.kernel().name_str(anon, "Check.abs_mul_wrong_target");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: wrong_ty,
        value: proof,
    });
    assert!(
        admitted.is_err(),
        "abs_mul's proof at (I, one) must NOT type-check against `abs (mul \
         I one) ~ CReal.zero`: {admitted:?}"
    );
}

/// A concrete instantiation of [`ComplexPrelude::abs_add_le`] at `z := I`,
/// `w := one` -- the same discriminating pair [`abs_mul_concrete_instantiation`]
/// uses, and one where the bound is genuinely non-trivial: `abs (I+1) =
/// sqrt 2 ≈ 1.41`, strictly less than `abs I + abs one = 2`, so this is not
/// a case where the inequality degenerates to equality and hides a swapped
/// direction.
#[test]
fn abs_add_le_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let proof = d.lemma(p.abs_add_le, &[i_c, one_c]);

    let sum_zw = d.const_app(p.add, &[i_c, one_c]);
    let abs_sum = d.const_app(p.abs, &[sum_zw]);
    let abs_i = d.const_app(p.abs, &[i_c]);
    let abs_one = d.const_app(p.abs, &[one_c]);
    let rhs = d.const_app(p.creal.add, &[abs_i, abs_one]);
    let ty = d.const_app(p.creal.le, &[abs_sum, rhs]);

    let name = d.kernel().name_str(anon, "Check.abs_add_le_at_I_one");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: proof,
    });
    assert!(
        admitted.is_ok(),
        "abs_add_le at (I, one) must give EXACTLY CReal.le (abs (add I one)) \
         (add (abs I) (abs one)): {admitted:?}"
    );
}

/// Negative control for [`abs_add_le_concrete_instantiation`]: the SAME
/// proof term must be REFUSED against the REVERSED inequality `le (add
/// (abs I) (abs one)) (abs (add I one))` -- `le` is not symmetric, and this
/// is the direction the classical triangle inequality does NOT claim.
#[test]
fn abs_add_le_direction_is_load_bearing() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let proof = d.lemma(p.abs_add_le, &[i_c, one_c]);

    let sum_zw = d.const_app(p.add, &[i_c, one_c]);
    let abs_sum = d.const_app(p.abs, &[sum_zw]);
    let abs_i = d.const_app(p.abs, &[i_c]);
    let abs_one = d.const_app(p.abs, &[one_c]);
    let rhs = d.const_app(p.creal.add, &[abs_i, abs_one]);
    let wrong_ty = d.const_app(p.creal.le, &[rhs, abs_sum]);

    let name = d
        .kernel()
        .name_str(anon, "Check.abs_add_le_wrong_direction");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: wrong_ty,
        value: proof,
    });
    assert!(
        admitted.is_err(),
        "abs_add_le's proof at (I, one) must NOT type-check against the \
         REVERSED `le (add (abs I) (abs one)) (abs (add I one))`: {admitted:?}"
    );
}

/// A concrete instantiation of [`ComplexPrelude::abs_neg`] at `z := I`:
/// `abs (neg I) ~ abs I`, i.e. `abs (-i) ~ abs i` (both `1`) -- a genuinely
/// discriminating instance (`neg I` is a distinct term from `I`, not a case
/// where `neg` happens to fix its argument).
#[test]
fn abs_neg_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let proof = d.lemma(p.abs_neg, &[i_c]);

    let neg_i = d.const_app(p.neg, &[i_c]);
    let abs_neg_i = d.const_app(p.abs, &[neg_i]);
    let abs_i = d.const_app(p.abs, &[i_c]);
    let ty = d.const_app(p.creal.equiv, &[abs_neg_i, abs_i]);

    let name = d.kernel().name_str(anon, "Check.abs_neg_at_I");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: proof,
    });
    assert!(
        admitted.is_ok(),
        "abs_neg at I must give EXACTLY CReal.Equiv (abs (neg I)) (abs I): \
         {admitted:?}"
    );
}

/// Negative control for [`abs_neg_concrete_instantiation`]: the SAME proof
/// term must be REFUSED against `Equiv (abs (neg I)) (abs Complex.zero)` --
/// `abs I ~ CReal.one`, `abs zero ~ CReal.zero`, genuinely different values,
/// so this is not a vacuous mismatch.
#[test]
fn abs_neg_wrong_value_is_load_bearing() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let proof = d.lemma(p.abs_neg, &[i_c]);

    let neg_i = d.const_app(p.neg, &[i_c]);
    let abs_neg_i = d.const_app(p.abs, &[neg_i]);
    let abs_zero = d.const_app(p.abs, &[zero_c]);
    let wrong_ty = d.const_app(p.creal.equiv, &[abs_neg_i, abs_zero]);

    let name = d.kernel().name_str(anon, "Check.abs_neg_wrong_value");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: wrong_ty,
        value: proof,
    });
    assert!(
        admitted.is_err(),
        "abs_neg's proof at I must NOT type-check against `Equiv (abs (neg \
         I)) (abs zero)`: {admitted:?}"
    );
}

/// A concrete instantiation of [`ComplexPrelude::abs_le_add_abs_sub`] at
/// `a := I`, `b := one`: `abs I ~ 1`, `abs one ~ 1`, `abs (I - 1) ~ sqrt 2`,
/// so the claim is `le 1 (1 + sqrt 2)` -- true, and not an equality (so a
/// swapped direction would be caught, unlike an instance where both sides
/// coincide).
#[test]
fn abs_le_add_abs_sub_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let proof = d.lemma(p.abs_le_add_abs_sub, &[i_c, one_c]);

    let neg_one = d.const_app(p.neg, &[one_c]);
    let diff = d.const_app(p.add, &[i_c, neg_one]);
    let abs_i = d.const_app(p.abs, &[i_c]);
    let abs_one = d.const_app(p.abs, &[one_c]);
    let abs_diff = d.const_app(p.abs, &[diff]);
    let rhs = d.const_app(p.creal.add, &[abs_one, abs_diff]);
    let ty = d.const_app(p.creal.le, &[abs_i, rhs]);

    let name = d
        .kernel()
        .name_str(anon, "Check.abs_le_add_abs_sub_at_I_one");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: proof,
    });
    assert!(
        admitted.is_ok(),
        "abs_le_add_abs_sub at (I, one) must give EXACTLY CReal.le (abs I) \
         (add (abs one) (abs (add I (neg one)))): {admitted:?}"
    );
}

/// Negative control for [`abs_le_add_abs_sub_concrete_instantiation`]: the
/// SAME proof term must be REFUSED against the REVERSED inequality `le (add
/// (abs one) (abs (add I (neg one)))) (abs I)` -- `le 1+sqrt2 1` is false,
/// so this is a genuinely discriminating (not merely vacuous) direction
/// swap.
#[test]
fn abs_le_add_abs_sub_direction_is_load_bearing() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let proof = d.lemma(p.abs_le_add_abs_sub, &[i_c, one_c]);

    let neg_one = d.const_app(p.neg, &[one_c]);
    let diff = d.const_app(p.add, &[i_c, neg_one]);
    let abs_i = d.const_app(p.abs, &[i_c]);
    let abs_one = d.const_app(p.abs, &[one_c]);
    let abs_diff = d.const_app(p.abs, &[diff]);
    let rhs = d.const_app(p.creal.add, &[abs_one, abs_diff]);
    let wrong_ty = d.const_app(p.creal.le, &[rhs, abs_i]);

    let name = d
        .kernel()
        .name_str(anon, "Check.abs_le_add_abs_sub_wrong_direction");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: wrong_ty,
        value: proof,
    });
    assert!(
        admitted.is_err(),
        "abs_le_add_abs_sub's proof at (I, one) must NOT type-check against \
         the REVERSED `le (add (abs one) (abs (add I (neg one)))) (abs I)`: \
         {admitted:?}"
    );
}

/// `Complex.abs_one` states `abs one ~ CReal.one`, checked directly against
/// the declared theorem's type rather than by re-deriving it, since
/// `declare_abs_one`'s own proof already exercises the derivation.
#[test]
fn abs_one_is_stated_as_creal_one() {
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.abs_one)
        .expect("Complex.abs_one must be declared")
    {
        Declaration::Theorem { ty, .. } => kernel.render_lean(*ty),
        other => panic!("{other:?} is not a theorem"),
    };
    assert!(
        ty.contains("Complex.abs"),
        "abs_one's statement must mention Complex.abs: {ty}"
    );
}

/// Negative control for `Complex.abs_one`: its proof term must NOT
/// type-check against `abs one ~ CReal.zero` -- otherwise the checker could
/// not distinguish a computed value from an arbitrary one.
#[test]
fn abs_one_value_is_load_bearing() {
    use super::ring::ceq;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let proof = d.lemma(p.abs_one, &[]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let abs_one_c = d.const_app(p.abs, &[one_c]);
    let zero_real = d.kernel().const_(p.creal.zero, vec![]);
    let wrong_ty = ceq(&mut d, p.creal, abs_one_c, zero_real);

    let name = d.kernel().name_str(anon, "Check.abs_one_wrong_value");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: wrong_ty,
        value: proof,
    });
    assert!(
        admitted.is_err(),
        "abs_one's proof must NOT type-check against `abs one ~ \
         CReal.zero`: {admitted:?}"
    );
}

/// `Complex.polyEval_polyAdd` instantiated at two PAIRWISE DISTINCT constant
/// coefficient functions (`c := fun _ => I`, `g := fun _ => one`) and a
/// concrete bound/point (`n = 2`, `x = I`), mirroring
/// `sub_div_concrete_instantiation`'s own "distinct values, not just I and
/// one collapsed together" discipline: a `c`/`g` swap in the production code
/// would produce a term that does not match this independently-built
/// expected type (`add` is not *definitionally* commutative here -- only
/// `Complex.add_comm`-provably so), so this genuinely exercises argument
/// order, not just "the Pi-type is what it says it is".
#[test]
fn poly_eval_poly_add_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let nat = d.nat_ty();
    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let c_i_fv = d.fresh_fvar();
    let c = d.lam_fv(c_i_fv, nat, i_c);
    let g_i_fv = d.fresh_fvar();
    let g = d.lam_fv(g_i_fv, nat, one_c);

    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);
    let x = i_c;

    // Equiv (polyEval (polyAdd c g) 2 I) (add (polyEval c 2 I) (polyEval g 2 I)).
    let proof = d.lemma(p.poly.poly_eval_poly_add, &[c, g, two_n, x]);

    let poly_add_cg = d.const_app(p.poly.poly_add, &[c, g]);
    let lhs_stmt = d.const_app(p.poly.poly_eval, &[poly_add_cg, two_n, x]);
    let eval_c = d.const_app(p.poly.poly_eval, &[c, two_n, x]);
    let eval_g = d.const_app(p.poly.poly_eval, &[g, two_n, x]);
    let rhs_stmt = d.const_app(p.add, &[eval_c, eval_g]);
    let ty = super::zeq(&mut d, p, lhs_stmt, rhs_stmt);

    let name = d
        .kernel()
        .name_str(anon, "Check.poly_eval_poly_add_concrete");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: proof,
    });
    assert!(
        admitted.is_ok(),
        "polyEval_polyAdd at (c := const I, g := const one, n := 2, x := I) \
         must give EXACTLY Equiv (polyEval (polyAdd c g) 2 I) \
         (add (polyEval c 2 I) (polyEval g 2 I)): {admitted:?}"
    );
}

/// `Complex.polyEval_polyScale` instantiated at a constant coefficient
/// function distinct from the scalar (`a := I`, `c := fun _ => one`) and a
/// concrete bound/point.
#[test]
fn poly_eval_poly_scale_concrete_instantiation() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let nat = d.nat_ty();
    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let a = i_c;
    let c_i_fv = d.fresh_fvar();
    let c = d.lam_fv(c_i_fv, nat, one_c);

    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);
    let x = one_c;

    // Equiv (polyEval (polyScale I c) 2 one) (mul I (polyEval c 2 one)).
    let proof = d.lemma(p.poly.poly_eval_poly_scale, &[a, c, two_n, x]);

    let poly_scale_ac = d.const_app(p.poly.poly_scale, &[a, c]);
    let lhs_stmt = d.const_app(p.poly.poly_eval, &[poly_scale_ac, two_n, x]);
    let eval_c = d.const_app(p.poly.poly_eval, &[c, two_n, x]);
    let rhs_stmt = d.const_app(p.mul, &[a, eval_c]);
    let ty = super::zeq(&mut d, p, lhs_stmt, rhs_stmt);

    let name = d
        .kernel()
        .name_str(anon, "Check.poly_eval_poly_scale_concrete");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: proof,
    });
    assert!(
        admitted.is_ok(),
        "polyEval_polyScale at (a := I, c := const one, n := 2, x := one) \
         must give EXACTLY Equiv (polyEval (polyScale I c) 2 one) \
         (mul I (polyEval c 2 one)): {admitted:?}"
    );
}

/// Negative control for `Complex.polyEval_polyAdd`: its proof must NOT
/// type-check against a `mul`-shaped conclusion (`mul (polyEval c n x)
/// (polyEval g n x)` in place of `add (...) (...)`) -- otherwise the
/// homomorphism statement would be too weak to distinguish `polyAdd`'s
/// evaluation behaviour from `polyScale`'s, or from no homomorphism at all.
/// Mirrors `abs_one_value_is_load_bearing`'s own "the proof is load-bearing
/// for the specific operation, not vacuously anything" shape.
#[test]
fn poly_eval_poly_add_would_reject_mul_instead_of_add() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let nat = d.nat_ty();
    let i_c = d.kernel().const_(p.i, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let c_i_fv = d.fresh_fvar();
    let c = d.lam_fv(c_i_fv, nat, i_c);
    let g_i_fv = d.fresh_fvar();
    let g = d.lam_fv(g_i_fv, nat, one_c);

    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);
    let x = i_c;

    let proof = d.lemma(p.poly.poly_eval_poly_add, &[c, g, two_n, x]);

    let poly_add_cg = d.const_app(p.poly.poly_add, &[c, g]);
    let lhs_stmt = d.const_app(p.poly.poly_eval, &[poly_add_cg, two_n, x]);
    let eval_c = d.const_app(p.poly.poly_eval, &[c, two_n, x]);
    let eval_g = d.const_app(p.poly.poly_eval, &[g, two_n, x]);
    let wrong_rhs = d.const_app(p.mul, &[eval_c, eval_g]);
    let wrong_ty = super::zeq(&mut d, p, lhs_stmt, wrong_rhs);

    let name = d
        .kernel()
        .name_str(anon, "Check.poly_eval_poly_add_wrong_mul");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: wrong_ty,
        value: proof,
    });
    assert!(
        admitted.is_err(),
        "polyEval_polyAdd's proof must NOT type-check against a `mul`-shaped \
         conclusion: {admitted:?}"
    );
}

/// Re-generalize `Complex.polyEval_polyMul` over fresh, mutually-opaque
/// witnesses for every one of its own arguments (`c`, `g`, `m`, `n`, `x`, and
/// PLACEHOLDER hypothesis fvars carrying exactly the `polyDegreeLt` types
/// this theorem demands -- never discharged, since only their *type* matters
/// for this check) and re-bind the result into a fresh closed declaration.
///
/// This is the concrete-instantiation discipline
/// `poly_eval_poly_add_concrete_instantiation` uses, adapted to a theorem
/// whose hypotheses make a genuinely NONZERO closed coefficient function
/// expensive here (it would need a nested `Nat.rec`, not attempted in this
/// slice). Distinct fresh free variables can never become definitionally
/// equal to one another or collapse under reduction the way `Complex.zero`
/// does, so `mul (eval_c) (eval_g)` and `add (eval_c) (eval_g)` stay
/// syntactically apart no matter how far the kernel reduces -- a `c`/`g`
/// swap anywhere in [`super::poly`]'s construction of
/// `Complex.polyEval_polyMul` would produce a term that does not match this
/// independently-built expected type.
#[test]
fn poly_eval_poly_mul_argument_order_is_load_bearing() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let nat = d.nat_ty();
    let carrier = super::complex_ty(&mut d, p);
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let degree_lt_c = d.const_app(p.poly.poly_degree_lt, &[c, m]);
    let degree_lt_g = d.const_app(p.poly.poly_degree_lt, &[g, n]);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let proof = d.lemma(p.poly.poly_eval_poly_mul, &[c, g, m, n, hc, hg, x]);

    let poly_mul_cg = d.const_app(p.poly.poly_mul, &[c, g]);
    let bound = d.add(m, n);
    let lhs_stmt = d.const_app(p.poly.poly_eval, &[poly_mul_cg, bound, x]);
    let eval_c = d.const_app(p.poly.poly_eval, &[c, m, x]);
    let eval_g = d.const_app(p.poly.poly_eval, &[g, n, x]);
    let rhs_stmt = d.const_app(p.mul, &[eval_c, eval_g]);
    let inner_ty = super::zeq(&mut d, p, lhs_stmt, rhs_stmt);

    let ty = {
        let over_x = d.pi_fv(x_fv, carrier, inner_ty);
        let after_hg = d.arrow(degree_lt_g, over_x);
        let after_hc = d.arrow(degree_lt_c, after_hg);
        let over_n = d.pi_fv(n_fv, nat, after_hc);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_g = d.pi_fv(g_fv, fn_ty, over_m);
        d.pi_fv(c_fv, fn_ty, over_g)
    };
    let value = {
        let over_x = d.lam_fv(x_fv, carrier, proof);
        let after_hg = d.lam_fv(hg_fv, degree_lt_g, over_x);
        let after_hc = d.lam_fv(hc_fv, degree_lt_c, after_hg);
        let over_n = d.lam_fv(n_fv, nat, after_hc);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_g = d.lam_fv(g_fv, fn_ty, over_m);
        d.lam_fv(c_fv, fn_ty, over_g)
    };

    let name = d
        .kernel()
        .name_str(anon, "Check.poly_eval_poly_mul_argument_order");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "polyEval_polyMul, re-closed over its own bound variables in the SAME \
         order, must give EXACTLY Equiv (polyEval (polyMul c g) (add m n) x) \
         (mul (polyEval c m x) (polyEval g n x)): {admitted:?}"
    );
}

/// Negative control for `Complex.polyEval_polyMul`, mirroring
/// `poly_eval_poly_add_would_reject_mul_instead_of_add`'s shape: the SAME
/// re-closed proof from
/// [`poly_eval_poly_mul_argument_order_is_load_bearing`] must NOT type-check
/// against an `add`-shaped conclusion in place of `mul`-shaped -- otherwise
/// the homomorphism statement would be too weak to distinguish `polyMul`'s
/// evaluation behaviour from `polyAdd`'s, or from no homomorphism at all.
#[test]
fn poly_eval_poly_mul_would_reject_add_instead_of_mul() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let nat = d.nat_ty();
    let carrier = super::complex_ty(&mut d, p);
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let degree_lt_c = d.const_app(p.poly.poly_degree_lt, &[c, m]);
    let degree_lt_g = d.const_app(p.poly.poly_degree_lt, &[g, n]);
    let hc_fv = d.fresh_fvar();
    let hc = d.kernel().fvar(hc_fv);
    let hg_fv = d.fresh_fvar();
    let hg = d.kernel().fvar(hg_fv);

    let proof = d.lemma(p.poly.poly_eval_poly_mul, &[c, g, m, n, hc, hg, x]);

    let poly_mul_cg = d.const_app(p.poly.poly_mul, &[c, g]);
    let bound = d.add(m, n);
    let lhs_stmt = d.const_app(p.poly.poly_eval, &[poly_mul_cg, bound, x]);
    let eval_c = d.const_app(p.poly.poly_eval, &[c, m, x]);
    let eval_g = d.const_app(p.poly.poly_eval, &[g, n, x]);
    let wrong_rhs = d.const_app(p.add, &[eval_c, eval_g]);
    let inner_ty = super::zeq(&mut d, p, lhs_stmt, wrong_rhs);

    let ty = {
        let over_x = d.pi_fv(x_fv, carrier, inner_ty);
        let after_hg = d.arrow(degree_lt_g, over_x);
        let after_hc = d.arrow(degree_lt_c, after_hg);
        let over_n = d.pi_fv(n_fv, nat, after_hc);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        let over_g = d.pi_fv(g_fv, fn_ty, over_m);
        d.pi_fv(c_fv, fn_ty, over_g)
    };
    let value = {
        let over_x = d.lam_fv(x_fv, carrier, proof);
        let after_hg = d.lam_fv(hg_fv, degree_lt_g, over_x);
        let after_hc = d.lam_fv(hc_fv, degree_lt_c, after_hg);
        let over_n = d.lam_fv(n_fv, nat, after_hc);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        let over_g = d.lam_fv(g_fv, fn_ty, over_m);
        d.lam_fv(c_fv, fn_ty, over_g)
    };

    let name = d
        .kernel()
        .name_str(anon, "Check.poly_eval_poly_mul_wrong_add");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_err(),
        "polyEval_polyMul's proof must NOT type-check against an `add`-shaped \
         conclusion: {admitted:?}"
    );
}

/// `fun i => Nat.rec(fun _ => Complex, a0, fun n _ => Nat.rec(fun _ =>
/// Complex, a1, fun _ _ => zero, n), i)` -- coefficients `a0, a1, 0, 0, …`, a
/// genuine (not opaque-witness) two-term polynomial coefficient function,
/// built the same way [`super::declare_pow`]'s own `Complex.pow` is (nested
/// `Nat.rec` at `Complex`'s own universe, not [`crate::nat_prelude::NatOps::induct`]
/// -- that helper's motive is `Prop`-valued only, so it cannot produce a
/// `Complex`-valued function).
///
/// The inner `Nat.rec`'s step ignores both its arguments and returns `zero`
/// unconditionally, so `f (succ (succ y)) ≡ zero` by exactly two ι-steps for
/// ANY `y`, symbolic or not -- the fact
/// [`two_term_polynomial_vanishes_from_two`] depends on.
fn two_term_polynomial(
    d: &mut crate::int_prelude::ops::IntDev<'_>,
    p: ComplexPrelude,
    a0: crate::expr::ExprId,
    a1: crate::expr::ExprId,
) -> crate::expr::ExprId {
    use crate::BinderInfo;
    use crate::nat_prelude::NatOps;

    let carrier = super::complex_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let zero_c = d.kernel().const_(p.zero, vec![]);

    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);

    let inner_minor_succ = {
        let j2_fv = d.fresh_fvar();
        let ih2_fv = d.fresh_fvar();
        let inner_body = d.lam_fv(ih2_fv, carrier, zero_c);
        d.lam_fv(j2_fv, nat, inner_body)
    };

    let outer_minor_succ = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let ih_fv = d.fresh_fvar();
        let inner_applied = d.apply(rec, &[motive, a1, inner_minor_succ, n]);
        let with_ih = d.lam_fv(ih_fv, carrier, inner_applied);
        d.lam_fv(n_fv, nat, with_ih)
    };

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let body = d.apply(rec, &[motive, a0, outer_minor_succ, i]);
    d.lam_fv(i_fv, nat, body)
}

/// `Complex.polyDegreeLt f 2`, proved for any `f` built by
/// [`two_term_polynomial`] -- genuinely, not assumed as a hypothesis fvar the
/// way every OTHER `poly_eval_poly_mul` test in this file does.
///
/// Given `hle : Nat.le 2 i`, `Nat.le_dest` recovers `Exists (fun k => Eq Nat
/// (add 2 k) i)`; `Exists` is `Prop`-only (`Exists.rec` cannot extract `k` as
/// DATA), but the GOAL here -- `Equiv (f i) zero` -- is itself a `Prop`, so
/// eliminating into it is exactly what `Exists.rec` allows, unlike the factor
/// theorem's quotient. `Nat.add_comm` puts the recovered `k` on the LEFT of
/// the literal `2` (`add k 2`, not `add 2 k` -- symbolic left, literal right,
/// the only form `Nat.add`'s right-recursion actually reduces), so `add k 2 ≡
/// succ (succ k)` by pure ι-reduction for ANY `k`, and `f`'s own nested
/// `Nat.rec` then collapses to `zero` the same way regardless of `k`. Both
/// reductions are short and fully structural (no partial evaluation of a
/// symbolic index against a concrete accumulator), so this does not hit the
/// "concrete witness costs more than symbolic" trap.
fn two_term_polynomial_vanishes_from_two(
    d: &mut crate::int_prelude::ops::IntDev<'_>,
    p: ComplexPrelude,
    f: crate::expr::ExprId,
) -> crate::expr::ExprId {
    use crate::int_prelude::ops::exists_elim;
    use crate::nat_prelude::NatOps;

    let nat = d.nat_ty();
    let nat_p = d.prelude();
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hle_fv = d.fresh_fvar();
    let hle = d.kernel().fvar(hle_fv);

    let witness = d.lemma(nat_p.le_dest, &[two_n, i, hle]);

    let predicate = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let add_2k = d.add(two_n, k);
        let eq_ty = d.eq(add_2k, i);
        d.lam_fv(k_fv, nat, eq_ty)
    };

    let target = {
        let fi = d.apply(f, &[i]);
        super::zeq(d, p, fi, zero_c)
    };

    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);

        let add_2k = d.add(two_n, k);
        let eq_ty = d.eq(add_2k, i);

        let add_k2 = d.add(k, two_n);
        let h_comm = d.lemma(nat_p.add_comm, &[two_n, k]);
        // h_comm : Eq Nat (add two_n k) (add k two_n)
        let h_comm_symm = d.symm(add_2k, add_k2, h_comm);
        // h_comm_symm : Eq Nat (add k two_n) (add two_n k)
        let h_final = d.trans(add_k2, add_2k, i, h_comm_symm, heq);
        // h_final : Eq Nat (add k two_n) i

        let motive = d.eq_motive(add_k2, &|dd, x| {
            let fx = dd.apply(f, &[x]);
            super::zeq(dd, p, fx, zero_c)
        });
        let refl_case = d.lemma(p.equiv_refl, &[zero_c]);
        // refl_case : Equiv(zero, zero), ascribed against Equiv(f (add k
        // two_n), zero) -- relies on `f (add k two_n)` reducing to `zero`
        // by pure δι (`add k two_n` ≡ succ(succ k)` since `two_n` is
        // LITERAL on the right, then two ι-steps of `f`'s own recursion).
        let body = d.transport(add_k2, motive, refl_case, i, h_final);

        let with_heq = d.lam_fv(heq_fv, eq_ty, body);
        d.lam_fv(k_fv, nat, with_heq)
    };

    let case_proof = exists_elim(d, predicate, target, witness, minor);
    let le_2_i = d.le(two_n, i);
    let with_hle = d.lam_fv(hle_fv, le_2_i, case_proof);
    d.lam_fv(i_fv, nat, with_hle)
}

/// `Equiv (polyEval f 2 x) (add (add zero (mul a0 one)) (mul a1 x))`, given
/// `f` is [`two_term_polynomial`]`(a0, a1)`.
///
/// `polyEval f 2 x` δι-reduces (`n = 2` is literal throughout, so this is
/// pure, bounded computation, not the "concrete witness" trap -- no symbolic
/// Nat index is involved anywhere in this step) to `add (add zero (mul (f 0)
/// (pow x 0))) (mul (f 1) (pow x 1))`; `f 0 ≡ a0` and `f 1 ≡ a1` by the same
/// two-`Nat.rec`-base-case δι-reduction [`two_term_polynomial`]'s own doc
/// describes, and `pow x 0 ≡ one` similarly. `pow x 1` alone needs one more
/// step: `Complex.pow`'s `Nat.rec` gives `mul (pow x 0) x`, not `x` itself, so
/// [`super::ring_law_proof`] closes `mul one x ~ x`.
fn two_term_poly_eval_clean(
    d: &mut crate::int_prelude::ops::IntDev<'_>,
    p: ComplexPrelude,
    f: crate::expr::ExprId,
    a0: crate::expr::ExprId,
    a1: crate::expr::ExprId,
    x: crate::expr::ExprId,
) -> (crate::expr::ExprId, crate::expr::ExprId) {
    use super::{CExpr, ring_law_proof};
    use crate::nat_prelude::NatOps;

    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);
    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);

    let eval_f_2_x = d.const_app(p.poly.poly_eval, &[f, two_n, x]);

    let f0 = d.apply(f, &[zero_n]);
    let f1 = d.apply(f, &[one_n]);
    let p0 = d.const_app(p.pow, &[x, zero_n]);
    let p1 = d.const_app(p.pow, &[x, one_n]);

    let mul_f0p0 = d.const_app(p.mul, &[f0, p0]);
    let mul_f1p1 = d.const_app(p.mul, &[f1, p1]);
    let inner_add = d.const_app(p.add, &[zero_c, mul_f0p0]);
    let ec = d.const_app(p.add, &[inner_add, mul_f1p1]);
    let h_defeq = d.lemma(p.equiv_refl, &[ec]);
    // h_defeq : Equiv(ec, ec), ascribed against Equiv(eval_f_2_x, ec) below
    // -- relies on `eval_f_2_x` reducing to `ec` by pure δι.

    let h_f0 = d.lemma(p.equiv_refl, &[a0]);
    let h_f1 = d.lemma(p.equiv_refl, &[a1]);
    let h_p0 = d.lemma(p.equiv_refl, &[one_c]);

    let mul_p0x = d.const_app(p.mul, &[one_c, x]);
    let h_p1_base = d.lemma(p.equiv_refl, &[mul_p0x]);
    // h_p1_base : Equiv(mul(one,x), mul(one,x)), ascribed against
    // Equiv(p1, mul(one,x)) -- relies on `pow x 1` reducing to `mul(pow x
    // 0, x)` then `pow x 0` reducing to `one`.
    let x_v = CExpr::var(d, p, x);
    let h_p1_ring = ring_law_proof(d, p, &CExpr::mul(CExpr::One, x_v.clone()), &x_v);
    let h_p1 = d.lemma(p.equiv_trans, &[p1, mul_p0x, x, h_p1_base, h_p1_ring]);

    let h_f0p0 = d.lemma(p.mul_congr, &[f0, a0, p0, one_c, h_f0, h_p0]);
    let h_f1p1 = d.lemma(p.mul_congr, &[f1, a1, p1, x, h_f1, h_p1]);

    let mul_a0one = d.const_app(p.mul, &[a0, one_c]);
    let mul_a1x = d.const_app(p.mul, &[a1, x]);
    let refl_zero = d.lemma(p.equiv_refl, &[zero_c]);
    let h_inner = d.lemma(
        p.add_congr,
        &[zero_c, zero_c, mul_f0p0, mul_a0one, refl_zero, h_f0p0],
    );
    let clean_inner = d.const_app(p.add, &[zero_c, mul_a0one]);
    let h_outer = d.lemma(
        p.add_congr,
        &[inner_add, clean_inner, mul_f1p1, mul_a1x, h_inner, h_f1p1],
    );
    let clean = d.const_app(p.add, &[clean_inner, mul_a1x]);

    let h_ec = d.lemma(p.equiv_trans, &[eval_f_2_x, ec, clean, h_defeq, h_outer]);
    (clean, h_ec)
}

/// The "richer concrete corroboration" the predecessor named and explicitly
/// deferred: `(X+1)(X-1) = X^2-1` at a point, over GENUINE two-term
/// coefficient functions built by nested `Nat.rec` (`c := X+1`, coefficients
/// `1, 1, 0, …`; `g := X-1`, coefficients `-1, 1, 0, …`) with their OWN
/// `polyDegreeLt` proofs -- not opaque witness fvars carrying only the
/// hypothesis TYPE the way every other `poly_eval_poly_mul` test in this file
/// does. Concrete and symbolic checks fail on disjoint defect classes (a
/// degenerate all-zero concrete instantiation would be vacuous; a
/// symbolic-only check can hide a defeq-shaped associativity gap numerals
/// paper over -- see the exponential-chapter incident this project's own
/// history records), so this exercises the axis the symbolic
/// `poly_eval_poly_mul` proof does not: it evaluates the point at
/// `Complex.I`, where `(I+1)(I-1) = I^2 - 1 = -2`, a genuinely nonzero value,
/// not the degenerate zero the module doc's own vacuity warning names.
///
/// Runs on [`on_a_deep_stack`]'s thread: the nested nine-lemma-chain proof
/// term this builds, plus the ring calculus's own recursion inside
/// `add_declaration`'s type-check, overflows the default 2 MiB debug stack —
/// the same reason `the_ring_calculus_proves_a_true_identity` needs it.
#[test]
fn poly_eval_poly_mul_x_plus_one_times_x_minus_one_is_x_squared_minus_one() {
    on_a_deep_stack(poly_eval_poly_mul_x_plus_one_times_x_minus_one_is_x_squared_minus_one_body);
}

fn poly_eval_poly_mul_x_plus_one_times_x_minus_one_is_x_squared_minus_one_body() {
    use super::CExpr;
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let one_c = d.kernel().const_(p.one, vec![]);
    let neg_one_c = d.const_app(p.neg, &[one_c]);
    let i_c = d.kernel().const_(p.i, vec![]);
    let x = i_c;

    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);

    let c = two_term_polynomial(&mut d, p, one_c, one_c);
    let g = two_term_polynomial(&mut d, p, neg_one_c, one_c);
    let hc = two_term_polynomial_vanishes_from_two(&mut d, p, c);
    let hg = two_term_polynomial_vanishes_from_two(&mut d, p, g);

    // Equiv (polyEval (polyMul c g) (add 2 2) x) (mul (polyEval c 2 x) (polyEval g 2 x)).
    let proof_mul = d.lemma(p.poly.poly_eval_poly_mul, &[c, g, two_n, two_n, hc, hg, x]);

    let (clean_c, h_clean_c) = two_term_poly_eval_clean(&mut d, p, c, one_c, one_c, x);
    let (clean_g, h_clean_g) = two_term_poly_eval_clean(&mut d, p, g, neg_one_c, one_c, x);

    let eval_c_2_x = d.const_app(p.poly.poly_eval, &[c, two_n, x]);
    let eval_g_2_x = d.const_app(p.poly.poly_eval, &[g, two_n, x]);
    let h_combined = d.lemma(
        p.mul_congr,
        &[
            eval_c_2_x, clean_c, eval_g_2_x, clean_g, h_clean_c, h_clean_g,
        ],
    );
    // h_combined : Equiv(mul(eval_c_2_x,eval_g_2_x), mul(clean_c,clean_g))

    let x2_minus_1 = {
        let x_v = CExpr::I;
        let lhs_ring = CExpr::mul(
            CExpr::add(
                CExpr::add(CExpr::Zero, CExpr::mul(CExpr::One, CExpr::One)),
                CExpr::mul(CExpr::One, x_v.clone()),
            ),
            CExpr::add(
                CExpr::add(CExpr::Zero, CExpr::mul(CExpr::neg(CExpr::One), CExpr::One)),
                CExpr::mul(CExpr::One, x_v.clone()),
            ),
        );
        let rhs_ring = CExpr::add(CExpr::mul(x_v.clone(), x_v.clone()), CExpr::neg(CExpr::One));
        let h_ring = super::ring_law_proof(&mut d, p, &lhs_ring, &rhs_ring);
        let mul_clean = d.const_app(p.mul, &[clean_c, clean_g]);
        let target = super::render_c(&mut d, p, &rhs_ring);
        let mul_evals_inner = d.const_app(p.mul, &[eval_c_2_x, eval_g_2_x]);
        let h_final = d.lemma(
            p.equiv_trans,
            &[mul_evals_inner, mul_clean, target, h_combined, h_ring],
        );
        (target, h_final)
    };
    let (target, h_final) = x2_minus_1;

    let poly_mul_cg = d.const_app(p.poly.poly_mul, &[c, g]);
    let bound = d.add(two_n, two_n);
    let lhs_stmt = d.const_app(p.poly.poly_eval, &[poly_mul_cg, bound, x]);
    let mul_evals = d.const_app(p.mul, &[eval_c_2_x, eval_g_2_x]);
    let overall = d.lemma(
        p.equiv_trans,
        &[lhs_stmt, mul_evals, target, proof_mul, h_final],
    );

    let ty = super::zeq(&mut d, p, lhs_stmt, target);
    let name = d
        .kernel()
        .name_str(anon, "Check.poly_eval_poly_mul_x_plus_one_x_minus_one");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value: overall,
    });
    assert!(
        admitted.is_ok(),
        "(X+1)(X-1) evaluated via polyMul/polyEval at genuine two-term \
         coefficient functions, at the point I, must give EXACTLY \
         Equiv(polyEval(polyMul c g)(4)(I), mul(I,I) + (-1)): {admitted:?}"
    );
}

/// `fun i => Nat.rec(…, a0, fun _ _ => Nat.rec(…, a1, fun _ _ =>
/// Nat.rec(…, a2, fun _ _ => zero, _), _), i)` — coefficients `a0, a1, a2,
/// 0, 0, …`, a genuine three-term coefficient function extending
/// [`two_term_polynomial`] by one more nested `Nat.rec` level, used here to
/// build a concrete `X² − 1` (`a0 = -1, a1 = 0, a2 = 1`) for
/// [`factor_quotient_reproduces_x_plus_one_at_the_root_and_not_elsewhere`].
fn three_term_polynomial(
    d: &mut crate::int_prelude::ops::IntDev<'_>,
    p: ComplexPrelude,
    a0: crate::expr::ExprId,
    a1: crate::expr::ExprId,
    a2: crate::expr::ExprId,
) -> crate::expr::ExprId {
    use crate::BinderInfo;
    use crate::nat_prelude::NatOps;

    let carrier = super::complex_ty(d, p);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();
    let zero_c = d.kernel().const_(p.zero, vec![]);

    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);

    let level3_minor_succ = {
        let j3_fv = d.fresh_fvar();
        let ih3_fv = d.fresh_fvar();
        let inner_body = d.lam_fv(ih3_fv, carrier, zero_c);
        d.lam_fv(j3_fv, nat, inner_body)
    };
    let level2_minor_succ = {
        let j2_fv = d.fresh_fvar();
        let j2 = d.kernel().fvar(j2_fv);
        let ih2_fv = d.fresh_fvar();
        let inner_applied = d.apply(rec, &[motive, a2, level3_minor_succ, j2]);
        let with_ih = d.lam_fv(ih2_fv, carrier, inner_applied);
        d.lam_fv(j2_fv, nat, with_ih)
    };
    let level1_minor_succ = {
        let j1_fv = d.fresh_fvar();
        let j1 = d.kernel().fvar(j1_fv);
        let ih1_fv = d.fresh_fvar();
        let inner_applied = d.apply(rec, &[motive, a1, level2_minor_succ, j1]);
        let with_ih = d.lam_fv(ih1_fv, carrier, inner_applied);
        d.lam_fv(j1_fv, nat, with_ih)
    };

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let body = d.apply(rec, &[motive, a0, level1_minor_succ, i]);
    d.lam_fv(i_fv, nat, body)
}

/// The reproduce-and-refute check the brief asks for: `factorQuotient`
/// applied to a genuine `X² − 1` (built by [`three_term_polynomial`], not an
/// opaque witness) must EXACTLY reproduce `X + 1`'s coefficients at the root
/// `a = 1` (`q 0 = 1, q 1 = 1`, plus the boundary `q 2 = 0` confirming the
/// degree bound concretely), and must NOT give the SAME `q 0` at the
/// non-root `a = 2` — where the correct (unconditional synthetic-division,
/// no-root-needed) value is `q 0 = a = 2`, distinct from the root case's `1`.
///
/// Both directions of "a negative control fails two ways" are covered here:
/// asserting the WRONG value (`q 0 = 1` at `a = 2`) must be **rejected**
/// (not vacuously — see the paired assertion that the RIGHT non-root value,
/// `q 0 = 2`, is accepted, which is what makes the rejection meaningful
/// rather than "everything about `a = 2` is refused").
#[test]
fn factor_quotient_reproduces_x_plus_one_at_the_root_and_not_elsewhere() {
    on_a_deep_stack(factor_quotient_reproduces_x_plus_one_at_the_root_and_not_elsewhere_body);
}

fn factor_quotient_reproduces_x_plus_one_at_the_root_and_not_elsewhere_body() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let zero_c = d.kernel().const_(p.zero, vec![]);
    let one_c = d.kernel().const_(p.one, vec![]);
    let neg_one_c = d.const_app(p.neg, &[one_c]);
    let two_c = d.const_app(p.add, &[one_c, one_c]);

    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);

    // c := X^2 - 1: coefficients -1, 0, 1, 0, 0, ...
    let cx = three_term_polynomial(&mut d, p, neg_one_c, zero_c, one_c);

    // One admit-or-reject case: `Equiv(factorQuotient(cx, a, n, k), expect)`,
    // checked with a freshly-named anonymous `Theorem`.
    let check = |d: &mut IntDev<'_>,
                 a: crate::expr::ExprId,
                 k: crate::expr::ExprId,
                 expect: crate::expr::ExprId,
                 label: &str| {
        let fq_call = d.const_app(p.poly.factor_quotient, &[cx, a, two_n, k]);
        let stmt = super::zeq(d, p, fq_call, expect);
        let proof = d.lemma(p.equiv_refl, &[expect]);
        let name = d.kernel().name_str(anon, label);
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: stmt,
            value: proof,
        })
    };

    // Root case (a = 1): must reproduce X+1 exactly, plus the boundary.
    let r0 = check(&mut d, one_c, zero_n, one_c, "Check.fq_root_q0");
    assert!(
        r0.is_ok(),
        "factorQuotient(X^2-1, a=1, n=2, k=0) must be 1 (X+1's q0): {r0:?}"
    );
    let r1 = check(&mut d, one_c, one_n, one_c, "Check.fq_root_q1");
    assert!(
        r1.is_ok(),
        "factorQuotient(X^2-1, a=1, n=2, k=1) must be 1 (X+1's q1): {r1:?}"
    );
    let r2 = check(&mut d, one_c, two_n, zero_c, "Check.fq_root_boundary");
    assert!(
        r2.is_ok(),
        "factorQuotient(X^2-1, a=1, n=2, k=2) must be 0 -- the degree bound, checked concretely: {r2:?}"
    );

    // Non-root case (a = 2): the CORRECT value differs from the root case's.
    let nr0_correct = check(&mut d, two_c, zero_n, two_c, "Check.fq_nonroot_q0_correct");
    assert!(
        nr0_correct.is_ok(),
        "factorQuotient(X^2-1, a=2, n=2, k=0) must be 2 (= a, the unconditional \
         synthetic-division value): {nr0_correct:?}"
    );
    let nr1_correct = check(&mut d, two_c, one_n, one_c, "Check.fq_nonroot_q1_correct");
    assert!(
        nr1_correct.is_ok(),
        "factorQuotient(X^2-1, a=2, n=2, k=1) must be 1 (= X^2-1's own leading \
         coefficient, independent of a): {nr1_correct:?}"
    );

    // The refute half: claiming the ROOT-case value (1) at the NON-root a=2
    // must be REJECTED -- not vacuously, since the paired check above just
    // confirmed a DIFFERENT claim about the same (cx, a=2, k=0) IS accepted.
    let nr0_wrong = check(&mut d, two_c, zero_n, one_c, "Check.fq_nonroot_q0_wrong");
    assert!(
        nr0_wrong.is_err(),
        "factorQuotient(X^2-1, a=2, n=2, k=0) is 2, not 1 -- claiming it is 1 \
         (X+1's root-case q0) must be REJECTED: {nr0_wrong:?}"
    );
}

/// Corroborates [`poly::PolyNames::horner_from_top_diag_eq_poly_eval`] at a
/// genuine three-term polynomial with a NONZERO middle coefficient (`1 + 2X +
/// 3X²`, at the non-root point `a = 2`) -- `X² − 1`'s middle coefficient is
/// zero, which would make this lemma's `a`-dependence invisible.
///
/// `hornerFromTop c a n n` and `polyEval c (succ n) a` are checked
/// SEPARATELY against the same hand-computed value at `n = 0, 1, 2` (`1`,
/// `5`, `17`), each paired with a wrong-value control that must be REJECTED,
/// so this is a discriminating check of the lemma's stated meaning and not
/// just of the kernel's willingness to accept `equiv_refl`.
#[test]
fn horner_from_top_diag_matches_poly_eval_at_a_nonzero_middle_coefficient() {
    on_a_deep_stack(horner_from_top_diag_matches_poly_eval_at_a_nonzero_middle_coefficient_body);
}

fn horner_from_top_diag_matches_poly_eval_at_a_nonzero_middle_coefficient_body() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let one_c = d.kernel().const_(p.one, vec![]);
    let two_c = d.const_app(p.add, &[one_c, one_c]);
    let three_c = d.const_app(p.add, &[two_c, one_c]);
    let five_c = d.const_app(p.add, &[three_c, two_c]);
    let seventeen_c = {
        // 5 + 3*2*2 = 17, built as repeated `add` of `one_c` to stay in the
        // same "small ring expression, checked by defeq" idiom the rest of
        // this file uses rather than introducing a numeral encoding.
        let mut acc = five_c;
        for _ in 0..12 {
            acc = d.const_app(p.add, &[acc, one_c]);
        }
        acc
    };

    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);
    let three_n = d.succ(two_n);

    // c := 1 + 2X + 3X^2.
    let cx = three_term_polynomial(&mut d, p, one_c, two_c, three_c);
    let a = two_c;

    let check = |d: &mut IntDev<'_>,
                 call: crate::expr::ExprId,
                 expect: crate::expr::ExprId,
                 label: &str| {
        let stmt = super::zeq(d, p, call, expect);
        let proof = d.lemma(p.equiv_refl, &[expect]);
        let name = d.kernel().name_str(anon, label);
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: stmt,
            value: proof,
        })
    };

    // n = 0: hornerFromTop c a 0 0 = c 0 = 1 = polyEval c 1 a.
    let h00 = d.const_app(p.poly.horner_from_top, &[cx, a, zero_n, zero_n]);
    let pe1 = d.const_app(p.poly.poly_eval, &[cx, one_n, a]);
    assert!(
        check(&mut d, h00, one_c, "Check.diag_h00_right").is_ok(),
        "hornerFromTop(c,a,0,0) must be 1"
    );
    assert!(
        check(&mut d, h00, two_c, "Check.diag_h00_wrong").is_err(),
        "hornerFromTop(c,a,0,0) is 1, not 2 -- must be REJECTED"
    );
    assert!(
        check(&mut d, pe1, one_c, "Check.diag_pe1_right").is_ok(),
        "polyEval(c,1,a) must be 1"
    );

    // n = 1: hornerFromTop c a 1 1 = c0 + a*c1 = 1 + 2*2 = 5 = polyEval c 2 a.
    let h11 = d.const_app(p.poly.horner_from_top, &[cx, a, one_n, one_n]);
    let pe2 = d.const_app(p.poly.poly_eval, &[cx, two_n, a]);
    assert!(
        check(&mut d, h11, five_c, "Check.diag_h11_right").is_ok(),
        "hornerFromTop(c,a,1,1) must be 5"
    );
    assert!(
        check(&mut d, h11, one_c, "Check.diag_h11_wrong").is_err(),
        "hornerFromTop(c,a,1,1) is 5, not 1 -- must be REJECTED"
    );
    assert!(
        check(&mut d, pe2, five_c, "Check.diag_pe2_right").is_ok(),
        "polyEval(c,2,a) must be 5"
    );

    // n = 2: hornerFromTop c a 2 2 = c0 + a*c1 + a^2*c2 = 1+4+12 = 17
    //      = polyEval c 3 a.
    let h22 = d.const_app(p.poly.horner_from_top, &[cx, a, two_n, two_n]);
    let pe3 = d.const_app(p.poly.poly_eval, &[cx, three_n, a]);
    assert!(
        check(&mut d, h22, seventeen_c, "Check.diag_h22_right").is_ok(),
        "hornerFromTop(c,a,2,2) must be 17"
    );
    assert!(
        check(&mut d, h22, five_c, "Check.diag_h22_wrong").is_err(),
        "hornerFromTop(c,a,2,2) is 17, not 5 -- must be REJECTED"
    );
    assert!(
        check(&mut d, pe3, seventeen_c, "Check.diag_pe3_right").is_ok(),
        "polyEval(c,3,a) must be 17"
    );

    // And the actual theorem applies at these concrete arguments.
    let applied0 = d.const_app(p.poly.horner_from_top_diag_eq_poly_eval, &[cx, a, zero_n]);
    let applied1 = d.const_app(p.poly.horner_from_top_diag_eq_poly_eval, &[cx, a, one_n]);
    let applied2 = d.const_app(p.poly.horner_from_top_diag_eq_poly_eval, &[cx, a, two_n]);
    for (label, applied) in [
        ("Check.diag_theorem_n0", applied0),
        ("Check.diag_theorem_n1", applied1),
        ("Check.diag_theorem_n2", applied2),
    ] {
        let inferred = d.kernel().infer(applied);
        assert!(
            inferred.is_ok(),
            "{label}: the diagonal theorem must apply at concrete (c,a,n): {inferred:?}"
        );
    }
}

/// Corroborates [`poly::PolyNames::factor_quotient_succ_eq`] at a genuine
/// three-term polynomial with a NONZERO middle coefficient (`1 + 2X + 3X²`,
/// at the non-root point `a = 2`), at the smallest nontrivial instance
/// (`n = 1, k = 0`, so `k < n` holds and `succ n = 2`).
///
/// Independently hand-computed (not by re-using the theorem's own RHS
/// shape): `factorQuotient(c,a,1,0) = hornerFromTop(c,a,1,0) = c(1) = 2`, and
/// `factorQuotient(c,a,2,0) = hornerFromTop(c,a,2,1) = c(1) + a·c(2) = 2 +
/// 2·3 = 8` -- matching the theorem's own correction-term formula `8 = 2 +
/// pow(a,1)·c(2)`. Each accept is paired with a wrong-value control that
/// must be REJECTED, and the theorem itself is applied at these concrete
/// arguments to confirm the statement actually types there.
#[test]
fn factor_quotient_succ_eq_matches_the_correction_term_at_a_nonzero_middle_coefficient() {
    on_a_deep_stack(
        factor_quotient_succ_eq_matches_the_correction_term_at_a_nonzero_middle_coefficient_body,
    );
}

fn factor_quotient_succ_eq_matches_the_correction_term_at_a_nonzero_middle_coefficient_body() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.creal.rat.int);

    let one_c = d.kernel().const_(p.one, vec![]);
    let two_c = d.const_app(p.add, &[one_c, one_c]);
    let three_c = d.const_app(p.add, &[two_c, one_c]);
    let eight_c = {
        // 2 + 2*3 = 8, built as repeated `add` of `one_c` to stay in the
        // same "small ring expression, checked by defeq" idiom the rest of
        // this file uses rather than introducing a numeral encoding.
        let mut acc = two_c;
        for _ in 0..6 {
            acc = d.const_app(p.add, &[acc, one_c]);
        }
        acc
    };

    let zero_n = d.zero();
    let one_n = d.succ(zero_n);

    // c := 1 + 2X + 3X^2.
    let cx = three_term_polynomial(&mut d, p, one_c, two_c, three_c);
    let a = two_c;

    let check = |d: &mut IntDev<'_>,
                 call: crate::expr::ExprId,
                 expect: crate::expr::ExprId,
                 label: &str| {
        let stmt = super::zeq(d, p, call, expect);
        let proof = d.lemma(p.equiv_refl, &[expect]);
        let name = d.kernel().name_str(anon, label);
        d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: stmt,
            value: proof,
        })
    };

    // factorQuotient(c,a,1,0) = c(1) = 2.
    let fq_1_0 = d.const_app(p.poly.factor_quotient, &[cx, a, one_n, zero_n]);
    assert!(
        check(&mut d, fq_1_0, two_c, "Check.fq_succ_eq_small_right").is_ok(),
        "factorQuotient(c,a,1,0) must be 2"
    );
    assert!(
        check(&mut d, fq_1_0, three_c, "Check.fq_succ_eq_small_wrong").is_err(),
        "factorQuotient(c,a,1,0) is 2, not 3 -- must be REJECTED"
    );

    // factorQuotient(c,a,2,0) = c(1) + a*c(2) = 2 + 2*3 = 8.
    let two_n = d.succ(one_n);
    let fq_2_0 = d.const_app(p.poly.factor_quotient, &[cx, a, two_n, zero_n]);
    assert!(
        check(&mut d, fq_2_0, eight_c, "Check.fq_succ_eq_big_right").is_ok(),
        "factorQuotient(c,a,2,0) must be 8"
    );
    assert!(
        check(&mut d, fq_2_0, two_c, "Check.fq_succ_eq_big_wrong").is_err(),
        "factorQuotient(c,a,2,0) is 8, not 2 -- must be REJECTED"
    );

    // And the actual theorem applies at these concrete arguments.
    let hlt = d.zero_lt_succ(zero_n);
    let applied = d.lemma(p.poly.factor_quotient_succ_eq, &[cx, a, one_n, zero_n, hlt]);
    let inferred = d.kernel().infer(applied);
    assert!(
        inferred.is_ok(),
        "the correction theorem must apply at concrete (c,a,n=1,k=0): {inferred:?}"
    );
}

// ---------------------------------------------------------------------------
// Build-order tests (level 1 of the phase-order fix, architecture review §1)
// ---------------------------------------------------------------------------

/// The `STEPS` labels, in the order the (now-deleted) hand-written
/// `build_complex_prelude` call sequence used. Pinned so a `STEPS` edit that
/// silently reorders or drops a step fails HERE, naming exactly that, instead
/// of only surfacing later as a `Kernel::add_declaration` rejection several
/// steps downstream. Recount by re-running the extraction described in
/// `docs/research/11-design-review/2026-08-27-prelude-build-spike.md`, never
/// by hand-editing this list to make a failure go away.
const EXPECTED_STEP_ORDER: [&str; 92] = [
    "declare_carrier",
    "declare_projections",
    "declare_equiv",
    "declare_setoid_laws",
    "declare_constants",
    "declare_operations",
    "declare_congruences",
    "declare_projection_congruences",
    "declare_ring_laws",
    "algebra_instance::declare_comm_ring_s",
    "declare_pinning",
    "declare_re_add_im",
    "declare_conj_laws",
    "declare_conj_sub_ofreal_i",
    "declare_conj_zero_one",
    "declare_eq_conj_iff_real",
    "declare_norm",
    "declare_norm_conjugation",
    "declare_norm_sq_eq_zero_of_eq_zero",
    "declare_eq_zero_of_norm_sq_eq_zero",
    "declare_norm_sq_eq_zero_iff",
    "declare_norm_sq_add",
    "declare_norm_sq_add_le",
    "declare_no_order",
    "declare_inv",
    "declare_complex_mul_inv_cancel",
    "declare_complex_inv_congr",
    "declare_inv_mul",
    "declare_div",
    "declare_div_congr",
    "declare_div_self",
    "declare_apart",
    "declare_apart_irrefl",
    "declare_apart_symm",
    "declare_apart_of_normsq_pos",
    "declare_mul_apart_zero",
    "declare_mul_eq_zero_not_both_apart_zero",
    "declare_complex_inv_mul_cancel",
    "declare_pos_bound_conj",
    "declare_conj_inv",
    "declare_conj_div",
    "declare_mul_div_assoc",
    "declare_div_mul_cancel",
    "declare_add_div",
    "declare_neg_div",
    "declare_sub_div",
    "declare_pow",
    "declare_pow_equations",
    "declare_pow_add",
    "declare_norm_sq_pow",
    "declare_conj_pow",
    "declare_sum_range",
    "declare_sum_range_equations",
    "declare_sum_range_congr",
    "declare_mul_sum_range",
    "declare_sum_range_mul",
    "declare_sum_range_mul_double",
    "declare_mul_sub_one_geom",
    "declare_geom_series_div",
    "declare_of_nat",
    "declare_of_nat_equations",
    "declare_of_nat_add",
    "declare_of_nat_mul",
    "declare_of_nat_eq_cast",
    "declare_sum_range_add",
    "declare_sum_range_shift_front",
    "declare_sum_range_congr_lt",
    "declare_sum_range_split",
    "declare_sum_range_swap",
    "declare_sum_range_diagonal",
    "declare_sum_range_rect_eq_diag_add_corner",
    "declare_sum_range_mul_eq_diag_add_corner",
    "poly::declare_polynomial",
    "declare_add_pow",
    "declare_is_root_of_unity",
    "declare_one_is_root_of_unity",
    "declare_i_is_fourth_root",
    "declare_pow_mul",
    "declare_geom_sum_eq_zero_of_root_of_unity",
    "declare_root_of_unity_mul",
    "declare_root_of_unity_pow",
    "declare_ptolemy_identity",
    "declare_norm_sq_congr",
    "declare_ptolemy_inequality_sq",
    "declare_abs",
    "declare_abs_nonneg",
    "declare_abs_congr",
    "declare_abs_one",
    "declare_abs_mul",
    "declare_abs_add_le",
    "declare_abs_neg",
    "declare_abs_le_add_abs_sub",
];

/// `STEPS` (the data-driven build order that replaced the hand-written call
/// sequence) reproduces that sequence exactly, in order. A silent reorder or
/// drop fails here, naming which position changed, rather than showing up as
/// an opaque `Kernel::add_declaration` rejection several steps later.
#[test]
fn steps_table_matches_recorded_extraction() {
    let labels: Vec<&str> = super::STEPS.iter().map(|s| s.label).collect();
    assert_eq!(
        labels.as_slice(),
        EXPECTED_STEP_ORDER.as_slice(),
        "STEPS no longer matches the recorded build order -- see \
         docs/research/11-design-review/2026-08-27-prelude-build-spike.md"
    );
}

/// The existing, hand-written build order is already a valid topological
/// order for the dependencies `STEPS` declares: every `requires` entry is
/// satisfied by a strictly earlier step. This is the level-2 question the
/// architecture review asks (§1) -- answered here structurally, without
/// reordering anything at runtime.
#[test]
fn existing_step_order_is_topologically_valid() {
    let (_, prelude) = built();
    let result = super::validate_step_order(prelude, super::STEPS);
    assert!(
        result.is_ok(),
        "the existing STEPS order should already be topologically valid, \
         found: {result:?}"
    );
}

/// The deliberate-failure control: a two-step order where the consumer comes
/// BEFORE its provider must be rejected, and the rejection must be precise --
/// naming the missing declaration, the step that would produce it, and both
/// steps' positions. This is what proves `validate_step_order` can actually
/// fail, not merely that it passes on the one order it has ever seen.
static BROKEN_ORDER: &[super::BuildStep] = &[
    super::BuildStep {
        label: "consumer_before_its_provider",
        requires: &[|p: ComplexPrelude| p.equiv],
        provides: &[],
        run: super::declare_carrier, // never invoked; validate_step_order does not call `run`
    },
    super::BuildStep {
        label: "provider_after_its_consumer",
        requires: &[],
        provides: &[|p: ComplexPrelude| p.equiv],
        run: super::declare_equiv, // never invoked; validate_step_order does not call `run`
    },
];

#[test]
fn order_violation_is_detected_and_precise() {
    let (_, prelude) = built();
    let violation = super::validate_step_order(prelude, BROKEN_ORDER)
        .expect_err("a consumer placed before its provider must be rejected");
    assert_eq!(violation.consumer_index, 0);
    assert_eq!(violation.consumer_label, "consumer_before_its_provider");
    assert_eq!(
        violation.missing, prelude.equiv,
        "must name the exact missing declaration, not merely that one is missing"
    );
    assert_eq!(
        violation.provider,
        Some((1, "provider_after_its_consumer")),
        "must name which step provides the missing declaration and at what position"
    );
}

/// A dependency table naming a declaration nothing in the order provides is a
/// bug in the table itself, not merely a misordering -- and must still be
/// reported precisely (`provider: None`), not panic or silently pass.
static INCOMPLETE_ORDER: &[super::BuildStep] = &[super::BuildStep {
    label: "requires_something_nobody_provides",
    requires: &[|p: ComplexPrelude| p.equiv],
    provides: &[],
    run: super::declare_carrier, // never invoked
}];

#[test]
fn order_violation_reports_missing_provider_as_table_bug() {
    let (_, prelude) = built();
    let violation = super::validate_step_order(prelude, INCOMPLETE_ORDER)
        .expect_err("a requirement nobody provides must be rejected");
    assert_eq!(violation.consumer_index, 0);
    assert_eq!(violation.missing, prelude.equiv);
    assert_eq!(
        violation.provider, None,
        "no step in this table provides `equiv`, so provider must be None"
    );
}
