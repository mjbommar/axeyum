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
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude = build_complex_prelude(&mut kernel).expect("Complex prelude must build");
            (kernel, prelude)
        })
    });
    (kernel.clone(), *prelude)
}

/// Run `f` on a thread with a **64 MiB stack**.
///
/// The default test-thread stack is 2 MiB, and building this prelude overflows
/// it in a debug build: the roots-of-unity work pushed the accumulated proof
/// terms past the limit and `cargo test --lib complex` aborted with
/// `fatal runtime error: stack overflow` (SIGABRT), before any assertion ran.
///
/// This is deliberately **not** solved with `RUST_MIN_STACK`. That would make
/// the suite pass only for whoever remembers to export it — CI runs a bare
/// `cargo test`, and a gate that needs an undocumented environment variable to
/// be green is a gate that reports a false red to everyone else. The recursion
/// is in the kernel's own type checker over a genuinely large term, not a bug to
/// fix, so the fix is to give it room where it is exercised.
fn on_a_deep_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawning a deep-stack thread must succeed")
        .join()
        .expect("the deep-stack thread must not panic")
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
