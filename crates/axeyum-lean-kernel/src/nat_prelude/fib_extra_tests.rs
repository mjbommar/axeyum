//! Concrete-instance tests for `nat_prelude::fib_extra`'s three theorems.
//! Separate file for the same merge-hazard reason as `size_extra_tests.rs`;
//! `Fixture` here is the identical small local copy.
//!
//! The evaluation control for `Nat.fib` itself — that it reduces to
//! `0,1,1,2,3,5,8,13,21,34,55` at `n = 0..10`, with two independent wrong
//! numerals rejected — already lives in
//! `nat_prelude_tests::fib_reduces_on_numerals_with_a_negative_control` and
//! is deliberately NOT duplicated here.

use crate::{
    BinderInfo, Kernel, LocalContext, LocalDecl, NatOps, NatPrelude, NatState, build_nat_prelude,
};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }
}

/// `Nat.fib_one` and `Nat.fib_two` state their own equations and are
/// axiom-free.
///
/// # What the controls here rule out, and what they cannot
///
/// Both statements REDUCE to `Eq 1 1`, so a `def_eq` check on the inferred
/// type cannot separate `fib_one` from `fib_two` — that is control failure
/// mechanism 1 (vacuous by numerals) and going symbolic does not fix it,
/// because there is no variable: `fib 1` and `fib 2` are literally the same
/// value. What IS separable, and is checked below, is the ARGUMENT each
/// theorem is about: `fib 1` and `fib 2` must both be `1`, while `fib 3`
/// (= 2) must not be, so neither statement is one of the false neighbours.
/// The fact ledger's own discriminator is the RENDERED (unreduced) kernel
/// type, in which `AxNat.fib (succ zero)` and `AxNat.fib (succ (succ zero))`
/// are syntactically distinct.
#[test]
fn fib_one_and_fib_two_state_their_equations_and_are_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);
    let two = f.num(2);
    let three = f.num(3);

    for (name, arg) in [(p.fib_one, one), (p.fib_two, two)] {
        let applied = f.const_app(name, &[]);
        let inferred =
            f.k.infer(applied)
                .unwrap_or_else(|e| panic!("fib_one/fib_two must type-check: {}", f.explain(&e)));
        let fib_arg = f.const_app(p.fib, &[arg]);
        let want = f.eq(fib_arg, one);
        assert!(
            f.k.def_eq(inferred, want),
            "the theorem must state Eq (fib <arg>) 1"
        );
        // The value really is 1 -- not merely that the kernel accepted a
        // well-typed sentence about it.
        assert!(f.k.def_eq(fib_arg, one), "fib <arg> must reduce to 1");
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "the theorem must rest on zero axioms"
        );
    }

    // Negative control: `fib 3` is 2, so `Eq (fib 3) 1` is FALSE. This rules
    // out "any statement of the shape `Eq (fib k) 1` would pass" -- i.e. that
    // the two theorems above are true for a reason unrelated to their
    // argument. It does NOT rule out confusing `fib_one` with `fib_two`
    // (see the doc comment).
    let fib_three = f.const_app(p.fib, &[three]);
    assert!(
        !f.k.def_eq(fib_three, one),
        "fib 3 is 2, not 1 -- def_eq must reject it"
    );
    // Second control in the other direction: `fib 2` must not be 2 either,
    // so the pair above is not passing because every small numeral is defeq
    // to every other.
    let fib_two_val = f.const_app(p.fib, &[two]);
    assert!(
        !f.k.def_eq(fib_two_val, two),
        "fib 2 is 1, not 2 -- def_eq must not be vacuously true"
    );
}

/// `Nat.fib_lt_fib_succ` applies at a concrete `n` and at a genuinely free
/// `n`, and its `2 <= n` hypothesis is load-bearing.
///
/// # Controls
///
/// * The TRANSPOSED statement (`fib (succ n) < fib n`) is rejected as the
///   inferred type. This is not vacuous: at `n = 2` it reads `2 < 1`, which
///   is false, so the two are genuinely different propositions.
/// * The hypothesis is shown to be load-bearing NUMERICALLY rather than by
///   assertion: at `n = 1` (below the threshold) `fib 1` and `fib 2` are
///   both `1`, so the unconditional form would claim `1 < 1`. This rules
///   out "the hypothesis is decoration and the theorem is really
///   unconditional".
/// * It does NOT rule out the theorem being provable from something
///   stronger than `fib_lt_fib`, nor does it check `2` is the SHARPEST
///   threshold (it is: the statement is false at `n = 1` and vacuously
///   uninteresting below).
#[test]
fn fib_lt_fib_succ_applies_concretely_and_symbolically_and_needs_its_hypothesis() {
    let mut f = Fixture::new();
    let p = f.p;
    let one = f.num(1);
    let two = f.num(2);

    assert!(
        f.k.axiom_footprint(p.fib_lt_fib_succ).is_empty(),
        "fib_lt_fib_succ must rest on zero axioms"
    );

    // Concrete: n = 2, hypothesis `Le 2 2` by `le_refl`.
    let le_refl_2 = f.lemma(p.le_refl, &[two]);
    let applied = f.const_app(p.fib_lt_fib_succ, &[two]);
    let derived = f.apply(applied, &[le_refl_2]);
    let derived_ty = f
        .k
        .infer(derived)
        .unwrap_or_else(|e| panic!("fib_lt_fib_succ at n=2 must type-check: {}", f.explain(&e)));
    let three = f.num(3);
    let fib_two = f.const_app(p.fib, &[two]);
    let fib_three = f.const_app(p.fib, &[three]);
    let want_concrete = f.lt(fib_two, fib_three);
    assert!(
        f.k.def_eq(derived_ty, want_concrete),
        "fib_lt_fib_succ at n=2 must give Lt (fib 2) (fib 3)"
    );

    // Symbolic: a genuinely free `n`, so nothing can reduce to a numeral.
    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let applied_sym = f.const_app(p.fib_lt_fib_succ, &[n]);
    // A bare unregistered `FVar` cannot be `infer`red, so push it into an
    // explicit `LocalContext` and use `infer_in` -- the same idiom
    // `nat_prelude_tests`'s symbolic checks use.
    let anon = f.anon_name();
    let nat = f.nat_ty();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let inferred = f.k.infer_in(applied_sym, &mut ctx).unwrap_or_else(|e| {
        panic!(
            "fib_lt_fib_succ must type-check at a free n: {}",
            f.explain(&e)
        )
    });
    let sn = f.succ(n);
    let fib_n = f.const_app(p.fib, &[n]);
    let fib_sn = f.const_app(p.fib, &[sn]);
    let hyp_ty = f.le(two, n);
    let concl_ty = f.lt(fib_n, fib_sn);
    let want_sym = f.arrow(hyp_ty, concl_ty);
    assert!(
        f.k.def_eq(inferred, want_sym),
        "fib_lt_fib_succ must state ∀ n, Le 2 n → Lt (fib n) (fib (succ n))"
    );

    // Negative control: the transposed conclusion is a DIFFERENT proposition
    // (false at n = 2, where it reads `2 < 1`).
    let transposed = f.lt(fib_sn, fib_n);
    let want_transposed = f.arrow(hyp_ty, transposed);
    assert!(
        !f.k.def_eq(inferred, want_transposed),
        "negative control: fib_lt_fib_succ must not state the transposed inequality"
    );

    // The hypothesis is load-bearing: below the threshold the conclusion is
    // false, because fib 1 = fib 2 = 1.
    let fib_one_val = f.const_app(p.fib, &[one]);
    assert!(
        f.k.def_eq(fib_one_val, one) && f.k.def_eq(fib_two, one),
        "fib 1 and fib 2 are both 1, so `Lt (fib 1) (fib 2)` is false -- \
         the `2 <= n` hypothesis cannot be dropped"
    );
}
