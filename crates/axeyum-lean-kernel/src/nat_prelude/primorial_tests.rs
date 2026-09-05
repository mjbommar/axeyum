//! Concrete-instance tests for `nat_prelude::primorial`.
//!
//! The kernel cannot tell a `Definition` is wrong: `Nat.primorial` has type
//! `Nat → Nat` whatever it computes, and every wrong variant this file rules
//! out (product over ALL indices; product over primes `< n` instead of `≤ n`;
//! a `succ` factor instead of the index) also has type `Nat → Nat`. So every
//! positive check below is a concrete-numeral evaluation against a value
//! computed by hand, and each carries a negative control naming the specific
//! wrong formula it separates from.
//!
//! Magnitudes are kept small on purpose: every `Nat` numeral in this kernel is
//! unary, so cost is superlinear in the largest magnitude FORMED. The largest
//! value asserted here is `primorial 7 = 210`.

use crate::env::Declaration;
use crate::{ExprId, Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

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

    fn primorial_at(&mut self, n: u32) -> ExprId {
        let p = self.p;
        let arg = self.num(n);
        self.const_app(p.primorial, &[arg])
    }
}

/// `Nat.primorial` computes `∏ {p prime, p ≤ n}` at every `n ≤ 7`.
///
/// The values are `1, 1, 2, 6, 6, 30, 30, 210` — hand-computed as the running
/// product of `2, 3, 5, 7`. Three rows are the ones that discriminate:
///
/// * `primorial 1 = 1` pins the `minFac 1 = 1` row the module doc describes:
///   `1` passes the `beq (minFac i) i` predicate and contributes the factor
///   `1`, so the product is unchanged. A predicate that instead admitted `1`
///   as a genuine prime factor would still give `1` here — which is why the
///   discriminating check is `primorial 0 = 1` paired with `primorial 2 = 2`:
///   `minFac 0 = 2 ≠ 0` keeps `0` out, and a definition that let `0` through
///   would make every later value `0`.
/// * `primorial 4 = 6` is the first COMPOSITE step: `4` must contribute
///   nothing. A product over the whole range would give `24` here.
/// * `primorial 7 = 210` is the first value where the range bound matters at
///   a prime: `primorial` is `≤ n`, not `< n`, so `7` is included. A `< n`
///   bound would give `30`.
#[test]
fn primorial_evaluates_on_small_numerals() {
    let mut f = Fixture::new();
    for (n, expected) in [
        (0_u32, 1_u32),
        (1, 1),
        (2, 2),
        (3, 6),
        (4, 6),
        (5, 30),
        (6, 30),
        (7, 210),
    ] {
        let lhs = f.primorial_at(n);
        let rhs = f.num(expected);
        assert!(
            f.k.def_eq(lhs, rhs),
            "primorial {n} must reduce to {expected}"
        );
    }
}

/// Negative controls: each names one wrong formula of the same type.
///
/// * `primorial 4 ≠ 24` rules out "product over the whole range `[0,n]`"
///   (`1·2·3·4`, with the `0` row contributing `1`).
/// * `primorial 7 ≠ 30` rules out a `< n` range bound (`2·3·5`).
/// * `primorial 3 ≠ 2` rules out a predicate that admits only `2` (e.g. a
///   `beq (minFac i) 2` typo).
/// * `primorial 2 ≠ 1` rules out a predicate that is never true — the shape a
///   `beq i (minFac i)` argument-order slip does NOT produce (`beq` is
///   symmetric on equal arguments) but a `beq (minFac i) (succ i)` slip does.
#[test]
fn primorial_separates_the_wrong_formulas() {
    let mut f = Fixture::new();
    for (n, wrong, why) in [
        (4_u32, 24_u32, "product over the whole range [0,n]"),
        (7, 30, "a `< n` range bound instead of `<= n`"),
        (3, 2, "a predicate admitting only 2"),
        (2, 1, "a predicate that is never true"),
    ] {
        let lhs = f.primorial_at(n);
        let rhs = f.num(wrong);
        assert!(
            !f.k.def_eq(lhs, rhs),
            "negative control: primorial {n} must NOT be {wrong} ({why})"
        );
    }
}

/// The two defining equations INSTANTIATE, and their statements are what the
/// module doc says.
///
/// `primorial_zero` is closed, so its own type is the check. `primorial_succ`
/// is checked at a FREE variable (not a numeral): a `succ`-equation that only
/// held at literals would reduce on both sides and pass a numeral test while
/// being useless to every induction downstream.
#[test]
fn the_defining_equations_instantiate() {
    let mut f = Fixture::new();
    let p = f.p;

    let zero_ty =
        f.k.environment()
            .get(p.primorial_zero)
            .expect("Nat.primorial_zero must be admitted")
            .ty();
    let expected_zero = {
        let lhs = f.primorial_at(0);
        let one = f.num(1);
        f.eq(lhs, one)
    };
    assert!(
        f.k.def_eq(zero_ty, expected_zero),
        "primorial_zero must state `primorial 0 = 1`, got {}",
        f.k.render_lean(zero_ty)
    );

    let n_fv = f.fresh_fvar();
    let n = f.k.fvar(n_fv);
    let applied = f.const_app(p.primorial_succ, &[n]);
    let ty = f.k.infer(applied).expect("primorial_succ must apply");
    let expected = {
        let sn = f.succ(n);
        let lhs = f.const_app(p.primorial, &[sn]);
        let prior = f.const_app(p.primorial, &[n]);
        let mf = f.const_app(p.min_fac, &[sn]);
        let cond = f.beq(mf, sn);
        let one = f.num(1);
        let sel = f.bool_select_nat(cond, sn, one);
        let rhs = f.mul(prior, sel);
        f.eq(lhs, rhs)
    };
    assert!(
        f.k.def_eq(ty, expected),
        "primorial_succ must state the selector equation at a free `n`, got {}",
        f.k.render_lean(ty)
    );

    // Negative control: the equation must NOT be the unconditional
    // `primorial (succ n) = primorial n * succ n` (true only at primes).
    let wrong = {
        let sn = f.succ(n);
        let lhs = f.const_app(p.primorial, &[sn]);
        let prior = f.const_app(p.primorial, &[n]);
        let rhs = f.mul(prior, sn);
        f.eq(lhs, rhs)
    };
    assert!(
        !f.k.def_eq(ty, wrong),
        "negative control: primorial_succ must NOT drop the selector"
    );
}

/// The `minFac` primality bridge is declared with the STATEMENT the module
/// doc claims, in both directions.
///
/// The declared types are compared against hand-rebuilt statements rather
/// than inferred from an application: both theorems take a `Prop`-typed
/// hypothesis, so an application would need a typed free variable the kernel
/// has no public way to supply. `pi_fv` abstracts the bound variable to a de
/// Bruijn index, so the fresh-fvar id used here is irrelevant to the
/// comparison.
///
/// Each carries a negative control naming a specific WEAKER statement of the
/// same shape: the forward direction must not be the trivial
/// `minFac n = minFac n`, and the reverse must not conclude primality of
/// `minFac n` (which is `min_fac_prime`, already in the environment — a
/// bridge that concluded that would be a duplicate, not a bridge).
#[test]
fn the_min_fac_prime_bridge_states_the_bridge() {
    let mut f = Fixture::new();
    let p = f.p;

    // Forward: ∀ n, prime_condition n → Eq (minFac n) n
    let forward_ty =
        f.k.environment()
            .get(p.min_fac_eq_self_of_prime)
            .expect("Nat.min_fac_eq_self_of_prime must be admitted")
            .ty();
    let expected_forward = {
        let nat = f.nat_ty();
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let hyp = prime_condition_at(&mut f, n);
        let mf = f.const_app(p.min_fac, &[n]);
        let concl = f.eq(mf, n);
        let inner = f.arrow(hyp, concl);
        f.pi_fv(n_fv, nat, inner)
    };
    assert!(
        f.k.def_eq(forward_ty, expected_forward),
        "min_fac_eq_self_of_prime must state `forall n, prime n -> minFac n = n`, got {}",
        f.k.render_lean(forward_ty)
    );
    let wrong_forward = {
        let nat = f.nat_ty();
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let hyp = prime_condition_at(&mut f, n);
        let mf = f.const_app(p.min_fac, &[n]);
        let concl = f.eq(mf, mf);
        let inner = f.arrow(hyp, concl);
        f.pi_fv(n_fv, nat, inner)
    };
    assert!(
        !f.k.def_eq(forward_ty, wrong_forward),
        "negative control: it must not be the trivial `minFac n = minFac n`"
    );

    // Reverse: ∀ n, Le 2 n → Eq (minFac n) n → prime_condition n
    let reverse_ty =
        f.k.environment()
            .get(p.prime_of_min_fac_eq_self)
            .expect("Nat.prime_of_min_fac_eq_self must be admitted")
            .ty();
    let expected_reverse = {
        let nat = f.nat_ty();
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let two = f.num(2);
        let h2 = f.le(two, n);
        let mf = f.const_app(p.min_fac, &[n]);
        let he = f.eq(mf, n);
        let concl = prime_condition_at(&mut f, n);
        let inner = f.arrow(he, concl);
        let mid = f.arrow(h2, inner);
        f.pi_fv(n_fv, nat, mid)
    };
    assert!(
        f.k.def_eq(reverse_ty, expected_reverse),
        "prime_of_min_fac_eq_self must state `forall n, 2 <= n -> minFac n = n -> prime n`, got {}",
        f.k.render_lean(reverse_ty)
    );
    let wrong_reverse = {
        let nat = f.nat_ty();
        let n_fv = f.fresh_fvar();
        let n = f.k.fvar(n_fv);
        let two = f.num(2);
        let h2 = f.le(two, n);
        let mf = f.const_app(p.min_fac, &[n]);
        let he = f.eq(mf, n);
        let concl = prime_condition_at(&mut f, mf);
        let inner = f.arrow(he, concl);
        let mid = f.arrow(h2, inner);
        f.pi_fv(n_fv, nat, mid)
    };
    assert!(
        !f.k.def_eq(reverse_ty, wrong_reverse),
        "negative control: it must conclude primality of `n`, not of `minFac n` \
         (the latter is `min_fac_prime`, already declared)"
    );
}

/// `prime_condition x`, rebuilt here so the tests do not depend on
/// `primes::prime_condition` being reachable from a `#[cfg(test)]` module.
fn prime_condition_at(f: &mut Fixture, x: ExprId) -> ExprId {
    let nat = f.nat_ty();
    let two = f.num(2);
    let one = f.num(1);
    let lower = f.le(two, x);
    let c_fv = f.fresh_fvar();
    let c = f.k.fvar(c_fv);
    let hypothesis = f.dvd(c, x);
    let trivial = f.eq(c, one);
    let whole = f.eq(c, x);
    let or_name = f.p.logic.or;
    let disjunction = f.const_app(or_name, &[trivial, whole]);
    let body = f.arrow(hypothesis, disjunction);
    let divisors = f.pi_fv(c_fv, nat, body);
    let and_name = f.p.logic.and;
    f.const_app(and_name, &[lower, divisors])
}

/// Every name this module declares is admitted, with the declaration KIND the
/// module doc claims, and every theorem rests on an EMPTY
/// `Kernel::axiom_footprint`.
///
/// `Environment::contains` is asserted FIRST for each name: `axiom_footprint`
/// returns an empty set for a name that is not in the environment at all, so
/// the footprint assertion alone would pass for a declaration that was never
/// made.
#[test]
fn the_primorial_shelf_is_admitted_and_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;

    let definitions = [p.primorial];
    let theorems = [
        p.primorial_zero,
        p.primorial_succ,
        p.min_fac_eq_self_of_prime,
        p.prime_of_min_fac_eq_self,
    ];

    for name in definitions {
        let shown = f.k.display_name(name).to_string();
        let decl =
            f.k.environment()
                .get(name)
                .unwrap_or_else(|| panic!("{shown} must be admitted"))
                .clone();
        assert!(
            matches!(decl, Declaration::Definition { .. }),
            "{shown} must be a Definition"
        );
    }

    for name in theorems {
        let shown = f.k.display_name(name).to_string();
        let decl =
            f.k.environment()
                .get(name)
                .unwrap_or_else(|| panic!("{shown} must be admitted"))
                .clone();
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{shown} must be a Theorem, not {decl:?}"
        );
        let footprint = f.k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{shown} must be axiom-free, found {:?}",
            footprint
                .iter()
                .map(|n| f.k.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}
