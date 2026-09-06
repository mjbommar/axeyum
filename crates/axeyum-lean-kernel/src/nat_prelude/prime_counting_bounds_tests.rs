//! Concrete-instance tests for `nat_prelude::prime_counting_bounds`.
//!
//! Every theorem here is a statement about `Nat.primeCounting'`, whose body is
//! two delta steps away from `Nat.countRange Nat.isPrime`. The kernel accepts
//! the monotonicity proofs through that defeq without ever evaluating
//! `isPrime`, so a `Nat.isPrime` that computed the WRONG predicate would leave
//! every proof in the module still admitted and still axiom-free. The
//! evaluation rows below are therefore not decoration: they are the only check
//! that the function the theorems are about is the prime-counting function.
//!
//! Magnitudes are kept small: every `Nat` numeral here is unary and `isPrime`
//! is itself a `countRange` over the divisors, so evaluating `primeCounting' n`
//! costs on the order of `n^2` unary `mod` steps. The largest argument
//! evaluated is `12`.

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

    fn counting_prime_at(&mut self, n: u32) -> ExprId {
        let p = self.p;
        let arg = self.num(n);
        self.const_app(p.prime_counting_prime, &[arg])
    }

    fn counting_at(&mut self, n: u32) -> ExprId {
        let p = self.p;
        let arg = self.num(n);
        self.const_app(p.prime_counting, &[arg])
    }
}

/// `Nat.primeCounting' n` counts the primes STRICTLY BELOW `n`.
///
/// Values hand-computed from the primes `2, 3, 5, 7, 11`:
///
/// | `n` | 0 | 1 | 2 | 3 | 4 | 5 | 8 | 12 |
/// | `π'(n)` | 0 | 0 | 0 | 1 | 2 | 2 | 4 | 5 |
///
/// Three rows discriminate, and each names the wrong definition it kills:
///
/// * `π'(2) = 0` and `π'(3) = 1`: the range is `[0, n)`, EXCLUSIVE at the top.
///   A `primeCounting'` that counted `p ≤ n` would give `1` and `2` here. This
///   is the off-by-one that separates `primeCounting'` from `primeCounting`,
///   and it is checked at the smallest `n` where the two differ.
/// * `π'(4) = 2` and `π'(5) = 2`: `4` is composite, so the count does NOT
///   move across it. A predicate that admitted every `n ≥ 2` would give `2`
///   and `3`.
/// * `π'(1) = 0`: `1` is not counted. `Nat.primorial`'s predicate
///   (`beq (minFac i) i`) DOES admit `1`, harmlessly, because a product is
///   unchanged by a factor of `1` — a COUNT is not. This row is what shows
///   `Nat.isPrime` is not that predicate.
#[test]
fn prime_counting_prime_evaluates_to_the_count_of_primes_below() {
    let mut f = Fixture::new();
    for (n, expected) in [
        (0u32, 0u32),
        (1, 0),
        (2, 0),
        (3, 1),
        (4, 2),
        (5, 2),
        (8, 4),
        (12, 5),
    ] {
        let lhs = f.counting_prime_at(n);
        let rhs = f.num(expected);
        assert!(
            f.k.def_eq(lhs, rhs),
            "primeCounting' {n} must be {expected}"
        );
    }
}

/// `Nat.primeCounting' 4` is NOT `1` and NOT `3` — the negative control for
/// the row above.
///
/// Without this the evaluation test could pass against a `def_eq` that
/// answered `true` for everything. `4` is chosen because both neighbours are
/// reachable by a plausible wrong definition: `1` is the count if `3` were
/// missed, `3` is the count if `1` were admitted as prime.
#[test]
fn prime_counting_prime_separates_its_neighbours() {
    let mut f = Fixture::new();
    for wrong in [1u32, 3] {
        let lhs = f.counting_prime_at(4);
        let rhs = f.num(wrong);
        assert!(
            !f.k.def_eq(lhs, rhs),
            "primeCounting' 4 must not be {wrong}"
        );
    }
}

/// `Nat.primeCounting n` counts the primes up to and INCLUDING `n`.
///
/// `π(2) = 1` against `π'(2) = 0` is the discriminating pair: it is the
/// smallest argument at which the inclusive and exclusive conventions differ,
/// and a `primeCounting` defined as `primeCounting'` outright would give `0`.
#[test]
fn prime_counting_evaluates_to_the_inclusive_count() {
    let mut f = Fixture::new();
    for (n, expected) in [(0u32, 0u32), (1, 0), (2, 1), (3, 2), (4, 2), (7, 4)] {
        let lhs = f.counting_at(n);
        let rhs = f.num(expected);
        assert!(f.k.def_eq(lhs, rhs), "primeCounting {n} must be {expected}");
    }
}

/// Every name this module declares is admitted with the declaration KIND the
/// module doc claims, and every theorem rests on an EMPTY
/// `Kernel::axiom_footprint`.
///
/// `Environment::contains` is asserted FIRST for each name: `axiom_footprint`
/// returns an empty set for a name that is not in the environment at all, so
/// the footprint assertion alone would pass for a declaration that was never
/// made.
#[test]
fn the_prime_counting_shelf_is_admitted_and_axiom_free() {
    let f = Fixture::new();
    let p = f.p;

    let theorems = [
        p.prime_counting_prime_mono,
        p.prime_counting_mono,
        p.is_prime_eq_true_of_prime,
        p.prime_counting_prime_unbounded,
    ];

    for name in theorems {
        let shown = f.k.display_name(name).to_string();
        assert!(
            f.k.environment().contains(name),
            "{shown} must be in the environment"
        );
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

/// `Nat.isPrime` is `true` at every prime below `12` and `false` at every
/// composite and at `0` and `1`.
///
/// `Nat.isPrime_eq_true_of_prime` proves the FORWARD direction symbolically,
/// and a symbolic proof cannot notice that the predicate it is about computes
/// something else at a concrete argument — `prime_condition` appears on both
/// sides of the bridge, so a wrong `isPrime` would simply make the theorem
/// unusable rather than false. These rows are what pin the predicate.
///
/// `isPrime 1 = false` is the discriminating row: `1` has exactly one divisor
/// in `[1,1]`, not two, and it is the value `Nat.primorial`'s own predicate
/// (`beq (minFac i) i`) answers `true` at.
#[test]
fn is_prime_evaluates_to_primality() {
    let mut f = Fixture::new();
    let p = f.p;
    for (n, expected) in [
        (0u32, false),
        (1, false),
        (2, true),
        (3, true),
        (4, false),
        (5, true),
        (6, false),
        (7, true),
        (9, false),
        (11, true),
    ] {
        let arg = f.num(n);
        let lhs = f.const_app(p.is_prime, &[arg]);
        let rhs = if expected {
            f.bool_true()
        } else {
            f.bool_false()
        };
        assert!(f.k.def_eq(lhs, rhs), "isPrime {n} must be {expected}");
        let wrong = if expected {
            f.bool_false()
        } else {
            f.bool_true()
        };
        assert!(
            !f.k.def_eq(lhs, wrong),
            "isPrime {n} must not be {}",
            !expected
        );
    }
}
