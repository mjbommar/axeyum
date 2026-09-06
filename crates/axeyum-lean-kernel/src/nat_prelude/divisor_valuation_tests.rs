//! Tests for `nat_prelude::divisor_valuation`.
//!
//! `Nat.Multiset.count_le_of_dvd_prod` is a THEOREM, so the trusted gate has
//! already checked that its proof proves its statement. What the gate cannot
//! check is that the statement is the one intended, and three specific ways of
//! getting it wrong all type-check:
//!
//! - the conclusion transposed (`Le (count m q) (count (factorization d) q)`),
//!   which is the FALSE direction and is what a swapped `lt_or_ge` branch
//!   pairing would give;
//! - the `Lt 0 d` hypothesis dropped, which makes it false at `d = 0`
//!   (`factorization 0` is `Multiset.zero`, so both counts are `0` and the
//!   statement happens to survive — but `prod_factorization` does not, and the
//!   proof would not close);
//! - `factorization d` replaced by `factorization (prod m)`, which is a
//!   different and much weaker statement.
//!
//! The declared type is therefore pinned character for character, the way
//! `subset_sum_tests.rs` pins its own five. A pin is the check that sees a
//! transposed conclusion; the axiom-footprint check below cannot, and neither
//! can the prelude build.
//!
//! The second test is about the objects the statement quantifies over rather
//! than the statement: `count (factorization n) q` has to be a non-trivial
//! function of both arguments, or the inequality would be vacuously true
//! everywhere. `12 = 2² · 3` gives counts `2`, `1`, `0` at `2`, `3`, `5`, and
//! each is paired with the wrong value it rules out. Magnitudes stay tiny —
//! this prelude's numerals are unary `Nat.succ` towers.

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::{Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

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

    /// `Nat.Multiset.count (Nat.factorization n) q`.
    fn factor_count(&mut self, n: u32, q: u32) -> ExprId {
        let n_lit = self.num(n);
        let fact_name = self.p.factorization;
        let fact = self.const_app(fact_name, &[n_lit]);
        let q_lit = self.num(q);
        let count_name = self.p.multiset_count;
        self.const_app(count_name, &[fact, q_lit])
    }
}

/// `Nat.Multiset.count_le_of_dvd_prod` is present, derived rather than
/// asserted, and rests on ZERO axioms.
///
/// `Kernel::axiom_footprint` returns an empty set for a name that does not
/// exist, so `Environment::contains` is asserted FIRST — otherwise a renamed or
/// never-declared theorem would pass this test silently.
#[test]
fn the_divisor_valuation_bound_is_present_and_axiom_free() {
    let f = Fixture::new();
    let name = f.p.multiset_count_le_of_dvd_prod;
    let shown = f.k.display_name(name).to_string();
    assert!(
        f.k.environment().contains(name),
        "{shown} must be declared -- an absent name has an EMPTY axiom \
         footprint, so the check below would pass without it"
    );
    let footprint = f.k.axiom_footprint(name);
    assert!(
        footprint.is_empty(),
        "{shown} must rest on zero axioms, found {:?}",
        footprint
            .iter()
            .map(|n| f.k.display_name(*n).to_string())
            .collect::<Vec<_>>()
    );
}

/// The declared type, pinned character for character.
///
/// Three distinctions no axiom-footprint check and no prelude build can see:
/// the conclusion's DIRECTION (`count (factorization d) q ≤ count m q`, not the
/// reverse); the `Lt 0 d` hypothesis being present; and the divisor `x1` being
/// the thing factorized, not `prod x0`.
#[test]
fn the_divisor_valuation_bound_states_the_intended_type() {
    let f = Fixture::new();
    let name = f.p.multiset_count_le_of_dvd_prod;
    let ty = match f.k.environment().get(name).expect("must be declared") {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
        other => panic!("{other:?} is neither a theorem nor a definition"),
    };
    assert_eq!(f.k.render_lean(ty), EXPECTED_COUNT_LE_OF_DVD_PROD);
}

/// The counts the bound compares are a real function of both arguments.
///
/// A statement about a function that is constantly `0` would be vacuously true,
/// and neither the pin above nor the kernel would notice. `12 = 2² · 3`
/// separates all three cases in one number.
#[test]
fn the_factorization_counts_discriminate_at_twelve() {
    let mut f = Fixture::new();

    let at_two = f.factor_count(12, 2);
    let two = f.num(2);
    assert!(
        f.k.def_eq(at_two, two),
        "count (factorization 12) 2 must be 2, got {}",
        f.k.render_lean(at_two)
    );
    let one = f.num(1);
    assert!(
        !f.k.def_eq(at_two, one),
        "negative control: it must NOT be 1 -- that is what a count blind to \
         MULTIPLICITY would give, and the bound would then be about the \
         distinct primes rather than the valuation"
    );

    let at_three = f.factor_count(12, 3);
    let one_again = f.num(1);
    assert!(
        f.k.def_eq(at_three, one_again),
        "count (factorization 12) 3 must be 1, got {}",
        f.k.render_lean(at_three)
    );
    assert!(
        !f.k.def_eq(at_three, at_two),
        "negative control: the counts at 2 and at 3 must DISAGREE, or a count \
         reading a constant would pass both checks"
    );

    let at_five = f.factor_count(12, 5);
    let zero = f.zero();
    assert!(
        f.k.def_eq(at_five, zero),
        "count (factorization 12) 5 must be 0 -- 5 does not divide 12 -- got {}",
        f.k.render_lean(at_five)
    );
    assert!(
        !f.k.def_eq(at_five, one_again),
        "negative control: a non-factor must count 0, not 1"
    );
}

const EXPECTED_COUNT_LE_OF_DVD_PROD: &str = "((x0 : AxNat.Multiset) -> ((x1 : AxNat) -> ((x2 : AxNat) -> ((x3 : ((x3 : AxNat) -> ((x4 : AxNat.lt AxNat.zero (AxNat.Multiset.count x0 x3)) -> And (AxNat.le (AxNat.succ (AxNat.succ AxNat.zero)) x3) (((x5 : AxNat) -> ((x6 : AxNat.dvd x5 x3) -> Or (Eq.{1} AxNat x5 (AxNat.succ AxNat.zero)) (Eq.{1} AxNat x5 x3))))))) -> ((x4 : AxNat.lt AxNat.zero x1) -> ((x5 : AxNat.dvd x1 (AxNat.Multiset.prod x0)) -> AxNat.le (AxNat.Multiset.count (AxNat.factorization x1) x2) (AxNat.Multiset.count x0 x2)))))))";
