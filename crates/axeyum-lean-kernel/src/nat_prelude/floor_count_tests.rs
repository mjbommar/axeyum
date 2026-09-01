//! Tests for [`nat_prelude::floor_count`](super::floor_count).
//!
//! A separate file rather than an addition to the dense `nat_prelude_tests.rs`,
//! per this repository's standing merge-hazard note: two lanes editing that one
//! file at once produce a conflict git cuts mid-item.
//!
//! Three kinds of check, because they fail on disjoint defect classes:
//!
//! 1. **Evaluation at concrete arguments.** The kernel admits a theorem whose
//!    statement is *true but not the one intended*, so numerals are what pin the
//!    counting convention (exclusive bound, `succ` shift) and the saturation
//!    point.
//! 2. **The declared types, rendered.** This is the probe for the third
//!    mutation outcome — *admitted, true, and not your theorem*. Transposing
//!    `Min.min n c` to `Min.min c n` is such a mutant: `Min.min` is
//!    commutative in value, every evaluation test passes, and only the stated
//!    type distinguishes them.
//! 3. **Negative controls.** Each positive `def_eq` is paired with a value the
//!    statement must NOT equal, chosen so a plausible off-by-one or dropped
//!    `min` fails it.

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
}

/// The counting core computes the saturating count at concrete arguments, on
/// BOTH sides of the saturation point.
///
/// `countRange (fun y => ble (succ y) 3) n` counts `y ∈ {0,1,2}`, so it is `n`
/// while `n ≤ 3` and pinned at `3` thereafter. Checking `n = 2` (below), `n = 3`
/// (exactly at) and `n = 5` (above) is what discriminates: a statement with the
/// `min` dropped would pass the first two and fail the third, and a statement
/// off by one in the `succ` shift fails all three against these values.
#[test]
fn the_counting_core_saturates_at_concrete_arguments() {
    let mut f = Fixture::new();
    let p = f.p;

    let three = f.num(3);
    let pred = {
        let nat = f.nat_ty();
        let y_fv = f.fresh_fvar();
        let y = f.k.fvar(y_fv);
        let sy = f.succ(y);
        let body = f.ble(sy, three);
        f.lam_fv(y_fv, nat, body)
    };

    for (n, expected) in [(0u32, 0u32), (2, 2), (3, 3), (5, 3)] {
        let n_term = f.num(n);
        let count = f.const_app(p.count_range, &[pred, n_term]);
        let expected_term = f.num(expected);
        assert!(
            f.k.def_eq(count, expected_term),
            "countRange (fun y => ble (succ y) 3) {n} must be {expected}"
        );
    }

    // Negative control: at `n = 5` the count is NOT `5`, i.e. the count really
    // does saturate. Without this the `min` could be anything at all above `c`.
    let five = f.num(5);
    let count_five = f.const_app(p.count_range, &[pred, five]);
    assert!(
        !f.k.def_eq(count_five, five),
        "negative control: the count must saturate, so it is not 5 at n = 5"
    );

    // Negative control on the `succ` shift: if the predicate were `ble y 3`
    // (i.e. `y <= 3`, four indices) the count at `n = 5` would be 4, not 3.
    let four = f.num(4);
    assert!(
        !f.k.def_eq(count_five, four),
        "negative control: the predicate is `y < 3`, not `y <= 3`"
    );
}

/// The executable corollary computes the floor count at concrete arguments.
///
/// `countRange (fun j => ble (mul 3 (succ j)) 11) n` counts
/// `j ∈ {0,1,2}` (since `3·1, 3·2, 3·3 ≤ 11 < 3·4`), and `⌊11/3⌋ = 3`. So it is
/// `min n 3`. The divisor `3` and bound `11` are chosen NOT to divide, so a
/// statement that silently used `⌈B/a⌉` or `(B+1)/a` would differ; `11 = 3·3+2`
/// keeps every formed numeral small, per this prelude's unary-numeral cost.
#[test]
fn the_floor_corollary_computes_at_concrete_arguments() {
    let mut f = Fixture::new();
    let p = f.p;

    let two = f.num(2);
    let eleven = f.num(11);
    let three = f.num(3);

    // `divisor = succ 2 = 3`.
    let pred = {
        let nat = f.nat_ty();
        let divisor = f.succ(two);
        let j_fv = f.fresh_fvar();
        let j = f.k.fvar(j_fv);
        let sj = f.succ(j);
        let prod = f.mul(divisor, sj);
        let body = f.ble(prod, eleven);
        f.lam_fv(j_fv, nat, body)
    };

    for (n, expected) in [(0u32, 0u32), (2, 2), (3, 3), (6, 3)] {
        let n_term = f.num(n);
        let count = f.const_app(p.count_range, &[pred, n_term]);
        let expected_term = f.num(expected);
        assert!(
            f.k.def_eq(count, expected_term),
            "countRange (fun j => ble (mul 3 (succ j)) 11) {n} must be {expected}"
        );
    }

    // The right-hand side the theorem names: `Min.min 6 (div 11 3)`.
    let six = f.num(6);
    let divisor = f.succ(two);
    let quotient = f.div(eleven, divisor);
    let rhs = f.const_app(p.min_min, &[six, quotient]);
    assert!(
        f.k.def_eq(rhs, three),
        "Min.min 6 (div 11 3) must be 3 -- the floor, not the ceiling"
    );
    let four = f.num(4);
    assert!(
        !f.k.def_eq(rhs, four),
        "negative control: 11/3 rounds DOWN, so this is 3 and not 4"
    );
}

/// Every declaration in the family rests on zero axioms.
#[test]
fn the_family_is_axiom_free() {
    let f = Fixture::new();
    let p = f.p;
    for name in [
        p.count_range_succ_le_eq_min,
        p.count_range_mul_succ_le_eq_min,
        p.count_range_mul_succ_le_eq_floor,
    ] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The family states the types it is supposed to state, pinned character for
/// character against `render_lean`.
///
/// This is the probe for *admitted, true, and not your theorem*, and the family
/// has two such mutants that no evaluation test can see:
///
/// * `Min.min c n` in place of `Min.min n c`. `Min.min` is commutative in
///   VALUE, so every numeral check passes; only the argument order in the
///   stated type distinguishes them, and `Min.min n c` is the order that reads
///   "the count is bounded by the range" rather than by the threshold.
/// * `countRange_mul_succ_le_eq_min` stated with `div bound a` in place of the
///   bound variable `q`. That is true and provable, but it re-introduces the
///   stuck `Nat.div` this whole family exists to route around, and it would
///   force a positivity hypothesis on every consumer. What to look for below is
///   that the middle row's right-hand side is `Min.min x4 x2` — a BOUND
///   VARIABLE — and mentions `AxNat.div` nowhere.
#[test]
fn the_family_states_the_intended_types() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let rendered = |k: &Kernel, name: crate::NameId| -> String {
        match k
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{} must be declared", k.display_name(name)))
        {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => {
                k.render_lean(*ty)
            }
            other => panic!("{other:?} is not a theorem or definition"),
        }
    };

    for (name, expected) in [
        (
            p.count_range_succ_le_eq_min,
            "((x0 : AxNat) -> ((x1 : AxNat) -> Eq.{1} AxNat (AxNat.countRange (fun (x2 : AxNat) \
             => AxNat.ble (AxNat.succ x2) x0) x1) (Min.min x1 x0)))",
        ),
        (
            p.count_range_mul_succ_le_eq_min,
            "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> ((x3 : AxNat) -> ((x4 : AxNat) -> \
             ((x5 : AxNat.divMod x0 x1 x2 x3) -> Eq.{1} AxNat (AxNat.countRange (fun (x6 : AxNat) \
             => AxNat.ble (AxNat.mul x0 (AxNat.succ x6)) x1) x4) (Min.min x4 x2)))))))",
        ),
        (
            p.count_range_mul_succ_le_eq_floor,
            "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> Eq.{1} AxNat (AxNat.countRange \
             (fun (x3 : AxNat) => AxNat.ble (AxNat.mul (AxNat.succ x0) (AxNat.succ x3)) x1) x2) \
             (Min.min x2 (AxNat.div x1 (AxNat.succ x0))))))",
        ),
    ] {
        assert_eq!(
            rendered(&k, name),
            expected,
            "{} states a different type than intended",
            k.display_name(name)
        );
    }

    // The relational bridge must NOT mention `AxNat.div` anywhere: that is the
    // whole point of stating it against `divMod` with an emitted quotient.
    assert!(
        !rendered(&k, p.count_range_mul_succ_le_eq_min).contains("AxNat.div "),
        "the relational bridge must not name `AxNat.div`"
    );
    // Positive control for that `contains` query: the executable corollary
    // DOES name it, so an empty match above is a real absence and not a
    // mistyped pattern.
    assert!(
        rendered(&k, p.count_range_mul_succ_le_eq_floor).contains("AxNat.div "),
        "positive control: the executable corollary does name `AxNat.div`"
    );
}
