//! Concrete-instance tests for `nat_prelude::unpair`'s three definitions.
//!
//! A separate file rather than an addition to the dense
//! `nat_prelude_tests.rs`, for the merge hazard that file has repeatedly
//! produced: two lanes adding items to it at once give git a conflict it
//! cuts mid-item. `Fixture` is the same small local copy `avg_pair_tests.rs`
//! uses.
//!
//! The kernel cannot tell a `Definition` is wrong — `Nat → Nat` is
//! `Nat → Nat` whatever the body computes — so every check is a `def_eq` at
//! concrete numerals against an independently hand-computed value, with a
//! negative control naming the specific wrong definition it rules out.
//!
//! The hand-computed table, from `pair a b := if a < b then b * b + a else
//! a * a + a + b` and `unpair n := let s := sqrt n; let r := n - s * s in
//! if r < s then (r, s) else (s, r - s)`:
//!
//! | n | s=sqrt n | r=n-s² | r<s | (left, right) | pair⁻¹ |
//! |---|----------|--------|-----|---------------|--------|
//! | 0 | 0        | 0      | no  | (0, 0)        | (0,0)  |
//! | 1 | 1        | 0      | yes | (0, 1)        | (0,1)  |
//! | 2 | 1        | 1      | no  | (1, 0)        | (1,0)  |
//! | 3 | 1        | 2      | no  | (1, 1)        | (1,1)  |
//! | 4 | 2        | 0      | yes | (0, 2)        | (0,2)  |
//! | 5 | 2        | 1      | yes | (1, 2)        | (1,2)  |
//! | 6 | 2        | 2      | no  | (2, 0)        | (2,0)  |
//! | 7 | 2        | 3      | no  | (2, 1)        | (2,1)  |
//! | 8 | 2        | 4      | no  | (2, 2)        | (2,2)  |
//!
//! The last column is `Nat.pair`'s own already-tested table read backwards,
//! which is what makes the round-trip test in this file a check of THIS
//! construction rather than a restatement of it.

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

/// `Nat.unpairLeft` and `Nat.unpairRight` compute the right VALUES at every
/// argument in `[0, 8]` — the full first block of the pairing, so each
/// branch of the `r < s` test is exercised on both sides.
///
/// The negative controls name three wrong definitions the type cannot see:
/// a TRANSPOSED branch condition (`s < r` rather than `r < s`, which swaps
/// the two arms), a projection that FORGETS the `- s` correction in the
/// false arm of `unpairRight`, and the two projections SWAPPED.
///
/// `n = 5` is the discriminator for the transposition: it takes the true
/// arm, giving `(1, 2)`, where a transposed test gives `(2, 1)` — different
/// on BOTH components. `n = 6` is the discriminator for the missing
/// correction: `r = 2`, `s = 2`, so `unpairRight 6 = r - s = 0` while a
/// definition returning `r` would give `2`. `n = 3` is where left and right
/// coincide (`(1, 1)`) and so discriminates nothing on its own; it is
/// included because a definition special-casing the diagonal would still
/// have to get it right.
#[test]
fn unpair_projections_evaluate_correctly() {
    let mut f = Fixture::new();
    let p = f.p;

    let num: Vec<_> = (0u32..=8).map(|i| f.num(i)).collect();

    // (n, expected left, expected right)
    let table = [
        (0usize, 0usize, 0usize),
        (1, 0, 1),
        (2, 1, 0),
        (3, 1, 1),
        (4, 0, 2),
        (5, 1, 2),
        (6, 2, 0),
        (7, 2, 1),
        (8, 2, 2),
    ];

    for &(n, left, right) in &table {
        let lhs = f.const_app(p.unpair_left, &[num[n]]);
        assert!(f.k.def_eq(lhs, num[left]), "unpairLeft {n} must be {left}");
        let rhs = f.const_app(p.unpair_right, &[num[n]]);
        assert!(
            f.k.def_eq(rhs, num[right]),
            "unpairRight {n} must be {right}"
        );
    }

    // Negative control 1 -- a TRANSPOSED branch condition. At n = 5 the
    // true arm fires, so `(left, right) = (1, 2)`; transposing the test
    // takes the false arm and yields `(2, 1)`.
    let left_5 = f.const_app(p.unpair_left, &[num[5]]);
    assert!(
        !f.k.def_eq(left_5, num[2]),
        "negative control: unpairLeft 5 must NOT be 2 (transposed branch)"
    );
    let right_5 = f.const_app(p.unpair_right, &[num[5]]);
    assert!(
        !f.k.def_eq(right_5, num[1]),
        "negative control: unpairRight 5 must NOT be 1 (transposed branch)"
    );

    // Negative control 2 -- the FALSE arm of `unpairRight` must subtract
    // `s`. At n = 6, r = 2 and s = 2, so returning `r` uncorrected gives 2.
    let right_6 = f.const_app(p.unpair_right, &[num[6]]);
    assert!(
        !f.k.def_eq(right_6, num[2]),
        "negative control: unpairRight 6 must NOT be 2 (forgot the `- s`)"
    );

    // Negative control 3 -- the two projections are not the same function.
    // At n = 4 they are 0 and 2.
    let left_4 = f.const_app(p.unpair_left, &[num[4]]);
    assert!(
        !f.k.def_eq(left_4, num[2]),
        "negative control: unpairLeft 4 must NOT be 2 (projections swapped)"
    );

    for name in [p.unpair_left, p.unpair_right] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The round trip against the already-declared `Nat.pair`: for every
/// `(a, b)` in `[0, 2]²`, `unpairLeft (pair a b) = a` and
/// `unpairRight (pair a b) = b`.
///
/// This is the strongest check available here, and it is a check of THIS
/// construction rather than a restatement of it: `Nat.pair`'s own values are
/// pinned by `avg_pair_tests.rs` against a different hand-computed table, so
/// a wrong branch in either projection breaks the round trip at an argument
/// pair that is already independently fixed.
///
/// Note the asymmetry that makes it bite: `pair` is NOT symmetric
/// (`pair 1 0 = 2` while `pair 0 1 = 1`), so a version of this test with the
/// projections swapped fails at six of the nine pairs.
#[test]
fn unpair_inverts_pair_on_the_first_block() {
    let mut f = Fixture::new();
    let p = f.p;

    let num: Vec<_> = (0u32..=2).map(|i| f.num(i)).collect();

    let mut off_diagonal = 0;
    for a in 0usize..=2 {
        for b in 0usize..=2 {
            let paired = f.const_app(p.pair_fn, &[num[a], num[b]]);
            let left = f.const_app(p.unpair_left, &[paired]);
            assert!(
                f.k.def_eq(left, num[a]),
                "unpairLeft (pair {a} {b}) must be {a}"
            );
            let right = f.const_app(p.unpair_right, &[paired]);
            assert!(
                f.k.def_eq(right, num[b]),
                "unpairRight (pair {a} {b}) must be {b}"
            );
            if a != b {
                // The swapped-projection reading would return `b` here.
                assert!(
                    !f.k.def_eq(left, num[b]),
                    "negative control: unpairLeft (pair {a} {b}) must NOT be {b}"
                );
                off_diagonal += 1;
            }
        }
    }

    // The negative control above is vacuous on the diagonal, where `a = b`.
    // Assert that it actually ran on a nonempty set rather than trusting the
    // loop: a control that never executes is the failure this repository
    // cares most about.
    assert_eq!(
        off_diagonal, 6,
        "the swapped-projection control must run at 6 off-diagonal pairs"
    );
}

/// `Nat.unpaired f n` applies `f` to the two projections IN ORDER.
///
/// The argument `f` is deliberately **asymmetric**. With `add` or `mul` the
/// test cannot see swapped projections at all — it would pass against a
/// definition computing `f (unpairRight n) (unpairLeft n)` — so `Nat.sub` is
/// used, at arguments where the two orders disagree.
///
/// `unpaired sub 6 = sub 2 0 = 2`, while the swapped reading gives
/// `sub 0 2 = 0` (`Nat.sub` truncates). `unpaired sub 5 = sub 1 2 = 0`
/// against a swapped `sub 2 1 = 1`. Both directions of the disagreement are
/// covered, so a definition that truncates its way to the right answer at
/// one argument fails at the other.
#[test]
fn unpaired_applies_the_projections_in_order() {
    let mut f = Fixture::new();
    let p = f.p;

    let nat = f.nat_ty();
    let zero = f.num(0);
    let one = f.num(1);
    let two = f.num(2);
    let five = f.num(5);
    let six = f.num(6);

    // `fun x y => Nat.sub x y`
    let sub_fn = {
        let x_fv = f.fresh_fvar();
        let x = f.kernel().fvar(x_fv);
        let y_fv = f.fresh_fvar();
        let y = f.kernel().fvar(y_fv);
        let body = f.sub(x, y);
        let with_y = f.lam_fv(y_fv, nat, body);
        f.lam_fv(x_fv, nat, with_y)
    };

    let at_6 = f.const_app(p.unpaired, &[sub_fn, six]);
    assert!(f.k.def_eq(at_6, two), "unpaired sub 6 must be sub 2 0 = 2");
    assert!(
        !f.k.def_eq(at_6, zero),
        "negative control: unpaired sub 6 must NOT be 0 (projections swapped)"
    );

    let at_5 = f.const_app(p.unpaired, &[sub_fn, five]);
    assert!(
        f.k.def_eq(at_5, zero),
        "unpaired sub 5 must be sub 1 2 = 0 (Nat.sub truncates)"
    );
    assert!(
        !f.k.def_eq(at_5, one),
        "negative control: unpaired sub 5 must NOT be 1 (projections swapped)"
    );

    // And a symmetric `f` to confirm the plumbing itself is right: with
    // `fun x y => Nat.add x y`, `unpaired add 5 = 1 + 2 = 3`. This one
    // CANNOT see a swap -- it is here for the application shape, and the
    // asymmetric checks above are what discriminate.
    let add_fn = {
        let x_fv = f.fresh_fvar();
        let x = f.kernel().fvar(x_fv);
        let y_fv = f.fresh_fvar();
        let y = f.kernel().fvar(y_fv);
        let body = f.add(x, y);
        let with_y = f.lam_fv(y_fv, nat, body);
        f.lam_fv(x_fv, nat, with_y)
    };
    let three = f.num(3);
    let add_at_5 = f.const_app(p.unpaired, &[add_fn, five]);
    assert!(
        f.k.def_eq(add_at_5, three),
        "unpaired add 5 must be 1 + 2 = 3"
    );

    let name = p.unpaired;
    assert!(
        f.k.axiom_footprint(name).is_empty(),
        "{} must rest on zero axioms",
        f.k.display_name(name)
    );
}
