//! Tests for [`nat_prelude::eisenstein_lattice`](super::eisenstein_lattice).
//!
//! A separate file rather than an addition to `nat_prelude_tests.rs`, per this
//! repository's standing merge-hazard note.
//!
//! Four kinds of check, chosen so that each fails on a defect class the others
//! cannot see:
//!
//! 1. **Concrete instantiation with every hypothesis discharged, and both
//!    sides evaluated.** Unlike the side condition (`eisenstein_side.rs`),
//!    this theorem's conclusion is an equation between two `Nat` VALUES, so
//!    there is something to compute: `Nat.gcd`, `Nat.div`, `Min.min`,
//!    `Nat.sumRange` and `Nat.mul` all reduce, and the sum of floors is
//!    checked against the numeral it must be — not just against `mul n m`,
//!    which a broken aggregate could still match by accident.
//! 2. **Both hypotheses shown load-bearing, numerically.** Dropping
//!    coprimality (`pp = q = 2`, `m = n = 1`) and dropping `Lt m pp`
//!    (`pp = 2`, `q = 1`, `m = 2`, `n = 1`) each give a FALSE identity, and
//!    the test asserts the two sides differ there. A theorem whose hypotheses
//!    are decoration cannot be told from this one by any instantiation the
//!    theorem itself reaches.
//! 3. **The selector partition's own hypothesis is load-bearing**, for the
//!    same reason and at the only point where it fails: `a = b`, where both
//!    comparisons hold and the selector sum is `2`.
//! 4. **The declared types, pinned character for character.** The four Nat
//!    binders and the two hypotheses can be permuted into a different (and in
//!    one case false) statement that every reachable instance still satisfies.

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

    /// A proof of `Le a b` for concrete `a <= b`, from the two `Nat.le`
    /// constructors only.
    fn le_proof(&mut self, a: u32, b: u32) -> ExprId {
        assert!(a <= b, "le_proof needs a <= b");
        let p = self.p;
        let a_term = self.num(a);
        let mut proof = self.lemma(p.le_refl, &[a_term]);
        for step in a..b {
            let upper = self.num(step);
            proof = self.lemma(p.le_step, &[a_term, upper, proof]);
        }
        proof
    }

    /// The left-hand side of `Nat.eisenstein_floor_sum` at concrete numerals:
    ///
    /// ```text
    /// sumRange (fun x => min n (div (q*(x+1)) pp)) m
    ///   + sumRange (fun y => min m (div (pp*(y+1)) q)) n
    /// ```
    fn floor_sum(&mut self, pp_v: u32, q_v: u32, m_v: u32, n_v: u32) -> ExprId {
        let p = self.p;
        let nat = self.nat_ty();
        let pp = self.num(pp_v);
        let q = self.num(q_v);
        let m = self.num(m_v);
        let n = self.num(n_v);

        let rows = {
            let x_fv = self.fresh_fvar();
            let x = self.k.fvar(x_fv);
            let sx = self.succ(x);
            let bnd = self.mul(q, sx);
            let quotient = self.div(bnd, pp);
            let body = self.const_app(p.min_min, &[n, quotient]);
            self.lam_fv(x_fv, nat, body)
        };
        let cols = {
            let y_fv = self.fresh_fvar();
            let y = self.k.fvar(y_fv);
            let sy = self.succ(y);
            let bnd = self.mul(pp, sy);
            let quotient = self.div(bnd, q);
            let body = self.const_app(p.min_min, &[m, quotient]);
            self.lam_fv(y_fv, nat, body)
        };
        let left = self.sum_range(rows, m);
        let right = self.sum_range(cols, n);
        self.add(left, right)
    }
}

/// The reference numbers, recomputed in Rust rather than inherited from any
/// ADR's Python. Two Eisenstein instances with small magnitudes, because every
/// numeral in this prelude is unary.
///
/// `(p, q) = (3, 5)`: `m = 1`, `n = 2`. Rows `⌊5·1/3⌋ = 1`, capped at `n = 2`,
/// so `1`. Columns `⌊3·1/5⌋ = 0` and `⌊3·2/5⌋ = 1`, capped at `m = 1`, so `1`.
/// Total `2 = n·m`.
///
/// `(p, q) = (5, 7)`: `m = 2`, `n = 3`. Rows `⌊7/5⌋ = 1`, `⌊14/5⌋ = 2`, sum
/// `3`. Columns `⌊5/7⌋ = 0`, `⌊10/7⌋ = 1`, `⌊15/7⌋ = 2`, sum `3`. Total
/// `6 = n·m`.
fn reference(pp: u32, q: u32, m: u32, n: u32) -> (u32, u32, u32) {
    let rows: u32 = (0..m).map(|x| n.min((q * (x + 1)) / pp)).sum();
    let cols: u32 = (0..n).map(|y| m.min((pp * (y + 1)) / q)).sum();
    (rows, cols, rows + cols)
}

/// The two reference instances are what the doc says they are, and the total
/// really is `n·m`. Checked in Rust first so a wrong expectation cannot be
/// laundered through the kernel evaluation below.
#[test]
fn the_reference_instances_are_what_the_docs_say() {
    assert_eq!(reference(3, 5, 1, 2), (1, 1, 2));
    assert_eq!(reference(5, 7, 2, 3), (3, 3, 6));
    // `n * m` at each: the identity's right-hand side, spelled the way the
    // theorem spells it.
    for (pp, q) in [(3u32, 5u32), (5, 7)] {
        let (m, n) = ((pp - 1) / 2, (q - 1) / 2);
        assert_eq!(reference(pp, q, m, n).2, n * m);
    }
}

/// `Nat.eisenstein_floor_sum` applies at two odd prime pairs, with the
/// coprimality proof by `Eq.refl` (so `Nat.gcd` genuinely reduces) and the
/// bound built from the `Nat.le` constructors — and its conclusion evaluates
/// to the numeral `reference` computes.
#[test]
fn the_lattice_identity_applies_and_computes_at_two_prime_pairs() {
    let mut f = Fixture::new();
    let p = f.p;

    for (pp_v, q_v) in [(3u32, 5u32), (5, 7)] {
        let (m_v, n_v) = ((pp_v - 1) / 2, (q_v - 1) / 2);
        let (_rows, _cols, total) = reference(pp_v, q_v, m_v, n_v);
        assert_eq!(
            total,
            n_v * m_v,
            "the reference instance must be a solution"
        );

        let ap = f.num(pp_v - 1);
        let aq = f.num(q_v - 1);
        let m = f.num(m_v);
        let n = f.num(n_v);

        // `gcd (succ ap) (succ aq) = 1` by reflexivity.
        let one = f.num(1);
        let cop = f.refl(one);
        // `Lt m (succ ap)`, i.e. `Le (succ m) pp`.
        let bound = f.le_proof(m_v + 1, pp_v);

        let instance = f.lemma(p.eisenstein_floor_sum, &[ap, aq, m, n, cop, bound]);
        let inferred =
            f.k.infer(instance)
                .expect("the concrete instance must type-check");

        let lhs = f.floor_sum(pp_v, q_v, m_v, n_v);
        let rhs = f.mul(n, m);
        let expected = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, expected),
            "at (p,q) = ({pp_v},{q_v}) the conclusion is not the floor identity"
        );

        // Both sides really are the numeral `reference` computes -- so the
        // aggregates are not merely equal to each other by being stuck.
        let total_term = f.num(total);
        assert!(
            f.k.def_eq(lhs, total_term),
            "at (p,q) = ({pp_v},{q_v}) the floor sum must reduce to {total}"
        );
        assert!(
            f.k.def_eq(rhs, total_term),
            "at (p,q) = ({pp_v},{q_v}) n*m must reduce to {total}"
        );
        // Negative control for those two `def_eq`s: they reject a neighbour.
        let off_by_one = f.num(total + 1);
        assert!(
            !f.k.def_eq(lhs, off_by_one),
            "positive control: the floor sum is not {}",
            total + 1
        );
    }
}

/// **The coprimality hypothesis is load-bearing.** At `pp = q = 2` (so
/// `gcd = 2`), `m = n = 1`, the identity is FALSE: the floor sum is `2` and
/// `n·m` is `1`. Every hypothesis of the theorem except coprimality holds
/// there (`m = 1 < 2 = pp`), so this is exactly the instance a version with
/// the hypothesis dropped would reach.
#[test]
fn dropping_coprimality_gives_a_false_identity() {
    let mut f = Fixture::new();

    let (rows, cols, total) = reference(2, 2, 1, 1);
    assert_eq!((rows, cols, total), (1, 1, 2));

    let lhs = f.floor_sum(2, 2, 1, 1);
    let one = f.num(1);
    let two = f.num(2);
    assert!(
        f.k.def_eq(lhs, two),
        "at pp = q = 2, m = n = 1 the floor sum is 2"
    );
    assert!(
        !f.k.def_eq(lhs, one),
        "at pp = q = 2, m = n = 1 the identity `= n*m = 1` is FALSE"
    );
}

/// **The `Lt m pp` hypothesis is load-bearing.** At `pp = 2`, `q = 1`
/// (coprime), `m = 2`, `n = 1` the identity is FALSE: the floor sum is `3` and
/// `n·m` is `2`. `m = 2` is not below `pp = 2`, which is the only hypothesis
/// that fails.
#[test]
fn dropping_the_bound_on_m_gives_a_false_identity() {
    let mut f = Fixture::new();

    let (rows, cols, total) = reference(2, 1, 2, 1);
    assert_eq!((rows, cols, total), (1, 2, 3));

    let lhs = f.floor_sum(2, 1, 2, 1);
    let two = f.num(2);
    let three = f.num(3);
    assert!(
        f.k.def_eq(lhs, three),
        "at pp = 2, q = 1, m = 2, n = 1 the floor sum is 3"
    );
    assert!(
        !f.k.def_eq(lhs, two),
        "at pp = 2, q = 1, m = 2, n = 1 the identity `= n*m = 2` is FALSE"
    );
}

/// `Nat.ble_select_add_of_ne` applies at a distinct pair and its conclusion
/// computes to `1`; at an EQUAL pair the same expression computes to `2`, so
/// the `Not (Eq a b)` hypothesis cannot be dropped.
#[test]
fn the_selector_partition_applies_and_needs_its_hypothesis() {
    let mut f = Fixture::new();
    let p = f.p;

    let one = f.num(1);
    let zero = f.zero();
    let two = f.num(2);

    // The expression the theorem is about, at `(a, b) = (9, 10)` -- the two
    // products `3*3` and `5*2` the side condition separates.
    let selector_sum = |f: &mut Fixture, a_v: u32, b_v: u32| -> ExprId {
        let a = f.num(a_v);
        let b = f.num(b_v);
        let ab = f.ble(a, b);
        let ba = f.ble(b, a);
        let s1 = f.bool_select_nat(ab, one, zero);
        let s2 = f.bool_select_nat(ba, one, zero);
        f.add(s1, s2)
    };

    for (a_v, b_v) in [(9u32, 10u32), (10, 9)] {
        let total = selector_sum(&mut f, a_v, b_v);
        assert!(
            f.k.def_eq(total, one),
            "at ({a_v},{b_v}) exactly one comparison holds"
        );
    }

    // The hypothesis is load-bearing exactly here.
    let equal = selector_sum(&mut f, 9, 9);
    assert!(
        f.k.def_eq(equal, two),
        "at a = b BOTH comparisons hold and the selector sum is 2"
    );
    assert!(
        !f.k.def_eq(equal, one),
        "so the statement without `Not (Eq a b)` is FALSE"
    );

    // ...and the theorem itself applies where the hypothesis holds. `9 <> 10`
    // is witnessed by `Nat.ne_of_beq_eq_false` at `Eq.refl Bool.false`.
    let nine = f.num(9);
    let ten = f.num(10);
    let false_ = f.bool_false();
    let refl_false = f.bool_refl(false_);
    let ne = f.lemma(p.ne_of_beq_eq_false, &[nine, ten, refl_false]);
    let instance = f.lemma(p.ble_select_add_of_ne, &[nine, ten, ne]);
    let inferred =
        f.k.infer(instance)
            .expect("the concrete instance must type-check");
    let lhs = selector_sum(&mut f, 9, 10);
    let expected = f.eq(lhs, one);
    assert!(
        f.k.def_eq(inferred, expected),
        "the instantiated conclusion is not the selector partition"
    );
}

/// Both declarations rest on zero axioms.
#[test]
fn the_lattice_assembly_rests_on_no_axiom() {
    let f = Fixture::new();
    let p = f.p;

    for name in [p.ble_select_add_of_ne, p.eisenstein_floor_sum] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The declared types, pinned character for character.
///
/// This is the probe for *admitted, true, and not your theorem*. The two
/// summands can be swapped, `Min.min`'s arguments can be swapped, and the
/// bound can be placed on `n` instead of `m` -- each yields a statement no
/// instantiation over reachable arguments distinguishes from this one (the
/// first two because the identity is symmetric in the swap, the third because
/// Eisenstein's own instance satisfies both).
#[test]
fn the_lattice_assembly_states_the_intended_types() {
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
        (p.ble_select_add_of_ne, EXPECTED_SELECT),
        (p.eisenstein_floor_sum, EXPECTED_FLOOR_SUM),
    ] {
        assert_eq!(
            rendered(&k, name),
            expected,
            "{} states a different type than intended",
            k.display_name(name)
        );
    }

    // The bound is on `m` (`x2`, the third binder -- the coordinate paired
    // with `q`), never on `n`. A `contains` query with its own negative
    // control, because an empty match and a mistyped pattern look the same.
    let floor_sum = rendered(&k, p.eisenstein_floor_sum);
    assert!(
        floor_sum.contains("AxNat.lt x2 (AxNat.succ x0)"),
        "the bound must be `m < succ ap`"
    );
    assert!(
        !floor_sum.contains("AxNat.lt x3 (AxNat.succ x0)"),
        "the bound must NOT be on `n`"
    );
}

const EXPECTED_SELECT: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : Not (Eq.{1} AxNat x0 x1)) -> Eq.{1} AxNat (AxNat.add (Bool.rec.{1} (fun (x3 : Bool) => AxNat) AxNat.zero (AxNat.succ AxNat.zero) (AxNat.ble x0 x1)) (Bool.rec.{1} (fun (x3 : Bool) => AxNat) AxNat.zero (AxNat.succ AxNat.zero) (AxNat.ble x1 x0))) (AxNat.succ AxNat.zero))))";
const EXPECTED_FLOOR_SUM: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> ((x3 : AxNat) -> ((x4 : Eq.{1} AxNat (AxNat.gcd (AxNat.succ x0) (AxNat.succ x1)) (AxNat.succ AxNat.zero)) -> ((x5 : AxNat.lt x2 (AxNat.succ x0)) -> Eq.{1} AxNat (AxNat.add (AxNat.sumRange (fun (x6 : AxNat) => Min.min x3 (AxNat.div (AxNat.mul (AxNat.succ x1) (AxNat.succ x6)) (AxNat.succ x0))) x2) (AxNat.sumRange (fun (x6 : AxNat) => Min.min x2 (AxNat.div (AxNat.mul (AxNat.succ x0) (AxNat.succ x6)) (AxNat.succ x1))) x3)) (AxNat.mul x3 x2)))))))";
