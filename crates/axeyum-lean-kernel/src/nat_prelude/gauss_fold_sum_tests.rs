//! Tests for [`nat_prelude::gauss_fold_sum`](super::gauss_fold_sum).
//!
//! Three kinds of check:
//!
//! 1. **Concrete instantiation with the coprimality hypothesis discharged by
//!    `Eq.refl`, and both sums evaluated to numerals.** `Nat.gaussFold` is a
//!    `Nat.mod`/`Nat.ble`/`Nat.sub` composite, so at numerals it reduces, and
//!    the folded sum can be checked against the triangular number it must be
//!    — not merely against the other side, which two stuck aggregates would
//!    also satisfy.
//! 2. **The coprimality hypothesis shown load-bearing.** At `m = 1`, `a = 3`
//!    (so `pp = 3` and `gcd 3 3 = 3`) the fold sum is `0` and the triangular
//!    sum is `1`: the statement without the hypothesis is FALSE, at an
//!    instance every other hypothesis of the theorem reaches.
//! 3. **The declared type, pinned character for character**, and the axiom
//!    footprint.

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

    /// `sumRange (fun k => succ k) m` at a concrete `m`.
    fn triangular(&mut self, m_v: u32) -> ExprId {
        let nat = self.nat_ty();
        let m = self.num(m_v);
        let f = {
            let k_fv = self.fresh_fvar();
            let k = self.k.fvar(k_fv);
            let body = self.succ(k);
            self.lam_fv(k_fv, nat, body)
        };
        self.sum_range(f, m)
    }

    /// `sumRange (fun j => gaussFold (succ (2*m)) a (succ j)) m` at concrete
    /// `m`, `a`.
    fn fold_sum(&mut self, m_v: u32, a_v: u32) -> ExprId {
        let p = self.p;
        let nat = self.nat_ty();
        let m = self.num(m_v);
        let a = self.num(a_v);
        let two = self.num(2);
        let mul2m = self.mul(two, m);
        let pp = self.succ(mul2m);
        let f = {
            let j_fv = self.fresh_fvar();
            let j = self.k.fvar(j_fv);
            let sj = self.succ(j);
            let body = self.const_app(p.gauss_fold, &[pp, a, sj]);
            self.lam_fv(j_fv, nat, body)
        };
        self.sum_range(f, m)
    }
}

/// `gaussFold pp a k` recomputed in Rust: the least residue `a*k mod pp`,
/// folded to `pp - r` when `r` exceeds `pp/2`.
fn gauss_fold(pp: u32, a: u32, k: u32) -> u32 {
    let r = (a * k) % pp;
    if pp / 2 < r { pp - r } else { r }
}

/// The reference sums, recomputed here rather than inherited from any ADR.
fn reference(m: u32, a: u32) -> (u32, u32) {
    let pp = 2 * m + 1;
    let triangular: u32 = (0..m).map(|k| k + 1).sum();
    let folded: u32 = (0..m).map(|j| gauss_fold(pp, a, j + 1)).sum();
    (triangular, folded)
}

/// The three reference instances really are permutations, and the
/// non-coprime one really is not. Checked in Rust first, so a wrong
/// expectation cannot be laundered through the kernel evaluation below.
#[test]
fn the_reference_instances_are_what_the_docs_say() {
    // `pp = 3, a = 2`; `pp = 5, a = 2`; `pp = 7, a = 3`.
    assert_eq!(reference(1, 2), (1, 1));
    assert_eq!(reference(2, 2), (3, 3));
    assert_eq!(reference(3, 3), (6, 6));
    // `pp = 3, a = 3`: `gcd 3 3 = 3`, and the fold collapses to zero.
    assert_eq!(reference(1, 3), (1, 0));
}

/// `Nat.gauss_fold_sumRange_eq` applies at three coprime instances, with the
/// coprimality proof by `Eq.refl` (so `Nat.gcd` genuinely reduces), and both
/// of its sums evaluate to the triangular number.
#[test]
fn the_additive_gauss_bijection_applies_and_computes() {
    let mut f = Fixture::new();
    let p = f.p;

    for (m_v, a_v) in [(1u32, 2u32), (2, 2), (3, 3)] {
        let (triangular, folded) = reference(m_v, a_v);
        assert_eq!(triangular, folded, "the reference instance must permute");

        let m = f.num(m_v);
        let a = f.num(a_v);
        let one = f.num(1);
        let cop = f.refl(one);

        let instance = f.lemma(p.gauss_fold_sum_range_eq, &[m, a, cop]);
        let inferred =
            f.k.infer(instance)
                .expect("the concrete instance must type-check");

        let lhs = f.triangular(m_v);
        let rhs = f.fold_sum(m_v, a_v);
        let expected = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, expected),
            "at (m,a) = ({m_v},{a_v}) the conclusion is not the additive bijection"
        );

        // Both sides reduce to the triangular number -- so neither aggregate
        // is stuck, and they are not equal merely by both failing to reduce.
        let value = f.num(triangular);
        assert!(
            f.k.def_eq(lhs, value),
            "at m = {m_v} the triangular sum must reduce to {triangular}"
        );
        assert!(
            f.k.def_eq(rhs, value),
            "at (m,a) = ({m_v},{a_v}) the fold sum must reduce to {folded}"
        );
        // Negative control for those two `def_eq`s: they reject a neighbour.
        let neighbour = f.num(triangular + 1);
        assert!(
            !f.k.def_eq(rhs, neighbour),
            "positive control: the fold sum is not {}",
            triangular + 1
        );
    }
}

/// **The coprimality hypothesis is load-bearing.** At `m = 1`, `a = 3` the
/// modulus is `pp = 3` and `gcd 3 3 = 3`: `leastResidue 3 3 1 = 0`, so the
/// fold sum is `0` while the triangular sum is `1`. Every other hypothesis of
/// the theorem (there are none) holds here, so this is exactly the instance a
/// version with the hypothesis dropped would reach.
#[test]
fn dropping_coprimality_gives_a_false_identity() {
    let mut f = Fixture::new();

    assert_eq!(reference(1, 3), (1, 0));

    let lhs = f.triangular(1);
    let rhs = f.fold_sum(1, 3);
    let zero = f.zero();
    let one = f.num(1);
    assert!(f.k.def_eq(lhs, one), "the triangular sum at m = 1 is 1");
    assert!(f.k.def_eq(rhs, zero), "at pp = 3, a = 3 the fold sum is 0");
    assert!(
        !f.k.def_eq(lhs, rhs),
        "so without coprimality the identity is FALSE"
    );
}

/// The declaration rests on zero axioms.
#[test]
fn the_additive_gauss_bijection_rests_on_no_axiom() {
    let f = Fixture::new();
    let p = f.p;

    assert!(
        f.k.axiom_footprint(p.gauss_fold_sum_range_eq).is_empty(),
        "{} must rest on zero axioms",
        f.k.display_name(p.gauss_fold_sum_range_eq)
    );
}

/// The declared type, pinned character for character.
///
/// The orientation matters and no instance can see it: the identity is an
/// equation, so swapping the two sides yields an equally true theorem with a
/// different `Eq` argument order, and every consumer that chains through it
/// would need a `symm` that is not there.
#[test]
fn the_additive_gauss_bijection_states_the_intended_type() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let ty = match k
        .environment()
        .get(p.gauss_fold_sum_range_eq)
        .expect("the theorem must be declared")
    {
        Declaration::Theorem { ty, .. } => k.render_lean(*ty),
        other => panic!("{other:?} is not a theorem"),
    };
    assert_eq!(
        ty, EXPECTED,
        "the additive bijection states a different type"
    );

    // The modulus is `succ (2*m)` in BOTH the hypothesis and the conclusion.
    // A `contains` query with its own negative control.
    assert!(
        ty.contains(
            "AxNat.gcd x1 (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))"
        ),
        "the hypothesis must be `gcd a (succ (2*m)) = 1`"
    );
    assert!(
        !ty.contains("AxNat.gcd x0 x1"),
        "the hypothesis must NOT be `gcd m a = 1`"
    );
}

const EXPECTED: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : Eq.{1} AxNat (AxNat.gcd x1 (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) (AxNat.succ AxNat.zero)) -> Eq.{1} AxNat (AxNat.sumRange (fun (x3 : AxNat) => AxNat.succ x3) x0) (AxNat.sumRange (fun (x3 : AxNat) => AxNat.gaussFold (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) x1 (AxNat.succ x3)) x0))))";
