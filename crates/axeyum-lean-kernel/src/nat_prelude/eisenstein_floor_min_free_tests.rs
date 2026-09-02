//! Tests for
//! [`nat_prelude::eisenstein_floor_min_free`](super::eisenstein_floor_min_free).
//!
//! The point of this file is that **the `min` is removable HERE and not in
//! general**, so the tests have to show both halves:
//!
//! 1. At the Eisenstein shape (`pp = 2m+1`, `q = 2n+1`) the cap never binds —
//!    checked index by index, not just on the totals — and the min-free
//!    identity evaluates on both sides.
//! 2. At a general instance `Nat.eisenstein_floor_sum` also reaches
//!    (`pp = 2`, `q = 5`, `m = 1`, `n = 0`, coprime and within the bound) the
//!    cap DOES bind and the min-free reading is FALSE: `2` against `0`. That
//!    reproduces ADR-1544's `M4` and is why this corollary is stated at the
//!    Eisenstein shape rather than proved for `eisenstein_floor_sum` itself.

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

/// `Sigma_{x<m} floor(q*(x+1)/pp)`.
fn row_sum(pp: u32, q: u32, m: u32) -> u32 {
    (0..m).map(|x| (q * (x + 1)) / pp).sum()
}

/// The largest row floor below `m` — what the `min` would cap.
fn max_row_floor(pp: u32, q: u32, m: u32) -> u32 {
    (0..m).map(|x| (q * (x + 1)) / pp).max().unwrap_or(0)
}

/// Coprime `(m, n)` pairs; `pp = 2m+1`, `q = 2n+1`.
const PAIRS: [(u32, u32); 3] = [(3, 2), (2, 1), (3, 1)];

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    /// `sumRange (fun x => div (mul q (succ x)) pp) m` at concrete numerals.
    fn bare_row_sum(&mut self, pp: u32, q: u32, m: u32) -> ExprId {
        let nat = self.nat_ty();
        let pp_e = self.num(pp);
        let q_e = self.num(q);
        let f = {
            let x_fv = self.fresh_fvar();
            let x = self.k.fvar(x_fv);
            let sx = self.succ(x);
            let prod = self.mul(q_e, sx);
            let body = self.div(prod, pp_e);
            self.lam_fv(x_fv, nat, body)
        };
        let m_e = self.num(m);
        self.sum_range(f, m_e)
    }

    /// `sumRange (fun x => min n (div (mul q (succ x)) pp)) m`.
    fn min_row_sum(&mut self, pp: u32, q: u32, m: u32, n: u32) -> ExprId {
        let p = self.p;
        let nat = self.nat_ty();
        let pp_e = self.num(pp);
        let q_e = self.num(q);
        let n_e = self.num(n);
        let f = {
            let x_fv = self.fresh_fvar();
            let x = self.k.fvar(x_fv);
            let sx = self.succ(x);
            let prod = self.mul(q_e, sx);
            let quot = self.div(prod, pp_e);
            let body = self.const_app(p.min_min, &[n_e, quot]);
            self.lam_fv(x_fv, nat, body)
        };
        let m_e = self.num(m);
        self.sum_range(f, m_e)
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

    fn reduces_to(&mut self, term: ExprId, value: u32) -> bool {
        let v = self.num(value);
        self.k.def_eq(term, v)
    }
}

/// The arithmetic, in Rust first: at the Eisenstein shape the cap never binds
/// on EITHER axis, and the two bare floor sums add to `n*m`.
#[test]
fn at_the_eisenstein_shape_the_cap_never_binds() {
    for (m, n) in PAIRS {
        let (pp, q) = (2 * m + 1, 2 * n + 1);
        assert_eq!(
            row_sum(pp, q, m) + row_sum(q, pp, n),
            n * m,
            "the min-free identity must hold at pp = {pp}, q = {q}"
        );
        assert!(
            max_row_floor(pp, q, m) <= n,
            "the row cap must not bind at pp = {pp}, q = {q}"
        );
        assert!(
            max_row_floor(q, pp, n) <= m,
            "the column cap must not bind at pp = {pp}, q = {q}"
        );
    }
    // And the sums are not all zero, so the identity is not vacuous.
    assert_eq!((row_sum(7, 5, 3), row_sum(5, 7, 2)), (3, 3));
}

/// **The general instance where the cap DOES bind**, reproducing ADR-1544's
/// `M4`: `pp = 2`, `q = 5`, `m = 1`, `n = 0`. Both of
/// `Nat.eisenstein_floor_sum`'s hypotheses hold there (`gcd 2 5 = 1` and
/// `1 < 2`), the min form gives `0 = n*m`, and the min-free reading gives `2`.
/// So the corollary in this module could NOT have been stated for
/// `eisenstein_floor_sum` itself.
#[test]
fn at_a_general_instance_the_cap_binds_and_the_min_free_reading_is_false() {
    let mut f = Fixture::new();
    let (pp, q, m, n) = (2u32, 5u32, 1u32, 0u32);

    assert_eq!(max_row_floor(pp, q, m), 2, "floor(5/2) = 2");
    assert!(max_row_floor(pp, q, m) > n, "the cap binds: 2 > 0");
    assert_eq!(n * m, 0);

    let bare = f.bare_row_sum(pp, q, m);
    let capped = f.min_row_sum(pp, q, m, n);
    assert!(f.reduces_to(bare, 2), "the bare row sum is 2");
    assert!(f.reduces_to(capped, 0), "the capped row sum is 0");
    assert!(
        !f.k.def_eq(bare, capped),
        "so dropping the min at this general instance is FALSE"
    );
    // This instance is NOT of the Eisenstein shape: `pp = 2` is not `2m+1`
    // for the `m = 1` used here (that would be `3`).
    assert_ne!(pp, 2 * m + 1);
}

/// The bound lemma applies and its conclusion is the one intended.
#[test]
fn the_bound_lemma_applies_at_every_index_below_m() {
    let mut f = Fixture::new();
    let p = f.p;

    for (m, n) in PAIRS {
        let (pp, q) = (2 * m + 1, 2 * n + 1);
        for x in 0..m {
            // `Le (succ x) m` from the two `Nat.le` constructors only.
            let m_e = f.num(m);
            let n_e = f.num(n);
            let x_e = f.num(x);
            let hyp = f.le_proof(x + 1, m);
            let instance = f.lemma(p.div_mul_succ_le_of_le, &[m_e, n_e, x_e, hyp]);
            let inferred =
                f.k.infer(instance)
                    .expect("the bound instance must type-check");

            let pp_e = f.num(pp);
            let q_e = f.num(q);
            let sx2 = {
                let x2 = f.num(x);
                f.succ(x2)
            };
            let prod = f.mul(q_e, sx2);
            let quot = f.div(prod, pp_e);
            let n_e2 = f.num(n);
            let expected = f.le(quot, n_e2);
            assert!(
                f.k.def_eq(inferred, expected),
                "at pp = {pp}, q = {q}, x = {x} the bound is not the intended one"
            );
            assert!(
                f.reduces_to(quot, (q * (x + 1)) / pp),
                "and the quotient reduces"
            );
        }
    }
}

/// The min-free identity, instantiated and evaluated on both sides.
#[test]
fn the_min_free_identity_applies_and_computes() {
    let mut f = Fixture::new();
    let p = f.p;

    for (m, n) in PAIRS {
        let (pp, q) = (2 * m + 1, 2 * n + 1);

        let m_e = f.num(m);
        let n_e = f.num(n);
        let one = f.num(1);
        let cop = f.refl(one);
        let instance = f.lemma(p.eisenstein_floor_sum_min_free, &[m_e, n_e, cop]);
        let inferred =
            f.k.infer(instance)
                .expect("the coprime instance must type-check");

        let rows = f.bare_row_sum(pp, q, m);
        let cols = f.bare_row_sum(q, pp, n);
        let lhs = f.add(rows, cols);
        let n_e2 = f.num(n);
        let m_e2 = f.num(m);
        let rhs = f.mul(n_e2, m_e2);
        let expected = f.eq(lhs, rhs);
        assert!(
            f.k.def_eq(inferred, expected),
            "at pp = {pp}, q = {q} the conclusion is not the min-free identity"
        );

        assert!(f.reduces_to(rows, row_sum(pp, q, m)));
        assert!(f.reduces_to(cols, row_sum(q, pp, n)));
        assert!(f.reduces_to(lhs, n * m), "both sides reduce to {}", n * m);
        assert!(f.reduces_to(rhs, n * m));
        assert!(!f.reduces_to(lhs, n * m + 1));
    }
}

/// Both declarations rest on zero axioms.
#[test]
fn the_min_free_family_rests_on_no_axiom() {
    let f = Fixture::new();
    let p = f.p;
    for name in [p.div_mul_succ_le_of_le, p.eisenstein_floor_sum_min_free] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The declared types, pinned character for character.
///
/// What the numeric instances cannot see: that both moduli are `succ (2*_)`
/// in every occurrence, and that the two sums are over `m` and `n`
/// respectively rather than both over the same bound.
#[test]
fn the_min_free_family_states_the_intended_types() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");

    let render = |k: &mut Kernel, name| match k
        .environment()
        .get(name)
        .expect("the theorem must be declared")
    {
        Declaration::Theorem { ty, .. } => {
            let ty = *ty;
            k.render_lean(ty)
        }
        other => panic!("{other:?} is not a theorem"),
    };

    assert_eq!(render(&mut k, p.div_mul_succ_le_of_le), EXPECTED_BOUND);
    assert_eq!(
        render(&mut k, p.eisenstein_floor_sum_min_free),
        EXPECTED_IDENTITY
    );

    // No `Min.min` survives in the corollary -- that is the whole point.
    assert!(
        !EXPECTED_IDENTITY.contains("Min.min"),
        "the corollary must be min-FREE"
    );
    // Negative control on that query: `eisenstein_floor_sum` DOES carry it.
    let with_min = render(&mut k, p.eisenstein_floor_sum);
    assert!(
        with_min.contains("Min.min"),
        "positive control: `eisenstein_floor_sum` carries the min"
    );
}

const EXPECTED_BOUND: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : AxNat) -> ((x3 : AxNat.le (AxNat.succ x2) x0) -> AxNat.le (AxNat.div (AxNat.mul (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) (AxNat.succ x2)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) x1))))";
const EXPECTED_IDENTITY: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : Eq.{1} AxNat (AxNat.gcd (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1))) (AxNat.succ AxNat.zero)) -> Eq.{1} AxNat (AxNat.add (AxNat.sumRange (fun (x3 : AxNat) => AxNat.div (AxNat.mul (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) (AxNat.succ x3)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) x0) (AxNat.sumRange (fun (x3 : AxNat) => AxNat.div (AxNat.mul (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) (AxNat.succ x3)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1))) x1)) (AxNat.mul x1 x0))))";
