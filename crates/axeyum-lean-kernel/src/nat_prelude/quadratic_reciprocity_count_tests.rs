//! Tests for
//! [`nat_prelude::quadratic_reciprocity_count`](super::quadratic_reciprocity_count).
//!
//! Three kinds, in the order they were written:
//!
//! 1. **The arithmetic in Rust first.** `gaussNegCount` and the floor sums are
//!    re-implemented here from their own definitions, and the reciprocity
//!    identity is checked at seven prime pairs before any kernel term is
//!    built. That is what caught the brief's expected signs being wrong at
//!    two of its five pairs — `(3,5)` and `(5,7)` are `+1`, not `-1`, because
//!    the product is `-1` only when BOTH primes are `3 mod 4`.
//! 2. **Concrete instantiation**, with the coprimality hypothesis discharged
//!    by `Eq.refl` (so `Nat.gcd` really does reduce at each pair), the
//!    inferred conclusion matched against a separately built expected term,
//!    and both aggregates reduced to numerals with their neighbours rejected.
//! 3. **The declared types pinned character for character**, which is the only
//!    check that sees what no numeral can: that both moduli are `succ (2*_)`
//!    in every occurrence, that the two counts take their arguments in
//!    OPPOSITE orders (`gaussNegCount pp q m` against `gaussNegCount q pp n`),
//!    and that the product on the right is `mul n m` rather than `mul m n`.
//!
//! **The coprimality hypothesis is load-bearing**, and the witness that shows
//! it is `(m, n) = (1, 1)` — `p = q = 3`, `gcd 3 3 = 3` — where `S + T = 1`,
//! which is odd. Recorded as a deliberate SURVIVOR: `(m, n) = (2, 2)`
//! (`p = q = 5`) is also non-coprime and its `S + T = 4` IS even, so a
//! non-coprime control drawn at that pair would pass while checking nothing.
//! Derive the witness from the statement, never from a neighbouring file.

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

/// `Nat.gaussNegCount pp a m := countRange (fun j => gaussSignNeg pp a (succ
/// j)) m`, with `gaussSignNeg pp a k := ble (succ (div pp 2)) (mod (mul a k)
/// pp)` — re-implemented from the definitions, not from a doc comment.
fn gauss_neg_count(pp: u32, a: u32, m: u32) -> u32 {
    (0..m)
        .filter(|j| (a * (j + 1)) % pp >= pp / 2 + 1)
        .count()
        .try_into()
        .expect("the count fits")
}

/// `Sigma_{x<m} floor(q*(x+1)/pp)`.
fn row_sum(pp: u32, q: u32, m: u32) -> u32 {
    (0..m).map(|x| (q * (x + 1)) / pp).sum()
}

/// Coprime `(m, n)` pairs; `p = 2m+1`, `q = 2n+1`, both prime. The largest
/// magnitude formed anywhere below is `17*6 = 102`, and every numeral in this
/// kernel is unary, so this list is deliberately short.
const PAIRS: [(u32, u32); 5] = [(1, 2), (2, 3), (1, 3), (2, 6), (6, 8)];

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    /// `Nat.gaussNegCount pp a m` at concrete numerals.
    fn count_term(&mut self, pp: u32, a: u32, m: u32) -> ExprId {
        let p = self.p;
        let pp_e = self.num(pp);
        let a_e = self.num(a);
        let m_e = self.num(m);
        self.const_app(p.gauss_neg_count, &[pp_e, a_e, m_e])
    }

    /// `add (add N_p N_q) (mul n m)` at concrete `(m, n)`.
    fn s_plus_t(&mut self, m: u32, n: u32) -> ExprId {
        let (pp, q) = (2 * m + 1, 2 * n + 1);
        let n_p = self.count_term(pp, q, m);
        let n_q = self.count_term(q, pp, n);
        let s = self.add(n_p, n_q);
        let n_e = self.num(n);
        let m_e = self.num(m);
        let t = self.mul(n_e, m_e);
        self.add(s, t)
    }

    fn reduces_to(&mut self, term: ExprId, value: u32) -> bool {
        let v = self.num(value);
        self.k.def_eq(term, v)
    }
}

/// **The arithmetic, in Rust, before any kernel term exists.** Both halves of
/// the assembly mesh at every pair, and the reciprocity sign is what the
/// classical law says it is.
#[test]
fn the_reciprocity_identity_holds_at_seven_prime_pairs() {
    // `(p, q)` rather than `(m, n)` here, so the `mod 4` reading is legible.
    for (p, q) in [(3, 5), (5, 7), (3, 7), (5, 13), (13, 17), (7, 11), (11, 19)] {
        let (m, n) = ((p - 1) / 2, (q - 1) / 2);
        let n_p = gauss_neg_count(p, q, m);
        let n_q = gauss_neg_count(q, p, n);
        // The floor half: `eisenstein_floor_sum_min_free`.
        assert_eq!(
            row_sum(p, q, m) + row_sum(q, p, n),
            n * m,
            "the floor sums must add to n*m at ({p}, {q})"
        );
        // The parity half: `eisenstein_lemma`, twice.
        assert_eq!(
            (row_sum(p, q, m) + n_p) % 2,
            0,
            "Eisenstein's lemma at ({p}, {q})"
        );
        assert_eq!(
            (row_sum(q, p, n) + n_q) % 2,
            0,
            "Eisenstein's lemma at ({q}, {p})"
        );
        // What this module declares.
        assert_eq!(
            (n_p + n_q + n * m) % 2,
            0,
            "gaussCount_sum_even must hold at ({p}, {q})"
        );
        // And that it is the classical sign: `-1` exactly when both are 3 mod 4.
        let sign = if (n_p + n_q) % 2 == 0 { 1i32 } else { -1 };
        let classical = if p % 4 == 3 && q % 4 == 3 { -1 } else { 1i32 };
        assert_eq!(sign, classical, "the Legendre product at ({p}, {q})");
    }
    // Not vacuous: both signs occur in that list.
    assert_eq!(
        (gauss_neg_count(3, 7, 1) + gauss_neg_count(7, 3, 3)) % 2,
        1,
        "(3, 7) is the -1 case"
    );
    assert_eq!(
        (gauss_neg_count(3, 5, 1) + gauss_neg_count(5, 3, 2)) % 2,
        0,
        "(3, 5) is the +1 case"
    );
}

/// **Coprimality is load-bearing**, at `(m, n) = (1, 1)`: `p = q = 3`,
/// `gcd 3 3 = 3`, and `S + T = 0 + 1 = 1`, which is odd. Refuted inside the
/// kernel: the term reduces to `1`, and `1` is not `k + k` for any reachable
/// `k` (every `k >= 1` gives `k + k >= 2`).
#[test]
fn the_coprimality_hypothesis_is_load_bearing() {
    let mut f = Fixture::new();
    let (m, n) = (1u32, 1u32);
    assert_eq!(
        gauss_neg_count(3, 3, m) + gauss_neg_count(3, 3, n) + n * m,
        1
    );

    let x = f.s_plus_t(m, n);
    assert!(f.reduces_to(x, 1), "the non-coprime instance reduces to 1");
    for k in 0..=2u32 {
        let k_e = f.num(k);
        let kk = f.add(k_e, k_e);
        let one = f.num(1);
        assert!(
            !f.k.def_eq(one, kk),
            "1 must not be {k} + {k}; larger k only grows"
        );
    }

    // A recorded SURVIVOR: `(2, 2)` is equally non-coprime (`gcd 5 5 = 5`)
    // and its `S + T = 4` IS even, so a control drawn there would pass while
    // separating nothing.
    assert_eq!(
        gauss_neg_count(5, 5, 2) + gauss_neg_count(5, 5, 2) + 2 * 2,
        4
    );
    let survivor = f.s_plus_t(2, 2);
    assert!(f.reduces_to(survivor, 4), "the survivor is even");
}

/// `Nat.gaussCount_sum_even` applies at each coprime pair, its conclusion is
/// the intended one, and the aggregate reduces to the hand-computed value.
#[test]
fn the_even_form_applies_and_computes() {
    let mut f = Fixture::new();
    let p = f.p;

    for (m, n) in PAIRS {
        let (pp, q) = (2 * m + 1, 2 * n + 1);
        let m_e = f.num(m);
        let n_e = f.num(n);
        let one = f.num(1);
        // `gcd q pp = 1` by `Eq.refl` -- so `Nat.gcd` reduces at this pair.
        let cop = f.refl(one);
        let instance = f.lemma(p.gauss_count_sum_even, &[m_e, n_e, cop]);
        let inferred =
            f.k.infer(instance)
                .expect("the coprime instance must type-check");

        let x = f.s_plus_t(m, n);
        let expected = f.const_app(p.even, &[x]);
        assert!(
            f.k.def_eq(inferred, expected),
            "at p = {pp}, q = {q} the conclusion is not `Even (S + T)`"
        );

        let total = gauss_neg_count(pp, q, m) + gauss_neg_count(q, pp, n) + n * m;
        assert_eq!(total % 2, 0);
        assert!(f.reduces_to(x, total), "S + T must reduce to {total}");
        assert!(!f.reduces_to(x, total + 1), "and must reject its neighbour");
    }
}

/// `Nat.gaussCount_sum_modEq` applies at each coprime pair and states the
/// congruence between the two counts' sum and `n*m`.
#[test]
fn the_congruence_form_applies_at_each_pair() {
    let mut f = Fixture::new();
    let p = f.p;

    for (m, n) in PAIRS {
        let (pp, q) = (2 * m + 1, 2 * n + 1);
        let m_e = f.num(m);
        let n_e = f.num(n);
        let one = f.num(1);
        let cop = f.refl(one);
        let instance = f.lemma(p.gauss_count_sum_mod_eq, &[m_e, n_e, cop]);
        let inferred =
            f.k.infer(instance)
                .expect("the coprime instance must type-check");

        let n_p = f.count_term(pp, q, m);
        let n_q = f.count_term(q, pp, n);
        let s = f.add(n_p, n_q);
        let n_e2 = f.num(n);
        let m_e2 = f.num(m);
        let t = f.mul(n_e2, m_e2);
        let two = f.num(2);
        let expected = f.mod_eq(two, s, t);
        assert!(
            f.k.def_eq(inferred, expected),
            "at p = {pp}, q = {q} the conclusion is not `modEq 2 S T`"
        );

        let s_val = gauss_neg_count(pp, q, m) + gauss_neg_count(q, pp, n);
        assert!(f.reduces_to(s, s_val));
        assert!(f.reduces_to(t, n * m));
        assert_eq!(s_val % 2, (n * m) % 2, "and it really is a congruence");
    }
}

/// Both declarations rest on zero axioms.
#[test]
fn the_reciprocity_count_family_rests_on_no_axiom() {
    let f = Fixture::new();
    let p = f.p;
    for name in [p.gauss_count_sum_even, p.gauss_count_sum_mod_eq] {
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            f.k.display_name(name)
        );
    }
}

/// The declared types, pinned character for character.
#[test]
fn the_reciprocity_count_family_states_the_intended_types() {
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

    assert_eq!(render(&mut k, p.gauss_count_sum_even), EXPECTED_EVEN);
    assert_eq!(render(&mut k, p.gauss_count_sum_mod_eq), EXPECTED_MOD_EQ);

    // The two counts must take their arguments in OPPOSITE orders, and the
    // product on the right must be `mul x1 x0` (i.e. `n*m`), not `mul x0 x1`.
    // No numeral check sees either: at a symmetric pair both spellings agree.
    assert_eq!(
        EXPECTED_EVEN.matches("AxNat.gaussNegCount").count(),
        2,
        "both counts must survive in the statement"
    );
    assert!(
        EXPECTED_EVEN.ends_with("(AxNat.mul x1 x0)))))"),
        "the right-hand product is `n*m`, in that order"
    );
    assert!(
        !EXPECTED_EVEN.contains("(AxNat.mul x0 x1)"),
        "and never `m*n`"
    );
}

const EXPECTED_EVEN: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : Eq.{1} AxNat (AxNat.gcd (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) (AxNat.succ AxNat.zero)) -> AxNat.Even (AxNat.add (AxNat.add (AxNat.gaussNegCount (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) x0) (AxNat.gaussNegCount (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) x1)) (AxNat.mul x1 x0)))))";
const EXPECTED_MOD_EQ: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : Eq.{1} AxNat (AxNat.gcd (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) (AxNat.succ AxNat.zero)) -> AxNat.modEq (AxNat.succ (AxNat.succ AxNat.zero)) (AxNat.add (AxNat.gaussNegCount (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) x0) (AxNat.gaussNegCount (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) x1)) (AxNat.mul x1 x0))))";
