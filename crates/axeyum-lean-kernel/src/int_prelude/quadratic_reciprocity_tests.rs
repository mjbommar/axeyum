//! Tests for [`super::quadratic_reciprocity`] — the law, the Legendre symbol
//! it is stated over, and that symbol's Euler-criterion specification.
//!
//! In its own file rather than appended to `int_prelude_tests.rs`, which is a
//! 6,000-line file every `Int` lane appends to (`CLAUDE.md` records what two
//! lanes editing one Rust file costs). The same reason `sum_maps_tests.rs`
//! gives.
//!
//! # What has to be checked, and why
//!
//! **`Int.legendreSym` is a `Definition`, so the trusted gate cannot tell you
//! it is wrong.** `Nat -> Nat -> Int` is that type whatever the body returns.
//! So the symbol is REDUCED at concrete arguments and compared against values
//! computed here in Rust from `gaussNegCount`'s own definition, at multipliers
//! whose counts have OPPOSITE parity, so a wrong body cannot agree by accident.
//!
//! For the law itself the interesting failure is different: `(-1)^k` takes
//! only two values, so **half of all wrong statements evaluate correctly at
//! any single pair**. The instances below therefore span both signs, and each
//! asserts that the OTHER sign is rejected.
//!
//! # The instantiation table
//!
//! Computed here in Rust and cross-checked in Python before any kernel term
//! was built. `N_p := gaussNegCount p q m`, `N_q := gaussNegCount q p n`,
//! `m := (p-1)/2`, `n := (q-1)/2`.
//!
//! | `p` | `q` | `m` | `n` | `N_p` | `N_q` | `n·m` | `(q|p)·(p|q)` |
//! | --- | --- | --- | --- | --- | --- | --- | --- |
//! | 3 | 5 | 1 | 2 | 1 | 1 | 2 | `+1` |
//! | 5 | 7 | 2 | 3 | 1 | 1 | 6 | `+1` |
//! | 3 | 7 | 1 | 3 | 0 | 1 | 3 | `-1` |
//! | 5 | 13 | 2 | 6 | 1 | 3 | 12 | `+1` |
//! | 13 | 17 | 6 | 8 | 4 | 4 | 48 | `+1` |
//!
//! **The brief this lane worked from predicted `-1` at `(3,5)` and `(5,7)`;
//! both are `+1`.** The product is `-1` exactly when BOTH primes are `3 mod
//! 4`, and `5 ≡ 1`. Only `(3,7)` in that list is the `-1` case, which is why
//! `(7,11)` was added to the Rust-side table — a second `-1` instance, so the
//! negative sign is not carried by one row.

use crate::env::Declaration;
use crate::nat_prelude::NatOps;
use crate::{ExprId, IntPrelude, Kernel, build_int_prelude};

use super::ops::IntDev;

/// `Nat.gaussNegCount pp a m := countRange (fun j => ble (succ (div pp 2))
/// (mod (mul a (succ j)) pp)) m` — re-implemented from the definitions.
fn gauss_neg_count(pp: u32, a: u32, m: u32) -> u32 {
    (0..m)
        .filter(|j| (a * (j + 1)) % pp > pp / 2)
        .count()
        .try_into()
        .expect("the count fits")
}

/// `(m, n)` for the odd pair `(2m+1, 2n+1)`. Every entry is a pair of
/// distinct odd primes; the largest magnitude formed is `17*6 = 102`, and
/// every numeral in this kernel is unary.
const PAIRS: [(u32, u32); 5] = [(1, 2), (2, 3), (1, 3), (2, 6), (6, 8)];

fn fixture() -> (Kernel, IntPrelude) {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    (k, p)
}

/// `Int.one` or `Int.neg Int.one`, as the sign `s` in `{1, -1}` says.
fn sign_term(d: &mut IntDev<'_>, s: i32) -> ExprId {
    let one = d.ione();
    if s >= 0 { one } else { d.ineg(one) }
}

/// **The definition computes what its name claims**, at multipliers whose
/// counts have opposite parity so a wrong body cannot pass by luck.
///
/// | `m` | `p = 2m+1` | `a` | `gaussNegCount p a m` | `legendreSym m a` |
/// | --- | --- | --- | --- | --- |
/// | 3 | 7 | 3 | 1 (odd) | `-1` |
/// | 3 | 7 | 2 | 2 (even) | `+1` |
/// | 6 | 13 | 17 | 4 (even) | `+1` |
/// | 1 | 3 | 7 | 0 (even) | `+1` |
#[test]
fn the_legendre_symbol_computes_at_both_parities() {
    let (mut k, p) = fixture();
    let mut d = IntDev::new(&mut k, p);

    for (m_val, a_val) in [(3_u32, 3_u32), (3, 2), (6, 17), (1, 7)] {
        let pp = 2 * m_val + 1;
        let count = gauss_neg_count(pp, a_val, m_val);
        let want = if count.is_multiple_of(2) { 1 } else { -1 };

        let m = d.num(m_val);
        let a = d.num(a_val);
        let leg = d.const_app(p.legendre_sym, &[m, a]);
        let expected = sign_term(&mut d, want);
        assert!(
            d.kernel().def_eq(leg, expected),
            "legendreSym {m_val} {a_val} must reduce to {want} (count {count})"
        );
        let wrong = sign_term(&mut d, -want);
        assert!(
            !d.kernel().def_eq(leg, wrong),
            "and must reject the opposite sign"
        );
    }

    // The two multipliers at `p = 7` really do differ, so the table above is
    // not four copies of one case.
    assert_ne!(gauss_neg_count(7, 3, 3) % 2, gauss_neg_count(7, 2, 3) % 2);
}

/// **The law**, instantiated at five prime pairs, with the coprimality
/// hypothesis discharged by `Eq.refl` (so `Nat.gcd` really does reduce), the
/// inferred conclusion matched against a separately built expected term, and
/// both sides reduced to a sign that rejects its opposite.
#[test]
fn the_law_applies_and_computes_at_five_prime_pairs() {
    let (mut k, p) = fixture();
    let mut d = IntDev::new(&mut k, p);

    let mut seen_minus = 0_u32;
    for (m_val, n_val) in PAIRS {
        let (pp_val, q_val) = (2 * m_val + 1, 2 * n_val + 1);
        let n_p = gauss_neg_count(pp_val, q_val, m_val);
        let n_q = gauss_neg_count(q_val, pp_val, n_val);
        let want = if (n_p + n_q).is_multiple_of(2) { 1 } else { -1 };
        if want < 0 {
            seen_minus += 1;
        }
        // The law's own right-hand side, computed independently.
        assert_eq!(
            want,
            if (n_val * m_val).is_multiple_of(2) {
                1
            } else {
                -1
            },
            "reciprocity must hold in Rust at ({pp_val}, {q_val})"
        );

        let m = d.num(m_val);
        let n = d.num(n_val);
        let one_nat = d.num(1);
        let cop = d.refl(one_nat);
        let instance = d.lemma(p.quadratic_reciprocity, &[m, n, cop]);
        let inferred = d
            .kernel()
            .infer(instance)
            .unwrap_or_else(|e| panic!("the law must apply at ({pp_val}, {q_val}): {e:?}"));

        // The expected conclusion, built from the definition rather than
        // copied from the declaration.
        let two = d.num(2);
        let ap = d.mul(two, m);
        let pp = d.succ(ap);
        let aq = d.mul(two, n);
        let q = d.succ(aq);
        let leg_p = d.const_app(p.legendre_sym, &[m, q]);
        let leg_q = d.const_app(p.legendre_sym, &[n, pp]);
        let lhs = d.imul(leg_p, leg_q);
        let t = d.mul(n, m);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);
        let rhs = d.ipow(neg_one, t);
        let expected = d.ieq(lhs, rhs);
        assert!(
            d.kernel().def_eq(inferred, expected),
            "at ({pp_val}, {q_val}) the conclusion is not the reciprocity law"
        );

        // Both sides reduce to the same sign, and reject the other one.
        let want_term = sign_term(&mut d, want);
        assert!(
            d.kernel().def_eq(lhs, want_term),
            "the Legendre product must reduce to {want} at ({pp_val}, {q_val})"
        );
        assert!(
            d.kernel().def_eq(rhs, want_term),
            "and so must (-1)^(n*m) at ({pp_val}, {q_val})"
        );
        let wrong = sign_term(&mut d, -want);
        assert!(
            !d.kernel().def_eq(lhs, wrong),
            "and the opposite sign must be rejected at ({pp_val}, {q_val})"
        );
    }
    assert_eq!(seen_minus, 1, "exactly (3,7) is the -1 case in PAIRS");
}

/// A second `-1` instance, so the negative sign is not carried by one row:
/// `(p, q) = (7, 11)`, where `N_p = 2`, `N_q = 3` and `n·m = 15`.
#[test]
fn the_law_applies_at_a_second_negative_pair() {
    let (mut k, p) = fixture();
    let mut d = IntDev::new(&mut k, p);
    let (m_val, n_val) = (3_u32, 5_u32);
    assert_eq!(gauss_neg_count(7, 11, 3), 2);
    assert_eq!(gauss_neg_count(11, 7, 5), 3);

    let m = d.num(m_val);
    let n = d.num(n_val);
    let one_nat = d.num(1);
    let cop = d.refl(one_nat);
    let instance = d.lemma(p.quadratic_reciprocity, &[m, n, cop]);
    d.kernel()
        .infer(instance)
        .expect("the law must apply at (7, 11)");

    let two = d.num(2);
    let ap = d.mul(two, m);
    let pp = d.succ(ap);
    let aq = d.mul(two, n);
    let q = d.succ(aq);
    let leg_p = d.const_app(p.legendre_sym, &[m, q]);
    let leg_q = d.const_app(p.legendre_sym, &[n, pp]);
    let lhs = d.imul(leg_p, leg_q);
    let minus = sign_term(&mut d, -1);
    assert!(
        d.kernel().def_eq(lhs, minus),
        "(11|7)*(7|11) must be -1: both are 3 mod 4"
    );
    let plus = sign_term(&mut d, 1);
    assert!(!d.kernel().def_eq(lhs, plus), "and must reject +1");
}

/// **Coprimality is load-bearing.** At `(m, n) = (1, 1)` — `p = q = 3`,
/// `gcd 3 3 = 3` — the law's two sides are `+1` and `-1`, so the statement is
/// FALSE there and the hypothesis is not decoration.
///
/// Recorded SURVIVOR: `(m, n) = (2, 2)` (`p = q = 5`) is equally non-coprime
/// and the two sides AGREE at `+1`, so a control drawn at that pair would pass
/// while separating nothing.
#[test]
fn the_coprimality_hypothesis_is_load_bearing() {
    let (mut k, p) = fixture();
    let mut d = IntDev::new(&mut k, p);

    // In Rust first.
    assert_eq!(gauss_neg_count(3, 3, 1) + gauss_neg_count(3, 3, 1), 0);
    assert!(!(1_u32).is_multiple_of(2), "n*m = 1*1 is odd at (1,1)");

    let m = d.num(1);
    let n = d.num(1);
    let two = d.num(2);
    let ap = d.mul(two, m);
    let pp = d.succ(ap);
    let aq = d.mul(two, n);
    let q = d.succ(aq);
    let leg_p = d.const_app(p.legendre_sym, &[m, q]);
    let leg_q = d.const_app(p.legendre_sym, &[n, pp]);
    let lhs = d.imul(leg_p, leg_q);
    let t = d.mul(n, m);
    let one_i = d.ione();
    let neg_one = d.ineg(one_i);
    let rhs = d.ipow(neg_one, t);

    let plus = sign_term(&mut d, 1);
    let minus = sign_term(&mut d, -1);
    assert!(
        d.kernel().def_eq(lhs, plus),
        "the Legendre product is +1 at p = q = 3"
    );
    assert!(
        d.kernel().def_eq(rhs, minus),
        "but (-1)^(1*1) is -1 at p = q = 3"
    );
    assert!(
        !d.kernel().def_eq(lhs, rhs),
        "so the law is FALSE at a non-coprime pair"
    );

    // The survivor.
    let two_e = d.num(2);
    let m2 = two_e;
    let ap2 = d.mul(two, m2);
    let pp2 = d.succ(ap2);
    let leg_a = d.const_app(p.legendre_sym, &[m2, pp2]);
    let leg_b = d.const_app(p.legendre_sym, &[m2, pp2]);
    let lhs2 = d.imul(leg_a, leg_b);
    let t2 = d.mul(m2, m2);
    let rhs2 = d.ipow(neg_one, t2);
    assert!(
        d.kernel().def_eq(lhs2, rhs2),
        "survivor: at p = q = 5 the two sides agree, so this pair separates nothing"
    );
}

/// The symbol's Euler-criterion specification, checked SYMBOLICALLY: the
/// statement's shape, at a free `m` and `a`, is Gauss's lemma with the count
/// packaged as `legendreSym`. Nothing numeric could see that the modulus is
/// `succ (2*m)` in every occurrence.
#[test]
fn the_symbol_specification_is_gausss_lemma_through_the_definition() {
    let (mut k, p) = fixture();
    let spec = match k
        .environment()
        .get(p.legendre_sym_mod_eq_pow)
        .expect("the spec must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };
    let gauss = match k
        .environment()
        .get(p.gauss_lemma_sign_count)
        .expect("Gauss's lemma must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };
    // They are the SAME proposition — `legendreSym` unfolds to the count.
    assert!(
        k.def_eq(spec, gauss),
        "the spec must be Gauss's lemma read through the definition"
    );
    // And they are not the same TEXT, which is the point of the definition.
    let spec_text = k.render_lean(spec);
    let gauss_text = k.render_lean(gauss);
    assert_ne!(spec_text, gauss_text);
    assert!(spec_text.contains("Int.legendreSym"));
    assert!(!gauss_text.contains("Int.legendreSym"));
}

/// All three declarations rest on zero axioms.
#[test]
fn the_reciprocity_family_rests_on_no_axiom() {
    let (k, p) = fixture();
    for name in [
        p.legendre_sym,
        p.legendre_sym_mod_eq_pow,
        p.quadratic_reciprocity,
    ] {
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            k.display_name(name)
        );
    }
}

/// The declared types and the definition's VALUE, pinned character for
/// character.
///
/// What no numeral can see: that the two symbols take their arguments in
/// OPPOSITE orders (`legendreSym m q` against `legendreSym n p`), that the
/// exponent on the right is `mul x1 x0` rather than `mul x0 x1`, and that the
/// definition's body is `pow (neg one) (gaussNegCount ...)` rather than, say,
/// `pow (neg one) (gaussNegCount ...)` with the modulus and multiplier
/// transposed.
#[test]
fn the_reciprocity_family_states_the_intended_types() {
    let (mut k, p) = fixture();

    let ty_of = |k: &mut Kernel, name| match k.environment().get(name).expect("must be declared") {
        Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => {
            let ty = *ty;
            k.render_lean(ty)
        }
        other => panic!("{other:?} has no type to render"),
    };
    let value_of = |k: &mut Kernel, name| match k.environment().get(name).expect("must be declared")
    {
        Declaration::Definition { value, .. } => {
            let value = *value;
            k.render_lean(value)
        }
        other => panic!("{other:?} is not a definition"),
    };

    assert_eq!(ty_of(&mut k, p.legendre_sym), EXPECTED_SYM_TY);
    assert_eq!(value_of(&mut k, p.legendre_sym), EXPECTED_SYM_VALUE);
    assert_eq!(ty_of(&mut k, p.legendre_sym_mod_eq_pow), EXPECTED_SPEC);
    assert_eq!(ty_of(&mut k, p.quadratic_reciprocity), EXPECTED_LAW);

    assert_eq!(
        EXPECTED_LAW.matches("Int.legendreSym").count(),
        2,
        "both symbols must survive in the law's statement"
    );
    assert!(
        EXPECTED_LAW.contains("(Int.pow (Int.neg Int.one) (AxNat.mul x1 x0))"),
        "the right-hand side is `(-1)^(n*m)`, with the product in that order"
    );
    assert!(
        !EXPECTED_LAW.contains("(AxNat.mul x0 x1)"),
        "and never `m*n`"
    );
}

const EXPECTED_SYM_TY: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> Int))";
const EXPECTED_SYM_VALUE: &str = "fun (x0 : AxNat) => fun (x1 : AxNat) => Int.pow (Int.neg Int.one) (AxNat.gaussNegCount (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)) x1 x0)";
const EXPECTED_SPEC: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : And (AxNat.le (AxNat.succ (AxNat.succ AxNat.zero)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) (((x2 : AxNat) -> ((x3 : AxNat.dvd x2 (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) -> Or (Eq.{1} AxNat x2 (AxNat.succ AxNat.zero)) (Eq.{1} AxNat x2 (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))))))) -> ((x3 : Eq.{1} AxNat (AxNat.gcd x1 (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) (AxNat.succ AxNat.zero)) -> Int.ModEq (Int.ofNat (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) (Int.pow (Int.ofNat x1) x0) (Int.legendreSym x0 x1)))))";
const EXPECTED_LAW: &str = "((x0 : AxNat) -> ((x1 : AxNat) -> ((x2 : Eq.{1} AxNat (AxNat.gcd (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1)) (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0))) (AxNat.succ AxNat.zero)) -> Eq.{1} Int (Int.mul (Int.legendreSym x0 (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x1))) (Int.legendreSym x1 (AxNat.succ (AxNat.mul (AxNat.succ (AxNat.succ AxNat.zero)) x0)))) (Int.pow (Int.neg Int.one) (AxNat.mul x1 x0)))))";
