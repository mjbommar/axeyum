//! Statement pins, application tests and negative controls for
//! [`super::fermat_two_squares`] — Fermat's theorem on sums of two squares and
//! the four pieces of Euler's descent it assembles (ADR-1650).
//!
//! Three batteries, each asserting what must hold AND what must fail, so no run
//! can be vacuous:
//!
//! 1. **the every-declaration sweep** — each of the twelve names is in the
//!    environment, is a checked `Theorem`, and rests on no axiom. The
//!    `Environment::contains` assertion comes FIRST, because
//!    `axiom_footprint` of a name the environment does not hold is *also*
//!    empty: without it the sweep would pass for a declaration never made.
//! 2. **the statement pin** — every one of the twelve has its full
//!    `∀`-telescoped type rebuilt here and compared against the type the
//!    ENVIRONMENT stores. This is the guard that survives a mutation which
//!    still type-checks: a hypothesis dropped, a bound relaxed, a `<` softened
//!    to `≤` leaves the prelude building and is invisible to the sweep above.
//!    The mutation table in the lane report is measured against this test.
//! 3. **application at `p = 5, 13, 17`** — `Int.fermatTwoSquares` is applied at
//!    `m = 2, 6, 8` and the instantiated type is required to be exactly
//!    `Int.IsSumOfTwoSquares (Int.ofNat p)`. The `Nat.Even m` hypothesis is a
//!    REAL witness (`Even n := ∃ k, n = k + k`, closed by `Eq.refl`); only the
//!    primality condition is a free variable in a `LocalContext`, because the
//!    conclusion's type does not depend on which proof inhabits it. Two
//!    refusals accompany it: the instantiation at `m = 2` must NOT be
//!    `IsSumOfTwoSquares (ofNat 7)`, and `Even 2`'s witness must NOT be
//!    accepted where `Even 6` is demanded — without those halves an
//!    application test only says the theorem has enough arguments.
//!
//! Magnitudes are deliberately tiny: `Nat` numerals here are unary and cost is
//! superlinear in the largest magnitude formed. The largest number formed
//! anywhere in this file is `17`.

use super::ops::IntDev;
use super::two_squares::imodeq;
use crate::NameId;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;
use crate::{BinderInfo, IntPrelude, Kernel, LocalContext, LocalDecl, build_int_prelude};

// ---------------------------------------------------------------------------
// plumbing
// ---------------------------------------------------------------------------

/// Every declaration `fermat_two_squares.rs` makes, in registration order.
fn owned_names(p: &IntPrelude) -> [NameId; 12] {
    [
        p.dvd_zero,
        p.dvd_of_mod_eq_zero,
        p.mul_mod_eq_zero,
        p.sq_add_sq_mod_eq_of_mod_eq,
        p.exists_next_multiplier,
        p.sq_mul_add_sq_mul,
        p.dvd_of_degenerate_descent,
        p.lt_of_nat_of_lt,
        p.le_two_of_nat_le_two,
        p.not_dvd_of_nat_of_prime_of_lt,
        p.exists_sum_of_two_squares_of_multiple,
        p.fermat_two_squares,
    ]
}

/// The type the environment stores for `name`.
fn stored_type(k: &Kernel, name: NameId) -> ExprId {
    match k
        .environment()
        .get(name)
        .expect("the declaration must be present")
    {
        Declaration::Theorem { ty, .. }
        | Declaration::Definition { ty, .. }
        | Declaration::Axiom { ty, .. }
        | Declaration::Opaque { ty, .. } => *ty,
        other => panic!("unexpected declaration kind: {other:?}"),
    }
}

/// `∀ (x_0 … x_{arity-1} : Int), build(x_0, …)` — the shape
/// `IntDev::int_theorem` wraps a statement in.
fn int_forall(
    d: &mut IntDev<'_>,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
) -> ExprId {
    let int_ty = d.int_ty();
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let mut ty = build(d, &vars);
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, int_ty, ty);
    }
    ty
}

/// `∀ (x_0 … x_{arity-1} : Nat), build(x_0, …)` — the shape `NatOps::theorem`
/// wraps a statement in.
fn nat_forall(
    d: &mut IntDev<'_>,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
    let vars: Vec<ExprId> = fvs.iter().map(|&f| d.kernel().fvar(f)).collect();
    let mut ty = build(d, &vars);
    for &fv in fvs.iter().rev() {
        ty = d.pi_fv(fv, nat, ty);
    }
    ty
}

/// The chained arrow `tys[0] → … → tys[n-1] → concl`.
fn arrows(d: &mut IntDev<'_>, tys: &[ExprId], concl: ExprId) -> ExprId {
    let mut ty = concl;
    for &hyp in tys.iter().rev() {
        ty = d.arrow(hyp, ty);
    }
    ty
}

/// `mul c c + mul e e`.
fn measure(d: &mut IntDev<'_>, c: ExprId, e: ExprId) -> ExprId {
    let cc = d.imul(c, c);
    let ee = d.imul(e, e);
    d.iadd(cc, ee)
}

/// `∃ a, ∃ b, Eq Int lhs (a*a + b*b)`.
fn exists_norm(d: &mut IntDev<'_>, lhs: ExprId) -> ExprId {
    let int_ty = d.int_ty();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let inner = {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let sum = measure(d, a, b);
        let body = d.ieq(lhs, sum);
        d.lam_fv(b_fv, int_ty, body)
    };
    let body = super::two_squares::int_exists(d, inner);
    let outer = d.lam_fv(a_fv, int_ty, body);
    super::two_squares::int_exists(d, outer)
}

/// A real proof of `Nat.Even value` at an EVEN numeral: `Nat.Even n` is
/// `∃ k, n = k + k`, `Nat.add k k` reduces at a numeral, so the equation is
/// `Eq.refl` and the witness is `value / 2`.
///
/// The parameter is the number whose evenness is claimed, NOT its half. That
/// distinction is what the first version of this file got wrong: the theorem's
/// hypothesis is `Nat.Even m` for the `m` in `p = 2m+1`, so at `p = 5` it wants
/// `Even 2` and not `Even 4`, and the kernel refused the whole application with
/// a bare `TypeMismatch` naming two `ExprId`s. The refusal was diagnosed by
/// handing the SAME argument pair to `Int.firstSupplementaryLawResidue`, an
/// existing declaration this lane did not touch, and watching it fail
/// identically -- which located the defect in the test rather than the theorem.
fn even_witness(d: &mut IntDev<'_>, value: u32) -> ExprId {
    assert_eq!(value % 2, 0, "even_witness is only for an even numeral");
    let nat = d.nat_ty();
    let one = d.level_one();
    let p = d.int();
    let target = d.num(value);
    let k = d.num(value / 2);
    let predicate = {
        let k_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(k_fv);
        let sum = d.add(bound, bound);
        let body = d.eq(target, sum);
        d.lam_fv(k_fv, nat, body)
    };
    // `Nat.add k k` reduces to the numeral, so `Eq.refl` closes the equation
    // the predicate demands (`Eq target (add k k)`) up to iota.
    let equation = {
        let eq_refl = d.int().logic.eq_refl;
        let refl = d.kernel().const_(eq_refl, vec![one]);
        d.apply(refl, &[nat, target])
    };
    let intro_name = p.logic.exists_intro;
    let intro = d.kernel().const_(intro_name, vec![one]);
    d.apply(intro, &[nat, predicate, k, equation])
}

// ---------------------------------------------------------------------------
// 1. the every-declaration sweep
// ---------------------------------------------------------------------------

/// Each name is in the environment, is a checked `Theorem`, and rests on no
/// axiom.
///
/// `Environment::contains` is asserted FIRST on purpose: `axiom_footprint` of
/// an absent name is also empty, so an axiom-freedom assertion alone would
/// pass for a declaration that was never made.
#[test]
fn every_declaration_is_a_checked_axiom_free_theorem() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut checked = 0_usize;
    for name in owned_names(&p) {
        assert!(
            k.environment().contains(name),
            "{} is not in the environment",
            k.display_name(name)
        );
        assert!(
            matches!(
                k.environment().get(name).unwrap(),
                Declaration::Theorem { .. }
            ),
            "{} should be a checked Theorem",
            k.display_name(name)
        );
        assert!(
            k.axiom_footprint(name).is_empty(),
            "{} should rest on no axiom, but rests on {:?}",
            k.display_name(name),
            k.axiom_footprint(name)
                .iter()
                .map(|a| k.display_name(*a).to_string())
                .collect::<Vec<_>>()
        );
        checked += 1;
    }
    assert_eq!(checked, 12, "the sweep must inspect every owned name");
}

// ---------------------------------------------------------------------------
// 2. the statement pin
// ---------------------------------------------------------------------------

/// Every declaration states exactly the proposition this test rebuilds —
/// checked against the type the ENVIRONMENT stores, never against the source
/// text.
///
/// This is the guard that survives a mutation which still type-checks. The
/// axiom-footprint sweep above cannot see a dropped hypothesis or a weakened
/// bound; `def_eq` against a separately built type can.
#[test]
#[allow(clippy::too_many_lines)]
fn fermat_two_squares_declarations_state_the_intended_types() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let mut checked = 0_usize;
    let mut check = |d: &mut IntDev<'_>, label: &str, name: NameId, expected: ExprId| {
        let stored = stored_type(d.kernel(), name);
        assert!(
            d.kernel().def_eq(stored, expected),
            "{label} does not state the intended proposition"
        );
        checked += 1;
    };

    // dvd_zero : ∀ a, dvd a 0
    let expected = int_forall(&mut d, 1, &|d, v| {
        let zero = d.izero();
        super::dvd::idvd(d, v[0], zero)
    });
    check(&mut d, "Int.dvd_zero", p.dvd_zero, expected);

    // dvd_of_modEq_zero : ∀ n a, ModEq n a 0 → dvd n a
    let expected = int_forall(&mut d, 2, &|d, v| {
        let zero = d.izero();
        let hyp = imodeq(d, v[0], v[1], zero);
        let concl = super::dvd::idvd(d, v[0], v[1]);
        d.arrow(hyp, concl)
    });
    check(
        &mut d,
        "Int.dvd_of_modEq_zero",
        p.dvd_of_mod_eq_zero,
        expected,
    );

    // mul_modEq_zero : ∀ m x, ModEq m (m*x) 0
    let expected = int_forall(&mut d, 2, &|d, v| {
        let zero = d.izero();
        let mx = d.imul(v[0], v[1]);
        imodeq(d, v[0], mx, zero)
    });
    check(&mut d, "Int.mul_modEq_zero", p.mul_mod_eq_zero, expected);

    // sq_add_sq_modEq_of_modEq :
    //   ∀ m a b c e, ModEq m c a → ModEq m e b → ModEq m (c²+e²) (a²+b²)
    let expected = int_forall(&mut d, 5, &|d, v| {
        let (m, a, b, c, e) = (v[0], v[1], v[2], v[3], v[4]);
        let hc = imodeq(d, m, c, a);
        let he = imodeq(d, m, e, b);
        let source = measure(d, c, e);
        let target = measure(d, a, b);
        let concl = imodeq(d, m, source, target);
        arrows(d, &[hc, he], concl)
    });
    check(
        &mut d,
        "Int.sq_add_sq_modEq_of_modEq",
        p.sq_add_sq_mod_eq_of_mod_eq,
        expected,
    );

    // exists_next_multiplier : ∀ m p a b c e,
    //   m*p = a²+b² → ModEq m c a → ModEq m e b → ∃ q, m*q = c²+e²
    let expected = int_forall(&mut d, 6, &|d, v| {
        let (m, pp, a, b, c, e) = (v[0], v[1], v[2], v[3], v[4], v[5]);
        let mp = d.imul(m, pp);
        let norm = measure(d, a, b);
        let hfact = d.ieq(mp, norm);
        let hc = imodeq(d, m, c, a);
        let he = imodeq(d, m, e, b);
        let int_ty = d.int_ty();
        let predicate = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let mq = d.imul(m, q);
            let s = measure(d, c, e);
            let body = d.ieq(mq, s);
            d.lam_fv(q_fv, int_ty, body)
        };
        let concl = super::two_squares::int_exists(d, predicate);
        arrows(d, &[hfact, hc, he], concl)
    });
    check(
        &mut d,
        "Int.exists_next_multiplier",
        p.exists_next_multiplier,
        expected,
    );

    // sq_mul_add_sq_mul : ∀ m u v, (m*u)² + (m*v)² = m*(m*(u²+v²))
    let expected = int_forall(&mut d, 3, &|d, v| {
        let (m, u, w) = (v[0], v[1], v[2]);
        let mu = d.imul(m, u);
        let mw = d.imul(m, w);
        let lhs = measure(d, mu, mw);
        let inner = measure(d, u, w);
        let once = d.imul(m, inner);
        let rhs = d.imul(m, once);
        d.ieq(lhs, rhs)
    });
    check(
        &mut d,
        "Int.sq_mul_add_sq_mul",
        p.sq_mul_add_sq_mul,
        expected,
    );

    // dvd_of_degenerate_descent : ∀ m p a b c e, m ≠ 0 → m*p = a²+b² →
    //   ModEq m c a → ModEq m e b → c²+e² = 0 → dvd m p
    let expected = int_forall(&mut d, 6, &|d, v| {
        let (m, pp, a, b, c, e) = (v[0], v[1], v[2], v[3], v[4], v[5]);
        let zero = d.izero();
        let m_zero = d.ieq(m, zero);
        let hm = d.not(m_zero);
        let mp = d.imul(m, pp);
        let norm = measure(d, a, b);
        let hfact = d.ieq(mp, norm);
        let hc = imodeq(d, m, c, a);
        let he = imodeq(d, m, e, b);
        let s = measure(d, c, e);
        let hz = d.ieq(s, zero);
        let concl = super::dvd::idvd(d, m, pp);
        arrows(d, &[hm, hfact, hc, he, hz], concl)
    });
    check(
        &mut d,
        "Int.dvd_of_degenerate_descent",
        p.dvd_of_degenerate_descent,
        expected,
    );

    // lt_ofNat_of_lt : ∀ (a b : Nat), Nat.lt a b → Int.lt (ofNat a) (ofNat b)
    let expected = nat_forall(&mut d, 2, &|d, v| {
        let hyp = d.lt(v[0], v[1]);
        let lhs = d.of_nat(v[0]);
        let rhs = d.of_nat(v[1]);
        let concl = d.ilt(lhs, rhs);
        d.arrow(hyp, concl)
    });
    check(&mut d, "Int.lt_ofNat_of_lt", p.lt_of_nat_of_lt, expected);

    // le_two_of_nat_le_two : ∀ (k : Nat), Nat.le 2 k → Int.le (1+1) (ofNat k)
    let expected = nat_forall(&mut d, 1, &|d, v| {
        let two_nat = d.num(2);
        let hyp = d.le(two_nat, v[0]);
        let one = d.ione();
        let two_int = d.iadd(one, one);
        let coerced = d.of_nat(v[0]);
        let concl = d.ile(two_int, coerced);
        d.arrow(hyp, concl)
    });
    check(
        &mut d,
        "Int.le_two_of_nat_le_two",
        p.le_two_of_nat_le_two,
        expected,
    );

    // not_dvd_ofNat_of_prime_of_lt : ∀ (p n : Nat), <p prime> → 1 < n → n < p →
    //   Not (dvd (ofNat n) (ofNat p))
    let expected = nat_forall(&mut d, 2, &|d, v| {
        let (pn, n) = (v[0], v[1]);
        let one_nat = d.num(1);
        let prime = super::wilson::prime_condition(d, pn);
        let hgt = d.lt(one_nat, n);
        let hlt = d.lt(n, pn);
        let coerced_n = d.of_nat(n);
        let coerced_p = d.of_nat(pn);
        let dvd = super::dvd::idvd(d, coerced_n, coerced_p);
        let concl = d.not(dvd);
        arrows(d, &[prime, hgt, hlt], concl)
    });
    check(
        &mut d,
        "Int.not_dvd_ofNat_of_prime_of_lt",
        p.not_dvd_of_nat_of_prime_of_lt,
        expected,
    );

    // exists_sum_of_two_squares_of_multiple : ∀ (p : Nat), <p prime> →
    //   ∀ (n : Nat), 0 < n → n < p → (∃ a b, (ofNat n)*(ofNat p) = a²+b²) →
    //   IsSumOfTwoSquares (ofNat p)
    let expected = nat_forall(&mut d, 1, &|d, v| {
        let pn = v[0];
        let nat = d.nat_ty();
        let prime = super::wilson::prime_condition(d, pn);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let zero_nat = d.num(0);
        let positive = d.lt(zero_nat, n);
        let below = d.lt(n, pn);
        let m = d.of_nat(n);
        let pp = d.of_nat(pn);
        let mp = d.imul(m, pp);
        let hypothesis = exists_norm(d, mp);
        let concl = super::two_squares::is_sum_of_two_squares(d, pp);
        let inner = arrows(d, &[positive, below, hypothesis], concl);
        let with_n = d.pi_fv(n_fv, nat, inner);
        d.arrow(prime, with_n)
    });
    check(
        &mut d,
        "Int.exists_sum_of_two_squares_of_multiple",
        p.exists_sum_of_two_squares_of_multiple,
        expected,
    );

    // fermatTwoSquares : ∀ (m : Nat), <succ (2*m) prime> → Nat.Even m →
    //   IsSumOfTwoSquares (ofNat (succ (2*m)))
    let expected = nat_forall(&mut d, 1, &|d, v| {
        let m = v[0];
        let np = d.prelude();
        let two_nat = d.num(2);
        let doubled = d.mul(two_nat, m);
        let pn = d.succ(doubled);
        let pp = d.of_nat(pn);
        let prime = super::wilson::prime_condition(d, pn);
        let even = d.const_app(np.even, &[m]);
        let concl = super::two_squares::is_sum_of_two_squares(d, pp);
        arrows(d, &[prime, even], concl)
    });
    check(
        &mut d,
        "Int.fermatTwoSquares",
        p.fermat_two_squares,
        expected,
    );

    assert_eq!(checked, 12, "the pin must cover every owned declaration");
}

// ---------------------------------------------------------------------------
// 3. application at p = 5, 13, 17
// ---------------------------------------------------------------------------

/// `Int.fermatTwoSquares` applied at `m`, with a real `Nat.Even m` witness and
/// the primality condition as a free variable registered in a `LocalContext`.
///
/// Returns the instantiated type the kernel infers.
fn fermat_at(d: &mut IntDev<'_>, m_value: u32) -> ExprId {
    let p = d.int();
    let m = d.num(m_value);
    let two_nat = d.num(2);
    let doubled = d.mul(two_nat, m);
    let pn = d.succ(doubled);

    let prime_ty = super::wilson::prime_condition(d, pn);
    let prime_fv = d.fresh_fvar();
    let prime_proof = d.kernel().fvar(prime_fv);
    let even = even_witness(d, m_value);

    let head = d.const_app(p.fermat_two_squares, &[m]);
    let applied = d.apply(head, &[prime_proof, even]);

    let anon = d.anon_name();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: prime_fv,
        name: anon,
        ty: prime_ty,
        info: BinderInfo::Default,
    });
    d.kernel()
        .infer_in(applied, &mut ctx)
        .expect("Int.fermatTwoSquares must apply at a concrete even m")
}

/// `Int.IsSumOfTwoSquares (Int.ofNat value)`.
fn sum_of_two_squares_at(d: &mut IntDev<'_>, value: u32) -> ExprId {
    let n = d.num(value);
    let coerced = d.of_nat(n);
    super::two_squares::is_sum_of_two_squares(d, coerced)
}

/// The theorem instantiates to exactly `IsSumOfTwoSquares (ofNat p)` at
/// `p = 5, 13, 17` — the three smallest primes congruent to `1 (mod 4)`.
///
/// `Nat.Even m` is discharged by a REAL witness at each; only primality is a
/// free variable, and it may be, because the instantiated conclusion does not
/// depend on which proof inhabits it (the same construction
/// `coprime_factorial_of_lt_prime_computes_at_pp_seven_m_four` uses).
#[test]
fn fermat_two_squares_instantiates_at_five_thirteen_and_seventeen() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let mut checked = 0_usize;
    for (m_value, prime) in [(2_u32, 5_u32), (6, 13), (8, 17)] {
        let inferred = fermat_at(&mut d, m_value);
        let expected = sum_of_two_squares_at(&mut d, prime);
        assert!(
            d.kernel().def_eq(inferred, expected),
            "Int.fermatTwoSquares at m = {m_value} must conclude \
             Int.IsSumOfTwoSquares (ofNat {prime})"
        );
        checked += 1;
    }
    assert_eq!(checked, 3, "all three primes must have been instantiated");
}

/// The REFUSAL half of the test above, in two directions.
///
/// Without these, the instantiation test says only that the theorem has enough
/// arguments and that its conclusion is *some* `IsSumOfTwoSquares`.
#[test]
fn fermat_two_squares_instantiation_is_discriminating() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    // The conclusion at `m = 2` is about `5`, not about any other number.
    let inferred = fermat_at(&mut d, 2);
    for wrong in [3_u32, 7, 13] {
        let other = sum_of_two_squares_at(&mut d, wrong);
        assert!(
            !d.kernel().def_eq(inferred, other),
            "Int.fermatTwoSquares at m = 2 must NOT conclude \
             Int.IsSumOfTwoSquares (ofNat {wrong})"
        );
    }

    // `Nat.Even 2`'s witness is not a proof of `Nat.Even 6`: the parity
    // hypothesis is load-bearing, not decorative.
    let m = d.num(6);
    let two_nat = d.num(2);
    let doubled = d.mul(two_nat, m);
    let pn = d.succ(doubled);
    let prime_ty = super::wilson::prime_condition(&mut d, pn);
    let prime_fv = d.fresh_fvar();
    let prime_proof = d.kernel().fvar(prime_fv);
    let wrong_even = even_witness(&mut d, 2);
    let head = d.const_app(p.fermat_two_squares, &[m]);
    let applied = d.apply(head, &[prime_proof, wrong_even]);

    let anon = d.anon_name();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: prime_fv,
        name: anon,
        ty: prime_ty,
        info: BinderInfo::Default,
    });
    assert!(
        d.kernel().infer_in(applied, &mut ctx).is_err(),
        "Int.fermatTwoSquares must REFUSE Nat.Even 2's witness where \
         Nat.Even 6 is demanded"
    );
}

/// `Int.fermatTwoSquares` takes the SAME primality condition
/// `Int.firstSupplementaryLawResidue` does — the composition claim ADR-1650
/// makes, checked against both stored types rather than asserted in prose.
///
/// If either statement's primality spelling drifted, the descent would still
/// build and the theorem would still be true; it would simply no longer be
/// reachable from the residue half, which is the only route this development
/// has to it.
#[test]
fn fermat_shares_the_residue_law_hypotheses() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let mut d = IntDev::new(&mut k, p);

    let m = d.num(2);
    let two_nat = d.num(2);
    let doubled = d.mul(two_nat, m);
    let pn = d.succ(doubled);

    let prime_ty = super::wilson::prime_condition(&mut d, pn);
    let prime_fv = d.fresh_fvar();
    let prime_proof = d.kernel().fvar(prime_fv);
    let even = even_witness(&mut d, 2);

    let anon = d.anon_name();
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: prime_fv,
        name: anon,
        ty: prime_ty,
        info: BinderInfo::Default,
    });

    // The very same two arguments feed both theorems.
    let residue_head = d.const_app(p.first_supplementary_law_residue, &[m]);
    let residue = d.apply(residue_head, &[prime_proof, even]);
    let residue_ty = d
        .kernel()
        .infer_in(residue, &mut ctx)
        .expect("Int.firstSupplementaryLawResidue must accept the same pair");

    let fermat_head = d.const_app(p.fermat_two_squares, &[m]);
    let fermat = d.apply(fermat_head, &[prime_proof, even]);
    let fermat_ty = d
        .kernel()
        .infer_in(fermat, &mut ctx)
        .expect("Int.fermatTwoSquares must accept the same pair");

    // …and they say different things, so this is not a vacuous comparison.
    assert!(
        !d.kernel().def_eq(residue_ty, fermat_ty),
        "the residue law and Fermat's theorem must have DIFFERENT conclusions"
    );
    let expected = sum_of_two_squares_at(&mut d, 5);
    assert!(
        d.kernel().def_eq(fermat_ty, expected),
        "Fermat's conclusion at m = 2 must be IsSumOfTwoSquares (ofNat 5)"
    );
}
