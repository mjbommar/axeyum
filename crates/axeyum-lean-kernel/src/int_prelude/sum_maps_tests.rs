//! Evaluation tests for [`super::sum_maps`].
//!
//! **The trusted gate cannot tell you a `Definition` is wrong.**
//! `Nat -> Nat -> ((Nat -> Nat) -> Int) -> Int` is that type whatever
//! `Int.sumMaps` returns, so `int_prelude_admits_all_declarations` passing says
//! only that the term is well-formed. Everything below reduces `Int.sumMaps`
//! to a normal form at concrete arguments and compares against a value
//! computed by hand.
//!
//! ## Why these particular arguments
//!
//! A sum over *every* map `[0,m) -> [0,n)` is symmetric under permuting the
//! `m` indices whenever every index draws from the same `[0,n)`. **So no total
//! can discriminate a transposed index**, and a test that varies `g 0` against
//! `g 1` in the summand would look rigorous and measure nothing. Two things are
//! genuinely testable and both are checked:
//!
//! - **Cardinality.** `sumMaps m n (fun _ => 1)` must be `n^m`. This is what
//!   catches a wrong bound, an off-by-one in the recursion, or a `cons` that
//!   fails to extend the map.
//! - **Independence.** `sumMaps 2 3 (fun g => g 0 * g 1)` must be
//!   `(0+1+2)^2 = 9`. An enumeration that walked only the DIAGONAL — the
//!   plausible defect, since the recursion threads one map through two
//!   nested folds — gives `0 + 1 + 4 = 5`, and the two are separated here in
//!   both directions.
//!
//! Every magnitude formed is at most `9`, so none of this touches the unary
//! numeral cost `CLAUDE.md` documents.

use crate::{BinderInfo, ExprId, IntPrelude, Kernel, build_int_prelude};

/// The raw `Nat` numeral `n` — a `zero`/`succ` chain.
///
/// A local copy of `int_prelude_tests`'s private helper rather than a
/// visibility widening: `int_prelude_tests.rs` is a 6,000-line file every
/// `Int` lane appends to, and `CLAUDE.md` records what two lanes editing one
/// Rust file costs. Every magnitude built here is at most `4`.
fn numeral_nat(k: &mut Kernel, p: &IntPrelude, n: u32) -> ExprId {
    let mut nat = k.const_(p.nat.zero, vec![]);
    for _ in 0..n {
        let succ = k.const_(p.nat.succ, vec![]);
        nat = k.app(succ, nat);
    }
    nat
}

/// `Int.ofNat n` for `n >= 0`, `Int.negSucc (-n-1)` for `n < 0` — the unique
/// normal form of the integer `n`. Local copy, same reason as above.
fn numeral(k: &mut Kernel, p: &IntPrelude, n: i32) -> ExprId {
    let magnitude = if n >= 0 {
        u32::try_from(n).expect("non-negative")
    } else {
        u32::try_from(-n - 1).expect("negative")
    };
    let nat = numeral_nat(k, p, magnitude);
    let ctor = if n >= 0 { p.of_nat } else { p.neg_succ };
    let c = k.const_(ctor, vec![]);
    k.app(c, nat)
}

/// `Int.sumMaps m n f` as a term.
fn sum_maps(k: &mut Kernel, p: &IntPrelude, m: u32, n: u32, f: ExprId) -> ExprId {
    let head = k.const_(p.sum_maps, vec![]);
    let m_t = numeral_nat(k, p, m);
    let n_t = numeral_nat(k, p, n);
    let a = k.app(head, m_t);
    let b = k.app(a, n_t);
    k.app(b, f)
}

/// `fun (g : Nat -> Nat) => <body(g)>`, with `g` as de Bruijn index 0.
fn map_lam(k: &mut Kernel, p: &IntPrelude, body: &dyn Fn(&mut Kernel, ExprId) -> ExprId) -> ExprId {
    let anon = k.anon();
    let nat_ty = k.const_(p.nat.nat, vec![]);
    let map_ty = k.pi(anon, nat_ty, nat_ty, BinderInfo::Default);
    let g = k.bvar(0);
    let b = body(k, g);
    k.lam(anon, map_ty, b, BinderInfo::Default)
}

/// `Int.ofNat (g i)` for the bound map `g`.
fn coe_at(k: &mut Kernel, p: &IntPrelude, g: ExprId, i: u32) -> ExprId {
    let idx = numeral_nat(k, p, i);
    let gi = k.app(g, idx);
    let of_nat = k.const_(p.of_nat, vec![]);
    k.app(of_nat, gi)
}

/// `Int.sumMaps m n (fun _ => 1)` counts the maps `[0,m) -> [0,n)`, so it must
/// be `n^m`.
///
/// This is the assertion that catches a wrong bound or a `cons` that does not
/// extend the map: every other property below is invariant under an
/// enumeration that visits the right *values* the wrong number of times.
///
/// `n = 0` is included deliberately and is the one case whose answer is not
/// `n^m` by the obvious reading: there are no maps into the empty range for
/// `m > 0`, so the sum is `0`, while `sumMaps 0 0 _` is `1` (the empty map
/// exists). Both are checked.
#[test]
fn sum_maps_counts_exactly_the_maps_into_the_range() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    for &(m, n, expected) in &[
        (0_u32, 3_u32, 1_i32),
        (1, 3, 3),
        (2, 3, 9),
        (3, 2, 8),
        (2, 1, 1),
        (0, 0, 1),
        (2, 0, 0),
    ] {
        let one = numeral(&mut k, &p, 1);
        let f = map_lam(&mut k, &p, &|_k, _g| one);
        let lhs = sum_maps(&mut k, &p, m, n, f);
        let rhs = numeral(&mut k, &p, expected);
        assert!(
            k.def_eq(lhs, rhs),
            "sumMaps {m} {n} (fun _ => 1) should be {expected} (the count of maps [0,{m}) -> [0,{n}))"
        );
    }

    // Negative control, in the same `def_eq` call that returns the positives
    // above: an off-by-one in the count is separated, so the assertions are
    // not passing because `def_eq` says yes to everything.
    let one = numeral(&mut k, &p, 1);
    let f = map_lam(&mut k, &p, &|_k, _g| one);
    let lhs = sum_maps(&mut k, &p, 2, 3, f);
    let eight = numeral(&mut k, &p, 8);
    assert!(
        !k.def_eq(lhs, eight),
        "sumMaps 2 3 (fun _ => 1) is 9, not 8 -- if this passes the count is not being computed"
    );
}

/// `Int.sumMaps 2 3 (fun g => g 0 * g 1)` must be `(0+1+2)^2 = 9`.
///
/// **This is the assertion that separates the whole product `[0,3) x [0,3)`
/// from its DIAGONAL**, which is the plausible way a two-index fold goes wrong:
/// the recursion threads one map through two nested folds, and a `cons` that
/// overwrote rather than extended would visit only `g 0 = g 1`. The diagonal
/// sum is `0*0 + 1*1 + 2*2 = 5`, asserted NOT to be the value.
///
/// Both numbers come from the same `def_eq` on inputs differing only in the
/// expected constant, which is what makes the negative non-vacuous.
#[test]
fn sum_maps_visits_the_full_product_and_not_only_the_diagonal() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let f = map_lam(&mut k, &p, &|k, g| {
        let g0 = coe_at(k, &p, g, 0);
        let g1 = coe_at(k, &p, g, 1);
        let mul = k.const_(p.mul, vec![]);
        let partial = k.app(mul, g0);
        k.app(partial, g1)
    });
    let lhs = sum_maps(&mut k, &p, 2, 3, f);

    let nine = numeral(&mut k, &p, 9);
    assert!(
        k.def_eq(lhs, nine),
        "sum over ALL 9 maps [0,2) -> [0,3) of g 0 * g 1 is (0+1+2)^2 = 9"
    );

    let five = numeral(&mut k, &p, 5);
    assert!(
        !k.def_eq(lhs, five),
        "5 is the DIAGONAL sum 0*0 + 1*1 + 2*2 -- if this passes, `cons` overwrites instead of extending"
    );
}

/// The two defining equations compute, and the `m = 0` one is applied at a
/// summand that would notice a different junk map.
///
/// `sumMaps 0 n F` is `F` at *some* map, and the module doc says any total map
/// would do. That is true of every CONSUMER here (each applies `prodRange _ 0`,
/// which never looks at its argument) and it is not true of an arbitrary `F`,
/// so this pins the choice actually made rather than leaving it unstated.
#[test]
fn sum_maps_defining_equations_compute_and_the_base_map_is_the_constant_zero() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    // sumMaps 0 3 (fun g => ofNat (g 0)) = ofNat 0, because the base map is
    // `fun _ => 0`.
    let f = map_lam(&mut k, &p, &|k, g| coe_at(k, &p, g, 0));
    let lhs = sum_maps(&mut k, &p, 0, 3, f);
    let zero = numeral(&mut k, &p, 0);
    assert!(
        k.def_eq(lhs, zero),
        "sumMaps 0 n F is F applied to the constant-zero map"
    );

    // sumMaps 1 4 (fun g => ofNat (g 0)) = 0 + 1 + 2 + 3 = 6, the successor
    // equation at m = 1 -- so the recursion really does peel an index and hand
    // it to `Int.sumRange`.
    let f = map_lam(&mut k, &p, &|k, g| coe_at(k, &p, g, 0));
    let lhs = sum_maps(&mut k, &p, 1, 4, f);
    let six = numeral(&mut k, &p, 6);
    assert!(
        k.def_eq(lhs, six),
        "sumMaps 1 4 (fun g => g 0) enumerates 0,1,2,3 and sums to 6"
    );
    let seven = numeral(&mut k, &p, 7);
    assert!(
        !k.def_eq(lhs, seven),
        "an inclusive bound would give 0+1+2+3+4 = 10 and a shifted one 7 -- neither is the value"
    );
}

/// `Int.prodRange_sumRange_expand` at a CONCRETE instance, both sides computed
/// independently.
///
/// The theorem is proved at symbolic `m`, `n` and `c`, so this instance is
/// automatic and adds nothing about the *proof*. What it adds is that the two
/// sides are the numbers they are supposed to be — a check on the STATEMENT,
/// which no amount of type-checking supplies. With `c i k := k + 1` and
/// `m = n = 2` the left side is `(1 + 2) * (1 + 2) = 9`, and the right side is
/// the sum over the four maps of `c 0 (g 0) * c 1 (g 1)`, namely
/// `1*1 + 1*2 + 2*1 + 2*2 = 9`.
#[test]
fn prod_range_sum_range_expand_computes_to_the_same_number_on_both_sides() {
    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");
    let anon = k.anon();
    let nat_ty = k.const_(p.nat.nat, vec![]);

    // c := fun (_i k : Nat) => Int.ofNat k + 1, ignoring the row index so the
    // hand-computed value stays a two-line calculation.
    let c = {
        let kk = k.bvar(0);
        let of_nat = k.const_(p.of_nat, vec![]);
        let coe = k.app(of_nat, kk);
        let one = numeral(&mut k, &p, 1);
        let add = k.const_(p.add, vec![]);
        let partial = k.app(add, coe);
        let body = k.app(partial, one);
        let inner = k.lam(anon, nat_ty, body, BinderInfo::Default);
        k.lam(anon, nat_ty, inner, BinderInfo::Default)
    };

    let two_nat = numeral_nat(&mut k, &p, 2);

    // LHS := prodRange (fun i => sumRange (c i) 2) 2.
    let lhs = {
        let i = k.bvar(0);
        let ci = k.app(c, i);
        let sum_range = k.const_(p.sum_range, vec![]);
        let partial = k.app(sum_range, ci);
        let body = k.app(partial, two_nat);
        let rows = k.lam(anon, nat_ty, body, BinderInfo::Default);
        let prod_range = k.const_(p.prod_range, vec![]);
        let a = k.app(prod_range, rows);
        k.app(a, two_nat)
    };

    // RHS := sumMaps 2 2 (fun g => prodRange (fun i => c i (g i)) 2).
    //
    // Built with explicit de Bruijn indices rather than through `map_lam`:
    // there are TWO binders here, so under the inner `fun i` the map `g` is
    // `bvar(1)` and only `i` is `bvar(0)`. The first draft reused `map_lam`'s
    // `g` (a bare `bvar(0)`) inside the inner lambda, which silently made the
    // body `c i (i i)` -- a term `def_eq` happily reduces to something stuck
    // rather than rejecting, so the only symptom was a wrong number.
    let rhs = {
        let map_ty = {
            let nt = k.const_(p.nat.nat, vec![]);
            k.pi(anon, nt, nt, BinderInfo::Default)
        };
        let inner = {
            let i = k.bvar(0);
            let g = k.bvar(1);
            let gi = k.app(g, i);
            let ci = k.app(c, i);
            let body = k.app(ci, gi);
            k.lam(anon, nat_ty, body, BinderInfo::Default)
        };
        let prod_range = k.const_(p.prod_range, vec![]);
        let a = k.app(prod_range, inner);
        let outer_body = k.app(a, two_nat);
        let f = k.lam(anon, map_ty, outer_body, BinderInfo::Default);
        sum_maps(&mut k, &p, 2, 2, f)
    };

    let nine = numeral(&mut k, &p, 9);
    assert!(
        k.def_eq(lhs, nine),
        "prodRange (fun i => sumRange (c i) 2) 2 is (1+2)*(1+2) = 9"
    );
    assert!(
        k.def_eq(rhs, nine),
        "the sum over the four maps of c 0 (g 0) * c 1 (g 1) is 1+2+2+4 = 9"
    );

    // Non-vacuity: the same `def_eq` distinguishes the neighbouring value, so
    // neither assertion above passes because everything is defeq to everything.
    let ten = numeral(&mut k, &p, 10);
    assert!(!k.def_eq(lhs, ten), "9 is not 10");
    assert!(!k.def_eq(rhs, ten), "9 is not 10");
}

/// Every declaration this file's module adds is `Theorem`- or
/// `Definition`-kinded with an EMPTY axiom footprint, read from the kernel
/// rather than from a list in this file.
#[test]
fn the_sum_maps_family_is_axiom_free() {
    use crate::env::Declaration;

    let mut k = Kernel::new();
    let p = build_int_prelude(&mut k).expect("Int prelude must build");

    let expected: [(crate::NameId, bool); 8] = [
        (p.sum_range_mul_right, true),
        (p.sum_range_mul_left, true),
        (p.sum_maps, false),
        (p.sum_maps_zero, true),
        (p.sum_maps_succ, true),
        (p.sum_maps_congr, true),
        (p.sum_maps_mul_left, true),
        (p.prod_range_sum_range_expand, true),
    ];

    for &(name, is_theorem) in &expected {
        let decl = k
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{} must be declared", k.display_name(name)));
        if is_theorem {
            assert!(
                matches!(decl, Declaration::Theorem { .. }),
                "{} must be a Theorem",
                k.display_name(name)
            );
        } else {
            assert!(
                matches!(decl, Declaration::Definition { .. }),
                "{} must be a Definition",
                k.display_name(name)
            );
        }
        let footprint = k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{} must be axiom-free, got {:?}",
            k.display_name(name),
            footprint
                .iter()
                .map(|&a| k.display_name(a).to_string())
                .collect::<Vec<_>>()
        );
    }
}
