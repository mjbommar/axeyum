//! Concrete-instance tests for `nat_prelude::rado` (ADR-1596).
//!
//! **The kernel cannot tell a `Definition` is wrong.** `Nat.Rado.Sol`,
//! `IsColouring`, `MonoSol`, `Arrows`, `IsRadoNumber`, `ofFinset` and
//! `schurSet` are all admitted on their TYPE, and a definition that means
//! something *else* has the right type, an empty axiom footprint, and passes
//! every sweep in this repository. `Sol` in particular has a specific wrong
//! form that is easy to write and hard to see — `a * (x - y) = b * z`, which
//! `Nat`'s truncating subtraction makes TRUE at every `x <= y, z = 0` — and
//! [`sol_is_subtraction_free_and_rejects_the_truncated_form`] is the test that
//! separates the two.
//!
//! Every theorem here is paired with a nearby statement that must be
//! **rejected**, and the pair is the point: a table of rejections alone
//! overstates coverage, because a proof term can fail to type-check for
//! reasons that have nothing to do with the statement being false. So each
//! control asks both questions — the intended statement is ACCEPTED, and the
//! statement differing in one small term is REJECTED, with the SAME proof
//! term in both halves wherever that is possible.
//!
//! Magnitudes: the largest numeral formed anywhere in this file is `5`. That
//! is not modesty, it is the constraint the whole module is built around —
//! see `rado.rs`'s "unary-numeral constraint".

use super::ops::{NatDev, NatOps};
use super::rado;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::{Kernel, NameId, NatPrelude, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    counter: u32,
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        Self { k, p, counter: 0 }
    }

    /// A fresh scratch name for an accept/reject control.
    fn scratch(&mut self) -> NameId {
        self.counter += 1;
        let anon = self.k.anon();
        let root = self.k.name_str(anon, "radoControl");
        let leaf = format!("c{}", self.counter);
        self.k.name_str(root, &leaf)
    }

    /// Offer `value` to the trusted gate at type `ty`. `true` means the kernel
    /// ADMITTED it — nothing here reads a boolean out of a checker of its own.
    fn admits(&mut self, ty: ExprId, value: ExprId) -> bool {
        let name = self.scratch();
        self.k
            .add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty,
                value,
            })
            .is_ok()
    }

    fn dev(&mut self) -> NatDev<'_> {
        let p = self.p;
        NatDev::new(&mut self.k, p)
    }
}

/// `Nat.le lo hi` at concrete magnitudes.
fn le_at(d: &mut NatDev<'_>, p: &NatPrelude, lo: u32, hi: u32) -> ExprId {
    let lo_e = d.num(lo);
    let mut proof = d.const_app(p.le_refl, &[lo_e]);
    for step in lo..hi {
        let from = d.num(step);
        proof = d.const_app(p.le_step, &[lo_e, from, proof]);
    }
    proof
}

/// `And.intro` for `Nat.inClosedInterval 1 n i` at concrete magnitudes.
fn in_range_at(d: &mut NatDev<'_>, p: &NatPrelude, n: u32, i: u32) -> ExprId {
    let one = d.num(1);
    let i_e = d.num(i);
    let n_e = d.num(n);
    let lo_ty = d.le(one, i_e);
    let hi_ty = d.le(i_e, n_e);
    let lo = le_at(d, p, 1, i);
    let hi = le_at(d, p, i, n);
    d.const_app(p.logic.and_intro, &[lo_ty, hi_ty, lo, hi])
}

/// `Exists.{1} Nat pred`.
fn exists_nat(d: &mut NatDev<'_>, p: &NatPrelude, pred: ExprId) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let ex = d.kernel().const_(p.logic.exists_, vec![one]);
    d.apply(ex, &[nat, pred])
}

/// `Exists.intro.{1} Nat pred w h`.
fn exists_intro_nat(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    pred: ExprId,
    w: ExprId,
    h: ExprId,
) -> ExprId {
    let one = d.level_one();
    let nat = d.nat_ty();
    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
    d.apply(intro, &[nat, pred, w, h])
}

/// The right-nested `And` chain `MonoSol` carries, rebuilt independently of
/// `rado.rs` so a change there cannot silently agree with itself.
fn mono_body_at(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    c: ExprId,
    x: ExprId,
    y: ExprId,
    z: ExprId,
) -> ExprId {
    let one = d.num(1);
    let rx = d.in_closed_interval(one, n, x);
    let ry = d.in_closed_interval(one, n, y);
    let rz = d.in_closed_interval(one, n, z);
    let sol = d.const_app(p.rado_sol, &[a, b, x, y, z]);
    let cx = d.apply(c, &[x]);
    let cy = d.apply(c, &[y]);
    let cz = d.apply(c, &[z]);
    let exy = d.eq(cx, cy);
    let eyz = d.eq(cy, cz);
    let tail = d.const_app(p.logic.and, &[exy, eyz]);
    let with_sol = d.const_app(p.logic.and, &[sol, tail]);
    let with_z = d.const_app(p.logic.and, &[rz, with_sol]);
    let with_y = d.const_app(p.logic.and, &[ry, with_z]);
    d.const_app(p.logic.and, &[rx, with_y])
}

fn mono_pred_z_at(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    c: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let body = mono_body_at(d, p, a, b, n, c, x, y, z);
    d.lam_fv(z_fv, nat, body)
}

fn mono_pred_y_at(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    c: ExprId,
    x: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let inner = mono_pred_z_at(d, p, a, b, n, c, x, y);
    let body = exists_nat(d, p, inner);
    d.lam_fv(y_fv, nat, body)
}

fn mono_pred_x_at(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: ExprId,
    b: ExprId,
    n: ExprId,
    c: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let inner = mono_pred_y_at(d, p, a, b, n, c, x);
    let body = exists_nat(d, p, inner);
    d.lam_fv(x_fv, nat, body)
}

/// The `MonoSol a b n c` witness at one concrete triple, with every side
/// condition discharged by `Eq.refl` / the `Nat.le` constructors. Returns the
/// statement and the proof so a caller can offer BOTH to the trusted gate.
#[allow(clippy::too_many_arguments)]
fn mono_witness(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    a: u32,
    b: u32,
    n: u32,
    c: ExprId,
    x: u32,
    y: u32,
    z: u32,
) -> (ExprId, ExprId) {
    let a_e = d.num(a);
    let b_e = d.num(b);
    let n_e = d.num(n);
    let x_e = d.num(x);
    let y_e = d.num(y);
    let z_e = d.num(z);
    let one = d.num(1);

    let rx_ty = d.in_closed_interval(one, n_e, x_e);
    let ry_ty = d.in_closed_interval(one, n_e, y_e);
    let rz_ty = d.in_closed_interval(one, n_e, z_e);
    let sol_ty = d.const_app(p.rado_sol, &[a_e, b_e, x_e, y_e, z_e]);
    let cx = d.apply(c, &[x_e]);
    let cy = d.apply(c, &[y_e]);
    let cz = d.apply(c, &[z_e]);
    let exy = d.eq(cx, cy);
    let eyz = d.eq(cy, cz);
    let tail_ty = d.const_app(p.logic.and, &[exy, eyz]);
    let with_sol_ty = d.const_app(p.logic.and, &[sol_ty, tail_ty]);
    let with_z_ty = d.const_app(p.logic.and, &[rz_ty, with_sol_ty]);
    let with_y_ty = d.const_app(p.logic.and, &[ry_ty, with_z_ty]);

    let rx = in_range_at(d, p, n, x);
    let ry = in_range_at(d, p, n, y);
    let rz = in_range_at(d, p, n, z);
    let sol_lhs = d.mul(a_e, x_e);
    let hsol = d.refl(sol_lhs);
    let hxy = d.refl(cx);
    let hyz = d.refl(cy);

    let tail = d.const_app(p.logic.and_intro, &[exy, eyz, hxy, hyz]);
    let with_sol = d.const_app(p.logic.and_intro, &[sol_ty, tail_ty, hsol, tail]);
    let with_z = d.const_app(p.logic.and_intro, &[rz_ty, with_sol_ty, rz, with_sol]);
    let with_y = d.const_app(p.logic.and_intro, &[ry_ty, with_z_ty, ry, with_z]);
    let packed = d.const_app(p.logic.and_intro, &[rx_ty, with_y_ty, rx, with_y]);

    let pz = mono_pred_z_at(d, p, a_e, b_e, n_e, c, x_e, y_e);
    let ez = exists_intro_nat(d, p, pz, z_e, packed);
    let py = mono_pred_y_at(d, p, a_e, b_e, n_e, c, x_e);
    let ey = exists_intro_nat(d, p, py, y_e, ez);
    let px = mono_pred_x_at(d, p, a_e, b_e, n_e, c);
    let ex = exists_intro_nat(d, p, px, x_e, ey);

    let stmt = d.const_app(p.rado_mono_sol, &[a_e, b_e, n_e, c]);
    (stmt, ex)
}

// ===========================================================================
// The definitions evaluate to what they are supposed to mean.
// ===========================================================================

/// `Nat.Rado.schurSet` is the set the search returned, and it truncates.
///
/// The two `false`s below `2` and the two above `3` are not redundant with
/// each other: `1` exercises the `beq` chain falling through to `Bool.false`
/// BELOW the bound, `5` exercises `Nat.Finset.memB`'s truncation branch
/// (`ble 6 5 = false`) at the bound. A `schurSet` that stored the complement,
/// or that put the bound at `4` and so lost the member `4`'s truncation, would
/// still pass one of them.
#[test]
fn schur_set_is_the_partition_the_search_found() {
    let mut f = Fixture::new();
    let expected = [false, false, true, true, false, false];
    for (i, want) in expected.iter().enumerate() {
        let p = f.p;
        let mut d = f.dev();
        let set = d.kernel().const_(p.rado_schur_set, vec![]);
        let i_e = d.num(u32::try_from(i).expect("small"));
        let mem = d.const_app(p.finset_mem_b, &[set, i_e]);
        let t = d.bool_true();
        let fa = d.bool_false();
        let want_e = if *want { t } else { fa };
        let other = if *want { fa } else { t };
        assert!(f.k.def_eq(mem, want_e), "memB schurSet {i} must be {want}");
        assert!(
            !f.k.def_eq(mem, other),
            "negative control: memB schurSet {i} must NOT be {}",
            !*want
        );
    }
}

/// `Nat.Rado.ofFinset` is the INDICATOR: `1` on members, `0` off them.
///
/// The wrong formula this rules out is the swap (`0` on members), which has
/// exactly the same type, is an equally valid 2-colouring, and colours
/// `{1,4}` and `{2,3}` the other way round — so `schur_not_arrows_four` would
/// still be true and nothing else in this module would notice.
#[test]
fn of_finset_is_the_indicator_colouring() {
    let mut f = Fixture::new();
    let expected: [u32; 6] = [0, 0, 1, 1, 0, 0];
    for (i, want) in expected.iter().enumerate() {
        let p = f.p;
        let mut d = f.dev();
        let set = d.kernel().const_(p.rado_schur_set, vec![]);
        let col = d.const_app(p.rado_of_finset, &[set]);
        let i_e = d.num(u32::try_from(i).expect("small"));
        let at = d.apply(col, &[i_e]);
        let want_e = d.num(*want);
        let other = d.num(1 - *want);
        assert!(
            f.k.def_eq(at, want_e),
            "ofFinset schurSet {i} must be {want}"
        );
        assert!(
            !f.k.def_eq(at, other),
            "negative control: ofFinset schurSet {i} must NOT be {}",
            1 - *want
        );
    }
}

/// **The decisive definition test.** `Sol a b x y z` is `a*x = a*y + b*z`, the
/// subtraction-free form, NOT `a*(x - y) = b*z`.
///
/// The two differ on exactly one shape and it is the shape a careless
/// transcription produces: `Nat` subtraction truncates, so `a*(x - y) = b*z`
/// is TRUE for every `x <= y` at `z = 0` — `Sol 5 3 1 2 0` would be
/// `5*(1-2) = 3*0`, i.e. `0 = 0`. The declared form makes it `5 = 10`, which
/// the kernel refuses. Nothing else in this file, and nothing in the
/// declaration's TYPE, separates the two.
#[test]
fn sol_is_subtraction_free_and_rejects_the_truncated_form() {
    let mut f = Fixture::new();

    // The degenerate argument the truncated form would admit.
    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let a = d.num(5);
        let b = d.num(3);
        let x = d.num(1);
        let y = d.num(2);
        let z = d.num(0);
        let ty = d.const_app(p.rado_sol, &[a, b, x, y, z]);
        let lhs = d.mul(a, x);
        (ty, d.refl(lhs))
    };
    assert!(
        !f.admits(ty, value),
        "Sol 5 3 1 2 0 must be REJECTED: 5*1 = 5 and 5*2 + 3*0 = 10. \
         The truncated form 5*(1-2) = 3*0 would make it 0 = 0 and ADMIT it."
    );

    // The paired positive at the same (a, b): a real solution of 5(x-y) = 3z.
    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let a = d.num(5);
        let b = d.num(3);
        let x = d.num(5);
        let y = d.num(2);
        let z = d.num(5);
        let ty = d.const_app(p.rado_sol, &[a, b, x, y, z]);
        let lhs = d.mul(a, x);
        (ty, d.refl(lhs))
    };
    assert!(
        f.admits(ty, value),
        "Sol 5 3 5 2 5 must be ADMITTED: 25 = 10 + 15"
    );
}

/// `Sol` at the Schur parameters, and at a second `(a, b)` so the test is not
/// blind to a definition that ignores `a` or `b`.
///
/// `Sol 1 1 3 1 2` is `3 = 1 + 2`. `Sol 2 3 4 1 2` is `8 = 2 + 6`; a `Sol`
/// that read `b * z` as `z`, or `a * y` as `y`, would be false there and true
/// at the `a = b = 1` instance.
#[test]
fn sol_evaluates_at_discriminating_arguments() {
    let cases: [(u32, u32, u32, u32, u32, bool); 6] = [
        (1, 1, 3, 1, 2, true),
        (1, 1, 3, 1, 1, false),
        (2, 3, 4, 1, 2, true),
        (2, 3, 4, 1, 1, false),
        (5, 3, 5, 2, 5, true),
        (5, 4, 5, 1, 5, true), // 25 = 5 + 20
    ];
    let mut f = Fixture::new();
    for (a, b, x, y, z, want) in cases {
        let (ty, value) = {
            let p = f.p;
            let mut d = f.dev();
            let a_e = d.num(a);
            let b_e = d.num(b);
            let x_e = d.num(x);
            let y_e = d.num(y);
            let z_e = d.num(z);
            let ty = d.const_app(p.rado_sol, &[a_e, b_e, x_e, y_e, z_e]);
            let lhs = d.mul(a_e, x_e);
            (ty, d.refl(lhs))
        };
        assert_eq!(
            f.admits(ty, value),
            want,
            "Sol {a} {b} {x} {y} {z}: expected admitted={want}"
        );
    }
}

/// A `MonoSol` witness is only admitted when all three colours AGREE, and
/// that is what makes `schurSet` a lower-bound certificate rather than a
/// number.
///
/// At `n = 5` the triple `(5, 1, 4)` is monochromatic under the `{2,3}`
/// colouring (all three land on colour `0`) and the kernel admits it. At
/// `n = 4` the range has exactly six solutions of `x = y + z` —
/// `(2,1,1) (3,1,2) (3,2,1) (4,1,3) (4,3,1) (4,2,2)` — and EVERY one must be
/// refused, because that is the statement "this colouring admits no
/// monochromatic solution" made concrete. A `MonoSol` that forgot one of its
/// two colour equations would admit `(3,1,2)`.
#[test]
fn mono_sol_admits_only_a_monochromatic_triple() {
    let mut f = Fixture::new();

    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let set = d.kernel().const_(p.rado_schur_set, vec![]);
        let col = d.const_app(p.rado_of_finset, &[set]);
        mono_witness(&mut d, &p, 1, 1, 5, col, 5, 1, 4)
    };
    assert!(
        f.admits(ty, value),
        "MonoSol 1 1 5 (ofFinset schurSet) at (5,1,4) must be ADMITTED: \
         5 = 1 + 4 and all three are colour 0"
    );

    let solutions: [(u32, u32, u32); 6] = [
        (2, 1, 1),
        (3, 1, 2),
        (3, 2, 1),
        (4, 1, 3),
        (4, 3, 1),
        (4, 2, 2),
    ];
    for (x, y, z) in solutions {
        let (ty, value) = {
            let p = f.p;
            let mut d = f.dev();
            let set = d.kernel().const_(p.rado_schur_set, vec![]);
            let col = d.const_app(p.rado_of_finset, &[set]);
            mono_witness(&mut d, &p, 1, 1, 4, col, x, y, z)
        };
        assert!(
            !f.admits(ty, value),
            "MonoSol 1 1 4 (ofFinset schurSet) at ({x},{y},{z}) must be REJECTED"
        );
    }
}

// ===========================================================================
// The search half. Untrusted, but its answers are the certificate, so they
// are pinned independently of the kernel.
// ===========================================================================

/// The lower-bound search finds `{2,3}` at `n = 4` and finds NOTHING at
/// `n = 5` — which is the two-colour Schur number, read off the enumeration
/// rather than off a kernel term.
///
/// The `None` at `5` is the load-bearing half: it is what makes `5` the LEAST
/// bound rather than merely a bound, and it is the assertion a search that had
/// silently stopped early would fail.
#[test]
fn the_search_bounds_the_two_colour_schur_number_at_five() {
    assert_eq!(
        rado::search_avoiding_set(1, 1, 4),
        Some(vec![2, 3]),
        "the 2^4 subsets of [1,4] contain exactly the {{1,4}}/{{2,3}} partition"
    );
    assert_eq!(
        rado::search_avoiding_set(1, 1, 5),
        None,
        "every 2-colouring of [1,5] has a monochromatic x = y + z"
    );
    assert!(
        rado::search_avoiding_set(1, 1, 3).is_some(),
        "smaller ranges also avoid, so the None at 5 is not a search that always says None"
    );

    // Re-check the returned set independently of the routine that found it:
    // its induced colouring must have no monochromatic solution, and adding
    // the excluded member 1 to it must create one (4 = 1 + 3 all in {1,2,3}
    // would be monochromatic). A set that merely LOOKED avoiding would pass
    // the first half and fail the second.
    let found = rado::search_avoiding_set(1, 1, 4).expect("an avoiding subset of [1,4]");
    let colours: Vec<u32> = (1..=4).map(|i| u32::from(found.contains(&i))).collect();
    assert_eq!(
        rado::search_witness(1, 1, 4, &colours),
        None,
        "the returned set {found:?} must induce a colouring with no monochromatic solution"
    );
    let widened: Vec<u32> = (1..=4)
        .map(|i| u32::from(found.contains(&i) || i == 1))
        .collect();
    assert!(
        rado::search_witness(1, 1, 4, &widened).is_some(),
        "adding 1 to {found:?} must create a monochromatic solution, so the set is maximal here"
    );
}

/// The search's own solution predicate reads BOTH coefficients.
///
/// `is_solution` is the untrusted half's copy of `Sol`, and at the Schur
/// parameters `a = b = 1` it is blind to both: `a * x == a * y + b * z`,
/// `x == a * y + z` and `a * x == y + b * z` all agree there, so every other
/// test in this file would pass with either coefficient dropped. These four
/// rows are the only thing that reads them.
#[test]
fn is_solution_reads_both_coefficients() {
    assert!(rado::is_solution(2, 3, 4, 1, 2), "2*4 = 2*1 + 3*2");
    assert!(
        !rado::is_solution(2, 3, 4, 1, 1),
        "2*4 = 8 and 2*1 + 3*1 = 5"
    );
    assert!(
        !rado::is_solution(2, 1, 4, 1, 2),
        "dropping b: 8 vs 2 + 2 = 4"
    );
    assert!(
        !rado::is_solution(1, 3, 4, 1, 2),
        "dropping a: 4 vs 1 + 6 = 7"
    );
}

/// The upper-bound search finds a triple for every one of the `2^5` colour
/// assignments, and finds none for the `{2,3}` colouring of `[1,4]`.
#[test]
fn the_witness_search_is_total_at_five_and_partial_at_four() {
    for bits in 0..32u32 {
        let colours: Vec<u32> = (0..5).map(|i| (bits >> i) & 1).collect();
        assert!(
            rado::search_witness(1, 1, 5, &colours).is_some(),
            "assignment {colours:?} of [1,5] must have a monochromatic x = y + z"
        );
    }
    assert_eq!(
        rado::search_witness(1, 1, 4, &[0, 1, 1, 0]),
        None,
        "the {{1,4}}/{{2,3}} colouring of [1,4] must have none"
    );
}

// ===========================================================================
// The theorems say what they are supposed to say.
// ===========================================================================

/// `Nat.Rado.schur_two` is leastness at `5`, and the SAME proof term does not
/// prove it at `4`.
///
/// The pair matters: a `schur_two` whose statement had drifted to
/// `IsRadoNumber 1 1 2 4` would still be a well-typed theorem about a defined
/// object with an empty axiom footprint, and would still be false.
#[test]
fn schur_two_is_leastness_at_five_and_not_at_four() {
    let mut f = Fixture::new();

    let (ty_five, value) = {
        let p = f.p;
        let mut d = f.dev();
        let a = d.num(1);
        let two = d.num(2);
        let five = d.num(5);
        let ty = d.const_app(p.rado_is_rado_number, &[a, a, two, five]);
        let value = d.kernel().const_(p.rado_schur_two, vec![]);
        (ty, value)
    };
    assert!(
        f.admits(ty_five, value),
        "schur_two must have type IsRadoNumber 1 1 2 5"
    );

    let (ty_four, value) = {
        let p = f.p;
        let mut d = f.dev();
        let a = d.num(1);
        let two = d.num(2);
        let four = d.num(4);
        let ty = d.const_app(p.rado_is_rado_number, &[a, a, two, four]);
        let value = d.kernel().const_(p.rado_schur_two, vec![]);
        (ty, value)
    };
    assert!(
        !f.admits(ty_four, value),
        "negative control: schur_two must NOT prove IsRadoNumber 1 1 2 4"
    );
}

/// `Nat.Rado.schur_arrows_five` is the upper bound at `5`, and the same term
/// does not give it at `6`.
///
/// `Arrows 1 1 2 6` is TRUE (monotonicity gives it from `5`), so this control
/// is about the STATEMENT the term carries, not about the mathematics: a
/// theorem whose bound had drifted upward would be silently weaker, and
/// `isRadoNumber_of_succ` would then join it to the `4` refutation and produce
/// a leastness claim at the wrong `n`.
#[test]
fn schur_arrows_five_carries_the_bound_it_was_proved_at() {
    let mut f = Fixture::new();
    for (n, want) in [(5u32, true), (6u32, false), (4u32, false)] {
        let (ty, value) = {
            let p = f.p;
            let mut d = f.dev();
            let a = d.num(1);
            let two = d.num(2);
            let n_e = d.num(n);
            let ty = d.const_app(p.rado_arrows, &[a, a, two, n_e]);
            let value = d.kernel().const_(p.rado_schur_arrows_five, vec![]);
            (ty, value)
        };
        assert_eq!(
            f.admits(ty, value),
            want,
            "schur_arrows_five at Arrows 1 1 2 {n}: expected admitted={want}"
        );
    }
}

/// `arrows_of_le` widens the bound and does NOT narrow it.
///
/// The control is the same theorem with its two bounds exchanged, which is the
/// single most likely transcription error and is FALSE: `Arrows 1 1 2 5` holds
/// and `Arrows 1 1 2 4` does not, so a narrowing version would prove the
/// negation of `schur_not_arrows_four`.
#[test]
fn arrows_of_le_widens_and_does_not_narrow() {
    let mut f = Fixture::new();

    // 5 <= 6, so Arrows 1 1 2 5 gives Arrows 1 1 2 6.
    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let a = d.num(1);
        let two = d.num(2);
        let five = d.num(5);
        let six = d.num(6);
        let hle = le_at(&mut d, &p, 5, 6);
        let up = d.kernel().const_(p.rado_schur_arrows_five, vec![]);
        let value = d.const_app(p.rado_arrows_of_le, &[a, a, two, five, six, hle, up]);
        let ty = d.const_app(p.rado_arrows, &[a, a, two, six]);
        (ty, value)
    };
    assert!(
        f.admits(ty, value),
        "arrows_of_le must widen Arrows 1 1 2 5 to Arrows 1 1 2 6"
    );

    // The same application with the bounds exchanged must not type-check.
    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let a = d.num(1);
        let two = d.num(2);
        let four = d.num(4);
        let five = d.num(5);
        let hle = le_at(&mut d, &p, 4, 5);
        let up = d.kernel().const_(p.rado_schur_arrows_five, vec![]);
        let value = d.const_app(p.rado_arrows_of_le, &[a, a, two, five, four, hle, up]);
        let ty = d.const_app(p.rado_arrows, &[a, a, two, four]);
        (ty, value)
    };
    assert!(
        !f.admits(ty, value),
        "negative control: arrows_of_le must NOT narrow Arrows 1 1 2 5 to Arrows 1 1 2 4"
    );
}

/// `isColouring_ofFinset` gives `k = 2` and nothing sharper.
///
/// The control is `IsColouring 1 n (ofFinset s)`, one below. It is FALSE (the
/// indicator takes the value `1` on members, and `1 < 1` does not hold), and
/// it differs from the true statement in a single `succ`.
#[test]
fn is_colouring_of_finset_is_two_colours_not_one() {
    let mut f = Fixture::new();
    for (k, want) in [(2u32, true), (1u32, false)] {
        let (ty, value) = {
            let p = f.p;
            let mut d = f.dev();
            let four = d.num(4);
            let k_e = d.num(k);
            let set = d.kernel().const_(p.rado_schur_set, vec![]);
            let col = d.const_app(p.rado_of_finset, &[set]);
            let ty = d.const_app(p.rado_is_colouring, &[k_e, four, col]);
            let value = d.const_app(p.rado_is_colouring_of_finset, &[four, set]);
            (ty, value)
        };
        assert_eq!(
            f.admits(ty, value),
            want,
            "isColouring_ofFinset at k = {k}: expected admitted={want}"
        );
    }
}

/// `isRadoNumber_of_succ` needs the refutation at the PREDECESSOR.
///
/// Handed the refutation at `succ m` instead of at `m` it must not type-check:
/// otherwise the reduction would accept "`n` arrows and `n` does not arrow",
/// which is a contradiction rather than a Rado number, and every certificate
/// routed through it would be meaningless.
#[test]
fn is_rado_number_of_succ_reads_the_refutation_at_the_predecessor() {
    let mut f = Fixture::new();

    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let a = d.num(1);
        let two = d.num(2);
        let four = d.num(4);
        let five = d.num(5);
        let up = d.kernel().const_(p.rado_schur_arrows_five, vec![]);
        let low = d.kernel().const_(p.rado_schur_not_arrows_four, vec![]);
        let value = d.const_app(p.rado_is_rado_number_of_succ, &[a, a, two, four, up, low]);
        let ty = d.const_app(p.rado_is_rado_number, &[a, a, two, five]);
        (ty, value)
    };
    assert!(
        f.admits(ty, value),
        "isRadoNumber_of_succ at m = 4 must give IsRadoNumber 1 1 2 5"
    );

    // `m := 5` asks for a refutation at 5; `schur_not_arrows_four` refutes at 4.
    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let a = d.num(1);
        let two = d.num(2);
        let five = d.num(5);
        let six = d.num(6);
        let hle = le_at(&mut d, &p, 5, 6);
        let up5 = d.kernel().const_(p.rado_schur_arrows_five, vec![]);
        let up6 = d.const_app(p.rado_arrows_of_le, &[a, a, two, five, six, hle, up5]);
        let low = d.kernel().const_(p.rado_schur_not_arrows_four, vec![]);
        let value = d.const_app(p.rado_is_rado_number_of_succ, &[a, a, two, five, up6, low]);
        let ty = d.const_app(p.rado_is_rado_number, &[a, a, two, six]);
        (ty, value)
    };
    assert!(
        !f.admits(ty, value),
        "negative control: isRadoNumber_of_succ at m = 5 must NOT accept a refutation at 4"
    );
}

/// `Nat.boolSelect_lt` needs a bound on BOTH branches.
///
/// The control supplies the true-branch bound twice. `Lt 1 2` holds and
/// `Lt 0 2` holds, so the values are fine; what must fail is the TYPE — the
/// second argument is at `f`, not at `t`, and a lemma that ignored one branch
/// would let a colouring escape its own colour count.
#[test]
fn bool_select_lt_bounds_both_branches() {
    let mut f = Fixture::new();

    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let zero = d.num(0);
        let one = d.num(1);
        let two = d.num(2);
        let three = d.num(3);
        let t = d.bool_true();
        let ht = le_at(&mut d, &p, 2, 2); // Lt 1 2
        let hf = le_at(&mut d, &p, 1, 2); // Lt 0 2
        let value = d.const_app(p.bool_select_lt, &[one, zero, two, t, ht, hf]);
        let selected = d.bool_select_nat(t, one, zero);
        let ty = d.lt(selected, two);
        let _ = three;
        (ty, value)
    };
    assert!(
        f.admits(ty, value),
        "boolSelect_lt must apply at t=1, f=0, k=2"
    );

    // The false-branch slot filled with the true branch's proof.
    let (ty, value) = {
        let p = f.p;
        let mut d = f.dev();
        let zero = d.num(0);
        let one = d.num(1);
        let two = d.num(2);
        let t = d.bool_true();
        let ht = le_at(&mut d, &p, 2, 2); // Lt 1 2
        let wrong = le_at(&mut d, &p, 2, 2); // Lt 1 2 again, where Lt 0 2 is wanted
        let value = d.const_app(p.bool_select_lt, &[one, zero, two, t, ht, wrong]);
        let selected = d.bool_select_nat(t, one, zero);
        let ty = d.lt(selected, two);
        (ty, value)
    };
    assert!(
        !f.admits(ty, value),
        "negative control: boolSelect_lt must not accept the true-branch bound in the false slot"
    );
}

// ===========================================================================
// The unary-numeral residue, measured rather than asserted.
// ===========================================================================

/// **The STATEMENT at the ledger's own constant type-checks. The PROOF is what
/// is missing, and it is missing for a reason that has nothing to do with
/// numerals.**
///
/// `F:rado-r4-a5-b3` says `R_4(5(x-y) = 3z) = 625`. In this kernel `625` is
/// `Nat.succ` applied 625 times to `Nat.zero`, and the standing rule is that
/// cost is superlinear in the largest magnitude FORMED. That rule is about
/// REDUCTION — `decide`'s `MAX_MAGNITUDE` is 30 because peeling a unary tower
/// costs real time — and a Prop that merely MENTIONS the numeral neither
/// reduces it nor unfolds anything: inferring the type of
/// `IsRadoNumber 5 3 4 625` walks 625 `Nat.succ` applications once each.
///
/// So this test admits `Nat.Rado.IsRadoNumber 5 3 4 625` as a `Prop`-valued
/// definition, in the same fixture and with the same budget as every other
/// test in this file. What it establishes is where the residue actually is:
/// **not in stating the ledger's result, but in proving it.** The upper half
/// would need a term ranging over every 4-colouring of `[1,625]`, and
/// colourings are functions — `schur_arrows_five`'s `Nat.lt_two_cases` tree
/// has `2^n` leaves and is already the wrong shape at `n = 10`, while the
/// lower half's `Nat.Finset.allBelow` reflection route runs `(n+1)^3` triples,
/// which is 216 here and 2.4e8 at `n = 624`.
///
/// The paired control is the same statement one `succ` away: `624` must be a
/// DIFFERENT proposition, so a `Nat.Rado.IsRadoNumber` that ignored its bound
/// would be caught rather than congratulated for type-checking.
#[test]
fn the_statement_at_the_ledgers_own_constant_type_checks() {
    let mut f = Fixture::new();

    let stmt = {
        let p = f.p;
        let mut d = f.dev();
        let a = d.num(5);
        let b = d.num(3);
        let k = d.num(4);
        let n = d.num(625);
        d.const_app(p.rado_is_rado_number, &[a, b, k, n])
    };
    let inferred = f.k.infer(stmt).expect(
        "IsRadoNumber 5 3 4 625 must type-check: the unary numeral is FORMED, never reduced",
    );
    let prop = f.k.sort_zero();
    assert!(
        f.k.def_eq(inferred, prop),
        "IsRadoNumber 5 3 4 625 must be a Prop"
    );

    // One `succ` away is a different proposition.
    let neighbour = {
        let p = f.p;
        let mut d = f.dev();
        let a = d.num(5);
        let b = d.num(3);
        let k = d.num(4);
        let n = d.num(624);
        d.const_app(p.rado_is_rado_number, &[a, b, k, n])
    };
    assert!(
        !f.k.def_eq(stmt, neighbour),
        "negative control: the statement at 625 must differ from the one at 624"
    );

    // And the OTHER ledger row, so the test is not blind to `a`/`b`/`k`.
    let other = {
        let p = f.p;
        let mut d = f.dev();
        let a = d.num(5);
        let b = d.num(4);
        let k = d.num(4);
        let n = d.num(741);
        d.const_app(p.rado_is_rado_number, &[a, b, k, n])
    };
    let inferred =
        f.k.infer(other)
            .expect("IsRadoNumber 5 4 4 741 must type-check too");
    assert!(f.k.def_eq(inferred, prop));
    assert!(
        !f.k.def_eq(stmt, other),
        "negative control: the two ledger rows must be different propositions"
    );
}

// ===========================================================================
// Exhaustiveness and footprints, derived from the kernel rather than a list.
// ===========================================================================

/// Every `Nat.Rado` declaration (plus `Nat.boolSelect_lt`) is checked and
/// axiom-free, with the population read from the live environment rather than
/// from a literal — a list would measure this file's author's memory.
#[test]
fn every_rado_declaration_is_axiom_free() {
    let f = Fixture::new();
    let mut names: Vec<NameId> = Vec::new();
    for (&name, _) in f.k.environment().iter() {
        let rendered = f.k.display_name(name).to_string();
        if rendered.starts_with("Nat.Rado.") || rendered == "Nat.boolSelect_lt" {
            names.push(name);
        }
    }
    assert_eq!(
        names.len(),
        17,
        "expected the 17 declarations rado.rs adds; found {}",
        names.len()
    );
    for name in names {
        let rendered = f.k.display_name(name).to_string();
        let footprint = f.k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{rendered} must be axiom-free; footprint = {footprint:?}"
        );
    }
}
