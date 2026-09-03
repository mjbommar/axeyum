//! Wall-clock cost of the `ring` producer, per emitted term.
//!
//! Beside `crate::linarith::cost`'s figures, the datum
//! `07-the-cost-model-and-pareto-position.md` §3 asks for: how many
//! milliseconds does one proof cost once nobody is writing it.
//!
//! **What is measured, and what deliberately is not.** Each shape builds its
//! prelude ONCE and then repeats one goal, so the prelude build sits outside
//! the loop.
//!
//! - `search_ms`: parse both sides, normalize, compare, build the term.
//! - `total_ms`: the same, plus `Kernel::add_declaration` re-checking it.
//!
//! Measure in `--release`. In debug the kernel's own recursion costs up to
//! 32x per frame and the number says nothing about the shipped
//! configuration.

use std::time::{Duration, Instant};

use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::{NatDev, NatOps};
use crate::{Kernel, build_int_prelude, build_nat_prelude, build_rat_prelude};

/// One measured goal shape.
#[derive(Clone, Debug)]
pub struct Row {
    /// What was proved, in words.
    pub label: String,
    /// Milliseconds per term for normalize plus emission, kernel excluded.
    pub search_ms: f64,
    /// Milliseconds per term end to end, `add_declaration` included.
    pub total_ms: f64,
}

fn row(label: &str, repeats: u32, total: Duration, search: Duration) -> Row {
    let n = f64::from(repeats);
    Row {
        label: label.to_owned(),
        search_ms: search.as_secs_f64() * 1000.0 / n,
        total_ms: total.as_secs_f64() * 1000.0 / n,
    }
}

/// Time `repeats` emissions of one ℕ goal shape.
fn time_nat(
    label: &str,
    repeats: u32,
    arity: usize,
    build: &dyn Fn(&mut NatDev<'_>, &[ExprId]) -> ExprId,
) -> Row {
    let mut kernel = Kernel::new();
    let prelude = build_nat_prelude(&mut kernel).expect("the Nat prelude must build");
    let anon = kernel.anon();
    let root = kernel.name_str(anon, "ring_cost");
    let mut d = NatDev::new(&mut kernel, prelude);

    // One full round first, so first-touch costs are not charged to the
    // sample.
    let warm = d.kernel().name_str(root, "warm");
    super::nat::theorem(&mut d, &prelude, warm, arity, build).expect("the warm-up must succeed");

    let mut search = Duration::ZERO;
    let start = Instant::now();
    for i in 0..repeats {
        let name = d.kernel().name_str(root, format!("t{i}"));
        let nat = d.nat_ty();
        let t0 = Instant::now();
        let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&v| d.kernel().fvar(v)).collect();
        let concl = build(&mut d, &vars);
        let proof = super::nat::prove(&mut d, &prelude, concl).expect("the goal is provable");
        search += t0.elapsed();

        let mut ty = concl;
        let mut value = proof;
        for &fv in fvs.iter().rev() {
            ty = d.pi_fv(fv, nat, ty);
            value = d.lam_fv(fv, nat, value);
        }
        d.declare_theorem(name, ty, value)
            .expect("the kernel must accept the emitted term");
    }
    row(label, repeats, start.elapsed(), search)
}

/// Measure every shape, `repeats` emissions each.
///
/// Call it from a `--release` binary; see the module docs.
#[must_use]
pub fn measure(repeats: u32) -> Vec<Row> {
    vec![
        time_nat("Nat  (x+y)+z = (x+z)+y", repeats, 3, &|d, v| {
            let (x, y, z) = (v[0], v[1], v[2]);
            let xy = d.add(x, y);
            let lhs = d.add(xy, z);
            let xz = d.add(x, z);
            let rhs = d.add(xz, y);
            d.eq(lhs, rhs)
        }),
        time_nat("Nat  (a+b)+(c+d) = (a+c)+(b+d)", repeats, 4, &|d, v| {
            let (a, b, c, dd) = (v[0], v[1], v[2], v[3]);
            let ab = d.add(a, b);
            let cd = d.add(c, dd);
            let lhs = d.add(ab, cd);
            let ac = d.add(a, c);
            let bd = d.add(b, dd);
            let rhs = d.add(ac, bd);
            d.eq(lhs, rhs)
        }),
        time_nat("Nat  (a+b)*c = a*c+b*c", repeats, 3, &|d, v| {
            let (a, b, c) = (v[0], v[1], v[2]);
            let sum = d.add(a, b);
            let lhs = d.mul(sum, c);
            let ac = d.mul(a, c);
            let bc = d.mul(b, c);
            let rhs = d.add(ac, bc);
            d.eq(lhs, rhs)
        }),
        time_nat(
            "Nat  g*(a*mp+b*np) = (g*a)*mp+(g*b)*np",
            repeats,
            5,
            &|d, v| {
                let (g, a, b, mp, np) = (v[0], v[1], v[2], v[3], v[4]);
                let a_mp = d.mul(a, mp);
                let b_np = d.mul(b, np);
                let whole = d.add(a_mp, b_np);
                let lhs = d.mul(g, whole);
                let ga = d.mul(g, a);
                let scaled_a_mp = d.mul(ga, mp);
                let gb = d.mul(g, b);
                let scaled_b_np = d.mul(gb, np);
                let rhs = d.add(scaled_a_mp, scaled_b_np);
                d.eq(lhs, rhs)
            },
        ),
    ]
}

/// Time `repeats` emissions of one ℤ goal shape.
fn time_int(
    label: &str,
    repeats: u32,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
) -> Row {
    let mut kernel = Kernel::new();
    let prelude = build_int_prelude(&mut kernel).expect("the Int prelude must build");
    let mut d = IntDev::new(&mut kernel, prelude);
    let int_ty = d.int_ty();

    let anon = d.kernel().anon();
    let root = d.kernel().name_str(anon, "ring_cost");
    let warm = d.kernel().name_str(root, "warm");
    super::int::theorem(&mut d, &prelude, warm, arity, build).expect("the warm-up must succeed");

    let mut search = Duration::ZERO;
    let start = Instant::now();
    for i in 0..repeats {
        let name = d.kernel().name_str(root, format!("t{i}"));
        let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&v| d.kernel().fvar(v)).collect();
        let concl = build(&mut d, &vars);
        let t0 = Instant::now();
        let proof = super::int::prove(&mut d, &prelude, concl).expect("the goal is provable");
        search += t0.elapsed();

        let mut ty = concl;
        let mut value = proof;
        for &fv in fvs.iter().rev() {
            ty = d.pi_fv(fv, int_ty, ty);
            value = d.lam_fv(fv, int_ty, value);
        }
        d.declare_theorem(name, ty, value)
            .expect("the kernel must accept the emitted term");
    }
    row(label, repeats, start.elapsed(), search)
}

/// Time `repeats` emissions of one ℚ goal shape.
fn time_rat(
    label: &str,
    repeats: u32,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> ExprId,
) -> Row {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the Rat prelude must build");
    let mut d = IntDev::new(&mut kernel, prelude.int);
    let rat_ty = crate::rat_prelude::ops::rat_ty(&mut d);

    let anon = d.kernel().anon();
    let root = d.kernel().name_str(anon, "ring_cost");
    let warm = d.kernel().name_str(root, "warm");
    super::rat::theorem(&mut d, &prelude, warm, arity, build).expect("the warm-up must succeed");

    let mut search = Duration::ZERO;
    let start = Instant::now();
    for i in 0..repeats {
        let name = d.kernel().name_str(root, format!("t{i}"));
        let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&v| d.kernel().fvar(v)).collect();
        let concl = build(&mut d, &vars);
        let t0 = Instant::now();
        let proof = super::rat::prove(&mut d, &prelude, concl).expect("the goal is provable");
        search += t0.elapsed();

        let mut ty = concl;
        let mut value = proof;
        for &fv in fvs.iter().rev() {
            ty = d.pi_fv(fv, rat_ty, ty);
            value = d.lam_fv(fv, rat_ty, value);
        }
        d.declare_theorem(name, ty, value)
            .expect("the kernel must accept the emitted term");
    }
    row(label, repeats, start.elapsed(), search)
}

/// Measure every ℤ shape, `repeats` emissions each — beside [`measure`]'s ℕ
/// figures. Call from a `--release` binary; see the module docs.
#[must_use]
pub fn measure_int(repeats: u32) -> Vec<Row> {
    vec![
        time_int(
            "Int  A*mp + neg(A*mn) = A*(mp+neg mn)",
            repeats,
            3,
            &|d, v| {
                let (a, mp, mn) = (v[0], v[1], v[2]);
                let bp = d.imul(a, mp);
                let q = d.imul(a, mn);
                let neg_q = d.ineg(q);
                let lhs = d.iadd(bp, neg_q);
                let neg_mn = d.ineg(mn);
                let u0 = d.iadd(mp, neg_mn);
                let rhs = d.imul(a, u0);
                d.ieq(lhs, rhs)
            },
        ),
        time_int("Int  (a-1)*(a+1) = a*a - 1", repeats, 1, &|d, v| {
            let a = v[0];
            let one = d.ione();
            let sub_a1 = d.isub(a, one);
            let add_a1 = d.iadd(a, one);
            let lhs = d.imul(sub_a1, add_a1);
            let aa = d.imul(a, a);
            let rhs = d.isub(aa, one);
            d.ieq(lhs, rhs)
        }),
    ]
}

/// Measure every ℚ shape, `repeats` emissions each — beside [`measure`]'s ℕ
/// figures. Call from a `--release` binary; see the module docs.
#[must_use]
pub fn measure_rat(repeats: u32) -> Vec<Row> {
    vec![
        time_rat("Rat  w*(x*y) = x*(w*y)", repeats, 3, &|d, v| {
            let (w, x, y) = (v[0], v[1], v[2]);
            let xy = crate::rat_prelude::ops::rmul(d, x, y);
            let lhs = crate::rat_prelude::ops::rmul(d, w, xy);
            let wy = crate::rat_prelude::ops::rmul(d, w, y);
            let rhs = crate::rat_prelude::ops::rmul(d, x, wy);
            crate::rat_prelude::ops::req(d, lhs, rhs)
        }),
        time_rat("Rat  (a*w)*(a*w) = (a*a)*(w*w)", repeats, 2, &|d, v| {
            let (a, w) = (v[0], v[1]);
            let aw = crate::rat_prelude::ops::rmul(d, a, w);
            let lhs = crate::rat_prelude::ops::rmul(d, aw, aw);
            let aa = crate::rat_prelude::ops::rmul(d, a, a);
            let ww = crate::rat_prelude::ops::rmul(d, w, w);
            let rhs = crate::rat_prelude::ops::rmul(d, aa, ww);
            crate::rat_prelude::ops::req(d, lhs, rhs)
        }),
    ]
}
