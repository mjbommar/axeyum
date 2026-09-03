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
use crate::nat_prelude::{NatDev, NatOps};
use crate::{Kernel, build_nat_prelude};

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
