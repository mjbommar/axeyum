//! Wall-clock cost of the `simp` producer, per emitted term — the same
//! measurement `ring::cost`/`linarith::cost` make for their own producers,
//! `07-the-cost-model-and-pareto-position.md` §3.
//!
//! - `search_ms`: match + rewrite-to-fixpoint on both sides + build the
//!   term, kernel excluded.
//! - `total_ms`: the same, plus `Kernel::add_declaration` re-checking it.
//!
//! Measure in `--release`. In debug the kernel's own recursion costs up to
//! 32x per frame and the number says nothing about the shipped
//! configuration.

use std::time::{Duration, Instant};

use crate::expr::ExprId;
use crate::nat_prelude::{NatDev, NatOps};
use crate::{Kernel, build_nat_prelude};

use super::nat::{self, Rule};

/// One measured goal shape.
#[derive(Clone, Debug)]
pub struct Row {
    /// What was proved, in words.
    pub label: String,
    /// Milliseconds per term for matching plus emission, kernel excluded.
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
    let root = kernel.name_str(anon, "simp_cost");
    let mut d = NatDev::new(&mut kernel, prelude);
    let rules: Vec<Rule<NatDev<'_>>> = nat::default_rules(&prelude);

    // One full round first, so first-touch costs are not charged to the
    // sample.
    let warm = d.kernel().name_str(root, "warm");
    nat::theorem(&mut d, &prelude, &rules, warm, arity, build).expect("the warm-up must succeed");

    let mut search = Duration::ZERO;
    let start = Instant::now();
    for i in 0..repeats {
        let name = d.kernel().name_str(root, format!("t{i}"));
        let nat_ty = d.nat_ty();
        let t0 = Instant::now();
        let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&v| d.kernel().fvar(v)).collect();
        let concl = build(&mut d, &vars);
        let proof = nat::prove(&mut d, &prelude, &rules, concl).expect("the goal is provable");
        search += t0.elapsed();

        let mut ty = concl;
        let mut value = proof;
        for &fv in fvs.iter().rev() {
            ty = d.pi_fv(fv, nat_ty, ty);
            value = d.lam_fv(fv, nat_ty, value);
        }
        d.declare_theorem(name, ty, value)
            .expect("the kernel must accept the emitted term");
    }
    row(label, repeats, start.elapsed(), search)
}

/// Measure every ℕ shape, `repeats` emissions each.
///
/// Call it from a `--release` binary; see the module docs.
#[must_use]
pub fn measure(repeats: u32) -> Vec<Row> {
    vec![
        time_nat("Nat  1+x = succ x", repeats, 1, &|d, v| {
            let x = v[0];
            let one = d.num(1);
            let lhs = d.add(one, x);
            let rhs = d.succ(x);
            d.eq(lhs, rhs)
        }),
        time_nat("Nat  2*x = x+x", repeats, 1, &|d, v| {
            let x = v[0];
            let two = d.num(2);
            let lhs = d.mul(two, x);
            let rhs = d.add(x, x);
            d.eq(lhs, rhs)
        }),
        time_nat("Nat  2+x = succ(succ x)", repeats, 1, &|d, v| {
            let x = v[0];
            let two = d.num(2);
            let lhs = d.add(two, x);
            let sx = d.succ(x);
            let rhs = d.succ(sx);
            d.eq(lhs, rhs)
        }),
        time_nat("Nat  (n+0*0)+n*0 = 0*0+n*1", repeats, 1, &|d, v| {
            let n = v[0];
            let zero = d.zero();
            let one = d.num(1);
            let zz = d.mul(zero, zero);
            let n_zero = d.mul(n, zero);
            let first = d.add(n, zz);
            let lhs = d.add(first, n_zero);
            let n_one = d.mul(n, one);
            let rhs = d.add(zz, n_one);
            d.eq(lhs, rhs)
        }),
    ]
}
