//! Wall-clock cost of the producer, per emitted term.
//!
//! The number this measures is the one the
//! [cost model](../../../../docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md)
//! asks for: an encoded strategy drives the marginal cost of a theorem toward
//! CPU, so "how many milliseconds does one proof cost once nobody is writing
//! it" is what replaces tokens-per-theorem.
//!
//! **What is measured, and what deliberately is not.** Each shape builds its
//! prelude ONCE and then repeats one goal, so the prelude build — which
//! dominates a cold run by orders of magnitude and is paid once per process,
//! not once per theorem — sits outside the loop. Two costs per shape:
//!
//! - `search_ms`: parse the goal, find the certificate, build the term.
//! - `total_ms`: the same, plus `Kernel::add_declaration` re-checking it.
//!   This is the honest end-to-end figure, because an unchecked term is not a
//!   proof, and the kernel's recheck is most of the cost.
//!
//! It lives in the crate rather than in the example because the ℤ half needs
//! `IntDev`, which is `pub(crate)`; the example is a printer.
//!
//! Measure in `--release`. In debug the kernel's own recursion costs up to 32x
//! per frame and the number says nothing about the shipped configuration.

use std::time::{Duration, Instant};

use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::{NatDev, NatOps};
use crate::{Kernel, build_int_prelude, build_nat_prelude};

/// One measured goal shape.
#[derive(Clone, Debug)]
pub struct Row {
    /// What was proved, in words.
    pub label: String,
    /// Milliseconds per term for search plus emission, kernel excluded.
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
    build: &dyn Fn(&mut NatDev<'_>, &[ExprId]) -> (Vec<ExprId>, ExprId),
) -> Row {
    let mut kernel = Kernel::new();
    let prelude = build_nat_prelude(&mut kernel).expect("the Nat prelude must build");
    let anon = kernel.anon();
    let root = kernel.name_str(anon, "linarith_cost");
    let mut d = NatDev::new(&mut kernel, prelude);

    // One full round first, so first-touch costs — interning the lemma
    // constants, growing the expression arena — are not charged to the sample.
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
        let (hyp_types, concl) = build(&mut d, &vars);
        let hyp_fvs: Vec<u64> = hyp_types.iter().map(|_| d.fresh_fvar()).collect();
        let assumptions: Vec<(ExprId, ExprId)> = hyp_types
            .iter()
            .zip(hyp_fvs.iter())
            .map(|(&ty, &fv)| {
                let h = d.kernel().fvar(fv);
                (ty, h)
            })
            .collect();
        let proof =
            super::nat::prove(&mut d, &prelude, &assumptions, concl).expect("the goal is provable");
        search += t0.elapsed();

        let mut ty = concl;
        let mut value = proof;
        for (&hty, &hfv) in hyp_types.iter().zip(hyp_fvs.iter()).rev() {
            ty = d.arrow(hty, ty);
            value = d.lam_fv(hfv, hty, value);
        }
        for &fv in fvs.iter().rev() {
            ty = d.pi_fv(fv, nat, ty);
            value = d.lam_fv(fv, nat, value);
        }
        d.declare_theorem(name, ty, value)
            .expect("the kernel must accept the emitted term");
    }
    row(label, repeats, start.elapsed(), search)
}

/// Time `repeats` emissions of one ℤ goal shape.
fn time_int(
    label: &str,
    repeats: u32,
    arity: usize,
    build: &dyn Fn(&mut IntDev<'_>, &[ExprId]) -> (Vec<ExprId>, ExprId),
) -> Row {
    let mut kernel = Kernel::new();
    let prelude = build_int_prelude(&mut kernel).expect("the Int prelude must build");
    let anon = kernel.anon();
    let root = kernel.name_str(anon, "linarith_cost_int");
    let mut d = IntDev::new(&mut kernel, prelude);

    let warm = d.kernel().name_str(root, "warm");
    super::int::declare(&mut d, &prelude, warm, arity, build).expect("the warm-up must succeed");

    let mut search = Duration::ZERO;
    let start = Instant::now();
    for i in 0..repeats {
        let name = d.kernel().name_str(root, format!("t{i}"));
        let int_ty = d.int_ty();
        let t0 = Instant::now();
        let fvs: Vec<u64> = (0..arity).map(|_| d.fresh_fvar()).collect();
        let vars: Vec<ExprId> = fvs.iter().map(|&v| d.kernel().fvar(v)).collect();
        let (hyp_types, concl) = build(&mut d, &vars);
        let hyp_fvs: Vec<u64> = hyp_types.iter().map(|_| d.fresh_fvar()).collect();
        let assumptions: Vec<(ExprId, ExprId)> = hyp_types
            .iter()
            .zip(hyp_fvs.iter())
            .map(|(&ty, &fv)| {
                let h = d.kernel().fvar(fv);
                (ty, h)
            })
            .collect();
        let proof =
            super::int::prove(&mut d, &prelude, &assumptions, concl).expect("the goal is provable");
        search += t0.elapsed();

        let mut ty = concl;
        let mut value = proof;
        for (&hty, &hfv) in hyp_types.iter().zip(hyp_fvs.iter()).rev() {
            ty = d.arrow(hty, ty);
            value = d.lam_fv(hfv, hty, value);
        }
        for &fv in fvs.iter().rev() {
            ty = d.pi_fv(fv, int_ty, ty);
            value = d.lam_fv(fv, int_ty, value);
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
        time_nat("Nat  n <= n", repeats, 1, &|d, v| {
            let concl = d.le(v[0], v[0]);
            (vec![], concl)
        }),
        time_nat("Nat  n <= m |- succ n <= succ m", repeats, 2, &|d, v| {
            let hyp = d.le(v[0], v[1]);
            let sn = d.succ(v[0]);
            let sm = d.succ(v[1]);
            (vec![hyp], d.le(sn, sm))
        }),
        time_nat("Nat  a<=b<=c<=d |- a <= d", repeats, 4, &|d, v| {
            let h1 = d.le(v[0], v[1]);
            let h2 = d.le(v[1], v[2]);
            let h3 = d.le(v[2], v[3]);
            (vec![h1, h2, h3], d.le(v[0], v[3]))
        }),
        time_nat("Nat  n <= m |- n+n <= m+m", repeats, 2, &|d, v| {
            let hyp = d.le(v[0], v[1]);
            let aa = d.add(v[0], v[0]);
            let bb = d.add(v[1], v[1]);
            (vec![hyp], d.le(aa, bb))
        }),
        time_int("Int  a + (b+c) = b + (a+c)", repeats, 3, &|d, v| {
            let bc = d.iadd(v[1], v[2]);
            let left = d.iadd(v[0], bc);
            let ac = d.iadd(v[0], v[2]);
            let right = d.iadd(v[1], ac);
            (vec![], d.ieq(left, right))
        }),
        time_int("Int  3 hyps |- (a+b)+c <= (d+e)+f", repeats, 6, &|d, v| {
            let h1 = d.ile(v[0], v[3]);
            let h2 = d.ile(v[1], v[4]);
            let h3 = d.ile(v[2], v[5]);
            let ab = d.iadd(v[0], v[1]);
            let abc = d.iadd(ab, v[2]);
            let de = d.iadd(v[3], v[4]);
            let def = d.iadd(de, v[5]);
            (vec![h1, h2, h3], d.ile(abc, def))
        }),
        time_int("Int  b <= c-a |- a+b <= c", repeats, 3, &|d, v| {
            let c_sub_a = d.isub(v[2], v[0]);
            let hyp = d.ile(v[1], c_sub_a);
            let ab = d.iadd(v[0], v[1]);
            (vec![hyp], d.ile(ab, v[2]))
        }),
    ]
}
