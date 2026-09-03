//! Wall-clock cost of `decide` alone and of `Then(Simp, Linarith)`, per
//! emitted term — the same measurement `linarith::cost`/`ring::cost`/
//! `simp::cost` make for their own producers
//! (`07-the-cost-model-and-pareto-position.md` §3), for the two producers
//! ADR-1589 adds. No new `cost` module: the combinator has no search of its
//! own to characterize beyond "the sum of what it calls", so this is a
//! direct timer around `decide::run`/`tactic::run`, not a library API.
//!
//! `--release` is MANDATORY — see `simp_cost.rs`'s module docs for why a
//! debug number is not a number about anything shipped.
//!
//! ```sh
//! cargo run --release -p axeyum-lean-kernel --example decide_and_tactic_cost
//! ```

use std::time::{Duration, Instant};

use axeyum_lean_kernel::simp::nat as simp_nat;
use axeyum_lean_kernel::tactic::{Ctx, Tactic};
use axeyum_lean_kernel::{
    Kernel, NatDev, NatOps, NatPrelude, build_nat_prelude, decide, on_a_deep_stack, tactic,
};

const REPEATS: u32 = 200;

fn fresh() -> (Kernel, NatPrelude) {
    let mut k = Kernel::new();
    let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
    (k, p)
}

/// `decide` on a small closed `Eq`/`Nat.le` goal.
fn decide_row(label: &str, goal_of: &dyn Fn(&mut NatDev<'_>) -> axeyum_lean_kernel::ExprId) {
    let (mut k0, p0) = fresh();
    let mut d = NatDev::new(&mut k0, p0);
    let root = {
        let anon = d.kernel().anon();
        d.kernel().name_str(anon, "decide_cost")
    };

    // Warm-up, uncharged.
    {
        let goal = goal_of(&mut d);
        let term = decide::run(&mut d, &p0, goal).expect("the warm-up goal must be provable");
        let name = d.kernel().name_str(root, "warm");
        d.declare_theorem(name, goal, term)
            .expect("the kernel must accept the warm-up term");
    }

    let mut search = Duration::ZERO;
    let start = Instant::now();
    for i in 0..REPEATS {
        let goal = goal_of(&mut d);
        let t0 = Instant::now();
        let term = decide::run(&mut d, &p0, goal).expect("the goal is provable");
        search += t0.elapsed();
        let name = d.kernel().name_str(root, format!("t{i}"));
        d.declare_theorem(name, goal, term)
            .expect("the kernel must accept the emitted term");
    }
    let total = start.elapsed();
    let n = f64::from(REPEATS);
    println!(
        "{label:42}  search+emit {:7.4} ms   +kernel {:7.4} ms",
        search.as_secs_f64() * 1000.0 / n,
        total.as_secs_f64() * 1000.0 / n,
    );
}

/// `Then(Simp, Linarith)` on `Le n (mul 2 n)` given `Lt zero n` — the exact
/// shape this ADR's retirement targets prove, so the number is about the
/// retirement, not a synthetic stand-in.
fn then_row() {
    let (mut k0, p0) = fresh();
    let mut d = NatDev::new(&mut k0, p0);
    let root = {
        let anon = d.kernel().anon();
        d.kernel().name_str(anon, "then_cost")
    };
    let rules = simp_nat::default_rules::<NatDev<'_>>(&p0);
    let tac = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Linarith));

    #[allow(clippy::type_complexity)]
    let build = |d: &mut NatDev<'_>| -> (
        axeyum_lean_kernel::ExprId,
        [(axeyum_lean_kernel::ExprId, axeyum_lean_kernel::ExprId); 1],
        u64,
        u64,
    ) {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let zero = d.zero();
        let pos_ty = d.lt(zero, n);
        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);
        let two = d.num(2);
        let mul_two_n = d.mul(two, n);
        let goal = d.lt(n, mul_two_n);
        (goal, [(pos_ty, pos)], n_fv, pos_fv)
    };

    let emit =
        |d: &mut NatDev<'_>, ctx: &Ctx<'_, NatDev<'_>>, n_fv: u64, pos_fv: u64, goal, term| {
            let nat = d.nat_ty();
            let pos_ty = ctx.assumptions[0].0;
            let ty0 = d.arrow(pos_ty, goal);
            let value0 = d.lam_fv(pos_fv, pos_ty, term);
            let ty = d.pi_fv(n_fv, nat, ty0);
            let value = d.lam_fv(n_fv, nat, value0);
            (ty, value)
        };

    // Warm-up.
    {
        let (goal, assumptions, n_fv, pos_fv) = build(&mut d);
        let ctx = Ctx {
            prelude: p0,
            assumptions: &assumptions,
            rules: &rules,
        };
        let term =
            tactic::run(&mut d, &ctx, &tac, goal).expect("the warm-up goal must be provable");
        let (ty, value) = emit(&mut d, &ctx, n_fv, pos_fv, goal, term);
        let name = d.kernel().name_str(root, "warm");
        d.declare_theorem(name, ty, value)
            .expect("the kernel must accept the warm-up term");
    }

    let mut search = Duration::ZERO;
    let start = Instant::now();
    for i in 0..REPEATS {
        let (goal, assumptions, n_fv, pos_fv) = build(&mut d);
        let ctx = Ctx {
            prelude: p0,
            assumptions: &assumptions,
            rules: &rules,
        };
        let t0 = Instant::now();
        let term = tactic::run(&mut d, &ctx, &tac, goal).expect("the goal is provable");
        search += t0.elapsed();
        let (ty, value) = emit(&mut d, &ctx, n_fv, pos_fv, goal, term);
        let name = d.kernel().name_str(root, format!("t{i}"));
        d.declare_theorem(name, ty, value)
            .expect("the kernel must accept the emitted term");
    }
    let total = start.elapsed();
    let n = f64::from(REPEATS);
    println!(
        "{:42}  search+emit {:7.4} ms   +kernel {:7.4} ms",
        "Then(Simp, Linarith)  n < 2n  (Lt 0 n)",
        search.as_secs_f64() * 1000.0 / n,
        total.as_secs_f64() * 1000.0 / n,
    );
}

fn main() {
    on_a_deep_stack(|| {
        if cfg!(debug_assertions) {
            eprintln!(
                "decide_and_tactic_cost: NOT --release. Debug frames cost up to 32x here. \
                 Re-run with --release."
            );
        }
        println!(
            "decide / tactic cost, {REPEATS} emissions per shape, prelude built once per shape"
        );
        println!("{:-<80}", "");
        decide_row("decide  Eq Nat (2+3) 5", &|d| {
            let two = d.num(2);
            let three = d.num(3);
            let five = d.num(5);
            let sum = d.add(two, three);
            d.eq(sum, five)
        });
        decide_row("decide  Nat.le 2 9", &|d| {
            let two = d.num(2);
            let nine = d.num(9);
            d.le(two, nine)
        });
        then_row();
    });
}
