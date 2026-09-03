//! Wall-clock cost of `decide` over ℤ and ℚ, and of `tactic::int`'s
//! `Then(Simp, Linarith)`, per emitted term (ADR-1591) — the same
//! measurement `examples/decide_and_tactic_cost.rs` makes for the ℕ
//! producers ADR-1589 added. Measure in `--release`; see
//! [`crate::simp::cost`]'s module docs for why a debug number is not a
//! number about anything shipped.

use std::time::{Duration, Instant};

use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{mk, req};
use crate::simp::cost::Row;
use crate::{Kernel, RatPrelude, build_int_prelude, build_rat_prelude};

fn row(label: &str, repeats: u32, total: Duration, search: Duration) -> Row {
    let n = f64::from(repeats);
    Row {
        label: label.to_owned(),
        search_ms: search.as_secs_f64() * 1000.0 / n,
        total_ms: total.as_secs_f64() * 1000.0 / n,
    }
}

/// Time `repeats` closed ℤ goals through `decide::int::run`.
fn time_int(label: &str, repeats: u32, goal_of: &dyn Fn(&mut IntDev<'_>) -> ExprId) -> Row {
    let mut kernel = Kernel::new();
    let p = build_int_prelude(&mut kernel).expect("Int prelude must build");
    let anon = kernel.anon();
    let root = kernel.name_str(anon, "decide_int_cost");
    let mut d = IntDev::new(&mut kernel, p);
    let warm_goal = goal_of(&mut d);
    let warm = super::int::run(&mut d, warm_goal).expect("warm-up must succeed");
    let warm_name = d.kernel().name_str(root, "warm");
    d.declare_theorem(warm_name, warm_goal, warm)
        .expect("warm-up accepted");

    let mut search = Duration::ZERO;
    let start = Instant::now();
    for i in 0..repeats {
        let name = d.kernel().name_str(root, format!("t{i}"));
        let t0 = Instant::now();
        let goal = goal_of(&mut d);
        let term = super::int::run(&mut d, goal).expect("the goal is decidable");
        search += t0.elapsed();
        d.declare_theorem(name, goal, term)
            .expect("the kernel must accept the emitted term");
    }
    row(label, repeats, start.elapsed(), search)
}

/// `sign * mag / 1` as a `Rat`, the recipe `rat_prelude::defs` uses for
/// `Rat.zero`/`Rat.one` (denominator `1`, positivity `Nat.le_refl 1`,
/// reducedness `gcd_one_right (natAbs numerator)`).
fn int_rat(d: &mut IntDev<'_>, p: &RatPrelude, mag: u32, negative: bool) -> ExprId {
    let numerator = if negative {
        let pred = d.num(mag - 1);
        d.neg_succ(pred)
    } else {
        let magnitude = d.num(mag);
        d.of_nat(magnitude)
    };
    let unit = d.num(1);
    let positive = d.lemma(p.int.nat.le_refl, &[unit]);
    let nat_abs = d.const_app(p.int.nat_abs, &[numerator]);
    let reduced = d.lemma(p.gcd_one_right, &[nat_abs]);
    mk(d, numerator, unit, positive, reduced)
}

/// Time `repeats` closed ℚ goals through `decide::rat::run`.
fn time_rat(
    label: &str,
    repeats: u32,
    goal_of: &dyn Fn(&mut IntDev<'_>, &RatPrelude) -> ExprId,
) -> Row {
    let mut kernel = Kernel::new();
    let p = build_rat_prelude(&mut kernel).expect("Rat prelude must build");
    let anon = kernel.anon();
    let root = kernel.name_str(anon, "decide_rat_cost");
    let mut d = IntDev::new(&mut kernel, p.int);
    let warm_goal = goal_of(&mut d, &p);
    let warm = super::rat::run(&mut d, &p, warm_goal).expect("warm-up must succeed");
    let warm_name = d.kernel().name_str(root, "warm");
    d.declare_theorem(warm_name, warm_goal, warm)
        .expect("warm-up accepted");

    let mut search = Duration::ZERO;
    let start = Instant::now();
    for i in 0..repeats {
        let name = d.kernel().name_str(root, format!("t{i}"));
        let t0 = Instant::now();
        let goal = goal_of(&mut d, &p);
        let term = super::rat::run(&mut d, &p, goal).expect("the goal is decidable");
        search += t0.elapsed();
        d.declare_theorem(name, goal, term)
            .expect("the kernel must accept the emitted term");
    }
    row(label, repeats, start.elapsed(), search)
}

/// Time `repeats` emissions of `tactic::int`'s `Then(Simp, Linarith)` on
/// `neg (x + y) <= neg x + neg y`, quantified over `x y : Int`.
fn time_int_then(label: &str, repeats: u32) -> Row {
    use crate::simp::int as simp_int;
    use crate::tactic::int::{self as tactic_int, Ctx, Tactic};

    let mut kernel = Kernel::new();
    let p = build_int_prelude(&mut kernel).expect("Int prelude must build");
    let anon = kernel.anon();
    let root = kernel.name_str(anon, "tactic_int_cost");
    let rules = simp_int::default_rules(&p);
    let ctx = Ctx {
        prelude: p,
        assumptions: &[],
        rules: &rules,
    };
    let tactic = Tactic::Then(Box::new(Tactic::Simp), Box::new(Tactic::Linarith));
    let mut d = IntDev::new(&mut kernel, p);
    let int_ty = d.int_ty();

    let emit = |d: &mut IntDev<'_>, name: crate::NameId, search: &mut Duration| {
        let t0 = Instant::now();
        let x_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y = d.kernel().fvar(y_fv);
        let xy = d.iadd(x, y);
        let lhs = d.ineg(xy);
        let nx = d.ineg(x);
        let ny = d.ineg(y);
        let rhs = d.iadd(nx, ny);
        let goal = d.ile(lhs, rhs);
        let proof = tactic_int::run(d, &ctx, &tactic, goal).expect("the goal is provable");
        *search += t0.elapsed();
        let ty = d.pi_fv(y_fv, int_ty, goal);
        let ty = d.pi_fv(x_fv, int_ty, ty);
        let value = d.lam_fv(y_fv, int_ty, proof);
        let value = d.lam_fv(x_fv, int_ty, value);
        d.declare_theorem(name, ty, value)
            .expect("the kernel must accept the emitted term");
    };

    let mut scratch = Duration::ZERO;
    let warm = d.kernel().name_str(root, "warm");
    emit(&mut d, warm, &mut scratch);

    let mut search = Duration::ZERO;
    let start = Instant::now();
    for i in 0..repeats {
        let name = d.kernel().name_str(root, format!("t{i}"));
        emit(&mut d, name, &mut search);
    }
    row(label, repeats, start.elapsed(), search)
}

/// Measure every ℤ/ℚ shape (ADR-1591), `repeats` emissions each.
#[must_use]
pub fn measure(repeats: u32) -> Vec<Row> {
    vec![
        time_int("decide  Eq Int (ofNat 3) (ofNat 3)", repeats, &|d| {
            let a = {
                let n = d.num(3);
                d.of_nat(n)
            };
            let b = {
                let n = d.num(3);
                d.of_nat(n)
            };
            d.ieq(a, b)
        }),
        time_int("decide  Int.le (negSucc 5) (negSucc 2)", repeats, &|d| {
            let a = {
                let n = d.num(5);
                d.neg_succ(n)
            };
            let b = {
                let n = d.num(2);
                d.neg_succ(n)
            };
            d.ile(a, b)
        }),
        time_int("decide  Int.lt (ofNat 2) (ofNat 5)", repeats, &|d| {
            let a = {
                let n = d.num(2);
                d.of_nat(n)
            };
            let b = {
                let n = d.num(5);
                d.of_nat(n)
            };
            d.ilt(a, b)
        }),
        time_rat("decide  Eq Rat 2 2", repeats, &|d, p| {
            let a = int_rat(d, p, 2, false);
            let b = int_rat(d, p, 2, false);
            req(d, a, b)
        }),
        time_rat("decide  Rat.le (-3) 0", repeats, &|d, p| {
            let a = int_rat(d, p, 3, true);
            let b = int_rat(d, p, 0, false);
            d.lemma(p.le, &[a, b])
        }),
        time_rat("decide  Rat.lt 2 5", repeats, &|d, p| {
            let a = int_rat(d, p, 2, false);
            let b = int_rat(d, p, 5, false);
            d.lemma(p.lt, &[a, b])
        }),
        time_int_then("Then(Simp,Linarith)  Int  -(x+y) <= -x + -y", repeats),
    ]
}
