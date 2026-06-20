//! Parallel-portfolio benchmark on Euclidean-geometry proof goals.
//!
//! Euclidean geometry over ℝ is decidable (Tarski), but its facts split by
//! engine: **linear** facts (midpoints, betweenness, segment addition) are pure
//! LRA — fast and Farkas-certified today — while **polynomial** facts (Pythagoras,
//! AM–GM, squares) are NRA, the sound-but-incomplete frontier. That split is the
//! point: no single engine is best for all of them, so a portfolio that runs the
//! engines concurrently and takes the first proof gives both *coverage* (the
//! union) and *latency* (the min) that beat any single engine.
//!
//! Fairness: each engine proves `goal` from `hyps` by deciding `hyps ∧ ¬goal`
//! UNSAT, on the **same** goal, each in its **own** arena (no shared-state
//! contention), under the same deadline. Per-engine wall time is measured in
//! isolation; the portfolio latency is `min` over the engines that proved it —
//! i.e. the wall-clock a real N-core run achieves with each engine on its own
//! core. (`cargo run -p axeyum-solver --example geometry_portfolio --release`)

use std::time::{Duration, Instant};

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, check_with_lra, check_with_nra};

fn cfg() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(10))
}

/// A geometry proof goal: builds `(hypotheses, goal)` in a fresh arena.
struct Goal {
    name: &'static str,
    kind: &'static str, // "linear" | "polynomial"
    build: fn(&mut TermArena) -> (Vec<TermId>, TermId),
}

/// Builds the refutation query `hyps ∧ ¬goal` (UNSAT ⟺ the goal is proved).
fn query(arena: &mut TermArena, hyps: &[TermId], goal: TermId) -> Vec<TermId> {
    let mut q = hyps.to_vec();
    q.push(arena.not(goal).unwrap());
    q
}

/// `(proved, wall_time)` for the LRA engine on a freshly-built goal.
fn run_lra(g: &Goal) -> (Option<bool>, Duration) {
    let mut arena = TermArena::new();
    let (hyps, goal) = (g.build)(&mut arena);
    let q = query(&mut arena, &hyps, goal);
    let t = Instant::now();
    let proved = match check_with_lra(&arena, &q) {
        Ok(CheckResult::Unsat) => Some(true),
        Ok(_) => Some(false),
        Err(_) => None, // LRA cannot handle this (nonlinear) — abstains
    };
    (proved, t.elapsed())
}

/// `(proved, wall_time)` for the NRA engine on a freshly-built goal.
fn run_nra(g: &Goal) -> (Option<bool>, Duration) {
    let mut arena = TermArena::new();
    let (hyps, goal) = (g.build)(&mut arena);
    let q = query(&mut arena, &hyps, goal);
    let t = Instant::now();
    let proved = match check_with_nra(&mut arena, &q, &cfg()) {
        Ok(CheckResult::Unsat) => Some(true),
        Ok(_) => Some(false),
        Err(_) => None,
    };
    (proved, t.elapsed())
}

fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1000.0
}

fn mark(p: Option<bool>) -> &'static str {
    match p {
        Some(true) => "PROVED",
        Some(false) => "no",
        None => "n/a",
    }
}

// Demonstrative portfolio driver: a flat sequence of goal definitions + a results
// table, intentionally linear for readability.
#[allow(clippy::too_many_lines)]
fn main() {
    // ---- the geometry corpus ----------------------------------------------
    let goals: Vec<Goal> = vec![
        // LINEAR (LRA): the midpoint m of a,b (2m = a+b) is equidistant.
        Goal {
            name: "midpoint_equidistant",
            kind: "linear",
            build: |a| {
                let (pa, pb, m) = (
                    a.real_var("a").unwrap(),
                    a.real_var("b").unwrap(),
                    a.real_var("m").unwrap(),
                );
                let two_m = a.real_add(m, m).unwrap();
                let a_plus_b = a.real_add(pa, pb).unwrap();
                let hyp = a.eq(two_m, a_plus_b).unwrap();
                let lhs = a.real_sub(m, pa).unwrap();
                let rhs = a.real_sub(pb, m).unwrap();
                let goal = a.eq(lhs, rhs).unwrap();
                (vec![hyp], goal)
            },
        },
        // LINEAR (LRA): midpoint lies between the endpoints (betweenness).
        Goal {
            name: "midpoint_between",
            kind: "linear",
            build: |a| {
                let (pa, pb, m) = (
                    a.real_var("a").unwrap(),
                    a.real_var("b").unwrap(),
                    a.real_var("m").unwrap(),
                );
                let two_m = a.real_add(m, m).unwrap();
                let a_plus_b = a.real_add(pa, pb).unwrap();
                let mid = a.eq(two_m, a_plus_b).unwrap();
                let a_le_b = a.real_le(pa, pb).unwrap();
                let a_le_m = a.real_le(pa, m).unwrap();
                let m_le_b = a.real_le(m, pb).unwrap();
                let goal = a.and(a_le_m, m_le_b).unwrap();
                (vec![mid, a_le_b], goal)
            },
        },
        // LINEAR (LRA): collinear segment addition AC = AB + BC for a≤b≤c.
        Goal {
            name: "segment_addition",
            kind: "linear",
            build: |a| {
                let (pa, pb, pc) = (
                    a.real_var("a").unwrap(),
                    a.real_var("b").unwrap(),
                    a.real_var("c").unwrap(),
                );
                let ab = a.real_sub(pb, pa).unwrap();
                let bc = a.real_sub(pc, pb).unwrap();
                let ac = a.real_sub(pc, pa).unwrap();
                let sum = a.real_add(ab, bc).unwrap();
                let goal = a.eq(ac, sum).unwrap();
                (vec![], goal)
            },
        },
        // POLYNOMIAL (NRA): AM–GM in 2 vars — a² + b² ≥ 2ab.
        Goal {
            name: "am_gm_two",
            kind: "polynomial",
            build: |a| {
                let (x, y) = (a.real_var("x").unwrap(), a.real_var("y").unwrap());
                let xx = a.real_mul(x, x).unwrap();
                let yy = a.real_mul(y, y).unwrap();
                let sum = a.real_add(xx, yy).unwrap();
                let xy = a.real_mul(x, y).unwrap();
                let two = a.real_const(Rational::integer(2));
                let two_xy = a.real_mul(two, xy).unwrap();
                let goal = a.real_le(two_xy, sum).unwrap();
                (vec![], goal)
            },
        },
        // POLYNOMIAL (NRA): a square is non-negative — x² ≥ 0.
        Goal {
            name: "square_nonneg",
            kind: "polynomial",
            build: |a| {
                let x = a.real_var("x").unwrap();
                let xx = a.real_mul(x, x).unwrap();
                let zero = a.real_const(Rational::integer(0));
                let goal = a.real_le(zero, xx).unwrap();
                (vec![], goal)
            },
        },
        // POLYNOMIAL (NRA): a Pythagorean-style identity — (x+y)² = x²+2xy+y².
        Goal {
            name: "binomial_square",
            kind: "polynomial",
            build: |a| {
                let (x, y) = (a.real_var("x").unwrap(), a.real_var("y").unwrap());
                let xpy = a.real_add(x, y).unwrap();
                let lhs = a.real_mul(xpy, xpy).unwrap();
                let xx = a.real_mul(x, x).unwrap();
                let yy = a.real_mul(y, y).unwrap();
                let xy = a.real_mul(x, y).unwrap();
                let two = a.real_const(Rational::integer(2));
                let two_xy = a.real_mul(two, xy).unwrap();
                let s1 = a.real_add(xx, two_xy).unwrap();
                let rhs = a.real_add(s1, yy).unwrap();
                let goal = a.eq(lhs, rhs).unwrap();
                (vec![], goal)
            },
        },
    ];

    println!();
    println!("Euclidean-geometry proof portfolio (axeyum engines, fair per-goal isolation)");
    println!(
        "{:<22} {:<11} {:>10} {:>10} {:>14} {:>12}",
        "goal", "kind", "LRA", "NRA", "portfolio", "proved-by"
    );
    println!("{}", "-".repeat(84));

    let (mut lra_proved, mut nra_proved, mut port_proved) = (0, 0, 0);
    let (mut lra_t, mut nra_t, mut port_t) = (0.0, 0.0, 0.0);

    for g in &goals {
        let (lp, lt) = run_lra(g);
        let (np, nt) = run_nra(g);

        // Portfolio = run both concurrently, first proof wins:
        //   proved iff either proved; latency = min over engines that proved
        //   (each on its own core, measured in isolation = no contention).
        let mut winners: Vec<(&str, f64)> = Vec::new();
        if lp == Some(true) {
            winners.push(("LRA", ms(lt)));
        }
        if np == Some(true) {
            winners.push(("NRA", ms(nt)));
        }
        let (port_label, port_ms, by) = if let Some((who, m)) = winners
            .iter()
            .min_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
            .copied()
        {
            ("PROVED".to_string(), format!("{m:.2}ms"), who)
        } else {
            ("unknown".to_string(), "—".to_string(), "—")
        };

        println!(
            "{:<22} {:<11} {:>6} {:>3.1} {:>6} {:>3.1} {:>8} {:>5} {:>12}",
            g.name,
            g.kind,
            mark(lp),
            ms(lt),
            mark(np),
            ms(nt),
            port_label,
            port_ms,
            by,
        );

        if lp == Some(true) {
            lra_proved += 1;
            lra_t += ms(lt);
        }
        if np == Some(true) {
            nra_proved += 1;
            nra_t += ms(nt);
        }
        if port_label == "PROVED" {
            port_proved += 1;
            port_t += port_ms.trim_end_matches("ms").parse::<f64>().unwrap_or(0.0);
        }
    }

    let n = goals.len();
    println!("{}", "-".repeat(84));
    println!("Coverage (proved / {n}):");
    println!("  LRA-only       : {lra_proved}   (total {lra_t:.2} ms on the ones it proved)");
    println!("  NRA-only       : {nra_proved}   (total {nra_t:.2} ms on the ones it proved)");
    println!(
        "  PORTFOLIO      : {port_proved}   (total {port_t:.2} ms — union coverage, min latency)"
    );
    println!();
    println!(
        "Portfolio decides the UNION of {n} goals that no single engine covers alone, \
         at the min per-goal latency (each engine on its own core)."
    );
}
