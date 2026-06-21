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

/// The honest outcome of running one engine on one refutation query. We keep the
/// three solver answers DISTINCT — collapsing `Unknown` into "no" would read as a
/// disproof when it is merely an incomplete search (and would hide the cardinal
/// Sat-vs-Unknown line). A `Countermodel` (the engine found `hyps ∧ ¬goal` SAT)
/// would mean the *goal is false*, not that the engine gave up.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Proved,        // Unsat: hyps ∧ ¬goal has no model ⇒ the goal is proved
    Countermodel,  // Sat: a concrete counterexample to the goal exists
    Unknown,       // sound-but-incomplete: budget exhausted, no verdict
    NotApplicable, // the engine abstains (e.g. LRA on a nonlinear query)
}

/// Map a solver result to the honest verdict. `Sat`/`Unknown` never collapse.
fn verdict(r: &Result<CheckResult, axeyum_solver::SolverError>) -> Verdict {
    match r {
        Ok(CheckResult::Unsat) => Verdict::Proved,
        Ok(CheckResult::Sat(_)) => Verdict::Countermodel,
        Ok(CheckResult::Unknown(_)) => Verdict::Unknown,
        Err(_) => Verdict::NotApplicable,
    }
}

/// `(verdict, wall_time)` for the LRA engine on a freshly-built goal.
fn run_lra(g: &Goal) -> (Verdict, Duration) {
    let mut arena = TermArena::new();
    let (hyps, goal) = (g.build)(&mut arena);
    let q = query(&mut arena, &hyps, goal);
    let t = Instant::now();
    let v = verdict(&check_with_lra(&arena, &q));
    (v, t.elapsed())
}

/// `(verdict, wall_time)` for the NRA engine on a freshly-built goal.
fn run_nra(g: &Goal) -> (Verdict, Duration) {
    let mut arena = TermArena::new();
    let (hyps, goal) = (g.build)(&mut arena);
    let q = query(&mut arena, &hyps, goal);
    let t = Instant::now();
    let v = verdict(&check_with_nra(&mut arena, &q, &cfg()));
    (v, t.elapsed())
}

fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1000.0
}

fn mark(v: Verdict) -> &'static str {
    match v {
        Verdict::Proved => "PROVED",
        Verdict::Countermodel => "FALSE", // a real countermodel ⇒ the goal is false
        Verdict::Unknown => "unknown",
        Verdict::NotApplicable => "n/a",
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
        if lp == Verdict::Proved {
            winners.push(("LRA", ms(lt)));
        }
        if np == Verdict::Proved {
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

        if lp == Verdict::Proved {
            lra_proved += 1;
            lra_t += ms(lt);
        }
        if np == Verdict::Proved {
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

    #[cfg(feature = "z3")]
    run_z3_inproc();
    #[cfg(not(feature = "z3"))]
    println!("\n(Z3 in-process column: rebuild with `--features z3` for the fair libz3 row.)");
}

/// In-process Z3 (libz3 via the `z3` crate) on the *same* goals — one context
/// reused across goals, so the measured `check()` is pure solve time, with **no**
/// subprocess spawn / binary load / SMT-LIB parse tax. This is the apples-to-apples
/// solver-speed row (vs the per-query subprocess measurement, which adds ~106 ms).
#[cfg(feature = "z3")]
#[allow(clippy::too_many_lines)]
fn run_z3_inproc() {
    use z3::ast::{Bool, Real};
    use z3::{Config, SatResult, Solver, with_z3_config};

    println!();
    println!("Z3 in-process (libz3, one reused context — no subprocess/parse tax):");
    println!("{:<22} {:<11} {:>10} {:>10}", "goal", "kind", "z3", "ms");
    println!("{}", "-".repeat(56));

    with_z3_config(&Config::new(), || {
        let two = Real::from_rational(2, 1);
        let zero = Real::from_rational(0, 1);

        // Each row: (name, kind, hyps ∧ ¬goal). UNSAT ⟺ goal proved.
        let mut rows: Vec<(&str, &str, Vec<Bool>)> = Vec::new();

        // 1 midpoint_equidistant: 2m=a+b ⊢ m-a = b-m.
        {
            let (a, b, m) = (
                Real::new_const("a"),
                Real::new_const("b"),
                Real::new_const("m"),
            );
            let hyp = (&m + &m).eq(&(&a + &b));
            let neg = (&m - &a).eq(&(&b - &m)).not();
            rows.push(("midpoint_equidistant", "linear", vec![hyp, neg]));
        }
        // 2 midpoint_between: 2m=a+b, a≤b ⊢ a≤m ∧ m≤b.
        {
            let (a, b, m) = (
                Real::new_const("a"),
                Real::new_const("b"),
                Real::new_const("m"),
            );
            let hyp = (&m + &m).eq(&(&a + &b));
            let a_le_b = a.le(&b);
            let conj = a.le(&m) & m.le(&b);
            rows.push(("midpoint_between", "linear", vec![hyp, a_le_b, conj.not()]));
        }
        // 3 segment_addition: ⊢ (c-a) = (b-a)+(c-b).
        {
            let (a, b, c) = (
                Real::new_const("a"),
                Real::new_const("b"),
                Real::new_const("c"),
            );
            let ac = &c - &a;
            let sum = &(&b - &a) + &(&c - &b);
            rows.push(("segment_addition", "linear", vec![ac.eq(&sum).not()]));
        }
        // 4 am_gm_two: ⊢ x²+y² ≥ 2xy.
        {
            let (x, y) = (Real::new_const("x"), Real::new_const("y"));
            let lhs = &two * &(&x * &y);
            let rhs = &(&x * &x) + &(&y * &y);
            rows.push(("am_gm_two", "polynomial", vec![lhs.le(&rhs).not()]));
        }
        // 5 square_nonneg: ⊢ x² ≥ 0.
        {
            let x = Real::new_const("x");
            let xx = &x * &x;
            rows.push(("square_nonneg", "polynomial", vec![zero.le(&xx).not()]));
        }
        // 6 binomial_square: ⊢ (x+y)² = x²+2xy+y².
        {
            let (x, y) = (Real::new_const("x"), Real::new_const("y"));
            let xpy = &x + &y;
            let lhs = &xpy * &xpy;
            let rhs = &(&(&x * &x) + &(&two * &(&x * &y))) + &(&y * &y);
            rows.push(("binomial_square", "polynomial", vec![lhs.eq(&rhs).not()]));
        }

        let n = rows.len();
        let (mut proved, mut total) = (0, 0.0);
        for (name, kind, q) in &rows {
            let solver = Solver::new();
            for c in q {
                solver.assert(c);
            }
            let t = std::time::Instant::now();
            let r = solver.check();
            let ms = t.elapsed().as_secs_f64() * 1000.0;
            let label = match r {
                SatResult::Unsat => "PROVED",
                SatResult::Sat => "no",
                SatResult::Unknown => "unknown",
            };
            if r == SatResult::Unsat {
                proved += 1;
                total += ms;
            }
            println!("{name:<22} {kind:<11} {label:>10} {ms:>9.3}");
        }
        println!("{}", "-".repeat(56));
        println!("Z3 in-process: proved {proved}/{n}  (total check() {total:.3} ms — pure solve)");
    });
}
