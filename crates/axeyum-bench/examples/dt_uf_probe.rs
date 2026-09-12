//! EXPERIMENT (dt-uf lane): what happens downstream when an uninterpreted
//! function takes or returns a datatype sort.
//!
//! ```sh
//! cargo run -q -p axeyum-bench --example dt_uf_probe -- <case>
//! ```
//! One case per process, so a stack overflow in one case does not hide the
//! others.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, solve};

fn report(name: &str, r: Result<CheckResult, axeyum_solver::SolverError>) {
    match r {
        Ok(CheckResult::Sat(_)) => println!("{name}: sat"),
        Ok(CheckResult::Unsat) => println!("{name}: unsat"),
        Ok(CheckResult::Unknown(reason)) => {
            println!(
                "{name}: unknown kind={:?} detail={}",
                reason.kind, reason.detail
            );
        }
        Err(e) => println!("{name}: ERR {e}"),
    }
}

fn cfg() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(5))
}

/// `Color = red | green`, a finite enum with no fields.
fn enum_dt(
    a: &mut TermArena,
) -> (
    axeyum_ir::DatatypeId,
    axeyum_ir::ConstructorId,
    axeyum_ir::ConstructorId,
) {
    let d = a.declare_datatype("Color");
    let red = a.add_constructor(d, "red", &[]);
    let green = a.add_constructor(d, "green", &[]);
    (d, red, green)
}

/// `Box = mk(v : Int)`.
fn box_dt(a: &mut TermArena) -> (axeyum_ir::DatatypeId, axeyum_ir::ConstructorId) {
    let d = a.declare_datatype("Box");
    let mk = a.add_constructor(d, "mk", &[("v".to_owned(), Sort::Int)]);
    (d, mk)
}

fn main() {
    let case = std::env::args().nth(1).unwrap_or_else(|| "all".to_owned());
    match case.as_str() {
        // ---- declaration gate itself -----------------------------------
        "declare" => {
            let mut a = TermArena::new();
            let (d, _, _) = enum_dt(&mut a);
            println!(
                "param D->Bool: {:?}",
                a.declare_fun("p", &[Sort::Datatype(d)], Sort::Bool)
                    .map(|_| "ok")
            );
            println!(
                "result Int->D: {:?}",
                a.declare_fun("f", &[Sort::Int], Sort::Datatype(d))
                    .map(|_| "ok")
            );
        }

        // ---- PARAMETER: the simplest possible query ---------------------
        // (declare-fun p (D) Bool) (declare-const o D) (assert (p o))
        // Expected sat. Does it terminate?
        "param-simple" => {
            let mut a = TermArena::new();
            let (d, _, _) = enum_dt(&mut a);
            let p = a
                .declare_fun("p", &[Sort::Datatype(d)], Sort::Bool)
                .unwrap();
            let o = a.declare("o", Sort::Datatype(d)).unwrap();
            let o = a.var(o);
            let t = a.apply(p, &[o]).unwrap();
            report("param-simple", solve(&mut a, &[t], &cfg()));
        }

        // ---- PARAMETER: congruence soundness ---------------------------
        // (= x y) /\ (p x) /\ not (p y)  -- MUST be unsat (congruence).
        "param-congruence" => {
            let mut a = TermArena::new();
            let (d, _, _) = enum_dt(&mut a);
            let p = a
                .declare_fun("p", &[Sort::Datatype(d)], Sort::Bool)
                .unwrap();
            let x = a.declare("x", Sort::Datatype(d)).unwrap();
            let y = a.declare("y", Sort::Datatype(d)).unwrap();
            let x = a.var(x);
            let y = a.var(y);
            let eq = a.eq(x, y).unwrap();
            let px = a.apply(p, &[x]).unwrap();
            let py = a.apply(p, &[y]).unwrap();
            let npy = a.not(py).unwrap();
            report(
                "param-congruence (MUST be unsat)",
                solve(&mut a, &[eq, px, npy], &cfg()),
            );
        }

        // ---- PARAMETER: exhaustiveness ---------------------------------
        // Color has exactly two constructors. p(red) /\ p(green) /\ not (p c)
        // is UNSAT only if the solver knows c is red or green. A `sat` here is
        // incomplete but not unsound; an `unsat` requires exhaustiveness.
        "param-exhaustive" => {
            let mut a = TermArena::new();
            let (d, red, green) = enum_dt(&mut a);
            let p = a
                .declare_fun("p", &[Sort::Datatype(d)], Sort::Bool)
                .unwrap();
            let r = a.construct(red, &[]).unwrap();
            let g = a.construct(green, &[]).unwrap();
            let c = a.declare("c", Sort::Datatype(d)).unwrap();
            let c = a.var(c);
            let pr = a.apply(p, &[r]).unwrap();
            let pg = a.apply(p, &[g]).unwrap();
            let pc = a.apply(p, &[c]).unwrap();
            let npc = a.not(pc).unwrap();
            report(
                "param-exhaustive (unsat iff exhaustive)",
                solve(&mut a, &[pr, pg, npc], &cfg()),
            );
        }

        // ---- PARAMETER: distinctness soundness -------------------------
        // p(red) /\ not p(green) -- MUST be sat (red != green, so no
        // congruence conflict). An `unsat` here would be a WRONG ANSWER:
        // it would mean the solver merged two distinct constructors.
        "param-distinct" => {
            let mut a = TermArena::new();
            let (d, red, green) = enum_dt(&mut a);
            let p = a
                .declare_fun("p", &[Sort::Datatype(d)], Sort::Bool)
                .unwrap();
            let r = a.construct(red, &[]).unwrap();
            let g = a.construct(green, &[]).unwrap();
            let pr = a.apply(p, &[r]).unwrap();
            let pg = a.apply(p, &[g]).unwrap();
            let npg = a.not(pg).unwrap();
            report(
                "param-distinct (MUST be sat)",
                solve(&mut a, &[pr, npg], &cfg()),
            );
        }

        // ---- RESULT: f : Int -> D --------------------------------------
        "result-test" => {
            let mut a = TermArena::new();
            let (d, mk) = box_dt(&mut a);
            let f = a.declare_fun("f", &[Sort::Int], Sort::Datatype(d)).unwrap();
            let one = a.int_const(1);
            let fa = a.apply(f, &[one]).unwrap();
            let t = a.dt_test(mk, fa).unwrap();
            report("result-test is-mk(f(1))", solve(&mut a, &[t], &cfg()));
        }

        // (= (select_mk_0 (f 1)) 5) /\ (= (select_mk_0 (f 1)) 6) -- unsat by
        // congruence on f. A `sat` would be WRONG.
        "result-congruence" => {
            let mut a = TermArena::new();
            let (d, mk) = box_dt(&mut a);
            let f = a.declare_fun("f", &[Sort::Int], Sort::Datatype(d)).unwrap();
            let one = a.int_const(1);
            let fa = a.apply(f, &[one]).unwrap();
            let sel = a.dt_select(mk, 0, fa).unwrap();
            let five = a.int_const(5);
            let six = a.int_const(6);
            let e5 = a.eq(sel, five).unwrap();
            let e6 = a.eq(sel, six).unwrap();
            report(
                "result-congruence (MUST NOT be sat)",
                solve(&mut a, &[e5, e6], &cfg()),
            );
        }

        // ---- MIXED: p over a datatype, plus real datatype reasoning -----
        // is-red(c) /\ p(c) /\ not p(red)  -- MUST be unsat: c = red.
        "mixed-refine" => {
            let mut a = TermArena::new();
            let (d, red, _green) = enum_dt(&mut a);
            let p = a
                .declare_fun("p", &[Sort::Datatype(d)], Sort::Bool)
                .unwrap();
            let c = a.declare("c", Sort::Datatype(d)).unwrap();
            let c = a.var(c);
            let isred = a.dt_test(red, c).unwrap();
            let pc = a.apply(p, &[c]).unwrap();
            let r = a.construct(red, &[]).unwrap();
            let pr = a.apply(p, &[r]).unwrap();
            let npr = a.not(pr).unwrap();
            report(
                "mixed-refine (MUST be unsat)",
                solve(&mut a, &[isred, pc, npr], &cfg()),
            );
        }

        // Read an SMT-LIB file: `dt_uf_probe file <path>`.
        "file" => {
            let path = std::env::args()
                .nth(2)
                .expect("usage: dt_uf_probe file <path>");
            let input = std::fs::read_to_string(&path).expect("read SMT-LIB file");
            match axeyum_solver::solve_smtlib(&input, &cfg()) {
                Ok(o) => report(&path, Ok(o.result)),
                Err(e) => println!("{path}: ERR {e}"),
            }
        }

        other => println!("unknown case {other}"),
    }
}
