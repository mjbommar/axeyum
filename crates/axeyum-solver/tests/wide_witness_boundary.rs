//! PROBE (temporary): what actually blocks a `> i128` witness end to end?
#![cfg(feature = "full")]

use axeyum_ir::{Assignment, Rational, Sort, TermArena, Value, eval};
use axeyum_solver::check_with_lra;

/// `x_i = 2 * x_{i+1}` for i in 0..N-1, plus `x_{N-1} >= 1`.
/// The unique vertex has `x_0 = 2^(N-1)`, which for N = 131 is `2^130 > i128::MAX`.
fn doubling_chain(n: usize) -> (TermArena, Vec<axeyum_ir::SymbolId>, Vec<axeyum_ir::TermId>) {
    let mut arena = TermArena::new();
    let syms: Vec<_> = (0..n)
        .map(|i| arena.declare(&format!("x{i}"), Sort::Real).unwrap())
        .collect();
    let vars: Vec<_> = syms.iter().map(|&s| arena.var(s)).collect();
    let two = arena.real_ratio(2, 1);
    let one = arena.real_ratio(1, 1);
    let mut assertions = Vec::new();
    for i in 0..(n - 1) {
        let doubled = arena.real_mul(two, vars[i + 1]).unwrap();
        assertions.push(arena.real_eq(vars[i], doubled).unwrap());
    }
    assertions.push(arena.real_ge(vars[n - 1], one).unwrap());
    (arena, syms, assertions)
}

fn pow2(k: u32) -> Rational {
    let mut acc = Rational::integer(1);
    for _ in 0..k {
        acc = acc.wide_add(acc).expect("pool has room");
    }
    acc
}

#[test]
fn probe_does_the_evaluator_replay_a_wide_real_model() {
    const N: usize = 131;
    let (arena, syms, assertions) = doubling_chain(N);
    let mut assignment = Assignment::new();
    for (i, &s) in syms.iter().enumerate() {
        let v = pow2((N - 1 - i) as u32);
        assignment.set(s, Value::Real(v));
    }
    for (i, &a) in assertions.iter().enumerate() {
        let r = eval(&arena, a, &assignment);
        match r {
            Ok(Value::Bool(true)) => {}
            other => {
                eprintln!("assertion {i} did NOT replay: {other:?}");
                eprintln!("(this is the finding; stopping at the first failure)");
                return;
            }
        }
    }
    eprintln!("every assertion replayed true under the wide model");
}

#[test]
fn probe_front_door_verdict_today() {
    const N: usize = 131;
    let (arena, _syms, assertions) = doubling_chain(N);
    let r = check_with_lra(&arena, &assertions);
    eprintln!("check_with_lra -> {r:?}");
}
