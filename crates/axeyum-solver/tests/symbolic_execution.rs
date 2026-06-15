//! A symbolic-execution client of the incremental solver (the end use case).
//!
//! This is the consumer the whole stack is built backwards from: a tiny
//! register VM is executed *symbolically*, forking at each branch, with the
//! path condition maintained incrementally in [`IncrementalBvSolver`] via
//! `push`/`pop`. Infeasible branches are pruned by a `check`, and every input
//! that reaches a `Win` state is cross-checked by **concrete re-execution** of
//! the program — an independent (unicorn-style) ground truth, not another
//! solver. It demonstrates, with checked evidence, that the incremental engine
//! supports realistic path exploration.

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value};
use axeyum_solver::{AssumptionOutcome, CheckResult, IncrementalBvSolver};

/// A register-machine instruction. Registers are `BV(WIDTH)`; `Branch` forks on
/// equality to a constant.
#[derive(Debug, Clone, Copy)]
enum Insn {
    Const {
        dst: usize,
        value: u128,
    },
    Add {
        dst: usize,
        a: usize,
        b: usize,
    },
    Sub {
        dst: usize,
        a: usize,
        b: usize,
    },
    Mul {
        dst: usize,
        a: usize,
        b: usize,
    },
    Xor {
        dst: usize,
        a: usize,
        b: usize,
    },
    /// If `reg == value` jump to `then_pc`, else `else_pc`.
    BranchEq {
        reg: usize,
        value: u128,
        then_pc: usize,
        else_pc: usize,
    },
    Win,
    Lose,
}

const WIDTH: u32 = 16;
const MASK: u128 = (1 << WIDTH) - 1;
const REG_COUNT: usize = 4;
const INPUT_COUNT: usize = 2;
const MAX_STEPS: usize = 64;

/// A program plus the symbols of its symbolic inputs.
struct Program {
    code: Vec<Insn>,
    inputs: Vec<SymbolId>,
}

/// One discovered winning path: concrete input values, in input order.
type WinningInputs = Vec<u128>;

/// Symbolically executes `program`, returning the concrete inputs for every
/// path that reaches `Win`. Each path condition is maintained incrementally.
fn symbolically_execute(arena: &mut TermArena, program: &Program) -> Vec<WinningInputs> {
    let mut solver = IncrementalBvSolver::new();
    // Initial registers: inputs first, remaining registers zeroed.
    let mut regs: Vec<TermId> = program.inputs.iter().map(|&s| arena.var(s)).collect();
    let zero = arena.bv_const(WIDTH, 0).unwrap();
    while regs.len() < REG_COUNT {
        regs.push(zero);
    }

    let mut wins = Vec::new();
    explore(arena, &mut solver, program, regs, 0, MAX_STEPS, &mut wins);
    wins
}

#[allow(clippy::too_many_arguments)]
fn explore(
    arena: &mut TermArena,
    solver: &mut IncrementalBvSolver,
    program: &Program,
    regs: Vec<TermId>,
    pc: usize,
    fuel: usize,
    wins: &mut Vec<WinningInputs>,
) {
    if fuel == 0 || pc >= program.code.len() {
        return;
    }
    match program.code[pc] {
        Insn::Const { dst, value } => {
            let mut next = regs;
            next[dst] = arena.bv_const(WIDTH, value & MASK).unwrap();
            explore(arena, solver, program, next, pc + 1, fuel - 1, wins);
        }
        Insn::Add { dst, a, b } => {
            let term = arena.bv_add(regs[a], regs[b]).unwrap();
            step(arena, solver, program, regs, dst, term, pc, fuel, wins);
        }
        Insn::Sub { dst, a, b } => {
            let term = arena.bv_sub(regs[a], regs[b]).unwrap();
            step(arena, solver, program, regs, dst, term, pc, fuel, wins);
        }
        Insn::Mul { dst, a, b } => {
            let term = arena.bv_mul(regs[a], regs[b]).unwrap();
            step(arena, solver, program, regs, dst, term, pc, fuel, wins);
        }
        Insn::Xor { dst, a, b } => {
            let term = arena.bv_xor(regs[a], regs[b]).unwrap();
            step(arena, solver, program, regs, dst, term, pc, fuel, wins);
        }
        Insn::BranchEq {
            reg,
            value,
            then_pc,
            else_pc,
        } => {
            let value_term = arena.bv_const(WIDTH, value & MASK).unwrap();
            let cond = arena.eq(regs[reg], value_term).unwrap();
            let not_cond = arena.not(cond).unwrap();

            // Then-branch: feasible iff the path condition + (reg == value) is sat.
            solver.push().unwrap();
            solver.assert(arena, cond).unwrap();
            if feasible(arena, solver) {
                explore(
                    arena,
                    solver,
                    program,
                    regs.clone(),
                    then_pc,
                    fuel - 1,
                    wins,
                );
            }
            solver.pop();

            // Else-branch: feasible iff the path condition + (reg != value) is sat.
            solver.push().unwrap();
            solver.assert(arena, not_cond).unwrap();
            if feasible(arena, solver) {
                explore(arena, solver, program, regs, else_pc, fuel - 1, wins);
            }
            solver.pop();
        }
        Insn::Win => {
            if let CheckResult::Sat(model) = solver.check(arena).unwrap() {
                let inputs = program
                    .inputs
                    .iter()
                    .map(|&symbol| match model.get(symbol) {
                        Some(Value::Bv { value, .. }) => value,
                        _ => 0,
                    })
                    .collect();
                wins.push(inputs);
            }
        }
        Insn::Lose => {}
    }
}

#[allow(clippy::too_many_arguments)]
fn step(
    arena: &mut TermArena,
    solver: &mut IncrementalBvSolver,
    program: &Program,
    regs: Vec<TermId>,
    dst: usize,
    term: TermId,
    pc: usize,
    fuel: usize,
    wins: &mut Vec<WinningInputs>,
) {
    let mut next = regs;
    next[dst] = term;
    explore(arena, solver, program, next, pc + 1, fuel - 1, wins);
}

fn feasible(arena: &TermArena, solver: &mut IncrementalBvSolver) -> bool {
    matches!(solver.check(arena).unwrap(), CheckResult::Sat(_))
}

/// Concrete (oracle-free) re-execution of the program: the unicorn-style ground
/// truth used to confirm a solver-found input really reaches `Win`.
fn concretely_reaches_win(program: &Program, inputs: &[u128]) -> bool {
    let mut regs = [0u128; REG_COUNT];
    for (reg, &value) in regs.iter_mut().zip(inputs.iter()) {
        *reg = value & MASK;
    }
    let mut pc = 0usize;
    for _ in 0..MAX_STEPS {
        match program.code.get(pc) {
            Some(Insn::Const { dst, value }) => {
                regs[*dst] = value & MASK;
                pc += 1;
            }
            Some(Insn::Add { dst, a, b }) => {
                regs[*dst] = regs[*a].wrapping_add(regs[*b]) & MASK;
                pc += 1;
            }
            Some(Insn::Sub { dst, a, b }) => {
                regs[*dst] = regs[*a].wrapping_sub(regs[*b]) & MASK;
                pc += 1;
            }
            Some(Insn::Mul { dst, a, b }) => {
                regs[*dst] = regs[*a].wrapping_mul(regs[*b]) & MASK;
                pc += 1;
            }
            Some(Insn::Xor { dst, a, b }) => {
                regs[*dst] = (regs[*a] ^ regs[*b]) & MASK;
                pc += 1;
            }
            Some(Insn::BranchEq {
                reg,
                value,
                then_pc,
                else_pc,
            }) => {
                pc = if regs[*reg] == (value & MASK) {
                    *then_pc
                } else {
                    *else_pc
                };
            }
            Some(Insn::Win) => return true,
            Some(Insn::Lose) | None => return false,
        }
    }
    false
}

fn declare_inputs(arena: &mut TermArena) -> Vec<SymbolId> {
    (0..INPUT_COUNT)
        .map(|i| {
            arena
                .declare(&format!("in{i}"), Sort::BitVec(WIDTH))
                .unwrap()
        })
        .collect()
}

#[test]
fn single_stage_keycheck_is_solved_and_concretely_verified() {
    // r0 = (in0 ^ 0x1234) + 0x00ff; win iff r0 == 0xBEEF.
    let mut arena = TermArena::new();
    let inputs = declare_inputs(&mut arena);
    let program = Program {
        code: vec![
            Insn::Const {
                dst: 1,
                value: 0x1234,
            },
            Insn::Xor { dst: 0, a: 0, b: 1 },
            Insn::Const {
                dst: 1,
                value: 0x00ff,
            },
            Insn::Add { dst: 0, a: 0, b: 1 },
            Insn::BranchEq {
                reg: 0,
                value: 0xBEEF,
                then_pc: 5,
                else_pc: 6,
            },
            Insn::Win,
            Insn::Lose,
        ],
        inputs,
    };

    let wins = symbolically_execute(&mut arena, &program);
    assert!(
        !wins.is_empty(),
        "symbolic execution should find a winning input"
    );
    for inputs in &wins {
        assert!(
            concretely_reaches_win(&program, inputs),
            "solver-found input {inputs:?} must concretely reach Win"
        );
    }
}

#[test]
fn two_stage_conjunction_finds_inputs_satisfying_both_branches() {
    // a = in0 + in1; b = in0 ^ in1; win iff a == 0x2f2f AND b == 0x0f0f.
    // (Satisfiable: a - b = 0x2020 is even, so the carry bits a&b are
    // consistent with the xor bits.)
    let mut arena = TermArena::new();
    let inputs = declare_inputs(&mut arena);
    let program = Program {
        code: vec![
            Insn::Add { dst: 2, a: 0, b: 1 }, // r2 = in0 + in1
            Insn::Xor { dst: 3, a: 0, b: 1 }, // r3 = in0 ^ in1
            Insn::BranchEq {
                reg: 2,
                value: 0x2f2f,
                then_pc: 3,
                else_pc: 5,
            },
            Insn::BranchEq {
                reg: 3,
                value: 0x0f0f,
                then_pc: 4,
                else_pc: 5,
            },
            Insn::Win,
            Insn::Lose,
        ],
        inputs,
    };

    let wins = symbolically_execute(&mut arena, &program);
    assert!(!wins.is_empty(), "the conjunction is satisfiable");
    for inputs in &wins {
        let (x, y) = (inputs[0], inputs[1]);
        assert_eq!((x + y) & MASK, 0x2f2f, "first branch condition");
        assert_eq!((x ^ y) & MASK, 0x0f0f, "second branch condition");
        assert!(concretely_reaches_win(&program, inputs));
    }
}

#[test]
fn arithmetic_keycheck_with_multiplication_and_subtraction() {
    // r0 = in0 * in1; r0 = r0 - 1; win iff r0 == 0x000f (find factors of 0x10).
    let mut arena = TermArena::new();
    let inputs = declare_inputs(&mut arena);
    let program = Program {
        code: vec![
            Insn::Mul { dst: 0, a: 0, b: 1 },
            Insn::Const { dst: 2, value: 1 },
            Insn::Sub { dst: 0, a: 0, b: 2 },
            Insn::BranchEq {
                reg: 0,
                value: 0x000f,
                then_pc: 4,
                else_pc: 5,
            },
            Insn::Win,
            Insn::Lose,
        ],
        inputs,
    };

    let wins = symbolically_execute(&mut arena, &program);
    assert!(!wins.is_empty(), "in0 * in1 - 1 == 0x0f has solutions");
    for inputs in &wins {
        let (x, y) = (inputs[0], inputs[1]);
        assert_eq!((x.wrapping_mul(y).wrapping_sub(1)) & MASK, 0x000f);
        assert!(concretely_reaches_win(&program, inputs));
    }
}

#[test]
fn infeasible_target_yields_no_winning_paths() {
    // win iff in0 == 1 AND in0 == 2 — impossible; the explorer prunes it.
    let mut arena = TermArena::new();
    let inputs = declare_inputs(&mut arena);
    let program = Program {
        code: vec![
            Insn::BranchEq {
                reg: 0,
                value: 1,
                then_pc: 1,
                else_pc: 4,
            },
            Insn::BranchEq {
                reg: 0,
                value: 2,
                then_pc: 2,
                else_pc: 4,
            },
            Insn::Win,
            Insn::Lose,
            Insn::Lose,
        ],
        inputs,
    };

    let wins = symbolically_execute(&mut arena, &program);
    assert!(wins.is_empty(), "no input can satisfy in0==1 and in0==2");
}

// --- assumption-core path pruning (the reachability primitive) ----------------

/// The path-pruning primitive symbolic execution / reachability is built on:
/// feed candidate branch conditions as assumptions; on `unsat`, the returned
/// core names exactly the conditions that cannot co-occur with the path prefix.
#[test]
fn assumption_core_isolates_the_infeasible_branch_conditions() {
    let mut arena = TermArena::new();
    let xs = arena.declare("x", Sort::BitVec(8)).unwrap();
    let ys = arena.declare("y", Sort::BitVec(8)).unwrap();
    let x = arena.var(xs);
    let y = arena.var(ys);
    let mut solver = IncrementalBvSolver::new();

    // Path prefix: x >= 10 (a hard assertion on this path).
    let ten = arena.bv_const(8, 10).unwrap();
    let prefix = arena.bv_uge(x, ten).unwrap();
    solver.assert(&arena, prefix).unwrap();

    // Candidate branch conditions for the next step: x < 5 and y == 7.
    let five = arena.bv_const(8, 5).unwrap();
    let x_lt_5 = arena.bv_ult(x, five).unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let y_eq_7 = arena.eq(y, seven).unwrap();

    // x >= 10 ∧ x < 5 is infeasible; y == 7 is irrelevant to the conflict, so
    // the core must be exactly {x < 5}.
    match solver
        .check_assuming_core(&arena, &[x_lt_5, y_eq_7])
        .unwrap()
    {
        AssumptionOutcome::Unsat { core } => {
            assert_eq!(core, vec![x_lt_5], "core must isolate x<5, got {core:?}");
        }
        other => panic!("expected unsat with a core, got {other:?}"),
    }

    // A feasible branch (x < 20) is sat — the prefix is not over-pruned.
    let twenty = arena.bv_const(8, 20).unwrap();
    let x_lt_20 = arena.bv_ult(x, twenty).unwrap();
    assert!(
        matches!(
            solver.check_assuming_core(&arena, &[x_lt_20]).unwrap(),
            AssumptionOutcome::Sat(_)
        ),
        "x in [10,20) is reachable"
    );
}

/// When several assumptions are jointly (but not individually) responsible, the
/// core contains all of them.
#[test]
#[allow(clippy::similar_names)] // x_lt_3 / x_gt_5 are intentionally parallel
fn assumption_core_reports_a_jointly_infeasible_pair() {
    let mut arena = TermArena::new();
    let xs = arena.declare("x", Sort::BitVec(8)).unwrap();
    let x = arena.var(xs);
    let mut solver = IncrementalBvSolver::new();

    let three = arena.bv_const(8, 3).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let x_lt_3 = arena.bv_ult(x, three).unwrap(); // x < 3
    let x_gt_5 = arena.bv_ugt(x, five).unwrap(); // x > 5

    // Neither alone is unsat; together they are. The core is the whole pair, and
    // its negation is a sound conflict clause.
    match solver
        .check_assuming_core(&arena, &[x_lt_3, x_gt_5])
        .unwrap()
    {
        AssumptionOutcome::Unsat { core } => {
            assert_eq!(core.len(), 2, "both conditions are needed, got {core:?}");
            assert!(core.contains(&x_lt_3) && core.contains(&x_gt_5));
        }
        other => panic!("expected unsat with a 2-element core, got {other:?}"),
    }
}
