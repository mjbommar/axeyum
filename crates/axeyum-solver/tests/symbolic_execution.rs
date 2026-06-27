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

use axeyum_ir::{ArraySortKey, Sort, SymbolId, TermArena, TermId, Value};
use axeyum_solver::{
    AssumptionOutcome, CfgExploreConfig, CfgStep, CheckResult, IncrementalBvSolver, PathStatus,
    SymbolicExecutor, SymbolicMemory, TinyBvBasicBlock, TinyBvCfgEdge, TinyBvCfgEdgeKind,
    TinyBvConcreteOutcome, TinyBvInsn, TinyBvProgram, TinyBvReachabilityStatus, TinyBvSafetyStatus,
    TinyBvWitness,
};

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

#[derive(Debug, Clone)]
struct VmState {
    pc: usize,
    regs: Vec<TermId>,
    fuel: usize,
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

/// The public CFG-shaped explorer over [`SymbolicExecutor`]: the frontend
/// provides the transfer relation and concrete replay hooks, while axeyum owns
/// branch feasibility, push/pop, pruning, model-witnessed target reporting, and
/// checked witness bucketing.
fn symbolically_execute_with_checked_cfg_explorer(
    arena: &mut TermArena,
    program: &Program,
) -> Vec<WinningInputs> {
    let mut regs: Vec<TermId> = program.inputs.iter().map(|&s| arena.var(s)).collect();
    let zero = arena.bv_const(WIDTH, 0).unwrap();
    while regs.len() < REG_COUNT {
        regs.push(zero);
    }
    let initial = VmState {
        pc: 0,
        regs,
        fuel: MAX_STEPS,
    };

    let mut executor = SymbolicExecutor::new();
    let outcome = executor
        .explore_cfg_checked(
            arena,
            initial,
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
            |arena, state| {
                if state.fuel == 0 || state.pc >= program.code.len() {
                    return Ok(CfgStep::Stop);
                }
                let next_fuel = state.fuel - 1;
                match program.code[state.pc] {
                    Insn::Const { dst, value } => {
                        let mut next = state;
                        next.regs[dst] = arena.bv_const(WIDTH, value & MASK).unwrap();
                        next.pc += 1;
                        next.fuel = next_fuel;
                        Ok(CfgStep::Continue(next))
                    }
                    Insn::Add { dst, a, b } => {
                        let mut next = state;
                        next.regs[dst] = arena.bv_add(next.regs[a], next.regs[b]).unwrap();
                        next.pc += 1;
                        next.fuel = next_fuel;
                        Ok(CfgStep::Continue(next))
                    }
                    Insn::Sub { dst, a, b } => {
                        let mut next = state;
                        next.regs[dst] = arena.bv_sub(next.regs[a], next.regs[b]).unwrap();
                        next.pc += 1;
                        next.fuel = next_fuel;
                        Ok(CfgStep::Continue(next))
                    }
                    Insn::Mul { dst, a, b } => {
                        let mut next = state;
                        next.regs[dst] = arena.bv_mul(next.regs[a], next.regs[b]).unwrap();
                        next.pc += 1;
                        next.fuel = next_fuel;
                        Ok(CfgStep::Continue(next))
                    }
                    Insn::Xor { dst, a, b } => {
                        let mut next = state;
                        next.regs[dst] = arena.bv_xor(next.regs[a], next.regs[b]).unwrap();
                        next.pc += 1;
                        next.fuel = next_fuel;
                        Ok(CfgStep::Continue(next))
                    }
                    Insn::BranchEq {
                        reg,
                        value,
                        then_pc,
                        else_pc,
                    } => {
                        let value_term = arena.bv_const(WIDTH, value & MASK).unwrap();
                        let condition = arena.eq(state.regs[reg], value_term).unwrap();
                        let mut if_true = state.clone();
                        if_true.pc = then_pc;
                        if_true.fuel = next_fuel;
                        let mut if_false = state;
                        if_false.pc = else_pc;
                        if_false.fuel = next_fuel;
                        Ok(CfgStep::Branch {
                            condition,
                            if_true,
                            if_false,
                        })
                    }
                    Insn::Win => Ok(CfgStep::Target(state)),
                    Insn::Lose => Ok(CfgStep::Stop),
                }
            },
            |model, _state| {
                let mut inputs = Vec::new();
                for &symbol in &program.inputs {
                    let Some(Value::Bv { value, .. }) = model.get(symbol) else {
                        return Ok(None);
                    };
                    inputs.push(value);
                }
                Ok(Some(inputs))
            },
            |state, inputs| {
                Ok(matches!(program.code.get(state.pc), Some(Insn::Win))
                    && concretely_reaches_win(program, inputs))
            },
        )
        .unwrap();
    assert!(
        !outcome.truncated,
        "tiny VM exploration should finish within configured limits"
    );
    assert_eq!(
        outcome.undecided_targets, 0,
        "reported target coverage must be model-decided"
    );
    assert!(
        outcome.missing_witnesses.is_empty(),
        "every symbolic target should lift to concrete VM inputs"
    );
    assert!(
        outcome.mismatches.is_empty(),
        "every lifted witness should pass concrete replay"
    );

    outcome
        .verified
        .iter()
        .map(|hit| {
            assert!(
                matches!(program.code.get(hit.state.pc), Some(Insn::Win)),
                "the target frontend state should be the Win instruction"
            );
            assert!(
                !hit.path_condition.is_empty(),
                "a winning path should carry branch constraints"
            );
            hit.witness.clone()
        })
        .collect()
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
fn cfg_explorer_finds_winning_paths_and_concrete_witnesses() {
    // Same shape as the manual DFS case, but exercised through the public
    // `SymbolicExecutor::explore_cfg` harness. The frontend provides transfer
    // states and branch conditions; the harness owns solver scopes and pruning.
    let mut arena = TermArena::new();
    let inputs = declare_inputs(&mut arena);
    let program = Program {
        code: vec![
            Insn::Add { dst: 2, a: 0, b: 1 },
            Insn::Xor { dst: 3, a: 0, b: 1 },
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

    let wins = symbolically_execute_with_checked_cfg_explorer(&mut arena, &program);
    assert!(!wins.is_empty(), "CFG explorer should find a winning path");
    for inputs in &wins {
        let (x, y) = (inputs[0], inputs[1]);
        assert_eq!((x + y) & MASK, 0x2f2f);
        assert_eq!((x ^ y) & MASK, 0x0f0f);
        assert!(
            concretely_reaches_win(&program, inputs),
            "solver-found CFG input {inputs:?} must concretely reach Win"
        );
    }
}

#[test]
fn tiny_bv_program_frontend_lifts_explores_and_replays() {
    // This is the reusable P4.2 frontend surface: the program validates its
    // tiny target IR, lifts instructions into symbolic CFG steps, extracts
    // concrete model witnesses, and independently replays them.
    let mut arena = TermArena::new();
    let program = TinyBvProgram::new(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        vec![
            TinyBvInsn::Add { dst: 2, a: 0, b: 1 },
            TinyBvInsn::Xor { dst: 3, a: 0, b: 1 },
            TinyBvInsn::BranchEq {
                reg: 2,
                value: 0x2f2f,
                then_pc: 3,
                else_pc: 5,
            },
            TinyBvInsn::BranchEq {
                reg: 3,
                value: 0x0f0f,
                then_pc: 4,
                else_pc: 5,
            },
            TinyBvInsn::Win,
            TinyBvInsn::Lose,
        ],
    )
    .unwrap();

    let outcome = program
        .explore_checked(
            &mut arena,
            "tiny_input",
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
        )
        .unwrap();

    assert!(!outcome.truncated);
    assert_eq!(outcome.undecided_targets, 0);
    assert!(outcome.missing_witnesses.is_empty());
    assert!(outcome.mismatches.is_empty());
    assert!(
        !outcome.verified.is_empty(),
        "library frontend should find a concrete winning witness"
    );
    for hit in &outcome.verified {
        assert_eq!(
            program.concrete_run(&hit.witness),
            TinyBvConcreteOutcome::Win
        );
        assert!(matches!(
            program.code().get(hit.state.pc),
            Some(TinyBvInsn::Win)
        ));
        assert!(
            !hit.path_condition.is_empty(),
            "winning path should preserve branch constraints"
        );
        let [x, y] = hit.witness.inputs[..] else {
            panic!("test program has exactly two input words");
        };
        assert_eq!((x + y) & MASK, 0x2f2f);
        assert_eq!((x ^ y) & MASK, 0x0f0f);
    }
}

#[test]
fn tiny_bv_reachability_reports_pc_witnesses() {
    let mut arena = TermArena::new();
    let program = TinyBvProgram::new(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        vec![
            TinyBvInsn::Add { dst: 2, a: 0, b: 1 },
            TinyBvInsn::Xor { dst: 3, a: 0, b: 1 },
            TinyBvInsn::BranchEq {
                reg: 2,
                value: 0x2f2f,
                then_pc: 3,
                else_pc: 5,
            },
            TinyBvInsn::BranchEq {
                reg: 3,
                value: 0x0f0f,
                then_pc: 4,
                else_pc: 5,
            },
            TinyBvInsn::Win,
            TinyBvInsn::Lose,
        ],
    )
    .unwrap();

    let reach = program
        .reach_pc_checked(
            &mut arena,
            "reach_input",
            4,
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
        )
        .unwrap();

    assert_eq!(reach.status(), TinyBvReachabilityStatus::Reachable);
    assert!(reach.is_reachable());
    assert!(!reach.outcome.verified.is_empty());
    for hit in &reach.outcome.verified {
        assert_eq!(hit.state.pc, 4);
        assert!(program.concrete_reaches_pc(&hit.witness, 4));
        let trace = program.concrete_trace(&hit.witness);
        assert!(trace.reaches_pc(4));
        assert_eq!(trace.outcome, TinyBvConcreteOutcome::Win);
        assert_eq!(
            trace.steps.iter().map(|step| step.pc).collect::<Vec<_>>(),
            vec![0, 1, 2, 3, 4]
        );
        let [x, y] = hit.witness.inputs[..] else {
            panic!("test program has exactly two input words");
        };
        assert_eq!((x + y) & MASK, 0x2f2f);
        assert_eq!((x ^ y) & MASK, 0x0f0f);
    }

    let safety = program
        .check_pc_safety_checked(
            &mut arena,
            "unsafe_input",
            4,
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
        )
        .unwrap();
    assert_eq!(safety.status(), TinyBvSafetyStatus::Unsafe);
    assert!(safety.is_unsafe());
}

#[test]
fn tiny_bv_safety_reports_unreachable_when_search_is_exhaustive() {
    let mut arena = TermArena::new();
    let program = TinyBvProgram::new(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        vec![
            TinyBvInsn::BranchEq {
                reg: 0,
                value: 1,
                then_pc: 1,
                else_pc: 4,
            },
            TinyBvInsn::BranchEq {
                reg: 0,
                value: 2,
                then_pc: 2,
                else_pc: 4,
            },
            TinyBvInsn::Win,
            TinyBvInsn::Lose,
            TinyBvInsn::Lose,
        ],
    )
    .unwrap();

    let safety = program
        .check_pc_safety_checked(
            &mut arena,
            "safe_input",
            2,
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
        )
        .unwrap();

    assert_eq!(safety.status(), TinyBvSafetyStatus::Safe);
    assert!(safety.is_safe());
    assert_eq!(
        safety.reachability.status(),
        TinyBvReachabilityStatus::Unreachable
    );
    assert!(safety.reachability.is_unreachable());
    assert!(safety.reachability.outcome.verified.is_empty());
    assert!(!safety.reachability.outcome.truncated);
    assert_eq!(safety.reachability.outcome.unknown_branches, 0);
    assert_eq!(safety.reachability.outcome.undecided_targets, 0);
}

#[test]
fn tiny_bv_memory_store_load_reachability_replays() {
    let mut arena = TermArena::new();
    let program = TinyBvProgram::new(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        vec![
            TinyBvInsn::Const {
                dst: 2,
                value: 0x0010,
            },
            TinyBvInsn::Store { addr: 2, src: 0 },
            TinyBvInsn::Load { dst: 3, addr: 2 },
            TinyBvInsn::BranchEq {
                reg: 3,
                value: 0xCAFE,
                then_pc: 4,
                else_pc: 5,
            },
            TinyBvInsn::Win,
            TinyBvInsn::Lose,
        ],
    )
    .unwrap();

    assert!(program.uses_memory());
    let reach = program
        .reach_pc_checked(
            &mut arena,
            "mem_reach_input",
            4,
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                // The frontend should route memory-bearing paths through the
                // memory-aware checker even if the caller leaves this off.
                memory_aware: false,
            },
        )
        .unwrap();

    assert_eq!(reach.status(), TinyBvReachabilityStatus::Reachable);
    assert!(!reach.outcome.verified.is_empty());
    for hit in &reach.outcome.verified {
        assert_eq!(hit.state.pc, 4);
        assert!(hit.state.memory.is_some());
        let trace = program.concrete_trace(&hit.witness);
        assert_eq!(trace.outcome, TinyBvConcreteOutcome::Win);
        assert_eq!(program.concrete_run(&hit.witness), trace.outcome);
        assert!(program.concrete_reaches_pc(&hit.witness, 4));
        assert!(trace.reaches_pc(4));
        assert_eq!(
            trace.steps.iter().map(|step| step.pc).collect::<Vec<_>>(),
            vec![0, 1, 2, 3, 4]
        );
        assert_eq!(trace.final_pc, Some(4));
        assert_eq!(hit.witness.inputs[0], 0xCAFE);
        assert_eq!(trace.final_regs[3], 0xCAFE);
        assert_eq!(trace.final_memory, vec![(0x0010, 0xCAFE)]);
    }
}

#[test]
fn tiny_bv_assembly_imports_memory_program_and_replays() {
    let mut arena = TermArena::new();
    let program = TinyBvProgram::from_assembly(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        "
            # raw frontend text: input r0 is stored, loaded, and checked
            entry:
            const r2 0x10
            store r2 r0
            load r3 r2
            beq r3 0xcafe win_block lose_block
            win_block: win
            lose_block:
            lose
        ",
    )
    .unwrap();

    assert_eq!(program.labels().len(), 3);
    assert_eq!(program.label_pc("entry"), Some(0));
    assert_eq!(program.label_pc("win_block"), Some(4));
    assert_eq!(program.label_pc("lose_block"), Some(5));
    assert_eq!(program.label_pc("missing"), None);
    assert_eq!(program.labels_at_pc(0), vec!["entry"]);
    assert_eq!(program.labels_at_pc(4), vec!["win_block"]);
    assert_eq!(program.labels_at_pc(5), vec!["lose_block"]);
    assert_eq!(program.labels_at_pc(99), Vec::<&str>::new());
    assert_eq!(program.source_lines().len(), program.code().len());
    assert_eq!(program.source_line(0), Some(4));
    assert_eq!(program.source_line(4), Some(8));
    assert_eq!(program.source_line(5), Some(10));
    assert_eq!(program.source_line(99), None);
    assert_eq!(
        program.code(),
        &[
            TinyBvInsn::Const {
                dst: 2,
                value: 0x0010
            },
            TinyBvInsn::Store { addr: 2, src: 0 },
            TinyBvInsn::Load { dst: 3, addr: 2 },
            TinyBvInsn::BranchEq {
                reg: 3,
                value: 0xCAFE,
                then_pc: 4,
                else_pc: 5,
            },
            TinyBvInsn::Win,
            TinyBvInsn::Lose,
        ]
    );
    assert!(program.uses_memory());
    assert_eq!(
        program.successors(0).unwrap(),
        vec![TinyBvCfgEdge {
            from: 0,
            to: 1,
            kind: TinyBvCfgEdgeKind::Fallthrough,
        }]
    );
    assert_eq!(
        program.successors(3).unwrap(),
        vec![
            TinyBvCfgEdge {
                from: 3,
                to: 4,
                kind: TinyBvCfgEdgeKind::BranchTrue,
            },
            TinyBvCfgEdge {
                from: 3,
                to: 5,
                kind: TinyBvCfgEdgeKind::BranchFalse,
            },
        ]
    );
    assert!(program.successors(4).unwrap().is_empty());
    assert!(program.successors(5).unwrap().is_empty());
    assert_eq!(
        program.cfg_edges(),
        vec![
            TinyBvCfgEdge {
                from: 0,
                to: 1,
                kind: TinyBvCfgEdgeKind::Fallthrough,
            },
            TinyBvCfgEdge {
                from: 1,
                to: 2,
                kind: TinyBvCfgEdgeKind::Fallthrough,
            },
            TinyBvCfgEdge {
                from: 2,
                to: 3,
                kind: TinyBvCfgEdgeKind::Fallthrough,
            },
            TinyBvCfgEdge {
                from: 3,
                to: 4,
                kind: TinyBvCfgEdgeKind::BranchTrue,
            },
            TinyBvCfgEdge {
                from: 3,
                to: 5,
                kind: TinyBvCfgEdgeKind::BranchFalse,
            },
        ]
    );
    assert_eq!(
        program.basic_blocks(),
        vec![
            TinyBvBasicBlock {
                start_pc: 0,
                end_pc: 4,
                labels: vec!["entry".to_owned()],
                source_lines: vec![Some(4), Some(5), Some(6), Some(7)],
                outgoing: vec![
                    TinyBvCfgEdge {
                        from: 3,
                        to: 4,
                        kind: TinyBvCfgEdgeKind::BranchTrue,
                    },
                    TinyBvCfgEdge {
                        from: 3,
                        to: 5,
                        kind: TinyBvCfgEdgeKind::BranchFalse,
                    },
                ],
            },
            TinyBvBasicBlock {
                start_pc: 4,
                end_pc: 5,
                labels: vec!["win_block".to_owned()],
                source_lines: vec![Some(8)],
                outgoing: Vec::new(),
            },
            TinyBvBasicBlock {
                start_pc: 5,
                end_pc: 6,
                labels: vec!["lose_block".to_owned()],
                source_lines: vec![Some(10)],
                outgoing: Vec::new(),
            },
        ]
    );
    assert_eq!(
        program.basic_block_containing_pc(2).map(|block| (
            block.start_pc,
            block.end_pc,
            block.source_lines
        )),
        Some((0, 4, vec![Some(4), Some(5), Some(6), Some(7)]))
    );
    assert_eq!(
        program.basic_block_containing_pc(4).map(|block| (
            block.start_pc,
            block.end_pc,
            block.labels
        )),
        Some((4, 5, vec!["win_block".to_owned()]))
    );
    assert_eq!(program.basic_block_containing_pc(99), None);
    assert_eq!(
        program.cfg_dot(),
        concat!(
            "digraph tiny_bv_cfg {\n",
            "  rankdir=TB;\n",
            "  bb_0 [label=\"entry\\npc 0..4\\nlines 4,5,6,7\"];\n",
            "  bb_4 [label=\"win_block\\npc 4..5\\nlines 8\"];\n",
            "  bb_5 [label=\"lose_block\\npc 5..6\\nlines 10\"];\n",
            "  bb_0 -> bb_4 [label=\"true\"];\n",
            "  bb_0 -> bb_5 [label=\"false\"];\n",
            "}\n",
        )
    );

    let reach = program
        .reach_label_checked(
            &mut arena,
            "asm_input",
            "win_block",
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
        )
        .unwrap();

    assert_eq!(reach.status(), TinyBvReachabilityStatus::Reachable);
    assert_eq!(reach.target_pc, 4);
    let hit = reach
        .outcome
        .verified
        .first()
        .expect("imported memory program should have a winning witness");
    let trace = program.concrete_trace(&hit.witness);
    assert_eq!(trace.outcome, TinyBvConcreteOutcome::Win);
    assert_eq!(
        trace.steps.iter().map(|step| step.pc).collect::<Vec<_>>(),
        vec![0, 1, 2, 3, 4]
    );
    assert_eq!(
        trace
            .steps
            .iter()
            .map(|step| program.source_line(step.pc))
            .collect::<Vec<_>>(),
        vec![Some(4), Some(5), Some(6), Some(7), Some(8)]
    );
    let source_steps = program.trace_source_steps(&trace);
    assert_eq!(
        source_steps
            .iter()
            .map(|step| (step.pc, step.source_line))
            .collect::<Vec<_>>(),
        vec![
            (0, Some(4)),
            (1, Some(5)),
            (2, Some(6)),
            (3, Some(7)),
            (4, Some(8))
        ]
    );
    assert_eq!(source_steps[0].labels, vec!["entry".to_owned()]);
    assert_eq!(source_steps[4].labels, vec!["win_block".to_owned()]);
    assert_eq!(
        source_steps[0].instruction,
        TinyBvInsn::Const {
            dst: 2,
            value: 0x0010
        }
    );
    assert_eq!(source_steps[0].regs_before[0], hit.witness.inputs[0]);
    let trace_blocks = program.trace_basic_blocks(&trace);
    assert_eq!(
        trace_blocks
            .iter()
            .map(|step| (
                step.block.start_pc,
                step.block.end_pc,
                step.executed_pcs.clone()
            ))
            .collect::<Vec<_>>(),
        vec![(0, 4, vec![0, 1, 2, 3]), (4, 5, vec![4])]
    );
    assert_eq!(trace_blocks[0].block.labels, vec!["entry".to_owned()]);
    assert_eq!(
        trace_blocks[0].block.source_lines,
        vec![Some(4), Some(5), Some(6), Some(7)]
    );
    assert_eq!(trace_blocks[1].block.labels, vec!["win_block".to_owned()]);
    let trace_edges = program.trace_cfg_edges(&trace);
    assert_eq!(
        trace_edges
            .iter()
            .map(|step| (step.edge.from, step.edge.to, step.edge.kind))
            .collect::<Vec<_>>(),
        vec![
            (0, 1, TinyBvCfgEdgeKind::Fallthrough),
            (1, 2, TinyBvCfgEdgeKind::Fallthrough),
            (2, 3, TinyBvCfgEdgeKind::Fallthrough),
            (3, 4, TinyBvCfgEdgeKind::BranchTrue),
        ]
    );
    assert_eq!(trace_edges[0].from_labels, vec!["entry".to_owned()]);
    assert_eq!(trace_edges[3].from_source_line, Some(7));
    assert_eq!(trace_edges[3].to_source_line, Some(8));
    assert_eq!(trace_edges[3].to_labels, vec!["win_block".to_owned()]);
    assert_eq!(
        program.cfg_dot_with_trace(&trace),
        concat!(
            "digraph tiny_bv_cfg {\n",
            "  rankdir=TB;\n",
            "  bb_0 [label=\"entry\\npc 0..4\\nlines 4,5,6,7\", style=\"filled\", fillcolor=\"#e8f0ff\", penwidth=2];\n",
            "  bb_4 [label=\"win_block\\npc 4..5\\nlines 8\", style=\"filled\", fillcolor=\"#e8f0ff\", penwidth=2];\n",
            "  bb_5 [label=\"lose_block\\npc 5..6\\nlines 10\"];\n",
            "  bb_0 -> bb_4 [label=\"true\", color=\"#1f6feb\", penwidth=2];\n",
            "  bb_0 -> bb_5 [label=\"false\"];\n",
            "}\n",
        )
    );
    let report = program.trace_report(&hit.witness);
    assert_eq!(report.witness, hit.witness);
    assert_eq!(report.trace, trace);
    assert_eq!(report.source_steps, source_steps);
    assert_eq!(report.block_steps, trace_blocks);
    assert_eq!(report.edge_steps, trace_edges);
    assert_eq!(hit.witness.inputs[0], 0xCAFE);
    assert_eq!(trace.final_regs[3], 0xCAFE);
    assert_eq!(trace.final_memory, vec![(0x0010, 0xCAFE)]);
    let mut test_arena = TermArena::new();
    let generated = program
        .test_cases_for_label_checked(
            &mut test_arena,
            "asm_generated_input",
            "win_block",
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
        )
        .unwrap();
    assert_eq!(generated.status(), TinyBvReachabilityStatus::Reachable);
    assert!(generated.has_test_cases());
    assert_eq!(generated.target_pc, 4);
    assert_eq!(generated.target_labels, vec!["win_block".to_owned()]);
    assert_eq!(generated.reachability.target_pc, 4);
    assert_eq!(generated.test_cases.len(), 1);
    let generated_case = &generated.test_cases[0];
    assert_eq!(generated_case.target_pc, 4);
    assert_eq!(generated_case.target_labels, vec!["win_block".to_owned()]);
    assert_eq!(
        generated_case.report.trace.outcome,
        TinyBvConcreteOutcome::Win
    );
    assert!(generated_case.report.trace.reaches_pc(4));
    assert_eq!(generated_case.report.witness.inputs[0], 0xCAFE);
    assert_eq!(
        generated_case.report.edge_steps.last().map(|step| (
            step.edge.from,
            step.edge.to,
            step.edge.kind
        )),
        Some((3, 4, TinyBvCfgEdgeKind::BranchTrue))
    );
    let mut coverage_arena = TermArena::new();
    let coverage = program
        .test_cases_for_basic_blocks_checked(
            &mut coverage_arena,
            "asm_block_suite_input",
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
        )
        .unwrap();
    assert_eq!(coverage.target_count(), 3);
    assert_eq!(coverage.covered_target_count(), 3);
    assert_eq!(coverage.generated_test_count(), 3);
    assert_eq!(coverage.unreachable_target_count(), 0);
    assert_eq!(coverage.unknown_target_count(), 0);
    assert!(coverage.is_complete());
    assert_eq!(
        coverage
            .targets
            .iter()
            .map(|target| (
                target.target_pc,
                target.target_labels.clone(),
                target.status(),
                target.test_cases.len()
            ))
            .collect::<Vec<_>>(),
        vec![
            (
                0,
                vec!["entry".to_owned()],
                TinyBvReachabilityStatus::Reachable,
                1
            ),
            (
                4,
                vec!["win_block".to_owned()],
                TinyBvReachabilityStatus::Reachable,
                1
            ),
            (
                5,
                vec!["lose_block".to_owned()],
                TinyBvReachabilityStatus::Reachable,
                1
            ),
        ]
    );
    let lose_target = coverage
        .targets
        .iter()
        .find(|target| target.target_pc == 5)
        .expect("coverage suite should target lose block");
    assert_eq!(
        lose_target.test_cases[0].report.trace.outcome,
        TinyBvConcreteOutcome::Lose
    );
    assert!(lose_target.test_cases[0].report.trace.reaches_pc(5));
    assert_eq!(
        lose_target.test_cases[0]
            .report
            .edge_steps
            .last()
            .map(|step| (step.edge.from, step.edge.to, step.edge.kind)),
        Some((3, 5, TinyBvCfgEdgeKind::BranchFalse))
    );
    assert_eq!(
        program.cfg_dot_with_coverage(&coverage),
        concat!(
            "digraph tiny_bv_cfg {\n",
            "  rankdir=TB;\n",
            "  bb_0 [label=\"entry\\npc 0..4\\nlines 4,5,6,7\", style=\"filled\", fillcolor=\"#e6ffed\", penwidth=2];\n",
            "  bb_4 [label=\"win_block\\npc 4..5\\nlines 8\", style=\"filled\", fillcolor=\"#e6ffed\", penwidth=2];\n",
            "  bb_5 [label=\"lose_block\\npc 5..6\\nlines 10\", style=\"filled\", fillcolor=\"#e6ffed\", penwidth=2];\n",
            "  bb_0 -> bb_4 [label=\"true\", color=\"#2da44e\", penwidth=2];\n",
            "  bb_0 -> bb_5 [label=\"false\", color=\"#2da44e\", penwidth=2];\n",
            "}\n",
        )
    );
    let mut edge_suite_arena = TermArena::new();
    let edge_suite = program
        .test_cases_for_cfg_edges_checked(
            &mut edge_suite_arena,
            "asm_edge_suite_input",
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
        )
        .unwrap();
    assert_eq!(edge_suite.edge_count(), 5);
    assert_eq!(edge_suite.covered_edge_count(), 5);
    assert_eq!(edge_suite.generated_test_count(), 5);
    assert_eq!(edge_suite.unreachable_edge_count(), 0);
    assert_eq!(edge_suite.unknown_edge_count(), 0);
    assert!(edge_suite.is_complete());
    assert_eq!(
        edge_suite
            .edges
            .iter()
            .map(|report| (report.edge.from, report.edge.to, report.edge.kind))
            .collect::<Vec<_>>(),
        program
            .cfg_edges()
            .iter()
            .map(|edge| (edge.from, edge.to, edge.kind))
            .collect::<Vec<_>>()
    );
    let true_edge_report = edge_suite
        .edges
        .iter()
        .find(|report| {
            report.edge.from == 3
                && report.edge.to == 4
                && report.edge.kind == TinyBvCfgEdgeKind::BranchTrue
        })
        .expect("edge suite should target the true branch");
    assert_eq!(
        true_edge_report.status(),
        TinyBvReachabilityStatus::Reachable
    );
    assert_eq!(true_edge_report.from_source_line, Some(7));
    assert_eq!(true_edge_report.to_source_line, Some(8));
    assert_eq!(true_edge_report.to_labels, vec!["win_block".to_owned()]);
    assert_eq!(true_edge_report.test_cases.len(), 1);
    assert_eq!(
        true_edge_report.test_cases[0].report.trace.outcome,
        TinyBvConcreteOutcome::Win
    );
    assert_eq!(
        true_edge_report.test_cases[0]
            .report
            .edge_steps
            .last()
            .map(|step| (step.edge.from, step.edge.to, step.edge.kind)),
        Some((3, 4, TinyBvCfgEdgeKind::BranchTrue))
    );
    let false_edge_report = edge_suite
        .edges
        .iter()
        .find(|report| {
            report.edge.from == 3
                && report.edge.to == 5
                && report.edge.kind == TinyBvCfgEdgeKind::BranchFalse
        })
        .expect("edge suite should target the false branch");
    assert_eq!(
        false_edge_report.status(),
        TinyBvReachabilityStatus::Reachable
    );
    assert_eq!(false_edge_report.to_labels, vec!["lose_block".to_owned()]);
    assert_eq!(
        false_edge_report.test_cases[0].report.trace.outcome,
        TinyBvConcreteOutcome::Lose
    );
    assert_eq!(
        false_edge_report.test_cases[0]
            .report
            .edge_steps
            .last()
            .map(|step| (step.edge.from, step.edge.to, step.edge.kind)),
        Some((3, 5, TinyBvCfgEdgeKind::BranchFalse))
    );
    assert_eq!(
        program.cfg_dot_with_edge_coverage(&edge_suite),
        concat!(
            "digraph tiny_bv_cfg {\n",
            "  rankdir=TB;\n",
            "  bb_0 [label=\"entry\\npc 0..4\\nlines 4,5,6,7\", style=\"filled\", fillcolor=\"#e6ffed\", penwidth=2];\n",
            "  bb_4 [label=\"win_block\\npc 4..5\\nlines 8\", style=\"filled\", fillcolor=\"#e6ffed\", penwidth=2];\n",
            "  bb_5 [label=\"lose_block\\npc 5..6\\nlines 10\", style=\"filled\", fillcolor=\"#e6ffed\", penwidth=2];\n",
            "  bb_0 -> bb_4 [label=\"true\", color=\"#8250df\", penwidth=2];\n",
            "  bb_0 -> bb_5 [label=\"false\", color=\"#8250df\", penwidth=2];\n",
            "}\n",
        )
    );

    let lose_witness = TinyBvWitness { inputs: vec![0, 0] };
    let lose_trace = program.concrete_trace(&lose_witness);
    assert_eq!(lose_trace.outcome, TinyBvConcreteOutcome::Lose);
    assert_eq!(
        lose_trace
            .steps
            .iter()
            .map(|step| step.pc)
            .collect::<Vec<_>>(),
        vec![0, 1, 2, 3, 5]
    );
    let lose_edges = program.trace_cfg_edges(&lose_trace);
    assert_eq!(
        lose_edges
            .iter()
            .map(|step| (step.edge.from, step.edge.to, step.edge.kind))
            .collect::<Vec<_>>(),
        vec![
            (0, 1, TinyBvCfgEdgeKind::Fallthrough),
            (1, 2, TinyBvCfgEdgeKind::Fallthrough),
            (2, 3, TinyBvCfgEdgeKind::Fallthrough),
            (3, 5, TinyBvCfgEdgeKind::BranchFalse),
        ]
    );
    assert_eq!(lose_edges[3].from_source_line, Some(7));
    assert_eq!(lose_edges[3].to_source_line, Some(10));
    assert_eq!(lose_edges[3].to_labels, vec!["lose_block".to_owned()]);
    assert_eq!(
        program.cfg_dot_with_trace(&lose_trace),
        concat!(
            "digraph tiny_bv_cfg {\n",
            "  rankdir=TB;\n",
            "  bb_0 [label=\"entry\\npc 0..4\\nlines 4,5,6,7\", style=\"filled\", fillcolor=\"#e8f0ff\", penwidth=2];\n",
            "  bb_4 [label=\"win_block\\npc 4..5\\nlines 8\"];\n",
            "  bb_5 [label=\"lose_block\\npc 5..6\\nlines 10\", style=\"filled\", fillcolor=\"#e8f0ff\", penwidth=2];\n",
            "  bb_0 -> bb_4 [label=\"true\"];\n",
            "  bb_0 -> bb_5 [label=\"false\", color=\"#1f6feb\", penwidth=2];\n",
            "}\n",
        )
    );
    let lose_report = program.trace_report(&lose_witness);
    assert_eq!(lose_report.witness, lose_witness);
    assert_eq!(lose_report.trace, lose_trace);
    assert_eq!(lose_report.edge_steps, lose_edges);
    assert_eq!(
        lose_report
            .block_steps
            .iter()
            .map(|step| (step.block.start_pc, step.executed_pcs.clone()))
            .collect::<Vec<_>>(),
        vec![(0, vec![0, 1, 2, 3]), (5, vec![5])]
    );

    let safety = program
        .check_label_safety_checked(
            &mut arena,
            "asm_unsafe_input",
            "win_block",
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
        )
        .unwrap();
    assert_eq!(safety.status(), TinyBvSafetyStatus::Unsafe);
    assert_eq!(safety.forbidden_pc, 4);
}

#[test]
fn tiny_bv_assembly_imports_register_equality_branch() {
    let mut arena = TermArena::new();
    let program = TinyBvProgram::from_assembly(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        "
            add r2 r0 r1
            xor r3 r0 r1
            beq r2 r3 equal done
            equal: win
            done: lose
        ",
    )
    .unwrap();

    assert_eq!(
        program.code()[2],
        TinyBvInsn::BranchRegEq {
            a: 2,
            b: 3,
            then_pc: 3,
            else_pc: 4,
        }
    );
    assert_eq!(program.source_line(2), Some(4));
    assert_eq!(program.labels_at_pc(3), vec!["equal"]);
    assert_eq!(program.labels_at_pc(4), vec!["done"]);
    assert_eq!(
        program.successors(2).unwrap(),
        vec![
            TinyBvCfgEdge {
                from: 2,
                to: 3,
                kind: TinyBvCfgEdgeKind::BranchTrue,
            },
            TinyBvCfgEdge {
                from: 2,
                to: 4,
                kind: TinyBvCfgEdgeKind::BranchFalse,
            },
        ]
    );
    assert_eq!(
        program.basic_blocks(),
        vec![
            TinyBvBasicBlock {
                start_pc: 0,
                end_pc: 3,
                labels: Vec::new(),
                source_lines: vec![Some(2), Some(3), Some(4)],
                outgoing: vec![
                    TinyBvCfgEdge {
                        from: 2,
                        to: 3,
                        kind: TinyBvCfgEdgeKind::BranchTrue,
                    },
                    TinyBvCfgEdge {
                        from: 2,
                        to: 4,
                        kind: TinyBvCfgEdgeKind::BranchFalse,
                    },
                ],
            },
            TinyBvBasicBlock {
                start_pc: 3,
                end_pc: 4,
                labels: vec!["equal".to_owned()],
                source_lines: vec![Some(5)],
                outgoing: Vec::new(),
            },
            TinyBvBasicBlock {
                start_pc: 4,
                end_pc: 5,
                labels: vec!["done".to_owned()],
                source_lines: vec![Some(6)],
                outgoing: Vec::new(),
            },
        ]
    );
    assert_eq!(
        program
            .basic_block_containing_pc(2)
            .map(|block| (block.start_pc, block.end_pc)),
        Some((0, 3))
    );
    assert_eq!(
        program
            .basic_block_containing_pc(3)
            .map(|block| (block.start_pc, block.labels)),
        Some((3, vec!["equal".to_owned()]))
    );

    let reach = program
        .reach_label_checked(
            &mut arena,
            "reg_branch_input",
            "equal",
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
        )
        .unwrap();

    assert_eq!(reach.status(), TinyBvReachabilityStatus::Reachable);
    let hit = reach
        .outcome
        .verified
        .first()
        .expect("register equality branch should have a reachable witness");
    let trace = program.concrete_trace(&hit.witness);
    assert_eq!(trace.outcome, TinyBvConcreteOutcome::Win);
    assert_eq!(
        trace.steps.iter().map(|step| step.pc).collect::<Vec<_>>(),
        vec![0, 1, 2, 3]
    );
    let source_steps = program.trace_source_steps(&trace);
    assert_eq!(
        source_steps
            .iter()
            .map(|step| (step.pc, step.source_line, step.labels.clone()))
            .collect::<Vec<_>>(),
        vec![
            (0, Some(2), Vec::<String>::new()),
            (1, Some(3), Vec::<String>::new()),
            (2, Some(4), Vec::<String>::new()),
            (3, Some(5), vec!["equal".to_owned()]),
        ]
    );
    assert_eq!(
        program
            .trace_basic_blocks(&trace)
            .iter()
            .map(|step| (
                step.block.start_pc,
                step.block.end_pc,
                step.executed_pcs.clone()
            ))
            .collect::<Vec<_>>(),
        vec![(0, 3, vec![0, 1, 2]), (3, 4, vec![3])]
    );
    let [x, y] = hit.witness.inputs[..] else {
        panic!("test program has exactly two input words");
    };
    assert_eq!((x + y) & MASK, (x ^ y) & MASK);
}

#[test]
fn tiny_bv_assembly_reports_parse_and_validation_errors() {
    let parse_err =
        TinyBvProgram::from_assembly(WIDTH, REG_COUNT, INPUT_COUNT, MAX_STEPS, "add r0 r1")
            .unwrap_err()
            .to_string();
    assert!(
        parse_err.contains("tiny BV assembly line 1"),
        "parse error should include the source line: {parse_err}"
    );
    assert!(
        parse_err.contains("`add` expects rD rA rB"),
        "parse error should describe the expected operands: {parse_err}"
    );

    let validation_err = TinyBvProgram::from_assembly(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        "
            const r4 0
            win
        ",
    )
    .unwrap_err()
    .to_string();
    assert!(
        validation_err.contains("instruction 0 references register 4"),
        "validation error should come from the shared program validator: {validation_err}"
    );

    let branch_reg_validation_err = TinyBvProgram::from_assembly(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        "
            beq r0 r4 ok ok
            ok: win
        ",
    )
    .unwrap_err()
    .to_string();
    assert!(
        branch_reg_validation_err.contains("instruction 0 references register 4"),
        "register branch validation should come from the shared validator: {branch_reg_validation_err}"
    );

    let program = TinyBvProgram::from_assembly(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        "
            win
        ",
    )
    .unwrap();
    let invalid_successor_err = program.successors(1).unwrap_err().to_string();
    assert!(
        invalid_successor_err.contains("source pc 1 is outside program length 1"),
        "successor lookup should reject out-of-range source PCs: {invalid_successor_err}"
    );

    let duplicate_label_err = TinyBvProgram::from_assembly(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        "
            again: win
            again: lose
        ",
    )
    .unwrap_err()
    .to_string();
    assert!(
        duplicate_label_err.contains("duplicate label `again`"),
        "duplicate labels should be rejected: {duplicate_label_err}"
    );

    let missing_label_err = TinyBvProgram::from_assembly(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        "
            beq r0 0 ok missing
            ok: win
            lose
        ",
    )
    .unwrap_err()
    .to_string();
    assert!(
        missing_label_err.contains("unknown else target label `missing`"),
        "branch labels should resolve before validation: {missing_label_err}"
    );

    let dangling_label_err = TinyBvProgram::from_assembly(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        "
            beq r0 0 ok ok
            ok: win
            dangling:
        ",
    )
    .unwrap_err()
    .to_string();
    assert!(
        dangling_label_err.contains("label `dangling` does not name an instruction"),
        "dangling labels should not enter the public label map: {dangling_label_err}"
    );

    let program = TinyBvProgram::from_assembly(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        "
            start: win
        ",
    )
    .unwrap();
    let mut query_arena = TermArena::new();
    let query_err = program
        .check_label_safety_checked(
            &mut query_arena,
            "missing_label_input",
            "not_declared",
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
        )
        .unwrap_err()
        .to_string();
    assert!(
        query_err.contains("unknown assembly label `not_declared`"),
        "label query wrappers should reject missing labels: {query_err}"
    );
}

#[test]
fn tiny_bv_memory_safety_uses_read_over_write() {
    let mut arena = TermArena::new();
    let program = TinyBvProgram::new(
        WIDTH,
        REG_COUNT,
        INPUT_COUNT,
        MAX_STEPS,
        vec![
            TinyBvInsn::Const { dst: 1, value: 0 },
            TinyBvInsn::Const {
                dst: 2,
                value: 0x0020,
            },
            TinyBvInsn::Store { addr: 2, src: 1 },
            TinyBvInsn::Load { dst: 3, addr: 2 },
            TinyBvInsn::BranchEq {
                reg: 3,
                value: 0xCAFE,
                then_pc: 5,
                else_pc: 6,
            },
            TinyBvInsn::Win,
            TinyBvInsn::Lose,
        ],
    )
    .unwrap();

    let safety = program
        .check_pc_safety_checked(
            &mut arena,
            "mem_safe_input",
            5,
            CfgExploreConfig {
                max_steps: 128,
                max_targets: 16,
                memory_aware: false,
            },
        )
        .unwrap();

    assert_eq!(safety.status(), TinyBvSafetyStatus::Safe);
    assert!(safety.is_safe());
    assert_eq!(
        safety.reachability.status(),
        TinyBvReachabilityStatus::Unreachable
    );
    assert!(safety.reachability.outcome.mismatches.is_empty());
    assert!(safety.reachability.outcome.missing_witnesses.is_empty());
    assert_eq!(safety.reachability.outcome.unknown_branches, 0);
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

// --- all-SAT / reachable-state enumeration (the reachability primitive) -------

/// Reachability analysis enumerates the reachable states. With `block_model`,
/// the incremental engine does all-SAT directly: check, record, block, repeat
/// until unsat — each step a distinct assignment. Here the reachable set of a
/// 4-bit `x` constrained to `2 <= x <= 5` is exactly {2,3,4,5}.
#[test]
fn all_sat_enumerates_reachable_states() {
    let mut arena = TermArena::new();
    let xs = arena.declare("x", Sort::BitVec(4)).unwrap();
    let x = arena.var(xs);
    let mut solver = IncrementalBvSolver::new();
    let two = arena.bv_const(4, 2).unwrap();
    let five = arena.bv_const(4, 5).unwrap();
    let lo = arena.bv_uge(x, two).unwrap();
    let hi = arena.bv_ule(x, five).unwrap();
    solver.assert(&arena, lo).unwrap();
    solver.assert(&arena, hi).unwrap();

    let mut reachable = std::collections::BTreeSet::new();
    loop {
        match solver.check(&arena).unwrap() {
            CheckResult::Sat(model) => {
                let value = match model.get(xs) {
                    Some(Value::Bv { value, .. }) => value,
                    other => panic!("expected a BV model value, got {other:?}"),
                };
                assert!(
                    reachable.insert(value),
                    "enumeration repeated a model: {value}"
                );
                solver.block_model(&mut arena, &model, &[xs]).unwrap();
            }
            CheckResult::Unsat => break, // enumeration exhausted
            CheckResult::Unknown(reason) => panic!("unexpected unknown: {reason:?}"),
        }
        assert!(
            reachable.len() <= 4,
            "must not exceed the 4 reachable values"
        );
    }
    assert_eq!(
        reachable,
        [2u128, 3, 4, 5].into_iter().collect(),
        "the reachable set must be exactly {{2,3,4,5}}"
    );
}

// --- symbolic memory (arrays) through the incremental engine (ADR-0030 slice) --

/// Read-over-write soundness through `check_with_memory`: at the same index, a
/// load after a store returns the stored value, so demanding otherwise is unsat.
/// This is the memory primitive symbolic execution needs.
#[test]
fn symbolic_memory_read_over_write_is_unsat_when_violated() {
    let mut arena = TermArena::new();
    let mem = arena
        .declare(
            "mem",
            Sort::Array {
                index: ArraySortKey::BitVec(8),
                element: ArraySortKey::BitVec(8),
            },
        )
        .unwrap();
    let mem_v = arena.var(mem);
    let is = arena.declare("i", Sort::BitVec(8)).unwrap();
    let js = arena.declare("j", Sort::BitVec(8)).unwrap();
    let vs = arena.declare("v", Sort::BitVec(8)).unwrap();
    let (i, j, v) = (arena.var(is), arena.var(js), arena.var(vs));

    let stored = arena.store(mem_v, i, v).unwrap();
    let loaded = arena.select(stored, j).unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();
    let load_ne_v = {
        let eq = arena.eq(loaded, v).unwrap();
        arena.not(eq).unwrap()
    };

    let mut solver = IncrementalBvSolver::new();
    solver.assert(&arena, i_eq_j).unwrap();
    solver.assert(&arena, load_ne_v).unwrap();

    // The warm path refuses array assertions rather than ignore them.
    assert!(
        solver.check(&arena).is_err(),
        "warm check must refuse active array assertions"
    );
    // The memory-aware path decides it: unsat.
    assert!(
        matches!(
            solver.check_with_memory(&mut arena).unwrap(),
            CheckResult::Unsat
        ),
        "select(store(mem,i,v),j) == v when i==j, so the inequality is unsat"
    );
}

/// Symbolic memory is sat-feasible and the model replays: find `v` such that
/// loading the just-stored cell yields a target, with `push`/`pop` scoping.
#[test]
fn symbolic_memory_reachability_is_sat_and_scoped() {
    let mut arena = TermArena::new();
    let mem = arena
        .declare(
            "m",
            Sort::Array {
                index: ArraySortKey::BitVec(8),
                element: ArraySortKey::BitVec(8),
            },
        )
        .unwrap();
    let mem_v = arena.var(mem);
    let is = arena.declare("ix", Sort::BitVec(8)).unwrap();
    let vs = arena.declare("val", Sort::BitVec(8)).unwrap();
    let (i, v) = (arena.var(is), arena.var(vs));

    let stored = arena.store(mem_v, i, v).unwrap();
    let loaded = arena.select(stored, i).unwrap(); // read same index back
    let target = arena.bv_const(8, 42).unwrap();
    let goal = arena.eq(loaded, target).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver.push().unwrap();
    solver.assert(&arena, goal).unwrap();
    // mem[i] := v then read i back == 42 forces v == 42 -> sat.
    match solver.check_with_memory(&mut arena).unwrap() {
        CheckResult::Sat(model) => {
            assert_eq!(
                model.get(vs),
                Some(Value::Bv {
                    width: 8,
                    value: 42
                }),
                "the stored value must be 42"
            );
        }
        other => panic!("expected sat, got {other:?}"),
    }
    // Popping the scope retracts the array assertion; the empty solver is sat.
    solver.pop();
    assert!(matches!(
        solver.check_with_memory(&mut arena).unwrap(),
        CheckResult::Sat(_)
    ));
}

#[test]
fn memory_assumption_checks_array_branch_without_persisting() {
    let mut arena = TermArena::new();
    let mem = arena
        .declare(
            "mem",
            Sort::Array {
                index: ArraySortKey::BitVec(8),
                element: ArraySortKey::BitVec(8),
            },
        )
        .unwrap();
    let mem_v = arena.var(mem);
    let is = arena.declare("i", Sort::BitVec(8)).unwrap();
    let js = arena.declare("j", Sort::BitVec(8)).unwrap();
    let vs = arena.declare("v", Sort::BitVec(8)).unwrap();
    let (i, j, v) = (arena.var(is), arena.var(js), arena.var(vs));

    let stored = arena.store(mem_v, i, v).unwrap();
    let loaded = arena.select(stored, j).unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();
    let loaded_eq_v = arena.eq(loaded, v).unwrap();
    let load_ne_v = arena.not(loaded_eq_v).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver.assert(&arena, i_eq_j).unwrap();

    assert_eq!(
        solver
            .check_assuming_with_memory(&mut arena, &[load_ne_v])
            .unwrap(),
        CheckResult::Unsat,
        "under i=j, select(store(mem,i,v),j) != v is infeasible"
    );
    match solver
        .check_assuming_core_with_memory(&mut arena, &[load_ne_v])
        .unwrap()
    {
        AssumptionOutcome::Unsat { core } => assert_eq!(core, vec![load_ne_v]),
        other => panic!("expected assumption-core unsat, got {other:?}"),
    }

    let CheckResult::Sat(_) = solver.check(&arena).unwrap() else {
        panic!("array assumption must not persist into the warm BV path");
    };
}

#[test]
fn memory_assumption_checks_uf_branch_without_persisting() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(2)], Sort::BitVec(2))
        .unwrap();
    let a = {
        let s = arena.declare("a", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let b = {
        let s = arena.declare("b", Sort::BitVec(2)).unwrap();
        arena.var(s)
    };
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let zero = arena.bv_const(2, 0).unwrap();
    let premise_output_zero = arena.eq(fa, zero).unwrap();
    let a_eq_b = arena.eq(a, b).unwrap();
    let contradictory_output_zero = arena.eq(fb, zero).unwrap();
    let contradictory_output_nonzero = arena.not(contradictory_output_zero).unwrap();

    let mut solver = IncrementalBvSolver::new();
    solver.assert(&arena, premise_output_zero).unwrap();
    solver.assert(&arena, a_eq_b).unwrap();
    assert!(
        solver.check(&arena).is_err(),
        "warm BV path must refuse active UF assertions instead of ignoring them"
    );
    assert_eq!(
        solver
            .check_assuming_with_memory(&mut arena, &[contradictory_output_nonzero])
            .unwrap(),
        CheckResult::Unsat,
        "a=b and f(a)=0 imply f(b)=0 by congruence"
    );
    assert!(
        matches!(
            solver.check_with_memory(&mut arena).unwrap(),
            CheckResult::Sat(_)
        ),
        "the UF assumption is one-shot and must not persist"
    );
}

#[test]
fn symbolic_executor_branches_on_memory_conditions() {
    let mut arena = TermArena::new();
    let mem = arena
        .declare(
            "mem",
            Sort::Array {
                index: ArraySortKey::BitVec(8),
                element: ArraySortKey::BitVec(8),
            },
        )
        .unwrap();
    let mem_v = arena.var(mem);
    let is = arena.declare("i", Sort::BitVec(8)).unwrap();
    let js = arena.declare("j", Sort::BitVec(8)).unwrap();
    let vs = arena.declare("v", Sort::BitVec(8)).unwrap();
    let (i, j, v) = (arena.var(is), arena.var(js), arena.var(vs));

    let stored = arena.store(mem_v, i, v).unwrap();
    let loaded = arena.select(stored, j).unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();
    let loaded_eq_v = arena.eq(loaded, v).unwrap();
    let load_ne_v = arena.not(loaded_eq_v).unwrap();

    let mut executor = SymbolicExecutor::new();
    assert!(
        executor
            .assume_with_memory(&mut arena, i_eq_j)
            .unwrap()
            .is_feasible()
    );

    let branch = executor.branch_with_memory(&mut arena, load_ne_v).unwrap();
    assert!(matches!(branch.if_true, PathStatus::Infeasible));
    assert!(branch.if_false.is_feasible());
    assert_eq!(
        executor.path_condition(),
        &[i_eq_j],
        "branch_with_memory must not commit either direction"
    );

    assert!(
        executor
            .assume_with_memory(&mut arena, loaded_eq_v)
            .unwrap()
            .is_feasible()
    );
    assert!(
        executor.model_with_memory(&mut arena).unwrap().is_some(),
        "memory-aware model extraction should replay the committed path"
    );
}

#[test]
fn cfg_explorer_auto_routes_array_branch_without_memory_flag() {
    let mut arena = TermArena::new();
    let mem = arena
        .declare(
            "auto_mem",
            Sort::Array {
                index: ArraySortKey::BitVec(8),
                element: ArraySortKey::BitVec(8),
            },
        )
        .unwrap();
    let mem_v = arena.var(mem);
    let is = arena.declare("auto_i", Sort::BitVec(8)).unwrap();
    let js = arena.declare("auto_j", Sort::BitVec(8)).unwrap();
    let vs = arena.declare("auto_v", Sort::BitVec(8)).unwrap();
    let (i, j, v) = (arena.var(is), arena.var(js), arena.var(vs));

    let stored = arena.store(mem_v, i, v).unwrap();
    let loaded = arena.select(stored, j).unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();
    let loaded_eq_v = arena.eq(loaded, v).unwrap();
    let load_ne_v = arena.not(loaded_eq_v).unwrap();

    let mut executor = SymbolicExecutor::new();
    let outcome = executor
        .explore_cfg(
            &mut arena,
            0u8,
            CfgExploreConfig {
                max_steps: 8,
                max_targets: 4,
                memory_aware: false,
            },
            move |_arena, state| {
                Ok(match state {
                    0 => CfgStep::Assume {
                        condition: i_eq_j,
                        next: 1,
                    },
                    1 => CfgStep::Branch {
                        condition: load_ne_v,
                        if_true: 2,
                        if_false: 3,
                    },
                    2 | 3 => CfgStep::Target(state),
                    _ => CfgStep::Stop,
                })
            },
        )
        .unwrap();

    assert_eq!(
        outcome.reached.len(),
        1,
        "only the read-over-write-consistent branch should reach a target"
    );
    assert_eq!(outcome.reached[0].state, 3);
    assert_eq!(
        outcome.pruned_infeasible, 1,
        "the disequality branch should be pruned by the auto-selected array route"
    );
    assert_eq!(
        outcome.unknown_branches, 0,
        "array support should not degrade this branch to Unknown"
    );
    assert!(
        executor.path_condition().is_empty(),
        "CFG exploration must restore the caller's incoming path"
    );
}

#[test]
fn symbolic_memory_helper_routes_load_branches_through_memory_executor() {
    let mut arena = TermArena::new();
    let is = arena.declare("helper_i", Sort::BitVec(8)).unwrap();
    let js = arena.declare("helper_j", Sort::BitVec(8)).unwrap();
    let vs = arena.declare("helper_v", Sort::BitVec(8)).unwrap();
    let (i, j, v) = (arena.var(is), arena.var(js), arena.var(vs));

    let mut memory = SymbolicMemory::declare_bv(&mut arena, "helper_mem", 8, 8).unwrap();
    assert_eq!(memory.index_sort(), Sort::BitVec(8));
    assert_eq!(memory.element_sort(), Sort::BitVec(8));
    let original_term = memory.term();
    let updated = memory.store(&mut arena, i, v).unwrap();
    assert_ne!(
        updated, original_term,
        "store advances the symbolic memory term"
    );

    let mut executor = SymbolicExecutor::new();
    let i_eq_j = arena.eq(i, j).unwrap();
    assert!(
        executor
            .assume_with_memory(&mut arena, i_eq_j)
            .unwrap()
            .is_feasible(),
        "address aliasing path prefix is feasible"
    );

    let branch = memory
        .branch_load_eq(&mut executor, &mut arena, j, v)
        .unwrap();
    assert!(
        branch.if_true.is_feasible(),
        "load after store at an equal address may take the equality branch"
    );
    assert!(
        branch.if_false.is_infeasible(),
        "read-over-write rules out the disequality branch"
    );
    assert_eq!(
        executor.path_condition(),
        &[i_eq_j],
        "branch_load_eq must not commit either direction"
    );

    assert!(
        memory
            .assume_load_eq(&mut executor, &mut arena, j, v)
            .unwrap()
            .is_feasible(),
        "committing the feasible load equality keeps the path alive"
    );
    assert!(
        executor.model_with_memory(&mut arena).unwrap().is_some(),
        "the memory-helper path yields a replay-checked model"
    );
}
