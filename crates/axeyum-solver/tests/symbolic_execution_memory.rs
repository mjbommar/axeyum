//! Memory-using symbolic execution over `QF_ABV` (the consumer payoff, ADR-0010).
//!
//! A program writes a symbolic value to a symbolic address and then reads a
//! fixed address; symbolic execution finds inputs reaching a target, and the
//! found model — including the reconstructed memory array — is **concretely
//! re-executed** to confirm it really reaches the target (unicorn-style,
//! oracle-free). This is the memory analogue of the scalar symbolic-execution
//! client, now that arrays are supported.

use axeyum_ir::{TermArena, Value};
use axeyum_solver::{CheckResult, SatBvBackend, SolverConfig, check_with_array_elimination};

const ADDR_WIDTH: u32 = 4;
const ELEM_WIDTH: u32 = 8;
const PROBE_ADDR: u128 = 3;
const TARGET: u128 = 0xab;

#[test]
fn memory_write_then_probe_load_finds_inputs_and_concretely_verifies() {
    // Program: mem[addr] = val; x = mem[3]; reach target iff x == 0xab.
    // (Solvable two ways: addr == 3 with val == 0xab, or addr != 3 with the
    // symbolic base memory already holding 0xab at address 3.)
    let mut arena = TermArena::new();
    let mem_sym = arena
        .declare(
            "mem",
            axeyum_ir::Sort::Array {
                index: axeyum_ir::ArraySortKey::BitVec(ADDR_WIDTH),
                element: axeyum_ir::ArraySortKey::BitVec(ELEM_WIDTH),
            },
        )
        .unwrap();
    let addr_sym = arena
        .declare("addr", axeyum_ir::Sort::BitVec(ADDR_WIDTH))
        .unwrap();
    let val_sym = arena
        .declare("val", axeyum_ir::Sort::BitVec(ELEM_WIDTH))
        .unwrap();
    let mem = arena.var(mem_sym);
    let addr = arena.var(addr_sym);
    let val = arena.var(val_sym);

    let written = arena.store(mem, addr, val).unwrap();
    let probe = arena.bv_const(ADDR_WIDTH, PROBE_ADDR).unwrap();
    let loaded = arena.select(written, probe).unwrap();
    let target = arena.bv_const(ELEM_WIDTH, TARGET).unwrap();
    let path_condition = arena.eq(loaded, target).unwrap();

    let mut backend = SatBvBackend::new();
    let result = check_with_array_elimination(
        &mut backend,
        &mut arena,
        &[path_condition],
        &SolverConfig::default(),
    )
    .expect("memory query decides without error");

    let CheckResult::Sat(model) = result else {
        panic!("the target is reachable, so the query is satisfiable");
    };

    // Extract the found inputs and the reconstructed memory.
    let addr_value = bv(model.get(addr_sym));
    let val_value = bv(model.get(val_sym));
    let memory = match model.get(mem_sym) {
        Some(Value::Array(array)) => array,
        other => panic!("memory symbol must have an array value, got {other:?}"),
    };

    // Concrete (oracle-free) re-execution of the program with the found inputs
    // and reconstructed memory: write, then read the probe address.
    let after_write = memory.store(addr_value, val_value);
    let observed = after_write.select(PROBE_ADDR);
    assert_eq!(
        observed, TARGET,
        "concrete re-execution must reach the target (addr={addr_value}, val={val_value})"
    );
}

fn bv(value: Option<Value>) -> u128 {
    match value {
        Some(Value::Bv { value, .. }) => value,
        other => panic!("expected a bit-vector value, got {other:?}"),
    }
}
