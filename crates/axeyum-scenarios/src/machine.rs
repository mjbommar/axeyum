//! Register-machine path-condition scenarios.
//!
//! [`register_machine_path`] mirrors symbolic execution of a single straight-
//! line path: a few symbolic inputs flow through a sequence of supported
//! bit-vector operations, and branch predicates are recorded in the direction a
//! concrete run takes them. The conjunction of taken predicates is the path
//! condition, satisfiable by construction with the concrete inputs as witness.
//!
//! [`conflicting_path`] models the common infeasible case: two incompatible
//! constraints on the same derived value, which no input can satisfy.

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};
use axeyum_query::Query;

use crate::{Expectation, Family, Scenario, SplitMix64, UnsatEvidence, mask};

/// Number of symbolic input registers in a machine path scenario.
const INPUTS: usize = 3;

/// Builds a satisfiable straight-line path condition over `width`-bit inputs
/// with `steps` data-flow steps, seeded by `seed`.
///
/// Concrete inputs are chosen from `seed` and used to decide the direction of
/// each branch predicate, so the asserted path condition is satisfiable with
/// those inputs as a known witness.
///
/// # Panics
///
/// Panics if `width` exceeds 64 or on arena corruption.
pub fn register_machine_path(width: u32, steps: usize, seed: u64) -> Scenario {
    assert!(
        (1..=64).contains(&width),
        "register_machine_path supports widths 1..=64"
    );
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();

    let mut witness = Assignment::new();
    let mut regs = Vec::with_capacity(INPUTS);
    for i in 0..INPUTS {
        let sym = arena
            .declare(&format!("x{i}"), Sort::BitVec(width))
            .unwrap();
        let value = rng.next_u128() & mask(width);
        witness.set(sym, Value::Bv { width, value });
        regs.push(arena.var(sym));
    }

    let mut predicates = Vec::new();
    for step in 0..steps {
        // One data-flow step: combine two registers (or a register and a
        // constant) and write the result back into the live register set.
        let a = regs[usize_below(&mut rng, regs.len())];
        let b = if rng.below(2) == 0 {
            regs[usize_below(&mut rng, regs.len())]
        } else {
            let value = rng.next_u128() & mask(width);
            arena.bv_const(width, value).unwrap()
        };
        let combined = apply_bin(&mut arena, &mut rng, a, b);
        let slot = step % regs.len();
        regs[slot] = combined;

        // Every other step contributes a branch predicate, recorded in the
        // direction the concrete run takes.
        if step % 2 == 1 {
            let lhs = regs[usize_below(&mut rng, regs.len())];
            let rhs = regs[usize_below(&mut rng, regs.len())];
            let predicate = apply_cmp(&mut arena, &mut rng, lhs, rhs);
            let taken = eval(&arena, predicate, &witness)
                .expect("predicate evaluates under the concrete inputs")
                .as_bool()
                .expect("predicate is Boolean");
            let asserted = if taken {
                predicate
            } else {
                arena.not(predicate).unwrap()
            };
            predicates.push(asserted);
        }
    }

    // Pin the final value of the first register to its concrete output, the way
    // a consumer constrains an observed result.
    let pinned_value = eval(&arena, regs[0], &witness)
        .expect("register evaluates under the concrete inputs")
        .as_bv()
        .expect("register is bit-vector sorted")
        .1;
    let pinned_const = arena.bv_const(width, pinned_value).unwrap();
    predicates.push(arena.eq(regs[0], pinned_const).unwrap());

    let mut builder = Query::builder(&arena);
    for predicate in predicates {
        builder.assert(predicate).unwrap();
    }
    let query = builder.build();

    Scenario {
        name: format!("machine/w{width}_n{steps}_s{seed:#018x}"),
        family: Family::Machine,
        width,
        seed,
        arena,
        query,
        expectation: Expectation::Sat { witness },
    }
}

/// Builds an unsatisfiable path: a derived value is constrained to equal two
/// distinct constants, so no `width`-bit input can satisfy both.
///
/// # Panics
///
/// Panics if `width` exceeds 64 or on arena corruption.
pub fn conflicting_path(width: u32, seed: u64) -> Scenario {
    assert!(
        (1..=64).contains(&width),
        "conflicting_path supports widths 1..=64"
    );
    let mut rng = SplitMix64::new(seed);
    let mut arena = TermArena::new();

    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let key = arena
        .bv_const(width, rng.next_u128() & mask(width))
        .unwrap();
    let addend = arena
        .bv_const(width, rng.next_u128() & mask(width))
        .unwrap();
    // Derived value v = (x ^ key) + addend is a function of x, so it cannot
    // equal two different constants at once.
    let xored = arena.bv_xor(x, key).unwrap();
    let derived = arena.bv_add(xored, addend).unwrap();

    let target_a = rng.next_u128() & mask(width);
    let target_b = target_a.wrapping_add(1) & mask(width);
    let const_a = arena.bv_const(width, target_a).unwrap();
    let const_b = arena.bv_const(width, target_b).unwrap();
    let eq_a = arena.eq(derived, const_a).unwrap();
    let eq_b = arena.eq(derived, const_b).unwrap();

    let mut builder = Query::builder(&arena);
    builder.assert(eq_a).unwrap();
    builder.assert(eq_b).unwrap();
    let query = builder.build();

    Scenario {
        name: format!("machine/conflict_w{width}_s{seed:#018x}"),
        family: Family::Machine,
        width,
        seed,
        arena,
        query,
        // Established by self_check; recorded here as the intended evidence.
        expectation: Expectation::Unsat {
            evidence: UnsatEvidence::Exhaustive { cases: 1 << width },
        },
    }
}

/// Applies one of the supported binary data-flow operators, chosen from `rng`.
fn apply_bin(arena: &mut TermArena, rng: &mut SplitMix64, a: TermId, b: TermId) -> TermId {
    match rng.below(7) {
        0 => arena.bv_add(a, b),
        1 => arena.bv_sub(a, b),
        2 => arena.bv_xor(a, b),
        3 => arena.bv_and(a, b),
        4 => arena.bv_or(a, b),
        5 => arena.bv_shl(a, b),
        _ => arena.bv_lshr(a, b),
    }
    .unwrap()
}

/// Applies one of the supported comparison operators, chosen from `rng`.
fn apply_cmp(arena: &mut TermArena, rng: &mut SplitMix64, a: TermId, b: TermId) -> TermId {
    match rng.below(5) {
        0 => arena.bv_ult(a, b),
        1 => arena.bv_ule(a, b),
        2 => arena.bv_slt(a, b),
        3 => arena.bv_sle(a, b),
        _ => arena.eq(a, b),
    }
    .unwrap()
}

fn usize_below(rng: &mut SplitMix64, bound: usize) -> usize {
    let bound = u64::try_from(bound).expect("register count fits u64");
    usize::try_from(rng.below(bound)).expect("value below bound fits usize")
}
