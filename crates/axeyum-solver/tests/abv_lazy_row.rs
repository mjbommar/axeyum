//! Lazy/on-demand read-over-write (ROW) for `QF_ABV` over **wide indices**
//! (P2.2). The eager array elimination decides plain wide-index
//! `select(store(…))` via its `ite` chain, but **refuses** a wide-index array
//! *equality involving a store* (`b = store(a, i, v)`) because bounded
//! extensionality enumerates `2^iw` indices and caps the index width. The
//! lazy-ROW path inlines the array-variable definition and adds the ROW axiom on
//! demand (CEGAR), deciding those cases without enumeration — and never changing
//! a verdict the eager path already decides (it delegates whenever eager
//! accepts).

// Array tests name arrays/indices/elements with the conventional single letters
// (`a`, `b`, `i`, `j`, `k`, `v`, `w`); mirror the existing `abv.rs` test module's
// lint configuration for the same reason.
#![allow(clippy::many_single_char_names, clippy::similar_names)]

use axeyum_ir::{TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, SatBvBackend, SolverConfig, check_qf_abv_lazy_row, check_with_array_elimination,
};

/// `Some(true)` for SAT, `Some(false)` for UNSAT, `None` for Unknown.
fn verdict(result: &CheckResult) -> Option<bool> {
    match result {
        CheckResult::Sat(_) => Some(true),
        CheckResult::Unsat => Some(false),
        CheckResult::Unknown(_) => None,
    }
}

/// Asserts the eager array-elimination path **refuses** `assertions` (so the
/// lazy-ROW path is genuinely covering ground the eager path cannot).
fn assert_eager_refuses(assertions: &[TermId], arena: &mut TermArena) {
    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    let eager = check_with_array_elimination(&mut backend, arena, assertions, &config);
    assert!(
        eager.is_err(),
        "expected the eager path to refuse this wide-index store query, got {eager:?}"
    );
}

#[test]
fn wide_index_store_select_is_sat_via_lazy_row() {
    // b = store(a, i, #xAB) over a 32-bit index, and select(b, i) = rv.
    // The eager path refuses (array equality over a 32-bit index exceeds the
    // bounded-extensionality cap); lazy-ROW decides it SAT with rv = 0xAB and the
    // model replays against the originals.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 32, 8).unwrap();
    let b = arena.array_var("b", 32, 8).unwrap();
    let i = arena.bv_var("i", 32).unwrap();
    let v = arena.bv_const(8, 0xAB).unwrap();
    let stored = arena.store(a, i, v).unwrap();
    let eqab = arena.eq(b, stored).unwrap();
    let read = arena.select(b, i).unwrap();
    let rv = arena.bv_var("rv", 8).unwrap();
    let reqv = arena.eq(read, rv).unwrap();
    let originals = [eqab, reqv];

    // The eager path cannot decide this wide-index store-equality query.
    {
        let mut probe = arena.clone();
        assert_eager_refuses(&originals, &mut probe);
    }

    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    let result = check_qf_abv_lazy_row(&mut backend, &mut arena, &originals, &config).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected SAT via lazy-ROW, got {result:?}");
    };

    // Replay-check the returned model against EVERY original assertion.
    let assignment = model.to_assignment();
    for &t in &originals {
        assert_eq!(
            eval(&arena, t, &assignment).unwrap(),
            Value::Bool(true),
            "lazy-ROW sat model must replay to true on every original assertion"
        );
    }
    // ROW forced select(b, i) = 0xAB, so the witness for rv must be 0xAB.
    assert_eq!(
        eval(&arena, rv, &assignment).unwrap(),
        Value::Bv {
            width: 8,
            value: 0xAB
        },
        "ROW pins the read to 0xAB, so rv = 0xAB"
    );
}

#[test]
fn row_unsat_transfers() {
    // b = store(a, i, v) over a 32-bit index, and select(b, i) != v.
    // ROW forces select(b, i) = v, so the query is UNSAT — and the eager path
    // refuses the wide-index equality, so lazy-ROW carries the refutation.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 32, 8).unwrap();
    let b = arena.array_var("b", 32, 8).unwrap();
    let i = arena.bv_var("i", 32).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let stored = arena.store(a, i, v).unwrap();
    let eqab = arena.eq(b, stored).unwrap();
    let read = arena.select(b, i).unwrap();
    let read_ne_v = {
        let e = arena.eq(read, v).unwrap();
        arena.not(e).unwrap()
    };
    let originals = [eqab, read_ne_v];

    {
        let mut probe = arena.clone();
        assert_eager_refuses(&originals, &mut probe);
    }

    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    let result = check_qf_abv_lazy_row(&mut backend, &mut arena, &originals, &config).unwrap();
    assert_eq!(result, CheckResult::Unsat, "wide-index ROW must refute");
}

#[test]
fn row_unsat_via_fallthrough_index() {
    // b = store(a, i, v) over a 32-bit index; with i != k, select(b, k) must equal
    // select(a, k) (ROW miss branch). Force select(a, k) = c1 and select(b, k) = c2
    // with c1 != c2 -> UNSAT (the read falls through to a, which is pinned).
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 32, 8).unwrap();
    let b = arena.array_var("b", 32, 8).unwrap();
    let i = arena.bv_var("i", 32).unwrap();
    let k = arena.bv_var("k", 32).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let stored = arena.store(a, i, v).unwrap();
    let eqab = arena.eq(b, stored).unwrap();

    let i_ne_k = {
        let e = arena.eq(i, k).unwrap();
        arena.not(e).unwrap()
    };
    let read_a = arena.select(a, k).unwrap();
    let read_b = arena.select(b, k).unwrap();
    let c1 = arena.bv_const(8, 0x11).unwrap();
    let c2 = arena.bv_const(8, 0x22).unwrap();
    let a_eq_c1 = arena.eq(read_a, c1).unwrap();
    let b_eq_c2 = arena.eq(read_b, c2).unwrap();
    let originals = [eqab, i_ne_k, a_eq_c1, b_eq_c2];

    {
        let mut probe = arena.clone();
        assert_eager_refuses(&originals, &mut probe);
    }

    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    let result = check_qf_abv_lazy_row(&mut backend, &mut arena, &originals, &config).unwrap();
    assert_eq!(
        result,
        CheckResult::Unsat,
        "ROW miss-branch (read falls through to a) must refute c1 != c2"
    );
}

/// Advances a 64-bit LCG and returns a 32-bit draw (no `rand` crate).
fn next_rand(state: &mut u64) -> u32 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    (*state >> 33) as u32
}

/// Builds one deterministic-random SMALL-index (`BitVec(3)` index / `BitVec(4)`
/// element) `QF_ABV` formula over store/select that the eager path decides,
/// returning its single top-level assertion.
fn build_small_case(arena: &mut TermArena, state: &mut u64) -> TermId {
    let iw = 3u32;
    let ew = 4u32;
    let a = arena.array_var("a", iw, ew).unwrap();
    let b = arena.array_var("b", iw, ew).unwrap();
    let arrays = [a, b];

    let mut idx_pool: Vec<TermId> = vec![
        arena.bv_var("i", iw).unwrap(),
        arena.bv_var("j", iw).unwrap(),
        arena.bv_var("k", iw).unwrap(),
    ];
    idx_pool.push(
        arena
            .bv_const(iw, u128::from(next_rand(state) & 0x7))
            .unwrap(),
    );
    let mut elem_pool: Vec<TermId> = vec![
        arena.bv_var("v", ew).unwrap(),
        arena.bv_var("w", ew).unwrap(),
    ];
    elem_pool.push(
        arena
            .bv_const(ew, u128::from(next_rand(state) & 0xf))
            .unwrap(),
    );

    let mut arr_pool: Vec<TermId> = arrays.to_vec();
    for _ in 0..2 {
        let base = arr_pool[(next_rand(state) as usize) % arr_pool.len()];
        let idx = idx_pool[(next_rand(state) as usize) % idx_pool.len()];
        let elem = elem_pool[(next_rand(state) as usize) % elem_pool.len()];
        let stored = arena.store(base, idx, elem).unwrap();
        arr_pool.push(stored);
    }

    for _ in 0..3 {
        let arr = arr_pool[(next_rand(state) as usize) % arr_pool.len()];
        let idx = idx_pool[(next_rand(state) as usize) % idx_pool.len()];
        let read = arena.select(arr, idx).unwrap();
        elem_pool.push(read);
    }

    let atom_count = 2 + (next_rand(state) % 3) as usize;
    let mut atoms: Vec<TermId> = Vec::with_capacity(atom_count);
    for _ in 0..atom_count {
        let lhs = elem_pool[(next_rand(state) as usize) % elem_pool.len()];
        let rhs = elem_pool[(next_rand(state) as usize) % elem_pool.len()];
        let eq = arena.eq(lhs, rhs).unwrap();
        let atom = if next_rand(state).is_multiple_of(2) {
            eq
        } else {
            arena.not(eq).unwrap()
        };
        atoms.push(atom);
    }

    let mut formula = atoms[0];
    for &atom in &atoms[1..] {
        formula = if next_rand(state).is_multiple_of(2) {
            arena.and(formula, atom).unwrap()
        } else {
            arena.or(formula, atom).unwrap()
        };
    }
    if next_rand(state).is_multiple_of(4) {
        formula = arena.not(formula).unwrap();
    }
    formula
}

#[test]
fn lazy_row_agrees_with_eager_on_small_cases() {
    // SOUNDNESS-NEGATIVE / differential: on a batch of small-index store/select
    // queries, the lazy-ROW path must AGREE with the eager array-elimination
    // oracle on every jointly-decided case (no disagreement). On accepted shapes
    // lazy-ROW delegates to the eager+lazy-congruence path, so this also pins down
    // that the delegation never changes a decided verdict.
    let config = SolverConfig::default();
    let mut jointly_decided = 0usize;
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;
    let mut state: u64 = 0x1234_5678_9abc_def0;

    for _case in 0..200usize {
        let mut arena = TermArena::new();
        let assertions = [build_small_case(&mut arena, &mut state)];

        let mut lazy_backend = SatBvBackend::new();
        let mut eager_backend = SatBvBackend::new();
        let lazy = check_qf_abv_lazy_row(&mut lazy_backend, &mut arena, &assertions, &config)
            .expect("lazy-ROW check");
        let eager =
            check_with_array_elimination(&mut eager_backend, &mut arena, &assertions, &config)
                .expect("eager check");

        if let (Some(l), Some(e)) = (verdict(&lazy), verdict(&eager)) {
            assert_eq!(
                l, e,
                "lazy-ROW/eager disagree on a jointly-decided case \
                 (lazy={lazy:?}, eager={eager:?})"
            );
            jointly_decided += 1;
            if l {
                sat_count += 1;
            } else {
                unsat_count += 1;
            }
        }

        // Every lazy-ROW `sat` must independently replay against the originals.
        if let CheckResult::Sat(model) = &lazy {
            let asg = model.to_assignment();
            for &t in &assertions {
                assert_eq!(
                    eval(&arena, t, &asg).unwrap(),
                    Value::Bool(true),
                    "lazy-ROW sat model must replay true on the original assertion"
                );
            }
        }
    }

    assert!(jointly_decided > 0, "expected some jointly-decided cases");
    assert!(sat_count > 0, "expected at least one SAT case");
    assert!(unsat_count > 0, "expected at least one UNSAT case");
}

#[test]
fn lazy_row_agrees_with_eager_on_small_array_defs() {
    // Differential over the canonical array-DEFINITION shape `b = store(a, i, v)`
    // at a SMALL index (4-bit) the eager bounded-extensionality DOES decide. The
    // lazy-ROW result (delegating to eager here, since eager accepts small
    // equalities) must agree, and every SAT replays. The index is kept narrow so
    // the eager `2^iw` extensionality oracle stays cheap.
    let config = SolverConfig::default();
    let mut sat = 0usize;
    let mut unsat = 0usize;
    let mut state: u64 = 0xfeed_face_dead_beef;

    for _case in 0..40usize {
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 4, 8).unwrap();
        let b = arena.array_var("b", 4, 8).unwrap();
        let i = arena.bv_var("i", 4).unwrap();
        let v = arena
            .bv_const(8, u128::from(next_rand(&mut state) & 0xff))
            .unwrap();
        let stored = arena.store(a, i, v).unwrap();
        let eqab = arena.eq(b, stored).unwrap();
        let read = arena.select(b, i).unwrap();
        // Randomly assert select(b,i) == v (SAT) or != v (UNSAT).
        let eqv = arena.eq(read, v).unwrap();
        let constraint = if next_rand(&mut state).is_multiple_of(2) {
            eqv
        } else {
            arena.not(eqv).unwrap()
        };
        let assertions = [eqab, constraint];

        let mut lazy_backend = SatBvBackend::new();
        let mut eager_backend = SatBvBackend::new();
        let lazy = check_qf_abv_lazy_row(&mut lazy_backend, &mut arena, &assertions, &config)
            .expect("lazy-ROW check");
        let eager =
            check_with_array_elimination(&mut eager_backend, &mut arena, &assertions, &config)
                .expect("eager check");

        if let (Some(l), Some(e)) = (verdict(&lazy), verdict(&eager)) {
            assert_eq!(
                l, e,
                "lazy-ROW/eager disagree (lazy={lazy:?}, eager={eager:?})"
            );
            if l {
                sat += 1;
            } else {
                unsat += 1;
            }
        }

        if let CheckResult::Sat(model) = &lazy {
            let asg = model.to_assignment();
            for &t in &assertions {
                assert_eq!(
                    eval(&arena, t, &asg).unwrap(),
                    Value::Bool(true),
                    "lazy-ROW sat model must replay true"
                );
            }
        }
    }

    assert!(sat > 0, "expected at least one SAT array-def case");
    assert!(unsat > 0, "expected at least one UNSAT array-def case");
}
