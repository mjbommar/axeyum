//! Lazy **array extensionality** for `QF_ABV` (Stump–Barrett–Dill style). A
//! *true* array (dis)equality `a = b` / `a != b` between two array terms — neither
//! of which is an inlinable variable definition — is decided on demand by
//! diff-skolem witnesses (`a != b => select(a,k)!=select(b,k)`) and select
//! congruence (`a = b => select(a,i)=select(b,i)`), woven into the existing
//! ROW/congruence CEGAR loop. These cases were previously declined (`Unknown`) by
//! the lazy-ROW path; here they are decided, while every verdict the eager / ROW
//! paths already reach is preserved (the differential vs the eager oracle).
#![cfg(feature = "full")]
// Conventional single-letter array/index/element names, as in the `abv.rs` and
// `abv_lazy_row.rs` test modules.
#![allow(clippy::many_single_char_names, clippy::similar_names)]

use std::time::Duration;

use axeyum_ir::{TermArena, TermId, Value, eval};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, SatBvBackend, SolverConfig, check_auto, check_qf_abv_lazy_row,
    check_with_array_elimination,
};

/// `Some(true)` for SAT, `Some(false)` for UNSAT, `None` for Unknown.
fn verdict(result: &CheckResult) -> Option<bool> {
    match result {
        CheckResult::Sat(_) => Some(true),
        CheckResult::Unsat => Some(false),
        CheckResult::Unknown(_) => None,
    }
}

/// Replays a `sat` model against every original assertion (must all be `true`).
fn assert_replays(model: &axeyum_solver::Model, arena: &TermArena, originals: &[TermId]) {
    let assignment = model.to_assignment();
    for &t in originals {
        assert_eq!(
            eval(arena, t, &assignment).unwrap(),
            Value::Bool(true),
            "lazy-extensionality sat model must replay true on every original assertion"
        );
    }
}

#[test]
fn extensionality_unsat_two_stores() {
    // store(a,i,v) != store(a,i,v): a term is not disequal from itself. Both sides
    // are non-inlinable store terms (not bare variables), so the surviving atom is
    // a TRUE structural array disequality the extensionality path must refute via
    // the diff-skolem witness collapsing against reflexivity. UNSAT.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 8, 8).unwrap();
    let i = arena.bv_var("i", 8).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let s = arena.store(a, i, v).unwrap();
    // `eq(s, s)` interns to one term; negate it: `s != s` is UNSAT.
    let a_ne_b = {
        let e = arena.eq(s, s).unwrap();
        arena.not(e).unwrap()
    };
    let originals = [a_ne_b];

    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    let result = check_qf_abv_lazy_row(&mut backend, &mut arena, &originals, &config).unwrap();
    assert_eq!(
        result,
        CheckResult::Unsat,
        "an array term cannot be disequal from itself: extensionality UNSAT"
    );
}

#[test]
fn extensionality_unsat_pinned_reads() {
    // a != b, but a and b are pinned to be equal everywhere they CAN differ.
    // Concretely over a 1-bit index (only two indices, 0 and 1): pin
    // select(a,0)=select(b,0) and select(a,1)=select(b,1). Then a and b agree at
    // every index, so a = b — and a != b is UNSAT. The diff-skolem k must land on
    // index 0 or 1, where the reads are pinned equal, so the witness lemma
    // select(a,k)!=select(b,k) is unsatisfiable. (Eager bounded extensionality
    // also decides this; the verdicts must match.)
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 1, 4).unwrap();
    let b = arena.array_var("b", 1, 4).unwrap();
    let zero = arena.bv_const(1, 0).unwrap();
    let one = arena.bv_const(1, 1).unwrap();
    let a0 = arena.select(a, zero).unwrap();
    let b0 = arena.select(b, zero).unwrap();
    let a1 = arena.select(a, one).unwrap();
    let b1 = arena.select(b, one).unwrap();
    let eq0 = arena.eq(a0, b0).unwrap();
    let eq1 = arena.eq(a1, b1).unwrap();
    let a_ne_b = {
        let e = arena.eq(a, b).unwrap();
        arena.not(e).unwrap()
    };
    let originals = [eq0, eq1, a_ne_b];

    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    let result = check_qf_abv_lazy_row(&mut backend, &mut arena, &originals, &config).unwrap();
    assert_eq!(
        result,
        CheckResult::Unsat,
        "a and b agree at every (of two) index, so a != b is UNSAT"
    );
}

#[test]
fn extensionality_sat_diseq_witness_replays() {
    // a != b with no further constraint: SAT, and the diff-skolem witnesses a
    // concrete index where the reconstructed arrays differ. The structural atom is
    // `store(a,i,#x01) != store(a,i,#x02)` so neither side is an inlinable
    // variable (both are stores over the same base) — a true extensionality SAT.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 8, 8).unwrap();
    let i = arena.bv_var("i", 8).unwrap();
    let v1 = arena.bv_const(8, 0x01).unwrap();
    let v2 = arena.bv_const(8, 0x02).unwrap();
    let lhs = arena.store(a, i, v1).unwrap();
    let rhs = arena.store(a, i, v2).unwrap();
    let ne = {
        let e = arena.eq(lhs, rhs).unwrap();
        arena.not(e).unwrap()
    };
    let originals = [ne];

    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    let result = check_qf_abv_lazy_row(&mut backend, &mut arena, &originals, &config).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected SAT (the two stores genuinely differ at i), got {result:?}");
    };
    assert_replays(&model, &arena, &originals);
}

#[test]
fn extensionality_eq_then_read_unsat() {
    // store(a,i,v) = store(b,i,w)  AND  select on a witnessing index forces a
    // contradiction. Take a = b structurally via two stores, then assert the
    // stored values differ: store(a,i,v) = store(a,i,w) with v != w is UNSAT,
    // because the two arrays agree iff v = w at index i.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 8, 8).unwrap();
    let i = arena.bv_var("i", 8).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let w = arena.bv_var("w", 8).unwrap();
    let lhs = arena.store(a, i, v).unwrap();
    let rhs = arena.store(a, i, w).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    let v_ne_w = {
        let e = arena.eq(v, w).unwrap();
        arena.not(e).unwrap()
    };
    let originals = [eq, v_ne_w];

    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    let result = check_qf_abv_lazy_row(&mut backend, &mut arena, &originals, &config).unwrap();
    assert_eq!(
        result,
        CheckResult::Unsat,
        "store(a,i,v)=store(a,i,w) with v!=w is UNSAT (they differ at i)"
    );
}

#[test]
fn extensionality_eq_then_read_sat_replays() {
    // store(a,i,v) = store(a,j,w) is SATISFIABLE (e.g. i=j and v=w, or the stores
    // happen to land equal). The non-substitutable array equality is decided SAT
    // and the model replays. Neither side is a bare variable, so this engages the
    // extensionality path's congruence handling.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 8, 8).unwrap();
    let i = arena.bv_var("i", 8).unwrap();
    let j = arena.bv_var("j", 8).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let w = arena.bv_var("w", 8).unwrap();
    let lhs = arena.store(a, i, v).unwrap();
    let rhs = arena.store(a, j, w).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    let originals = [eq];

    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    let result = check_qf_abv_lazy_row(&mut backend, &mut arena, &originals, &config).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected SAT (i=j,v=w is a model), got {result:?}");
    };
    assert_replays(&model, &arena, &originals);
}

#[test]
fn lazy_ext_timeout_reports_refinement_counters() {
    // The structural equality between two wide-index store terms forces the lazy
    // extensionality path (not variable-definition ROW). With an already-expired
    // timeout it should return a telemetry-rich decline before solving.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 16, 8).unwrap();
    let b = arena.array_var("b", 16, 8).unwrap();
    let i = arena.bv_var("i", 16).unwrap();
    let v = arena.bv_var("v", 8).unwrap();
    let w = arena.bv_var("w", 8).unwrap();
    let lhs = arena.store(a, i, v).unwrap();
    let rhs = arena.store(b, i, w).unwrap();
    let eq = arena.eq(lhs, rhs).unwrap();
    let originals = [eq];

    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default().with_timeout(Duration::ZERO);
    let result = check_qf_abv_lazy_row(&mut backend, &mut arena, &originals, &config).unwrap();
    let CheckResult::Unknown(reason) = result else {
        panic!("expected lazy-ext timeout unknown, got {result:?}");
    };

    assert!(
        reason
            .detail
            .contains("lazy-extensionality deadline exceeded before refinement converged"),
        "unexpected unknown detail: {}",
        reason.detail
    );
    for field in [
        "round=0",
        "sites=",
        "array_eq_atoms=1",
        "row_lemmas=0",
        "cong_lemmas=0",
        "diff_skolems=0",
        "working_assertions=",
    ] {
        assert!(
            reason.detail.contains(field),
            "missing `{field}` in unknown detail: {}",
            reason.detail
        );
    }
}

#[test]
fn extensionality_nested_array_equalities_materialize_reads_after_completion() {
    let mut script = parse_script(
        r"
        (set-logic QF_ABV)
        (declare-const a0 (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const a1 (Array (_ BitVec 32) (_ BitVec 8)))
        (declare-const a2 (Array (_ BitVec 32) (_ BitVec 8)))
        (assert
          (= #b1
             (bvnot
               (ite (= (ite (= (ite (= a0 a1) #b1 #b0)
                              (ite (= a0 a2) #b1 #b0))
                         #b1 #b0)
                       (ite (= a1 a2) #b1 #b0))
                    #b1 #b0))))
        (check-sat)
    ",
    )
    .unwrap();
    let assertions = script.checked_flat_view().to_vec();
    let result = check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected SAT for the rw134 extensionality shape, got {result:?}");
    };
    assert_replays(&model, &script.arena, &assertions);
}

/// Advances a 64-bit LCG and returns a 32-bit draw (no `rand` crate).
fn next_rand(state: &mut u64) -> u32 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    (*state >> 33) as u32
}

/// Builds one deterministic-random small `QF_ABV` formula that ALWAYS includes at
/// least one array (dis)equality atom between non-trivial array terms (so the
/// extensionality path is genuinely exercised), at a small index/element width the
/// eager bounded-extensionality oracle can also decide.
fn build_ext_case(arena: &mut TermArena, state: &mut u64) -> TermId {
    let iw = 4u32;
    let ew = 4u32;
    let a = arena.array_var("a", iw, ew).unwrap();
    let b = arena.array_var("b", iw, ew).unwrap();

    let idx_pool: Vec<TermId> = vec![
        arena.bv_var("i", iw).unwrap(),
        arena.bv_var("j", iw).unwrap(),
        arena
            .bv_const(iw, u128::from(next_rand(state) & 0xf))
            .unwrap(),
    ];
    let elem_pool: Vec<TermId> = vec![
        arena.bv_var("v", ew).unwrap(),
        arena.bv_var("w", ew).unwrap(),
        arena
            .bv_const(ew, u128::from(next_rand(state) & 0xf))
            .unwrap(),
    ];

    // Build two array terms, each either a variable or a store over a variable.
    let make_arr = |arena: &mut TermArena, state: &mut u64, base: TermId| -> TermId {
        if next_rand(state).is_multiple_of(2) {
            base
        } else {
            let idx = idx_pool[(next_rand(state) as usize) % idx_pool.len()];
            let elem = elem_pool[(next_rand(state) as usize) % elem_pool.len()];
            arena.store(base, idx, elem).unwrap()
        }
    };
    let arr1 = make_arr(arena, state, a);
    let arr2 = make_arr(arena, state, b);

    // The mandatory array (dis)equality atom.
    let arr_eq = arena.eq(arr1, arr2).unwrap();
    let arr_atom = if next_rand(state).is_multiple_of(2) {
        arr_eq
    } else {
        arena.not(arr_eq).unwrap()
    };

    // A couple of scalar select atoms to interact with the equality.
    let r1 = {
        let idx = idx_pool[(next_rand(state) as usize) % idx_pool.len()];
        arena.select(arr1, idx).unwrap()
    };
    let r2 = {
        let idx = idx_pool[(next_rand(state) as usize) % idx_pool.len()];
        arena.select(arr2, idx).unwrap()
    };
    let scalar_eq = arena.eq(r1, r2).unwrap();
    let scalar_atom = if next_rand(state).is_multiple_of(2) {
        scalar_eq
    } else {
        arena.not(scalar_eq).unwrap()
    };

    // Combine: arr_atom AND/OR scalar_atom.
    if next_rand(state).is_multiple_of(2) {
        arena.and(arr_atom, scalar_atom).unwrap()
    } else {
        arena.or(arr_atom, scalar_atom).unwrap()
    }
}

#[test]
fn lazy_ext_matches_eager_differential() {
    // DIFFERENTIAL vs the eager `check_with_array_elimination` oracle over a
    // deterministic LCG corpus of small QF_ABV queries that each carry an array
    // (dis)equality. Whenever BOTH decide, verdicts MUST agree (0 disagreements);
    // the lazy-extensionality path may additionally decide cases the bounded eager
    // path declines (value-add). Every lazy `sat` replays.
    let config = SolverConfig::default();
    let mut jointly_decided = 0usize;
    let mut disagreements = 0usize;
    let mut value_add = 0usize;
    let mut lazy_sat = 0usize;
    let mut lazy_unsat = 0usize;
    let mut state: u64 = 0x0bad_c0de_dead_1357;

    for _case in 0..300usize {
        let mut arena = TermArena::new();
        let assertions = [build_ext_case(&mut arena, &mut state)];

        let mut lazy_backend = SatBvBackend::new();
        let mut eager_backend = SatBvBackend::new();
        let lazy = check_qf_abv_lazy_row(&mut lazy_backend, &mut arena, &assertions, &config)
            .expect("lazy-ext check");
        // The eager path refuses some array-equality shapes; treat its refusal as
        // "did not decide" (the lazy path may still decide it — value-add).
        let eager =
            check_with_array_elimination(&mut eager_backend, &mut arena, &assertions, &config).ok();

        match (verdict(&lazy), eager.as_ref().and_then(verdict)) {
            (Some(l), Some(e)) => {
                if l != e {
                    disagreements += 1;
                }
                jointly_decided += 1;
            }
            (Some(_), None) => value_add += 1,
            _ => {}
        }

        match &lazy {
            CheckResult::Sat(model) => {
                lazy_sat += 1;
                assert_replays(model, &arena, &assertions);
            }
            CheckResult::Unsat => lazy_unsat += 1,
            CheckResult::Unknown(_) => {}
        }
    }

    assert_eq!(
        disagreements, 0,
        "lazy-extensionality disagreed with the eager oracle on a jointly-decided case"
    );
    assert!(jointly_decided > 0, "expected some jointly-decided cases");
    assert!(lazy_sat > 0, "expected at least one lazy SAT");
    assert!(lazy_unsat > 0, "expected at least one lazy UNSAT");
    // `value_add` may legitimately be 0 at this width (the eager oracle decides
    // these small cases); it is reported, not asserted positive.
    let _ = value_add;
}

#[test]
fn soundness_negative_distinct_diff_skolems() {
    // SOUNDNESS-NEGATIVE: two independent disequalities a != b and a != c must each
    // get their OWN diff-skolem witness — a naive shared skolem could pin b and c
    // to differ from a at the SAME index and spuriously over-constrain or, worse,
    // mis-witness. Here a != b AND a != c AND b = c. b = c is an inlinable
    // definition (c := b), leaving a != b AND a != b — satisfiable (a single
    // witness suffices). The result must be SAT and replay (b and c equal, both
    // differing from a somewhere), never a wrong UNSAT.
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 6, 6).unwrap();
    let b = arena.array_var("b", 6, 6).unwrap();
    let c = arena.array_var("c", 6, 6).unwrap();
    let a_ne_b = {
        let e = arena.eq(a, b).unwrap();
        arena.not(e).unwrap()
    };
    let a_ne_c = {
        let e = arena.eq(a, c).unwrap();
        arena.not(e).unwrap()
    };
    let b_eq_c = arena.eq(b, c).unwrap();
    let originals = [a_ne_b, a_ne_c, b_eq_c];

    let mut backend = SatBvBackend::new();
    let config = SolverConfig::default();
    let result = check_qf_abv_lazy_row(&mut backend, &mut arena, &originals, &config).unwrap();
    match result {
        CheckResult::Sat(model) => assert_replays(&model, &arena, &originals),
        CheckResult::Unknown(_) => {
            // A sound decline is acceptable; a wrong UNSAT is not.
        }
        CheckResult::Unsat => panic!("a != b, a != c, b = c is SATISFIABLE — wrong UNSAT"),
    }
}

/// Regression guard for verdict nondeterminism in the lazy-extensionality
/// scalar (declared-sort EUF) route. The `QF_AX` `arrays3` instance is SAT and
/// replayable; before the fix, the EUF model assigned uninterpreted class codes
/// in `HashMap` iteration order (per-process randomized), so successive runs
/// relabelled the model differently and the downstream array projection/repair
/// declined to `Unknown` on a subset of runs (~12% flake rate). Running the
/// route many times in-process exercises distinct `HashMap` seeds (each
/// `HashMap::new()` advances the thread-local key), so a hash-order-dependent
/// verdict shows up here as a mix of `Sat` and `Unknown`.
#[test]
fn qf_ax_arrays3_lazy_ext_verdict_is_deterministic() {
    use axeyum_solver::check_qf_ax_declared_sort_lazy_row;

    let input = include_str!(
        "../../../corpus/public-curated/non-incremental/QF_AX/cvc5-regress-clean/cli__regress0__arrays__arrays3.smt2"
    );
    for _ in 0..64 {
        let mut script = parse_script(input).unwrap();
        let assertions = script.checked_flat_view().to_vec();
        let result = check_qf_ax_declared_sort_lazy_row(
            &mut script.arena,
            &assertions,
            &SolverConfig::default(),
        )
        .unwrap();
        let CheckResult::Sat(model) = result else {
            panic!("arrays3 must decide SAT on every run; got {result:?}");
        };
        let assignment = model.to_assignment();
        for &assertion in &script.assertions {
            assert_eq!(
                eval(&script.arena, assertion, &assignment),
                Ok(Value::Bool(true))
            );
        }
    }
}
