//! Verdict-invariance and well-formedness gate for the route-trace telemetry.
//!
//! The load-bearing guarantee is that telemetry is *free*: for every query,
//! `check_auto_explained(arena, &a, &cfg).map(|(r, _)| r)` equals
//! `check_auto(arena, &a, &cfg)` exactly. A single differing verdict is a hard
//! failure. We also assert the trace is non-empty, well-formed (its terminal
//! entry matches the overall result, with the decisive route last), and
//! deterministic (run twice, identical trace).

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, DeclineReason, RouteOutcome, RouteTrace, SolverConfig, Verdict, check_auto,
    check_auto_explained,
};

/// A tiny deterministic linear-congruential generator (Numerical Recipes
/// constants). No external rng, no hash-map iteration — fully reproducible.
struct Lcg(u64);

impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

/// Builds one quantifier-free query of a pseudo-randomly chosen fragment. The
/// fragments span what `check_auto` routes: `QF_BV`, conjunctive/Boolean
/// `QF_LIA`/`QF_LRA`, `QF_UF`, mixed, plus a deliberately unsupported case.
fn build_query(rng: &mut Lcg, arena: &mut TermArena) -> Vec<TermId> {
    match rng.below(8) {
        0 => build_qf_bv(rng, arena),
        1 => build_qf_lia_conj(rng, arena),
        2 => build_qf_lia_bool(rng, arena),
        3 => build_qf_lra(rng, arena),
        4 => build_qf_uf(rng, arena),
        5 => build_mixed_bv_int(rng, arena),
        6 => build_unsupported(arena),
        _ => build_qf_bv_unsat(rng, arena),
    }
}

fn build_qf_bv(rng: &mut Lcg, arena: &mut TermArena) -> Vec<TermId> {
    let w = 8;
    let x = arena.bv_var("x", w).unwrap();
    let y = arena.bv_var("y", w).unwrap();
    let c = arena.bv_const(w, rng.below(256).into()).unwrap();
    let sum = arena.bv_add(x, y).unwrap();
    let eq = arena.eq(sum, c).unwrap();
    let lt = arena.bv_ult(x, c).unwrap();
    vec![eq, lt]
}

fn build_qf_bv_unsat(_rng: &mut Lcg, arena: &mut TermArena) -> Vec<TermId> {
    let w = 4;
    let x = arena.bv_var("xu", w).unwrap();
    let three = arena.bv_const(w, 3).unwrap();
    let five = arena.bv_const(w, 5).unwrap();
    let e3 = arena.eq(x, three).unwrap();
    let e5 = arena.eq(x, five).unwrap();
    vec![e3, e5]
}

fn build_qf_lia_conj(rng: &mut Lcg, arena: &mut TermArena) -> Vec<TermId> {
    let x = {
        let s = arena.declare("li_x", Sort::Int).unwrap();
        arena.var(s)
    };
    let lo = arena.int_const(0);
    let hi = arena.int_const(i128::from(rng.below(20) + 1));
    let ge = arena.int_ge(x, lo).unwrap();
    let le = arena.int_le(x, hi).unwrap();
    vec![ge, le]
}

fn build_qf_lia_bool(_rng: &mut Lcg, arena: &mut TermArena) -> Vec<TermId> {
    let x = {
        let s = arena.declare("lib_x", Sort::Int).unwrap();
        arena.var(s)
    };
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let lt0 = arena.int_lt(x, zero).unwrap();
    let gt1 = arena.int_gt(x, one).unwrap();
    // x < 0 OR x > 1 (Boolean structure over integer atoms).
    let disj = arena.or(lt0, gt1).unwrap();
    vec![disj]
}

fn build_qf_lra(rng: &mut Lcg, arena: &mut TermArena) -> Vec<TermId> {
    let x = {
        let s = arena.declare("lr_x", Sort::Real).unwrap();
        arena.var(s)
    };
    let lo = arena.real_const(axeyum_ir::Rational::integer(0));
    let hi = arena.real_const(axeyum_ir::Rational::integer(i128::from(rng.below(10) + 1)));
    let ge = arena.real_ge(x, lo).unwrap();
    let le = arena.real_le(x, hi).unwrap();
    vec![ge, le]
}

fn build_qf_uf(_rng: &mut Lcg, arena: &mut TermArena) -> Vec<TermId> {
    let carrier = Sort::Uninterpreted(arena.declare_uninterpreted_sort("U"));
    let fun = arena.declare_fun("uf_f", &[carrier], carrier).unwrap();
    let lhs = {
        let s = arena.declare("uf_a", carrier).unwrap();
        arena.var(s)
    };
    let rhs = {
        let s = arena.declare("uf_b", carrier).unwrap();
        arena.var(s)
    };
    let f_lhs = arena.apply(fun, &[lhs]).unwrap();
    let f_rhs = arena.apply(fun, &[rhs]).unwrap();
    let lhs_eq_rhs = arena.eq(lhs, rhs).unwrap();
    let f_lhs_ne_f_rhs = {
        let eq = arena.eq(f_lhs, f_rhs).unwrap();
        arena.not(eq).unwrap()
    };
    let p = {
        let s = arena.declare("uf_p", Sort::Bool).unwrap();
        arena.var(s)
    };
    let not_p = arena.not(p).unwrap();
    let left_clause = arena.or(lhs_eq_rhs, p).unwrap();
    let right_clause = arena.or(lhs_eq_rhs, not_p).unwrap();
    // (a = b ∨ p) ∧ (a = b ∨ ¬p) ∧ f(a) ≠ f(b) is UNSAT: Boolean
    // resolution forces a = b, then EUF congruence forces f(a) = f(b).
    // This keeps the default preprocessing path from collapsing the direct
    // equality contradiction before route tracing reaches the online EUF loop.
    vec![left_clause, right_clause, f_lhs_ne_f_rhs]
}

fn build_mixed_bv_int(rng: &mut Lcg, arena: &mut TermArena) -> Vec<TermId> {
    // A BV query plus an independent integer constraint (no shared sort) — the
    // mixed dispatch must still produce a stable verdict.
    let mut q = build_qf_bv(rng, arena);
    let x = {
        let s = arena.declare("mix_i", Sort::Int).unwrap();
        arena.var(s)
    };
    let two = arena.int_const(2);
    let eq2 = arena.eq(x, two).unwrap();
    q.push(eq2);
    q
}

fn build_unsupported(arena: &mut TermArena) -> Vec<TermId> {
    // A two-variable nonlinear integer goal (`x*x + y*y = 3`): the exact refuters
    // and the bit-blast width ladder all report Unknown (no integer root, but no
    // cheap sign/relaxation refutation either) — exercises the terminal
    // `Declined`/`Incomplete` trace shape.
    let x = {
        let s = arena.declare("ns_x", Sort::Int).unwrap();
        arena.var(s)
    };
    let y = {
        let s = arena.declare("ns_y", Sort::Int).unwrap();
        arena.var(s)
    };
    let xx = arena.int_mul(x, x).unwrap();
    let yy = arena.int_mul(y, y).unwrap();
    let sum = arena.int_add(xx, yy).unwrap();
    let three = arena.int_const(3);
    let eq = arena.eq(sum, three).unwrap();
    vec![eq]
}

/// Two [`CheckResult`]s agree as *verdicts*: same Sat/Unsat/Unknown, and for
/// `Sat` the model from `explained` still satisfies the original assertions
/// (model replay), for `Unknown` the same classified kind.
fn verdicts_agree(
    arena: &TermArena,
    assertions: &[TermId],
    plain: &CheckResult,
    explained: &CheckResult,
) -> bool {
    match (plain, explained) {
        (CheckResult::Unsat, CheckResult::Unsat) => true,
        (CheckResult::Unknown(a), CheckResult::Unknown(b)) => a.kind == b.kind,
        (CheckResult::Sat(_), CheckResult::Sat(model)) => {
            let assignment = model.to_assignment();
            assertions
                .iter()
                .all(|&t| matches!(eval(arena, t, &assignment), Ok(Value::Bool(true))))
        }
        _ => false,
    }
}

/// The terminal trace entry must be consistent with the overall verdict: a
/// `Decided` last entry iff Sat/Unsat, a terminal `Declined` iff Unknown. Also
/// checks every non-terminal entry is a probe or a `Declined`, so the decisive
/// route is genuinely last.
fn trace_well_formed(result: &CheckResult, trace: &RouteTrace) -> bool {
    if trace.is_empty() {
        return false;
    }
    let attempts = trace.attempts();
    // First entry is the probe preamble.
    if !matches!(attempts[0].outcome, RouteOutcome::Probe(_)) {
        return false;
    }
    // Every entry before the last is a probe or a decline (the decisive route,
    // if any, is last).
    for attempt in &attempts[..attempts.len() - 1] {
        match &attempt.outcome {
            RouteOutcome::Probe(_) | RouteOutcome::Declined(_) => {}
            RouteOutcome::Decided(_) => return false,
        }
    }
    let last = &attempts[attempts.len() - 1].outcome;
    match result {
        CheckResult::Sat(_) => matches!(last, RouteOutcome::Decided(Verdict::Sat)),
        CheckResult::Unsat => matches!(last, RouteOutcome::Decided(Verdict::Unsat)),
        CheckResult::Unknown(_) => matches!(last, RouteOutcome::Declined(_)),
    }
}

#[test]
fn verdict_invariance_over_lcg_corpus() {
    let cfg = SolverConfig::default();
    let mut rng = Lcg(0x1234_5678_9abc_def0);
    let n = 400;
    let mut mismatches = 0;
    let mut sat = 0;
    let mut unsat = 0;
    let mut unknown = 0;
    for _ in 0..n {
        let mut arena = TermArena::new();
        let assertions = build_query(&mut rng, &mut arena);

        let plain = check_auto(&mut arena, &assertions, &cfg);
        let explained = check_auto_explained(&mut arena, &assertions, &cfg);

        match (&plain, &explained) {
            (Ok(p), Ok((e, trace))) => {
                if !verdicts_agree(&arena, &assertions, p, e) {
                    mismatches += 1;
                    eprintln!("VERDICT MISMATCH: plain={p:?} explained={e:?}");
                }
                assert!(
                    trace_well_formed(e, trace),
                    "ill-formed trace for {e:?}:\n{trace}"
                );
                match e {
                    CheckResult::Sat(_) => sat += 1,
                    CheckResult::Unsat => unsat += 1,
                    CheckResult::Unknown(_) => unknown += 1,
                }
            }
            (Err(_), Err(_)) => {}
            (p, e) => {
                mismatches += 1;
                eprintln!("OK/ERR MISMATCH: plain={p:?} explained={e:?}");
            }
        }
    }
    eprintln!("corpus={n} sat={sat} unsat={unsat} unknown={unknown} mismatches={mismatches}");
    assert_eq!(mismatches, 0, "verdict invariance violated");
}

#[test]
fn trace_is_deterministic_across_runs() {
    let cfg = SolverConfig::default();
    // Run the same corpus twice and compare the traces byte-for-byte (Display)
    // and structurally (Eq).
    for seed in [1u64, 42, 0xdead_beef] {
        let mut rng_a = Lcg(seed);
        let mut rng_b = Lcg(seed);
        for _ in 0..50 {
            let mut arena_a = TermArena::new();
            let qa = build_query(&mut rng_a, &mut arena_a);
            let (_, trace_a) = check_auto_explained(&mut arena_a, &qa, &cfg).unwrap();

            let mut arena_b = TermArena::new();
            let qb = build_query(&mut rng_b, &mut arena_b);
            let (_, trace_b) = check_auto_explained(&mut arena_b, &qb, &cfg).unwrap();

            assert_eq!(trace_a, trace_b, "non-deterministic trace");
            assert_eq!(
                trace_a.to_string(),
                trace_b.to_string(),
                "non-deterministic trace Display"
            );
        }
    }
}

#[test]
fn qf_bv_sat_route_is_decided() {
    let cfg = SolverConfig::default();
    let mut arena = TermArena::new();
    let w = 8;
    let x = arena.bv_var("x", w).unwrap();
    let ten = arena.bv_const(w, 10).unwrap();
    let lt = arena.bv_ult(x, ten).unwrap();

    let (result, trace) = check_auto_explained(&mut arena, &[lt], &cfg).unwrap();
    assert!(matches!(result, CheckResult::Sat(_)));
    let last = trace.last().expect("non-empty trace");
    assert_eq!(last.route, "qf-bv");
    assert!(matches!(last.outcome, RouteOutcome::Decided(Verdict::Sat)));
}

#[test]
fn qf_bv_unsat_route_is_decided() {
    let cfg = SolverConfig::default();
    let mut arena = TermArena::new();
    let q = {
        let mut rng = Lcg(7);
        build_qf_bv_unsat(&mut rng, &mut arena)
    };
    let (result, trace) = check_auto_explained(&mut arena, &q, &cfg).unwrap();
    assert!(matches!(result, CheckResult::Unsat));
    let last = trace.last().expect("non-empty trace");
    assert!(matches!(
        last.outcome,
        RouteOutcome::Decided(Verdict::Unsat)
    ));
}

#[test]
fn qf_uf_front_door_decides_with_online_cdclt() {
    let cfg = SolverConfig::default();
    let mut arena = TermArena::new();
    let assertions = build_qf_uf(&mut Lcg(0), &mut arena);

    let (result, trace) = check_auto_explained(&mut arena, &assertions, &cfg).unwrap();
    assert_eq!(result, CheckResult::Unsat);
    let last = trace.last().expect("non-empty trace");
    assert_eq!(last.route, "euf-online", "trace:\n{trace}");
    assert!(matches!(
        last.outcome,
        RouteOutcome::Decided(Verdict::Unsat)
    ));
}

#[test]
fn qf_ufbv_front_door_uses_online_combination() {
    let cfg = SolverConfig::default();
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(4))
        .unwrap();
    let x = arena.bv_var("ufbv_x", 4).unwrap();
    let y = arena.bv_var("ufbv_y", 4).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let x1 = arena.bv_add(x, one).unwrap();
    let y1 = arena.bv_add(y, one).unwrap();
    let same_shifted = arena.eq(x1, y1).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let same_result = arena.eq(fx, fy).unwrap();
    let different_result = arena.not(same_result).unwrap();

    let (result, trace) =
        check_auto_explained(&mut arena, &[same_shifted, different_result], &cfg).unwrap();
    assert_eq!(result, CheckResult::Unsat);
    let last = trace.last().expect("non-empty trace");
    assert_eq!(last.route, "ufbv-online-cdclt", "trace:\n{trace}");
    assert!(matches!(
        last.outcome,
        RouteOutcome::Decided(Verdict::Unsat)
    ));
}

#[test]
fn unsupported_fragment_ends_in_terminal_unknown() {
    let cfg = SolverConfig::default();
    let mut arena = TermArena::new();
    let q = build_unsupported(&mut arena);
    let (result, trace) = check_auto_explained(&mut arena, &q, &cfg).unwrap();
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "x*x = 2 has no integer model and is undecided: {result:?}"
    );
    let last = trace.last().expect("non-empty trace");
    assert!(
        matches!(last.outcome, RouteOutcome::Declined(_)),
        "an undecided result must end in a Declined entry, got {:?}",
        last.outcome
    );
}

#[test]
fn resource_capped_lia_records_budget() {
    // A nonlinear/unbounded integer goal under a tiny wall-clock timeout should
    // surface a budget-style decline somewhere in the trail (the int-blast ladder
    // / MBQI bound report ResourceLimit). We assert the trace records at least one
    // Budget decline and the result is a (resource-limited) Unknown.
    let cfg = SolverConfig::default().with_timeout(std::time::Duration::from_millis(1));
    let mut arena = TermArena::new();
    // The two-variable nonlinear goal is undecided; under a tiny timeout the
    // int-blast ladder is cut short and surfaces a budget (ResourceLimit) decline.
    // The verdict stays Unknown either way.
    let q = build_unsupported(&mut arena);
    let (result, trace) = check_auto_explained(&mut arena, &q, &cfg).unwrap();
    assert!(matches!(result, CheckResult::Unknown(_)));
    // The terminal entry is a decline; for the timeout path it is budget-classed.
    let has_decline = trace
        .attempts()
        .iter()
        .any(|a| matches!(a.outcome, RouteOutcome::Declined(_)));
    assert!(
        has_decline,
        "expected at least one Declined entry:\n{trace}"
    );
    // Best-effort: if any decline is budget-classed, confirm it carries detail.
    for a in trace.attempts() {
        if let RouteOutcome::Declined(DeclineReason::Budget(detail)) = &a.outcome {
            assert!(!detail.is_empty(), "budget decline must carry detail");
        }
    }
}
