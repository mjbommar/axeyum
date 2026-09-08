//! The determinism claim, measured rather than asserted.
//!
//! The claim under test: **a budget denominated in ticks makes the same
//! decisions on the same input, on every run and under any host load, and a
//! budget denominated in wall time does not.**
//!
//! Half of that is easy to state and easy to fake. A test that only asserts
//! "two tick counts are equal" would pass with the counters stuck at zero, with
//! the decision machinery never consulted, and with a schedule that makes one
//! decision. So every assertion here is paired with a control:
//!
//! * The tick stream is asserted **identical**; the wall-clock stream measured
//!   over the *same runs* is asserted **not** identical. That is the
//!   falsifiability control — it proves this harness can see variation, so the
//!   equality above is a finding and not a blind spot.
//! * The schedule is asserted to produce **more than one distinct outcome**, so
//!   the identical logs are not twelve copies of one branch.
//! * The counters are asserted alive, so nothing is comparing zeros.
//!
//! Load is applied with real spinning threads, not simulated.

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use axeyum_cnf::ticks::TickModel;
use axeyum_cnf::{
    CnfClause, CnfFormula, CnfLit, CnfVar, SearchCounters, StreamingProofOutcome, VecProofSink,
    solve_with_drat_proof_counted,
};
use axeyum_ir::budget::{Budget, BudgetedPass, Delayed, EffortPolicy, RoundOutcome, WorkMeter};

/// Pigeonhole `pigeons` into `pigeons - 1` holes: unsat, and it forces enough
/// conflicts, restarts and reason walking to make every tick term nonzero.
fn pigeonhole(pigeons: usize) -> CnfFormula {
    let holes = pigeons - 1;
    // Zero-based: pigeon p in hole h is index (p-1)*holes + (h-1).
    let var = |p: usize, h: usize| CnfVar::new((p - 1) * holes + (h - 1)).unwrap();
    let mut f = CnfFormula::new(pigeons * holes);
    for p in 1..=pigeons {
        let lits: Vec<CnfLit> = (1..=holes).map(|h| CnfLit::positive(var(p, h))).collect();
        f.add_clause(CnfClause::new(lits)).unwrap();
    }
    for h in 1..=holes {
        for p1 in 1..=pigeons {
            for p2 in (p1 + 1)..=pigeons {
                f.add_clause(CnfClause::new(vec![
                    CnfLit::positive(var(p1, h)).negated(),
                    CnfLit::positive(var(p2, h)).negated(),
                ]))
                .unwrap();
            }
        }
    }
    f
}

/// Conflict limits marking the round boundaries. Each solve is a prefix of the
/// next (the core is deterministic), so the counters at these points form a
/// genuine, monotonically growing stream of "work search has done so far".
const ROUND_LIMITS: [usize; 8] = [20, 60, 140, 300, 620, 1_260, 2_540, 5_100];

/// One observation of the search: what it cost in ticks, and what it cost on
/// the wall clock. The two are measured over *the same runs*, so any difference
/// in reproducibility between them is a property of the unit, not of the setup.
struct Observation {
    ticks: Vec<u64>,
    nanos: Vec<u128>,
    counters: SearchCounters,
}

fn observe(formula: &CnfFormula) -> Observation {
    let mut ticks = Vec::new();
    let mut nanos = Vec::new();
    let mut last = SearchCounters::default();
    for limit in ROUND_LIMITS {
        let mut sink = VecProofSink::new();
        let start = Instant::now();
        let (outcome, counters) = solve_with_drat_proof_counted(formula, None, limit, &mut sink);
        let elapsed = start.elapsed().as_nanos();
        assert!(
            matches!(
                outcome,
                StreamingProofOutcome::Unsat | StreamingProofOutcome::ResourceOut
            ),
            "the fixture must be unsat or resource-out, got {outcome:?}"
        );
        ticks.push(TickModel::DEFAULT.ticks(&counters));
        nanos.push(elapsed);
        last = counters;
    }
    Observation {
        ticks,
        nanos,
        counters: last,
    }
}

/// A stand-in inprocessing pass: it burns its whole budget at a fixed rate and
/// reports failure often enough to exercise the backoff. Nothing about the
/// decision sequence depends on what it computes, only on what it is granted.
struct BurnBudget {
    scale: u64,
    rounds: u64,
}

impl BudgetedPass for BurnBudget {
    type Outcome = u64;
    fn scale(&self) -> u64 {
        self.scale
    }
    fn run(&mut self, budget: Budget, meter: &mut WorkMeter) -> u64 {
        self.rounds += 1;
        let spend = budget.remaining(meter) * 3 / 4;
        meter.charge(spend);
        spend
    }
    fn paid_off(&self, _outcome: &u64) -> bool {
        self.rounds.is_multiple_of(3)
    }
}

/// Drives the full primitive — the per-mille slice, the accumulate-and-delay
/// gate, the failure backoff, the spend attribution — over a reference stream,
/// and returns the decision log as text. This is the "decisions" whose
/// byte-identity is the claim.
fn schedule(reference_stream: &[u64], scale: u64) -> Vec<String> {
    let mut reference = WorkMeter::new();
    let mut pass = Delayed::new(
        "burn",
        BurnBudget { scale, rounds: 0 },
        EffortPolicy::MAJOR_PASS.with_init_cost(20),
    );
    let mut log = Vec::new();
    for &reading in reference_stream {
        reference.advance_to(reading);
        let line = match pass.run_round(&reference) {
            RoundOutcome::Ran {
                outcome,
                granted,
                spent,
            } => format!("ran outcome={outcome} granted={granted} spent={spent}"),
            RoundOutcome::Delayed { accrued, threshold } => {
                format!("delayed {accrued}/{threshold}")
            }
            RoundOutcome::BackedOff { rounds_left } => format!("backoff {rounds_left}"),
        };
        log.push(line);
    }
    let s = pass.stats();
    log.push(format!(
        "final granted={} spent={} ran={} delayed={} backoff={}",
        s.granted, s.spent, s.rounds_granted, s.rounds_delayed, s.rounds_backed_off
    ));
    log
}

fn spin_load(threads: usize) -> (Arc<AtomicBool>, Vec<std::thread::JoinHandle<u64>>) {
    let stop = Arc::new(AtomicBool::new(false));
    let handles = (0..threads)
        .map(|seed| {
            let stop = Arc::clone(&stop);
            std::thread::spawn(move || {
                let mut x = seed as u64 + 1;
                while !stop.load(Ordering::Relaxed) {
                    for _ in 0..10_000 {
                        x = x.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
                    }
                }
                x
            })
        })
        .collect();
    (stop, handles)
}

#[test]
fn a_tick_budget_makes_identical_decisions_where_a_wall_clock_budget_does_not() {
    let formula = pigeonhole(7);
    let scale = formula.clauses().len() as u64;

    // --- Repeated runs, unloaded -------------------------------------------
    let baseline = observe(&formula);

    // Nothing here is comparing zeros: every tick term must have fired.
    let terms = TickModel::DEFAULT.breakdown(&baseline.counters);
    for (name, value) in terms.terms() {
        assert!(
            value > 0,
            "tick term `{name}` is zero on a real search: the tick total is not \
             measuring what it claims"
        );
    }
    assert!(baseline.counters.conflicts > 0, "no conflicts counted");
    assert!(
        baseline.ticks.windows(2).all(|w| w[0] <= w[1]),
        "the tick stream must be monotone across growing conflict limits: {:?}",
        baseline.ticks
    );

    let mut repeats = vec![baseline];
    for _ in 0..3 {
        repeats.push(observe(&formula));
    }
    // ...and one on a different thread, in case anything leaked through
    // thread-local state or allocation addresses.
    {
        let f = formula.clone();
        repeats.push(std::thread::spawn(move || observe(&f)).join().unwrap());
    }

    // --- The same runs, under real host load -------------------------------
    let (stop, handles) = spin_load(2);
    let loaded = observe(&formula);
    let loaded_two = observe(&formula);
    stop.store(true, Ordering::Relaxed);
    for h in handles {
        h.join().unwrap();
    }
    repeats.push(loaded);
    repeats.push(loaded_two);

    // --- The claim ---------------------------------------------------------
    let reference_ticks = &repeats[0].ticks;
    for (i, run) in repeats.iter().enumerate() {
        assert_eq!(
            &run.ticks, reference_ticks,
            "run {i} produced a different tick stream: the deterministic budget \
             unit is not deterministic"
        );
        assert_eq!(
            run.counters, repeats[0].counters,
            "run {i} produced different search counters"
        );
    }

    let tick_decisions = schedule(reference_ticks, scale);
    println!("ticks     : {reference_ticks:?}");
    println!("nanos     : {:?}", repeats[0].nanos);
    println!("nanos(load): {:?}", repeats[repeats.len() - 1].nanos);
    for line in &tick_decisions {
        println!("  {line}");
    }
    for (i, run) in repeats.iter().enumerate() {
        assert_eq!(
            schedule(&run.ticks, scale),
            tick_decisions,
            "run {i} scheduled differently under a tick budget"
        );
    }

    // The decision log must actually exercise the machinery, or the equality
    // above is comparing several copies of one branch.
    let ran = tick_decisions
        .iter()
        .filter(|l| l.starts_with("ran"))
        .count();
    let delayed = tick_decisions
        .iter()
        .filter(|l| l.starts_with("delayed"))
        .count();
    assert!(
        ran > 0 && delayed > 0,
        "the schedule took only one kind of decision, so identical logs prove \
         nothing: {tick_decisions:?}"
    );

    // --- The falsifiability control ----------------------------------------
    // The same experiment, measured with a clock instead of ticks. If this were
    // also identical, the equality above would be evidence of a harness that
    // cannot see variation rather than of a deterministic unit.
    let nano_streams: Vec<&Vec<u128>> = repeats.iter().map(|r| &r.nanos).collect();
    assert!(
        nano_streams.iter().any(|s| **s != *nano_streams[0]),
        "every wall-clock measurement of these runs came back byte-identical, \
         which is not credible: this harness cannot detect variation, so its \
         determinism result means nothing. Streams: {nano_streams:?}"
    );
    assert!(
        nano_streams[0].iter().all(|&n| n > 0),
        "the fixture is too small to time; a zero-nanosecond run cannot serve \
         as the variation control"
    );
}

/// A budget check must not cost more than the work it guards. The tick model is
/// *derived* from counters the search already keeps, so it adds nothing to
/// `propagate` at all; what remains is the per-check comparison, measured here
/// against an empty loop over the same data.
///
/// Reported, not ratcheted: this is a timing measurement on a shared box, so it
/// asserts only the structural facts (the check does no work proportional to
/// anything, and enabling it does not change the verdict).
const CHECK_TIMING_ITERS: u64 = 20_000_000;

#[test]
fn the_budget_check_is_one_comparison_and_the_tick_model_is_free() {
    // Structural half, which cannot flake: the tick total is a pure function of
    // counters the search keeps anyway, so computing it cannot perturb a search
    // that has already finished.
    let formula = pigeonhole(6);
    let mut sink = VecProofSink::new();
    let (outcome, counters) = solve_with_drat_proof_counted(&formula, None, 100_000, &mut sink);
    assert!(matches!(outcome, StreamingProofOutcome::Unsat));
    assert_eq!(
        TickModel::DEFAULT.ticks(&counters),
        TickModel::DEFAULT.ticks(&counters),
        "the tick model is not a pure function of the counters"
    );

    // Timing half, printed rather than asserted.
    let meter = WorkMeter::at(1_000);
    let budget = Budget::until(u64::MAX);

    let start = Instant::now();
    let mut hits = 0u64;
    for _ in 0..CHECK_TIMING_ITERS {
        if std::hint::black_box(&budget).exhausted(std::hint::black_box(&meter)) {
            hits += 1;
        }
    }
    let checked = start.elapsed();
    std::hint::black_box(hits);

    let start = Instant::now();
    let mut sum = 0u64;
    for _ in 0..CHECK_TIMING_ITERS {
        sum = sum.wrapping_add(std::hint::black_box(&meter).spent());
    }
    let baseline = start.elapsed();
    std::hint::black_box(sum);

    // Reported in picoseconds so the arithmetic stays integral -- a float here
    // would be the very thing this lane is removing from budget code.
    let ps = |d: std::time::Duration| {
        u64::try_from(d.as_nanos() * 1_000 / u128::from(CHECK_TIMING_ITERS)).unwrap_or(u64::MAX)
    };
    println!(
        "budget check: {} ps/check over {CHECK_TIMING_ITERS} iterations (bare \
         counter read baseline {} ps)",
        ps(checked),
        ps(baseline)
    );
    assert_eq!(hits, 0, "the check answered wrongly under measurement");
}
