//! The tick valve, end to end through the shipping inprocessing schedule.
//!
//! # The claim, and how each half is kept honest
//!
//! **A pass schedule denominated in ticks makes the same decisions on the same
//! input however long the run takes; one denominated in wall time does not.**
//!
//! The easy half is easy to fake. "Two schedules are equal" passes with the
//! counters stuck at zero, with the valve never consulted, and with a schedule
//! that only ever makes one decision. So every equality here is paired:
//!
//! * The tick schedule is asserted **identical** across two arms whose wall
//!   time differs materially; the **wall-clock** schedule over the *same two
//!   arms* is asserted **not** identical. That second assertion is the
//!   falsifiability control — it is this file's own answer to "denominate the
//!   valve in wall time instead and show the test failing", run on every
//!   build rather than once by hand.
//! * The schedule is asserted to contain more than one kind of decision, so
//!   identical logs are not several copies of one branch.
//! * The refusal rule is asserted against a control arm that admits the same
//!   round, so "refused" is distinguishable from "this fixture cannot run".
//! * The backoff's skip runs are asserted as the actual gaps between admitted
//!   rounds — 0, 2, 5, 10 — not as "a backoff happened".
//!
//! # What must survive
//!
//! A valve changes WHEN a pass runs, which changes the reduced formula, which
//! changes the proof. The property ADR-1780 bought — an inprocessed `unsat`
//! checks against the **original** formula through `ReductionLink` — is
//! asserted here under a valve, with the same three vacuity guards the
//! unvalved test carries.

use std::time::Instant;

use axeyum_cnf::inprocess::{InprocessSchedule, TickValve, inprocess_scheduled};
use axeyum_cnf::ticks::{TickEffort, TickGrant, TickModel, TickValveAccount};
use axeyum_cnf::{
    CnfClause, CnfFormula, CnfLit, CnfVar, InprocessObserver, OccurrencePass, ProofSolveOutcome,
    RecordingObserver, SatResult, StreamingProofOutcome, VecProofSink, solve_with_drat_proof,
    solve_with_drat_proof_counted, solve_with_native_core,
};

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

fn v(i: usize) -> CnfVar {
    CnfVar::new(i).expect("var")
}
fn p(i: usize) -> CnfLit {
    CnfLit::positive(v(i))
}
fn n(i: usize) -> CnfLit {
    CnfLit::positive(v(i)).negated()
}

/// Pigeonhole `pigeons` into `pigeons - 1` holes: unsat, and it drives every
/// tick term nonzero.
fn pigeonhole(pigeons: usize) -> CnfFormula {
    let holes = pigeons - 1;
    let var = |pigeon: usize, hole: usize| (pigeon - 1) * holes + (hole - 1);
    let mut f = CnfFormula::new(pigeons * holes);
    for pigeon in 1..=pigeons {
        let lits: Vec<CnfLit> = (1..=holes).map(|h| p(var(pigeon, h))).collect();
        f.add_clause(CnfClause::new(lits)).expect("in range");
    }
    for hole in 1..=holes {
        for a in 1..=pigeons {
            for b in (a + 1)..=pigeons {
                f.add_clause(CnfClause::new(vec![n(var(a, hole)), n(var(b, hole))]))
                    .expect("in range");
            }
        }
    }
    f
}

/// A formula subsumption really reduces: every clause has a strict superset
/// sitting beside it, so the pass has work and the work is visible in the
/// clause count.
fn subsumable(pairs: usize) -> CnfFormula {
    let mut f = CnfFormula::new(pairs + 2);
    for i in 0..pairs {
        f.add_clause(CnfClause::new(vec![p(i), p(pairs)]))
            .expect("in range");
        f.add_clause(CnfClause::new(vec![p(i), p(pairs), p(pairs + 1)]))
            .expect("in range");
    }
    f
}

/// A formula subsumption finds **nothing** in: an all-positive chain, so no
/// clause subsumes another, no pair resolves, and no clause is a tautology.
/// The backoff needs a fixture that genuinely fails, not one that is merely
/// budgeted out.
fn irreducible_chain(links: usize) -> CnfFormula {
    let mut f = CnfFormula::new(links + 1);
    for i in 0..links {
        f.add_clause(CnfClause::new(vec![p(i), p(i + 1)]))
            .expect("in range");
    }
    f
}

/// The shipping schedule, with the certificate recorded.
fn recording_schedule() -> InprocessSchedule {
    InprocessSchedule {
        xor_propagate: true,
        xor_propagate_max_clauses: 20_000,
        vivify: true,
        vivify_step_guard: true,
        recording: true,
        ..InprocessSchedule::OFF
    }
}

// ---------------------------------------------------------------------------
// Observers used to make wall time differ without changing anything else
// ---------------------------------------------------------------------------

/// Wraps an observer and burns CPU on every counter it records.
///
/// It changes nothing a decision can see — not a grant, not a counter value,
/// not the formula — only how long the round takes. That is exactly the axis a
/// deterministic schedule must be blind to, so it is the axis the two arms
/// differ on.
struct Slow<O> {
    inner: O,
    spins: u64,
    burned: u64,
}

impl<O> Slow<O> {
    fn new(inner: O, spins: u64) -> Self {
        Self {
            inner,
            spins,
            burned: 0,
        }
    }
}

impl<O: InprocessObserver> InprocessObserver for Slow<O> {
    fn grant(&mut self, pass: OccurrencePass, formula: &CnfFormula) -> Option<u64> {
        self.inner.grant(pass, formula)
    }
    fn count(&mut self, name: &str, value: f64) {
        let mut x = self.burned | 1;
        for _ in 0..self.spins {
            x = x
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
        }
        self.burned = x;
        self.inner.count(name, value);
    }
}

/// Grants a fixed step budget to `Subsume` and declines `Bve`, so a test about
/// subsumption's admission is not also a test of elimination's.
#[derive(Default)]
struct SubsumeOnly {
    counts: Vec<(String, f64)>,
}

impl InprocessObserver for SubsumeOnly {
    fn grant(&mut self, pass: OccurrencePass, _formula: &CnfFormula) -> Option<u64> {
        match pass {
            OccurrencePass::Subsume => Some(u64::MAX),
            OccurrencePass::Bve => None,
        }
    }
    fn count(&mut self, name: &str, value: f64) {
        self.counts.push((name.to_owned(), value));
    }
}

// ---------------------------------------------------------------------------
// The reference stream: a real search's ticks, and the same runs' wall times
// ---------------------------------------------------------------------------

/// Conflict limits marking round boundaries. Each solve is a prefix of the next
/// (the core is deterministic), so the readings form a genuine growing stream
/// of "work the search has done so far".
const ROUND_LIMITS: [usize; 8] = [20, 60, 140, 300, 620, 1_260, 2_540, 5_100];

/// One run of the whole experiment: the search's tick stream, the same runs'
/// wall-clock stream, and the valve's decision log.
struct Run {
    ticks: Vec<u64>,
    nanos: Vec<u128>,
    schedule: Vec<String>,
    reduced_clauses: Vec<usize>,
    subsume_rounds: (u64, u64, u64),
}

/// The gate the experiment runs under.
///
/// `threshold_per_clause: 50` over the 204-clause fixture puts the bar at
/// 10 200 ticks of allowance, i.e. an accrued window of 102 000 ticks. The
/// fixture's stream is `[823, 3139, 8899, 27354, 91393, 335810, 1205391,
/// 2415902]`, so the first five rounds are refused and the last three are not —
/// which is what makes the byte-identity below a statement about a schedule
/// rather than about one branch. The test asserts both kinds are present, so
/// this paragraph cannot rot into a comfortable fiction.
///
/// `bootstrap_reference: 0` because the experiment always has a real search
/// behind it; the pre-search bootstrap is a different case and has its own
/// unit test.
const EXPERIMENT_EFFORT: TickEffort = TickEffort {
    threshold_per_clause: 50,
    bootstrap_reference: 0,
    ..TickEffort::MAJOR_PASS
};

/// Runs `ROUND_LIMITS.len()` inprocessing rounds, each preceded by a search
/// whose tick reading advances the valve's numeraire. `spins` inflates the wall
/// time of each round without touching anything a decision reads.
///
/// Only the inprocessing round is timed, not the search in front of it: the
/// decision under test is the round's, and folding the search's cost into the
/// measurement would dilute exactly the difference the two arms exist to
/// create.
fn run_rounds(formula: &CnfFormula, spins: u64) -> Run {
    let mut valve = TickValve::new(
        Slow::new(RecordingObserver::granting(u64::MAX), spins),
        EXPERIMENT_EFFORT,
        EXPERIMENT_EFFORT,
    );

    let mut ticks = Vec::new();
    let mut nanos = Vec::new();
    let mut reduced_clauses = Vec::new();
    for limit in ROUND_LIMITS {
        let mut sink = VecProofSink::new();
        let (outcome, counters) = solve_with_drat_proof_counted(formula, None, limit, &mut sink);
        assert!(
            matches!(
                outcome,
                StreamingProofOutcome::Unsat | StreamingProofOutcome::ResourceOut
            ),
            "the fixture must be unsat or resource-out, got {outcome:?}"
        );
        let reading = TickModel::DEFAULT.ticks(&counters);
        valve.advance_search_ticks(reading);
        let start = Instant::now();
        let out = valve.round(|v| inprocess_scheduled(formula, recording_schedule(), None, v));
        nanos.push(start.elapsed().as_nanos());
        ticks.push(reading);
        reduced_clauses.push(out.formula.clauses().len());
    }

    Run {
        ticks,
        nanos,
        schedule: valve.schedule_log(),
        reduced_clauses,
        subsume_rounds: valve.subsume_account().rounds(),
    }
}

/// The same gate, the same policy, the same log shape — with a **wall-clock**
/// reference in place of the tick one.
///
/// This is the negative control, and it is deliberately symmetric: the tick log
/// and this one are compared the same way (whole lines, decision inputs
/// included), so any difference in reproducibility between them is a property
/// of the unit and not of how each was measured.
fn wall_clock_schedule(nanos: &[u128], clauses: u64) -> Vec<String> {
    let mut account = TickValveAccount::new(EXPERIMENT_EFFORT);
    let mut cumulative = 0u64;
    let mut log = Vec::new();
    for &ns in nanos {
        cumulative = cumulative.saturating_add(u64::try_from(ns).unwrap_or(u64::MAX));
        let grant = account.request(cumulative, clauses);
        let detail = match grant {
            TickGrant::Granted {
                allowance,
                reference,
            } => format!("allowance={allowance} reference={reference}"),
            TickGrant::Refused { accrued, threshold } => {
                format!("accrued={accrued} threshold={threshold}")
            }
            TickGrant::BackedOff { rounds_left } => format!("rounds_left={rounds_left}"),
        };
        log.push(format!(
            "wall {} nanos={cumulative} clauses={clauses} {detail}",
            grant.tag()
        ));
    }
    log
}

// ---------------------------------------------------------------------------
// The exit criterion
// ---------------------------------------------------------------------------

/// The headline: two runs whose wall time differs materially schedule
/// identically under a tick valve, and do not under a wall-clock one.
#[test]
fn the_tick_schedule_is_identical_across_runs_of_materially_different_duration() {
    let formula = pigeonhole(8);
    let clauses = formula.clauses().len() as u64;
    assert_eq!(
        clauses, 204,
        "EXPERIMENT_EFFORT's threshold is stated in terms of this clause count"
    );

    let fast = run_rounds(&formula, 0);
    let slow = run_rounds(&formula, 200_000);
    let fast_again = run_rounds(&formula, 0);

    let fast_total: u128 = fast.nanos.iter().sum();
    let slow_total: u128 = slow.nanos.iter().sum();
    println!("fast ns  : {fast_total} ({:?})", fast.nanos);
    println!("slow ns  : {slow_total} ({:?})", slow.nanos);
    println!("ticks    : {:?}", fast.ticks);
    for line in &fast.schedule {
        println!("  {line}");
    }

    // The arms must actually differ in duration, or "identical under different
    // wall times" is a statement about one wall time.
    assert!(
        slow_total > fast_total * 2,
        "the slow arm must be materially slower or this experiment has no \
         second condition: fast {fast_total} ns, slow {slow_total} ns"
    );

    // Nothing here is comparing zeros.
    assert!(
        fast.ticks.iter().all(|&t| t > 0),
        "a zero tick reading means the counters never filled: {:?}",
        fast.ticks
    );
    assert!(
        fast.ticks.windows(2).all(|w| w[0] <= w[1]),
        "the tick stream must be monotone: {:?}",
        fast.ticks
    );

    // The claim.
    assert_eq!(
        fast.ticks, slow.ticks,
        "the tick stream itself moved with wall time"
    );
    assert_eq!(
        fast.schedule, slow.schedule,
        "the pass schedule moved with wall time: the valve is not deterministic"
    );
    assert_eq!(
        fast.schedule, fast_again.schedule,
        "the pass schedule is not even reproducible run to run"
    );
    assert_eq!(
        fast.reduced_clauses, slow.reduced_clauses,
        "the reduced formula moved with wall time, so the certificate would too"
    );

    // ...and the schedule really took more than one kind of decision, or the
    // equality above is several copies of one branch.
    let granted = fast
        .schedule
        .iter()
        .filter(|l| l.contains(" granted "))
        .count();
    let refused = fast
        .schedule
        .iter()
        .filter(|l| l.contains(" refused "))
        .count();
    assert!(
        granted > 0 && refused > 0,
        "the schedule took only one kind of decision, so identical logs prove \
         nothing: {:?}",
        fast.schedule
    );
    assert_eq!(
        fast.subsume_rounds.0 + fast.subsume_rounds.1 + fast.subsume_rounds.2,
        ROUND_LIMITS.len() as u64,
        "every round must have reached the valve"
    );

    // --- The falsifiability control ----------------------------------------
    // The same gate over the same runs, denominated in wall time. If this also
    // came back identical, the equality above would be evidence of a harness
    // that cannot see variation rather than of a deterministic unit.
    let wall_fast = wall_clock_schedule(&fast.nanos, clauses);
    let wall_slow = wall_clock_schedule(&slow.nanos, clauses);
    let wall_fast_again = wall_clock_schedule(&fast_again.nanos, clauses);
    for line in &wall_fast {
        println!("  {line}");
    }
    for line in &wall_slow {
        println!("  {line}");
    }
    assert_eq!(
        wall_fast.len(),
        fast.ticks.len(),
        "the control must produce one decision per round, like the tick log, \
         or the two are not being compared the same way"
    );
    assert!(
        wall_fast != wall_slow && wall_fast != wall_fast_again,
        "every wall-clock schedule over these runs came back identical, which \
         is not credible: this harness cannot detect variation, so its \
         determinism result means nothing.\n  fast: {wall_fast:?}\n  slow: \
         {wall_slow:?}\n  again: {wall_fast_again:?}"
    );
    assert!(
        fast.nanos.iter().all(|&ns| ns > 0),
        "a zero-nanosecond round cannot serve as the variation control"
    );
}

// ---------------------------------------------------------------------------
// The refusal rule
// ---------------------------------------------------------------------------

/// A refused pass does not run **at all**, and the control arm shows the same
/// round running.
///
/// The discriminator is `subsume_work_spent`. A pass that ran with a budget of
/// zero would still have normalized every clause and built the first round's
/// occurrence lists, so its meter would read the setup cost; a pass that was
/// never entered reports the `SubsumeStats::default()` zero. That is the
/// difference the refusal exists to buy, and it is the only observable that
/// distinguishes the two.
#[test]
fn a_refused_pass_does_not_run_and_the_control_arm_shows_it_would_have() {
    let f = subsumable(300);
    let clauses_before = f.clauses().len();

    // Gated: 40 000 accrued ticks buys 4 000, and the bar is 20 x 600 = 12 000.
    let gated_effort = TickEffort {
        threshold_per_clause: 20,
        bootstrap_reference: 0,
        ..TickEffort::MAJOR_PASS
    };
    let mut gated = TickValve::new(
        RecordingObserver::granting(u64::MAX),
        gated_effort,
        gated_effort,
    );
    gated.advance_search_ticks(40_000);
    let refused = gated.round(|v| inprocess_scheduled(&f, recording_schedule(), None, v));

    assert!(
        matches!(
            gated.decisions()[0].grant,
            TickGrant::Refused {
                accrued: 4_000,
                threshold: 12_000
            }
        ),
        "expected a refusal with numbers derivable by hand, got {:?}",
        gated.decisions()
    );
    assert_eq!(
        gated.inner().get("subsume_work_spent"),
        Some(0.0),
        "a refused pass must not have paid its occurrence-list setup"
    );
    assert_eq!(
        gated.inner().get("subsume_tick_admitted"),
        Some(0.0),
        "the valve must record its own refusal"
    );
    assert_eq!(
        refused.formula.clauses().len(),
        clauses_before,
        "a refused round must leave the formula alone"
    );

    // The control: the same formula, the same tick reading, the gate off.
    let mut ungated = TickValve::new(
        RecordingObserver::granting(u64::MAX),
        TickEffort::UNGATED,
        TickEffort::UNGATED,
    );
    ungated.advance_search_ticks(40_000);
    let admitted = ungated.round(|v| inprocess_scheduled(&f, recording_schedule(), None, v));

    assert!(
        matches!(ungated.decisions()[0].grant, TickGrant::Granted { .. }),
        "the control arm must admit: {:?}",
        ungated.decisions()
    );
    assert!(
        ungated.inner().get("subsume_work_spent").unwrap_or(0.0) > 0.0,
        "the control arm's pass must actually have run"
    );
    assert!(
        admitted.formula.clauses().len() < clauses_before,
        "the control arm must reduce the formula ({} -> {}), or 'refused' is \
         indistinguishable from 'nothing to do'",
        clauses_before,
        admitted.formula.clauses().len()
    );
}

// ---------------------------------------------------------------------------
// The backoff
// ---------------------------------------------------------------------------

/// A pass that keeps finding nothing is offered exponentially less often, and
/// the gaps are asserted as the actual admitted-round indices.
///
/// The fixture is irreducible for subsumption, so the pass genuinely fails
/// rather than being budgeted out; the effort has `threshold_per_clause: 0`, so
/// the only gate in play is the one under test.
#[test]
fn an_unproductive_pass_is_offered_exponentially_less_often() {
    let f = irreducible_chain(64);
    let effort = TickEffort {
        max_backoff_rounds: 32,
        ..TickEffort::UNGATED
    };
    let mut valve = TickValve::new(SubsumeOnly::default(), effort, effort);
    valve.advance_search_ticks(10_000_000);

    let mut admitted = Vec::new();
    for round in 0..12 {
        valve.round(|v| inprocess_scheduled(&f, InprocessSchedule::OFF, None, v));
        let last = valve
            .decisions()
            .iter()
            .rev()
            .find(|d| d.pass == OccurrencePass::Subsume)
            .copied()
            .expect("subsumption is offered every round");
        if matches!(last.grant, TickGrant::Granted { .. }) {
            admitted.push(round);
        }
    }

    assert_eq!(
        admitted,
        vec![0, 2, 5, 10],
        "the gaps between admitted rounds must double (0, then 1, then 2, then \
         4 skipped): {:?}",
        valve.schedule_log()
    );

    // The control: the same fixture with the backoff disabled is admitted every
    // round, so the pattern above is the backoff and not the fixture.
    let mut always = TickValve::new(
        SubsumeOnly::default(),
        TickEffort::UNGATED,
        TickEffort::UNGATED,
    );
    always.advance_search_ticks(10_000_000);
    for _ in 0..12 {
        always.round(|v| inprocess_scheduled(&f, InprocessSchedule::OFF, None, v));
    }
    assert_eq!(
        always.subsume_account().rounds(),
        (12, 0, 0),
        "with the backoff off, every round must be admitted"
    );

    // ...and the fixture really is one subsumption finds nothing in, or the
    // backoff above fired for the wrong reason.
    assert_eq!(
        always
            .inner()
            .counts
            .iter()
            .filter(|(k, val)| k == "subsume_clauses_subsumed" && *val > 0.0)
            .count(),
        0,
        "the fixture must be irreducible for subsumption"
    );
}

// ---------------------------------------------------------------------------
// What must survive: the certificate and the verdict
// ---------------------------------------------------------------------------

/// ADR-1780's property under a valve: a refutation of the formula the search
/// ran over lifts, through the link, into a refutation of the formula the
/// CALLER handed in.
///
/// The three vacuity guards are the unvalved test's: a reduction that changed
/// nothing makes "covers the original" true and meaningless, a prefix that
/// refuted on its own means the search contributed nothing, and a compaction
/// that renumbered nothing leaves the lift untested.
#[test]
fn a_valved_unsat_still_certifies_against_the_original_formula() {
    let f = pigeonhole(4);
    let mut valve = TickValve::new(
        RecordingObserver::granting(u64::MAX),
        TickEffort::UNGATED,
        TickEffort::UNGATED,
    );
    valve.advance_search_ticks(5_000_000);
    let out = valve.round(|v| inprocess_scheduled(&f, recording_schedule(), None, v));

    assert!(
        matches!(valve.decisions()[0].grant, TickGrant::Granted { .. }),
        "the valve must have admitted, or this tests the unvalved path"
    );
    assert!(
        out.link.prefix_len() > 0,
        "the passes must have derived something"
    );
    assert!(
        out.link.has_renaming(),
        "compaction must renumber, or the lift is untested"
    );
    assert!(out.link.is_checkable(), "the link must stay usable");

    let ProofSolveOutcome::Unsat(search_proof) = solve_with_drat_proof(&out.formula) else {
        panic!("the reduced formula must still be unsatisfiable");
    };
    assert!(
        !search_proof.is_empty(),
        "the search must contribute steps, or the prefix refuted alone"
    );

    let check = out
        .link
        .check_unsat(&f, &out.formula, &search_proof, usize::MAX);
    assert!(
        check.verified,
        "the concatenation must verify: {:?}",
        check.error
    );
    assert!(
        check.coverage.is_original(),
        "and it must cover the ORIGINAL formula: {:?}",
        check.coverage
    );
}

/// The valve is a scheduling change, not a semantics change: no verdict moves,
/// and a `sat` model still replays against the caller's formula.
#[test]
fn the_valve_never_moves_a_verdict() {
    let corpus: Vec<(&str, CnfFormula)> = vec![
        ("pigeonhole-4", pigeonhole(4)),
        ("pigeonhole-5", pigeonhole(5)),
        ("subsumable", subsumable(40)),
        ("chain", irreducible_chain(32)),
    ];

    // Three arms: no valve, an admitting valve, and a refusing one. All three
    // must agree, because admission is about cost and never about truth.
    let arms: Vec<(&str, Option<TickEffort>)> = vec![
        ("unvalved", None),
        ("admitting", Some(TickEffort::UNGATED)),
        (
            "refusing",
            Some(TickEffort {
                threshold_per_clause: u64::MAX,
                bootstrap_reference: 0,
                ..TickEffort::MAJOR_PASS
            }),
        ),
    ];

    for (name, f) in &corpus {
        let baseline = verdict(f, None);
        for (arm, effort) in &arms {
            let got = verdict(f, *effort);
            assert_eq!(
                got, baseline,
                "{name} under `{arm}`: the valve moved a verdict"
            );
        }
    }
}

/// Solves `f` through the schedule under an optional valve, checking a `sat`
/// model against the ORIGINAL formula on the way out.
fn verdict(f: &CnfFormula, effort: Option<TickEffort>) -> &'static str {
    let mut plain = RecordingObserver::granting(u64::MAX);
    let out = match effort {
        None => inprocess_scheduled(f, recording_schedule(), None, &mut plain),
        Some(e) => {
            let mut valve = TickValve::new(RecordingObserver::granting(u64::MAX), e, e);
            valve.advance_search_ticks(5_000_000);
            valve.round(|v| inprocess_scheduled(f, recording_schedule(), None, v))
        }
    };
    match solve_with_native_core(&out.formula).expect("the core reports a valid result") {
        SatResult::Sat(model) => {
            let reduced = out.compaction.expand(model.values());
            let lifted = out.reconstruction.extend(&reduced);
            assert_eq!(
                f.evaluate(&lifted),
                Ok(true),
                "a `sat` model must replay against the ORIGINAL formula"
            );
            "sat"
        }
        SatResult::Unsat(_) => "unsat",
        // Not folded into the `unsat` arm: an `unknown` compared equal against
        // an `unknown` would let both sides of this test degrade together and
        // still agree, which is the vacuity trap a verdict comparison is most
        // exposed to.
        SatResult::Unknown(reason) => panic!("the fixtures must all decide: {reason:?}"),
    }
}
