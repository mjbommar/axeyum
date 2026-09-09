//! Fused portfolio groups: a contiguous run of ladder positions whose arms are
//! raced rather than queued.
//!
//! # What this is for, measured
//!
//! The ladder is a sequence, and every route's budget is a *reservation* out of
//! one wall clock. That is zero-sum: every second guaranteed to the routes below
//! is a second the leading route does not get. It works whenever the winner is
//! cheap. It cannot work when **two routes each need most of one clock** — no
//! split of 24 s serves two routes that each want 15-18 s, and two cores serve
//! both trivially.
//!
//! That band is not hypothetical here. On the committed loss population
//! (`bench-results/portfolio-oracle-20260908/solo/`) four files are decided by
//! one route alone, at the competition budget, in 8.5-17.3 s, while the ladder
//! spends the same clock in a route that decides nothing:
//!
//! | file | ladder spends | the arm that decides alone |
//! |---|---|---|
//! | `QF_LIA/…/182-incremental_scheduling-17280-0` | `lia-dpll` 23,993 ms | `qf-bv` 8,693 ms |
//! | `QF_IDL/…/queen42-1` | `dl-online` 21 s, then `lia-dpll` | `qf-bv` 17,324 ms |
//! | `QF_IDL/…/super_queen61-1` | `dl-online` 21 s, then `lia-dpll` | `qf-bv` 16,068 ms |
//! | `QF_IDL/…/super_queen83-1` | `dl-online` 21 s, then `lia-dpll` | `qf-bv` ~16 s |
//!
//! A sequential reserve cannot collect any of them: on `182-incremental` the
//! whole 24 s is inside `lia-dpll`, and on the `QF_IDL` three the ladder has
//! 2.6 s left when it gives up. The arithmetic is the point of this module.
//!
//! # The composition
//!
//! A **reservation** assigns each ladder position a share of the group's clock.
//! A **fused group** takes a contiguous run of those positions and gives each of
//! its arms the group's *whole* share, run concurrently. The two are the same
//! object at different worker counts:
//!
//! - `workers == 1` — the arms are run in declared order, each taking its
//!   reserved slice of the group's share, with carry-over
//!   ([`axeyum_ir::budget::Budget::split`]). **This is exactly the sequential
//!   reservation**, which is why a one-worker fused group cannot regress the
//!   sequential path: it *is* the sequential path.
//! - `workers > 1` — every arm gets the whole share on its own worker.
//!
//! A single-arm group is the sequential ladder position itself at every worker
//! count, which is the property [`FusedGroup::run`] is tested against.
//!
//! # Determinism
//!
//! Determinism is a public API promise, and a race is not deterministic. The
//! promise this module keeps is precise:
//!
//! - **The verdict is stable.** Every decisive arm result is collected and the
//!   winner is chosen by **declared arm order**, never by finishing order. Two
//!   arms that both decide always yield the earlier-declared arm's verdict,
//!   whichever finished first.
//! - **The attribution may vary.** Which arms *reached* a verdict before the
//!   group stopped them depends on the machine, so a route trail from a
//!   multi-worker group is a record of this run, not a reproducible one. The
//!   trail is emitted in declared order so at least its shape is stable.
//!
//! # Soundness
//!
//! Two arms returning **different** decisive verdicts is a soundness defect in
//! one of them, and this module refuses to pick: it returns
//! [`SolverError::Backend`] naming both arms. That is deliberately louder than
//! an `unknown` — `unknown` is a first-class result for "we did not decide",
//! not a place to hide "two of our routes contradict each other". The check is
//! at **top-level dispatch granularity**: an arm is one whole route invocation
//! on the same query, not a refinement round (79 of 796 files have disagreeing
//! *attempts*, because attempts are rounds over different queries; that is
//! normal and is not what this gate looks at).
//!
//! Stopping a losing arm can only turn its search into `unknown`
//! ([`axeyum_ir::stop`]), so a stop never changes a verdict — it discards work
//! whose answer the group was not going to use.
//!
//! # Memory
//!
//! A competition memory limit is **per solver process**, so N arms share one
//! limit — it is `limit / N` per arm, never `N × limit`. Two things follow, and
//! both are implemented rather than hoped for:
//!
//! - each arm's `SolverConfig::memory_limit_mb` is set to its share, so the
//!   per-arm *encoding* ceilings (`MemoryBudget::clause_ceiling`, the
//!   `encoding_refusal` projections) refuse at a size the arm can actually
//!   afford beside its siblings;
//! - the process-wide sticky watchdog (`crate::memory_budget`) samples the
//!   **process** resident set, so if the arms together exceed the limit it trips
//!   for all of them and every arm declines with a `MemoryLimit` `unknown`. That
//!   is the conservative direction — the group returns `unknown`, never a
//!   verdict — and it is why a group is kept to two or three arms rather than
//!   sized to the core count.

use std::sync::mpsc;
use std::time::{Duration, Instant};

use axeyum_ir::budget::{Budget, WorkMeter};
use axeyum_ir::stop::{StopScope, StopToken};
use axeyum_ir::{TermArena, TermId};

use crate::{CheckResult, SolverConfig, SolverError};

/// The one authority for "should this search stop now?".
///
/// Every `past_deadline` helper in this crate delegates here, so a cooperative
/// stop reaches a route through the sites that already poll its deadline rather
/// than through a new mechanism each route would have to opt into.
#[inline]
#[must_use]
pub(crate) fn stop_or_past_deadline(deadline: Option<Instant>) -> bool {
    axeyum_ir::stop::past_deadline(deadline)
}

std::thread_local! {
    /// How many fused groups this **thread** has run.
    ///
    /// The degeneracy property -- "at one worker the sequential path is the
    /// pre-portfolio path" -- is enforced in `auto.rs` by not constructing a
    /// group at all, and that is a claim about control flow that no verdict
    /// comparison can check: two paths agreeing on every answer is exactly what
    /// a *correct* portfolio also looks like. This counter makes the claim
    /// falsifiable, and
    /// `crates/axeyum-solver/tests/portfolio_fused_group.rs` asserts it does
    /// not move across a batch of integer queries at the default worker count.
    ///
    /// Thread-local, not process-global, and the difference is load-bearing:
    /// the assertion is about the dispatch the test just made, and a test
    /// binary runs its cases in parallel, so a global counter would be moved by
    /// a sibling case racing a group of its own. That is not a hypothetical --
    /// it is what the process-global first version of this counter did, and the
    /// failure looked like a broken degeneracy property rather than a broken
    /// instrument.
    static GROUPS_RUN: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// How many fused groups this thread has run. See [`GROUPS_RUN`].
#[must_use]
pub fn groups_run() -> u64 {
    GROUPS_RUN.with(std::cell::Cell::get)
}

/// One route as a portfolio arm.
///
/// The `run` signature is the shape every ladder route already has, so an arm
/// is a route *reference*, never a reimplementation of one — a portfolio whose
/// arms are second copies of the dispatch logic would drift out of agreement
/// with the ladder it is supposed to be part of.
#[derive(Clone, Copy)]
pub(crate) struct Arm {
    /// The route name, spelled as it appears in the route trail.
    pub(crate) route: &'static str,
    /// Relative slice of the group's share this arm takes **when the group runs
    /// on one worker**. Ignored at higher worker counts, where every arm gets
    /// the whole share.
    pub(crate) weight: u64,
    /// The route entry point.
    pub(crate) run: ArmFn,
}

/// A route entry point usable as a portfolio arm.
pub(crate) type ArmFn =
    fn(&mut TermArena, &[TermId], &SolverConfig) -> Result<CheckResult, SolverError>;

impl std::fmt::Debug for Arm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Arm")
            .field("route", &self.route)
            .field("weight", &self.weight)
            .finish_non_exhaustive()
    }
}

/// What one arm produced, for the caller to record on its own thread.
///
/// The arms run on workers and `Recorder` is neither `Send` nor shareable, so
/// the group returns outcomes and the caller records them **in declared order**.
/// That keeps the emitted trail's order independent of finishing order even
/// though its contents are not.
#[derive(Debug)]
pub(crate) struct ArmOutcome {
    /// The arm's route name.
    pub(crate) route: &'static str,
    /// What the arm returned, or the error it raised.
    pub(crate) result: Result<CheckResult, SolverError>,
    /// Wall time the arm spent. Advisory: under a race this is contended time.
    pub(crate) elapsed: Duration,
    /// Whether the group asked this arm to stop before it finished.
    pub(crate) stopped: bool,
}

impl ArmOutcome {
    /// Whether this arm reached a `sat`/`unsat`.
    fn decisive(&self) -> bool {
        matches!(self.result, Ok(CheckResult::Sat(_) | CheckResult::Unsat))
    }

    /// `"sat"` / `"unsat"` for a decisive arm; used only in the disagreement
    /// message, so it never has to describe an undecided arm.
    fn verdict_name(&self) -> &'static str {
        match self.result {
            Ok(CheckResult::Sat(_)) => "sat",
            Ok(CheckResult::Unsat) => "unsat",
            _ => "undecided",
        }
    }
}

/// The result of running a fused group.
#[derive(Debug)]
pub(crate) struct GroupOutcome {
    /// Every arm that ran, in **declared** order.
    pub(crate) arms: Vec<ArmOutcome>,
    /// Index into [`Self::arms`] of the arm whose verdict the group returns, if
    /// any arm decided.
    pub(crate) winner: Option<usize>,
}

impl GroupOutcome {
    /// The winning arm's route name and verdict, consuming the outcome.
    pub(crate) fn into_decision(mut self) -> Option<(&'static str, CheckResult)> {
        let index = self.winner?;
        let arm = self.arms.swap_remove(index);
        match arm.result {
            Ok(result @ (CheckResult::Sat(_) | CheckResult::Unsat)) => Some((arm.route, result)),
            // `winner` is only ever set to a decisive arm, so this is
            // unreachable through `run`; returning `None` rather than
            // panicking keeps a future caller that builds a `GroupOutcome` by
            // hand from turning a bookkeeping slip into an abort.
            _ => None,
        }
    }
}

/// A contiguous run of ladder positions, raced.
#[derive(Debug, Clone, Copy)]
pub(crate) struct FusedGroup<'a> {
    /// The arms, in priority order. The first arm is the ladder's own next
    /// route, so a one-arm group is that route and nothing else.
    arms: &'a [Arm],
    /// How many arms may run at once. `1` is the sequential reservation.
    workers: usize,
}

impl<'a> FusedGroup<'a> {
    /// A group over `arms` running on `workers` concurrent workers.
    ///
    /// `workers` is clamped to at least one and at most `arms.len()`: spawning
    /// a worker with no arm to run is a way to spend a core on nothing.
    pub(crate) fn new(arms: &'a [Arm], workers: usize) -> Self {
        Self {
            arms,
            workers: workers.clamp(1, arms.len().max(1)),
        }
    }

    /// The number of arms that will actually run at once.
    pub(crate) fn workers(self) -> usize {
        self.workers
    }

    /// Runs the group over `assertions`.
    ///
    /// `config` must already be clamped to the group's share of the wall clock
    /// — the group divides that share among its arms (one worker) or hands each
    /// arm all of it (more than one), and never reaches past it.
    ///
    /// # Errors
    ///
    /// Propagates a [`SolverError`] from the winning arm, and raises
    /// [`SolverError::Backend`] when two arms return **different** decisive
    /// verdicts (see the module docs on soundness).
    pub(crate) fn run(
        self,
        arena: &TermArena,
        assertions: &[TermId],
        config: &SolverConfig,
    ) -> Result<GroupOutcome, SolverError> {
        GROUPS_RUN.with(|runs| runs.set(runs.get().saturating_add(1)));
        if self.arms.is_empty() {
            return Ok(GroupOutcome {
                arms: Vec::new(),
                winner: None,
            });
        }
        let outcomes = if self.workers == 1 {
            self.run_reserved(arena, assertions, config)
        } else {
            self.run_raced(arena, assertions, config)
        };
        let winner = pick_winner(&outcomes)?;
        Ok(GroupOutcome {
            arms: outcomes,
            winner,
        })
    }

    /// One worker: the arms in declared order, each taking its reserved slice of
    /// the group's share, with carry-over. Stops at the first decision.
    ///
    /// This is the sequential reservation, expressed through the shared
    /// [`Budget::split`] primitive rather than another hand-rolled division of a
    /// clock — the tree grew four of those before it grew a name for the shape.
    fn run_reserved(
        self,
        arena: &TermArena,
        assertions: &[TermId],
        config: &SolverConfig,
    ) -> Vec<ArmOutcome> {
        let weight_sum: u64 = self.arms.iter().map(|arm| arm.weight).sum();
        // The meter's unit is nanoseconds of the group's share, so the split's
        // carry-over property lands exactly where it is wanted: an arm that
        // declines early donates the rest of its slice to the next one.
        let share_nanos = config
            .timeout
            .map(|t| u64::try_from(t.as_nanos()).unwrap_or(u64::MAX));
        let started = Instant::now();
        let mut meter = WorkMeter::new();
        let mut split =
            share_nanos.map(|nanos| Budget::until(nanos).split(&meter).weights(weight_sum));

        let mut outcomes = Vec::with_capacity(self.arms.len());
        for arm in self.arms {
            let mut arm_config = config.clone();
            if let Some(split) = split.as_mut() {
                let cumulative = split.take(arm.weight).limit();
                arm_config.timeout = Some(Duration::from_nanos(
                    cumulative.saturating_sub(meter.spent()),
                ));
            }
            let mut scratch = arena.clone();
            let arm_started = Instant::now();
            let result = (arm.run)(&mut scratch, assertions, &arm_config);
            let elapsed = arm_started.elapsed();
            meter.advance_to(u64::try_from(started.elapsed().as_nanos()).unwrap_or(u64::MAX));
            let decided = matches!(result, Ok(CheckResult::Sat(_) | CheckResult::Unsat));
            outcomes.push(ArmOutcome {
                route: arm.route,
                result,
                elapsed,
                stopped: false,
            });
            if decided {
                break;
            }
        }
        outcomes
    }

    /// More than one worker: every arm gets the group's whole share on its own
    /// thread; the first decisive verdict stops the rest.
    fn run_raced(
        self,
        arena: &TermArena,
        assertions: &[TermId],
        config: &SolverConfig,
    ) -> Vec<ArmOutcome> {
        // The CDCL core is in `axeyum-cnf`, which must not depend on the term
        // IR for one `bool`, so it consults an embedder hook instead. Installing
        // it here rather than at crate init keeps a solver that never races
        // exactly as it was: no hook, and the core's check is its deadline.
        static INSTALL_CNF_STOP_HOOK: std::sync::Once = std::sync::Once::new();
        INSTALL_CNF_STOP_HOOK.call_once(|| {
            axeyum_cnf::interrupt::set_stop_hook(axeyum_ir::stop::stop_requested);
        });
        let arm_config = self.arm_config(config);
        let tokens: Vec<StopToken> = self.arms.iter().map(|_| StopToken::new()).collect();
        let mut outcomes: Vec<Option<ArmOutcome>> = (0..self.arms.len()).map(|_| None).collect();

        std::thread::scope(|scope| {
            let (tx, rx) = mpsc::channel::<(usize, ArmOutcome)>();
            let mut handles = Vec::with_capacity(self.arms.len());
            for (index, arm) in self.arms.iter().enumerate() {
                let tx = tx.clone();
                let token = tokens[index].clone();
                let mut scratch = arena.clone();
                let arm_config = arm_config.clone();
                let arm = *arm;
                handles.push(scope.spawn(move || {
                    let _installed = StopScope::install(&token);
                    let started = Instant::now();
                    let result = (arm.run)(&mut scratch, assertions, &arm_config);
                    let outcome = ArmOutcome {
                        route: arm.route,
                        result,
                        elapsed: started.elapsed(),
                        stopped: token.is_requested(),
                    };
                    // A send failure means the coordinator is already gone,
                    // which cannot happen while it holds `rx` across the whole
                    // scope; drop the outcome rather than panicking a worker.
                    drop(tx.send((index, outcome)));
                }));
            }
            // The coordinator's own copy must go, or `rx` never sees a
            // disconnect and a group whose arms all panicked would block here.
            drop(tx);

            let mut remaining = self.arms.len();
            while remaining > 0 {
                let Ok((index, outcome)) = rx.recv() else {
                    break;
                };
                remaining -= 1;
                let decisive = outcome.decisive();
                outcomes[index] = Some(outcome);
                if decisive {
                    // Someone decided. Every other arm's answer is now surplus,
                    // so ask them all to stop; the winner has already returned
                    // and cannot be affected by a request on its own token.
                    for token in &tokens {
                        token.request();
                    }
                }
            }
            // Joining is not optional. An abandoned arm bounds its own *time*
            // (it holds a deadline) but nothing bounds its *memory*, and a
            // detached route that keeps allocating is how this repository once
            // reached 125 GB and OOM-killed the host. The stop request above is
            // what makes the join cheap.
            for handle in handles {
                drop(handle.join());
            }
        });

        outcomes
            .into_iter()
            .zip(self.arms)
            .map(|(outcome, arm)| {
                outcome.unwrap_or_else(|| ArmOutcome {
                    // A worker that panicked never sends; report it as an arm
                    // that produced nothing rather than silently shortening the
                    // group.
                    route: arm.route,
                    result: Ok(CheckResult::Unknown(crate::UnknownReason {
                        kind: crate::UnknownKind::Other,
                        detail: format!("portfolio arm {} produced no outcome", arm.route),
                    })),
                    elapsed: Duration::ZERO,
                    stopped: true,
                })
            })
            .collect()
    }

    /// The config each arm gets in a raced group: the group's whole wall share,
    /// and its **share of one process memory limit**.
    fn arm_config(self, config: &SolverConfig) -> SolverConfig {
        let mut arm_config = config.clone();
        if let Some(limit) = arm_config.memory_limit_mb {
            let arms = u64::try_from(self.arms.len()).unwrap_or(1).max(1);
            arm_config.memory_limit_mb = Some((limit / arms).max(1));
        }
        arm_config
    }
}

/// The declared-order winner among the decisive arms, or a disagreement error.
///
/// Order, not finishing time: that is the whole of this module's verdict
/// determinism promise.
fn pick_winner(outcomes: &[ArmOutcome]) -> Result<Option<usize>, SolverError> {
    let mut winner: Option<usize> = None;
    for (index, outcome) in outcomes.iter().enumerate() {
        if !outcome.decisive() {
            continue;
        }
        let Some(first) = winner else {
            winner = Some(index);
            continue;
        };
        let agree = matches!(
            (&outcomes[first].result, &outcome.result),
            (Ok(CheckResult::Sat(_)), Ok(CheckResult::Sat(_)))
                | (Ok(CheckResult::Unsat), Ok(CheckResult::Unsat))
        );
        if !agree {
            return Err(SolverError::Backend(format!(
                "portfolio arm disagreement on one query: {} returned {} and {} returned {}. \
                 One of these routes is unsound; the group refuses to choose between them.",
                outcomes[first].route,
                outcomes[first].verdict_name(),
                outcome.route,
                outcome.verdict_name(),
            )));
        }
    }
    Ok(winner)
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;

    use axeyum_ir::{TermArena, TermId};

    use super::{Arm, FusedGroup};
    use crate::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};

    const fn is_send<T: Send>() {}

    #[test]
    fn the_types_a_worker_moves_are_send() {
        // A compile-time claim: if either of these stops being `Send` the group
        // cannot run at all, and this test is where that is stated.
        is_send::<TermArena>();
        is_send::<CheckResult>();
        is_send::<SolverConfig>();
    }

    static SEQUENTIAL_CALLS: AtomicUsize = AtomicUsize::new(0);

    fn undecided(detail: &str) -> CheckResult {
        CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Other,
            detail: detail.to_owned(),
        })
    }

    fn declines(
        _: &mut TermArena,
        _: &[TermId],
        _: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        Ok(undecided("declined"))
    }

    fn says_unsat(
        _: &mut TermArena,
        _: &[TermId],
        _: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        Ok(CheckResult::Unsat)
    }

    fn says_sat(
        arena: &mut TermArena,
        _: &[TermId],
        _: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        let _ = arena.bool_const(true);
        Ok(CheckResult::Sat(crate::Model::default()))
    }

    fn counts_then_declines(
        _: &mut TermArena,
        _: &[TermId],
        _: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        SEQUENTIAL_CALLS.fetch_add(1, Ordering::SeqCst);
        Ok(undecided("declined"))
    }

    fn slow_then_unsat(
        _: &mut TermArena,
        _: &[TermId],
        config: &SolverConfig,
    ) -> Result<CheckResult, SolverError> {
        // Polls the same predicate every route polls, so this arm is stopped by
        // exactly the mechanism a real one is.
        let deadline = config.timeout.map(|t| std::time::Instant::now() + t);
        while !super::stop_or_past_deadline(deadline) {
            std::thread::yield_now();
        }
        Ok(undecided("stopped or out of time"))
    }

    fn config_with(timeout_ms: u64) -> SolverConfig {
        SolverConfig {
            timeout: Some(Duration::from_millis(timeout_ms)),
            ..SolverConfig::default()
        }
    }

    #[test]
    fn a_single_arm_group_is_the_route_itself_at_every_worker_count() {
        let arena = TermArena::new();
        let arms = [Arm {
            route: "only",
            weight: 1,
            run: says_unsat,
        }];
        for workers in [1, 2, 8] {
            let group = FusedGroup::new(&arms, workers);
            assert_eq!(
                group.workers(),
                1,
                "a one-arm group must never claim more than one worker"
            );
            let outcome = group
                .run(&arena, &[], &config_with(1_000))
                .expect("group ran");
            let (route, result) = outcome.into_decision().expect("decided");
            assert_eq!(route, "only");
            assert!(matches!(result, CheckResult::Unsat));
        }
    }

    #[test]
    fn one_worker_runs_the_arms_in_declared_order_and_stops_at_the_first_decision() {
        let arena = TermArena::new();
        let arms = [
            Arm {
                route: "first",
                weight: 1,
                run: declines,
            },
            Arm {
                route: "second",
                weight: 1,
                run: says_unsat,
            },
            Arm {
                route: "third",
                weight: 1,
                run: counts_then_declines,
            },
        ];
        SEQUENTIAL_CALLS.store(0, Ordering::SeqCst);
        let outcome = FusedGroup::new(&arms, 1)
            .run(&arena, &[], &config_with(1_000))
            .expect("group ran");
        assert_eq!(outcome.arms.len(), 2, "the third arm must not have run");
        assert_eq!(outcome.arms[0].route, "first");
        assert_eq!(outcome.arms[1].route, "second");
        assert_eq!(
            SEQUENTIAL_CALLS.load(Ordering::SeqCst),
            0,
            "an arm after the winner must not be entered"
        );
    }

    #[test]
    fn one_worker_gives_each_arm_its_reserved_slice_with_carry_over() {
        // Two equally weighted arms of a 1,000 ms share: the first must be
        // offered ~500 ms. It declines instantly, so the second must be offered
        // the whole remainder, not another 500 ms — that is the carry-over.
        static OFFERED: std::sync::Mutex<Vec<u128>> = std::sync::Mutex::new(Vec::new());
        fn records(
            _: &mut TermArena,
            _: &[TermId],
            config: &SolverConfig,
        ) -> Result<CheckResult, SolverError> {
            OFFERED
                .lock()
                .expect("lock")
                .push(config.timeout.expect("a share").as_millis());
            Ok(undecided("declined"))
        }
        OFFERED.lock().expect("lock").clear();
        let arena = TermArena::new();
        let arms = [
            Arm {
                route: "a",
                weight: 1,
                run: records,
            },
            Arm {
                route: "b",
                weight: 1,
                run: records,
            },
        ];
        FusedGroup::new(&arms, 1)
            .run(&arena, &[], &config_with(1_000))
            .expect("group ran");
        let offered = OFFERED.lock().expect("lock").clone();
        assert_eq!(offered.len(), 2);
        assert!(
            (400..=600).contains(&offered[0]),
            "the first arm gets about half the share, got {}ms",
            offered[0]
        );
        assert!(
            offered[1] >= 900,
            "an arm that declined instantly must donate its slice forward, got {}ms",
            offered[1]
        );
    }

    #[test]
    fn a_raced_group_returns_the_declared_order_winner_not_the_first_finisher() {
        let arena = TermArena::new();
        // `slow` cannot decide; `says_unsat` returns instantly. Declared order
        // puts the instant one second, so it is also the winner — and the point
        // of the test is the reverse arrangement below.
        let arms = [
            Arm {
                route: "slow",
                weight: 1,
                run: slow_then_unsat,
            },
            Arm {
                route: "fast",
                weight: 1,
                run: says_unsat,
            },
        ];
        let outcome = FusedGroup::new(&arms, 2)
            .run(&arena, &[], &config_with(30_000))
            .expect("group ran");
        assert_eq!(outcome.arms.len(), 2);
        assert_eq!(
            outcome.arms[0].route, "slow",
            "outcomes are reported in declared order"
        );
        assert!(
            outcome.arms[0].stopped,
            "the losing arm must have been asked to stop"
        );
        assert!(
            outcome.arms[0].elapsed < Duration::from_secs(25),
            "the stop must actually shorten the losing arm; it ran {:?} of a 30 s budget",
            outcome.arms[0].elapsed
        );
        let (route, _) = outcome.into_decision().expect("decided");
        assert_eq!(route, "fast");
    }

    #[test]
    fn two_arms_that_both_decide_yield_the_earlier_declared_one() {
        let arena = TermArena::new();
        let arms = [
            Arm {
                route: "first-declared",
                weight: 1,
                run: says_unsat,
            },
            Arm {
                route: "second-declared",
                weight: 1,
                run: says_unsat,
            },
        ];
        for workers in [1, 2] {
            let outcome = FusedGroup::new(&arms, workers)
                .run(&arena, &[], &config_with(5_000))
                .expect("group ran");
            let (route, _) = outcome.into_decision().expect("decided");
            assert_eq!(
                route, "first-declared",
                "the winner is chosen by declared order at {workers} worker(s)"
            );
        }
    }

    #[test]
    fn two_arms_that_disagree_are_a_hard_failure_not_a_choice() {
        let arena = TermArena::new();
        let arms = [
            Arm {
                route: "claims-unsat",
                weight: 1,
                run: says_unsat,
            },
            Arm {
                route: "claims-sat",
                weight: 1,
                run: says_sat,
            },
        ];
        // One worker stops at the first decision, so the disagreement is only
        // observable when both arms actually run — which is the raced case, and
        // is exactly why the gate lives in the group rather than in a route.
        let error = FusedGroup::new(&arms, 2)
            .run(&arena, &[], &config_with(5_000))
            .expect_err("a disagreement must not produce a verdict");
        let text = error.to_string();
        assert!(text.contains("claims-unsat"), "names both arms: {text}");
        assert!(text.contains("claims-sat"), "names both arms: {text}");
        assert!(text.contains("unsound"), "says what it means: {text}");
    }

    #[test]
    fn each_arm_of_a_raced_group_gets_a_share_of_one_process_memory_limit() {
        static SEEN: std::sync::Mutex<Vec<Option<u64>>> = std::sync::Mutex::new(Vec::new());
        fn records_memory(
            _: &mut TermArena,
            _: &[TermId],
            config: &SolverConfig,
        ) -> Result<CheckResult, SolverError> {
            SEEN.lock().expect("lock").push(config.memory_limit_mb);
            Ok(undecided("declined"))
        }
        SEEN.lock().expect("lock").clear();
        let arena = TermArena::new();
        let arms = [
            Arm {
                route: "a",
                weight: 1,
                run: records_memory,
            },
            Arm {
                route: "b",
                weight: 1,
                run: records_memory,
            },
        ];
        let config = SolverConfig {
            timeout: Some(Duration::from_millis(500)),
            memory_limit_mb: Some(8_192),
            ..SolverConfig::default()
        };
        FusedGroup::new(&arms, 2)
            .run(&arena, &[], &config)
            .expect("group ran");
        let seen = SEEN.lock().expect("lock").clone();
        assert_eq!(seen.len(), 2);
        for limit in seen {
            assert_eq!(
                limit,
                Some(4_096),
                "a competition limit is per PROCESS: two arms get half each, never the whole"
            );
        }
    }
}
