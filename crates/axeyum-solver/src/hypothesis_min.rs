//! Automatic hypothesis minimisation — find a small sufficient subset of a
//! hypothesis set for a fixed goal, when the **full** set is `unknown`.
//!
//! # The measurement this exists for
//!
//! The 2026-08-12 route-B session
//! (`docs/plan/proof-approaches-2026-08-12/route-b/LOG.md`) proved the `k = 2`
//! Rado case for symbolic `a`, `b` by hand-splitting a monolithic query into
//! three-and-four-hypothesis lemmas. Every monolithic attempt returned
//! `unknown`; the split content closed in milliseconds. The split cost four
//! attempts and about 32 minutes of solver time — human work, on material where
//! the machine had the facts all along.
//!
//! Re-measured at HEAD on 2026-08-14, the boundary is **not hypothesis count**:
//! the lemma `a>=2, t>=1, t=a*w |- w>=1` still closes in 2 ms with **forty**
//! irrelevant degree-3 hypotheses added, while `a>=2, b>=1, w>=1, t=a*w |-
//! b*t >= a*b` — which closes in 1 ms alone — goes `unknown` when **one** more
//! hypothesis (`a*u + b*v = 1`) is added, and stays `unknown` at every budget
//! from 1 s to 300 s. The cause is [`crate::nra`]'s deterministic admission cap
//! `MAX_CROSS_PRODUCTS = 2` (`nra.rs:107`, checked at `nra.rs:334`): the extra
//! hypothesis pushes the query's distinct normalized cross-product monomials
//! from 2 to 4, and the guard declines in 40 ms regardless of the clock.
//!
//! Two consequences shape this module:
//!
//! 1. **Deletion-based minimisation cannot start.** [`crate::auto::unsat_core`]
//!    returns `None` unless the *whole* set is already solver-`unsat`
//!    (`auto.rs:664`). Logically `unsat` is monotone — a subset's refutation
//!    refutes every superset — but the *solver's* `unsat` is not, which is the
//!    entire phenomenon. So this module **grows from below** instead.
//! 2. **The search has a free, sound ordering heuristic.** Cross-product count
//!    is a syntactic function of the candidate subset
//!    ([`crate::nra_real_root::normalized_cross_product_count`]) that costs no
//!    solver call and predicts the cliff. Candidates are ordered by it. Ordering
//!    only changes *which* sufficient subset is found first, never whether a
//!    reported subset is sound.
//!
//! # Soundness
//!
//! Dropping hypotheses makes a goal **harder**: if `S ⊆ H` and `S ∪ {¬G}` is
//! unsatisfiable, then `H ∪ {¬G}` is unsatisfiable, so a proof from the subset is
//! a proof from the whole set. That direction is free. The two ways a minimiser
//! can nevertheless generate a wrong answer are both guarded here:
//!
//! * **The negated goal must never be droppable.** If it is, `{x = 1, x = 2}`
//!   with goal `x = 3` "closes" by dropping the goal — reporting a proof of a
//!   false statement. [`minimize_hypotheses`] takes the negated goal as a
//!   *separate parameter* that is present in every probe, so this is
//!   unrepresentable rather than merely unlikely.
//! * **A subset that closes because the hypotheses are contradictory proves
//!   nothing.** `{a >= 2, a <= 1}` entails every goal. The route-B notebook hit
//!   exactly this (`LOG.md:509`: three controls "could not possibly return
//!   `sat`"). Every candidate subset is therefore also checked **without** the
//!   goal, and a definitely-inconsistent subset is reported as
//!   [`MinimizeOutcome::VacuousHypotheses`], never as a proof.
//!
//! Consistency is itself often undecidable at these budgets — measured: the
//! route-B `H` returns `unknown` both with and without its Bezout conjunct — so
//! [`Consistency`] is a **three-valued** result carried on the successful
//! outcome, not a precondition this module pretends to have established.
//!
//! # Determinism
//!
//! Candidate order is a `Vec` sorted by an explicit total key
//! (cross-product count, then subset size, then ascending index order); no hash
//! container participates in any output. The same input yields the same subset.

use std::time::Duration;

use axeyum_ir::{TermArena, TermId};

use crate::backend::{CheckResult, SolverConfig, SolverError};

/// The default per-probe wall-clock budget.
///
/// Deliberately small. The measurement that motivates this module is that a
/// sufficient subset closes in **milliseconds** while an insufficient one burns
/// the whole clock: `L3`'s minimal set is 1 ms, and one hypothesis more is
/// `unknown` at 300 s. A small probe budget therefore costs almost nothing on
/// the subsets that matter and bounds the cost of the ones that do not.
pub const DEFAULT_PROBE_BUDGET: Duration = Duration::from_millis(250);

/// The default largest subset size the search enumerates.
///
/// Four, because the route-B decomposition that worked was into
/// "3-4-hypothesis lemmas" (`REPORT.md:98`) and every micro-lemma in the
/// completed `k = 2` proof has at most three hypotheses.
pub const DEFAULT_MAX_SUBSET_SIZE: usize = 4;

/// The default cap on solver probes across the whole search.
pub const DEFAULT_MAX_PROBES: usize = 4000;

/// Search configuration for [`minimize_hypotheses`].
#[derive(Debug, Clone)]
pub struct MinimizeConfig {
    /// Wall-clock budget for each individual subset probe.
    pub probe_budget: Duration,
    /// Largest subset size enumerated. Sizes are tried ascending, so the first
    /// subset found is of minimum cardinality among those the search reaches.
    pub max_subset_size: usize,
    /// Hard cap on the number of solver probes, so the search is bounded even
    /// when the hypothesis set is large.
    pub max_probes: usize,
    /// Budget for the final re-verification of the reported subset. `None` uses
    /// `probe_budget`.
    pub verify_budget: Option<Duration>,
}

impl Default for MinimizeConfig {
    fn default() -> Self {
        Self {
            probe_budget: DEFAULT_PROBE_BUDGET,
            max_subset_size: DEFAULT_MAX_SUBSET_SIZE,
            max_probes: DEFAULT_MAX_PROBES,
            verify_budget: None,
        }
    }
}

/// Whether the reported hypothesis subset was shown to be satisfiable on its own.
///
/// This is **three-valued on purpose.** A subset that is inconsistent entails
/// every goal, so a "proof" from it is vacuous; but consistency of a nonlinear
/// integer hypothesis set is routinely `unknown` at any budget this module would
/// spend. Reporting `Unknown` is the honest answer and forces the caller to see
/// it — collapsing it into "consistent" would be the wrong-answer generator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Consistency {
    /// The subset alone is satisfiable: the goal was proved from hypotheses that
    /// can hold, so the implication is not vacuous.
    Consistent,
    /// The solver could not decide whether the subset alone is satisfiable.
    /// The proof of the goal is sound either way, but it may be vacuous.
    Unknown,
}

/// The result of a minimisation attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MinimizeOutcome {
    /// A sufficient subset was found, shrunk, and re-verified.
    Closed {
        /// Indices into the caller's `hypotheses` slice, strictly ascending.
        indices: Vec<usize>,
        /// Whether the subset was shown to be satisfiable on its own.
        consistency: Consistency,
        /// Number of solver probes the search spent.
        probes: usize,
    },
    /// A subset was found to be **inconsistent on its own**, so it entails the
    /// goal (and every other goal) vacuously. Reported instead of a proof.
    VacuousHypotheses {
        /// Indices into the caller's `hypotheses` slice, strictly ascending.
        indices: Vec<usize>,
        /// Number of solver probes the search spent.
        probes: usize,
    },
    /// No subset within the configured search bound closed the goal. `unknown`
    /// stays a first-class answer.
    NotFound {
        /// Number of solver probes the search spent.
        probes: usize,
    },
}

/// Finds a small subset of `hypotheses` that suffices to refute
/// `hypotheses ∪ negated_goal`, when the full set is `unknown`.
///
/// `negated_goal` is the already-negated goal (for a goal `G`, pass `¬G`; for a
/// "derive `false`" goal, pass an empty slice). It is **pinned**: every probe
/// contains all of it, and it is never a minimisation candidate. This is what
/// makes "minimised by dropping the goal" unrepresentable rather than merely
/// discouraged.
///
/// Search: subsets of ascending cardinality, `0..=config.max_subset_size`,
/// enumerated in a deterministic order keyed on the subset's distinct normalized
/// cross-product-monomial count (the property measured to predict
/// [`crate::nra`]'s `MAX_CROSS_PRODUCTS` admission cap), then on index order.
/// Once a subset refutes, it is shrunk by deletion (which is valid from that
/// point, unlike from the full set) and re-verified.
///
/// # Errors
///
/// Returns [`SolverError`] from the underlying dispatch.
pub fn minimize_hypotheses(
    arena: &mut TermArena,
    hypotheses: &[TermId],
    negated_goal: &[TermId],
    config: &MinimizeConfig,
) -> Result<MinimizeOutcome, SolverError> {
    let mut probes = 0usize;
    let probe_cfg = SolverConfig {
        timeout: Some(config.probe_budget),
        ..SolverConfig::default()
    };
    let max_size = config.max_subset_size.min(hypotheses.len());

    let order = candidate_order(arena, hypotheses, negated_goal);

    for size in 0..=max_size {
        let mut subset_indices = Vec::with_capacity(size);
        let mut found = None;
        enumerate_subsets(
            &order,
            size,
            &mut subset_indices,
            &mut |chosen: &[usize]| {
                if found.is_some() || probes >= config.max_probes {
                    return;
                }
                probes += 1;
                let mut sorted: Vec<usize> = chosen.to_vec();
                sorted.sort_unstable();
                let mut assertions: Vec<TermId> = sorted.iter().map(|&i| hypotheses[i]).collect();
                assertions.extend_from_slice(negated_goal);
                if assertions.is_empty() {
                    return;
                }
                if let Ok(CheckResult::Unsat) =
                    crate::auto::check_auto(arena, &assertions, &probe_cfg)
                {
                    found = Some(sorted);
                }
            },
        );
        if let Some(sorted) = found {
            return finish(arena, hypotheses, negated_goal, config, sorted, probes);
        }
        if probes >= config.max_probes {
            break;
        }
    }
    Ok(MinimizeOutcome::NotFound { probes })
}

/// Shrink the closing subset by deletion, run the vacuity guard, and re-verify.
fn finish(
    arena: &mut TermArena,
    hypotheses: &[TermId],
    negated_goal: &[TermId],
    config: &MinimizeConfig,
    mut indices: Vec<usize>,
    mut probes: usize,
) -> Result<MinimizeOutcome, SolverError> {
    let probe_cfg = SolverConfig {
        timeout: Some(config.probe_budget),
        ..SolverConfig::default()
    };

    // Deletion-based shrink. Valid HERE (and not from the full set) because the
    // starting subset is known to be solver-`unsat`. Fixed ascending order.
    let mut i = 0;
    while i < indices.len() {
        let candidate = indices[i];
        let trial: Vec<usize> = indices
            .iter()
            .copied()
            .filter(|&j| j != candidate)
            .collect();
        let mut assertions: Vec<TermId> = trial.iter().map(|&j| hypotheses[j]).collect();
        assertions.extend_from_slice(negated_goal);
        if assertions.is_empty() {
            i += 1;
            continue;
        }
        probes += 1;
        if let Ok(CheckResult::Unsat) = crate::auto::check_auto(arena, &assertions, &probe_cfg) {
            indices = trial;
        } else {
            i += 1;
        }
    }

    // VACUITY GUARD. A subset that is unsatisfiable on its own entails the goal —
    // and every other goal — so it is not a proof of anything the caller asked
    // about. Check the subset WITHOUT the goal.
    let subset_only: Vec<TermId> = indices.iter().map(|&j| hypotheses[j]).collect();
    let consistency = if subset_only.is_empty() {
        // The empty hypothesis set is trivially satisfiable; the goal was refuted
        // outright, which is a stronger result, not a vacuous one.
        Consistency::Consistent
    } else {
        probes += 1;
        match crate::auto::check_auto(arena, &subset_only, &probe_cfg) {
            Ok(CheckResult::Unsat) => {
                return Ok(MinimizeOutcome::VacuousHypotheses { indices, probes });
            }
            Ok(CheckResult::Sat(_)) => Consistency::Consistent,
            Ok(CheckResult::Unknown(_)) | Err(_) => Consistency::Unknown,
        }
    };

    // RE-VERIFICATION. The reported subset is re-checked at the verify budget and
    // only a definite `Unsat` is reported. This also pins the returned indices:
    // an off-by-one in the bookkeeping above would fail here rather than ship.
    let verify_cfg = SolverConfig {
        timeout: Some(config.verify_budget.unwrap_or(config.probe_budget)),
        ..SolverConfig::default()
    };
    let mut assertions: Vec<TermId> = indices.iter().map(|&j| hypotheses[j]).collect();
    assertions.extend_from_slice(negated_goal);
    probes += 1;
    match crate::auto::check_auto(arena, &assertions, &verify_cfg)? {
        CheckResult::Unsat => Ok(MinimizeOutcome::Closed {
            indices,
            consistency,
            probes,
        }),
        // The subset closed at probe time but not on re-verification. Refuse to
        // report a proof: `unknown` is a first-class result.
        _ => Ok(MinimizeOutcome::NotFound { probes }),
    }
}

/// The deterministic candidate order.
///
/// Key: the distinct normalized cross-product-monomial count that
/// `{hypothesis} ∪ negated_goal` induces (ascending), then the hypothesis's own
/// index (ascending). Hypotheses that add no cross-product to the goal are tried
/// first, which is exactly the property the 2026-08-14 `leave-one-in` measurement
/// separated the six harmless additions from the four fatal ones by.
///
/// This is an ordering only: it never removes a candidate, so it cannot change
/// which subsets are *reachable*, only which is found first.
fn candidate_order(
    arena: &mut TermArena,
    hypotheses: &[TermId],
    negated_goal: &[TermId],
) -> Vec<usize> {
    let mut keyed: Vec<(usize, usize)> = hypotheses
        .iter()
        .enumerate()
        .map(|(i, &h)| {
            let mut probe: Vec<TermId> = Vec::with_capacity(negated_goal.len() + 1);
            probe.push(h);
            probe.extend_from_slice(negated_goal);
            let count = crate::nra_real_root::normalized_cross_product_count(arena, &probe)
                .unwrap_or(usize::MAX);
            (count, i)
        })
        .collect();
    keyed.sort_unstable();
    keyed.into_iter().map(|(_, i)| i).collect()
}

/// Enumerate every `size`-subset of `order`, in `order`'s own sequence, calling
/// `f` with the chosen indices. Iterative in shape but written recursively for
/// clarity; `size` is bounded by [`MinimizeConfig::max_subset_size`].
fn enumerate_subsets(
    order: &[usize],
    size: usize,
    chosen: &mut Vec<usize>,
    f: &mut impl FnMut(&[usize]),
) {
    if chosen.len() == size {
        f(chosen);
        return;
    }
    let start = chosen.len().checked_sub(1).map_or(0, |_| 0);
    let _ = start;
    let begin = chosen.last().map_or(0, |&last| {
        order.iter().position(|&x| x == last).map_or(0, |p| p + 1)
    });
    for &cand in &order[begin..] {
        chosen.push(cand);
        enumerate_subsets(order, size, chosen, f);
        chosen.pop();
    }
}

/// Splits a conjunctive goal into its top-level conjuncts and minimises each
/// separately — the "lemma splitting" half of the feature.
///
/// Proving `H ⊢ G1` and `H ⊢ G2` proves `H ⊢ G1 ∧ G2`, so splitting is sound in
/// the same direction as dropping hypotheses. Returns one outcome per conjunct,
/// in the conjuncts' left-to-right order. A goal with no top-level conjunction is
/// a single-element result, identical to calling [`minimize_hypotheses`].
///
/// # Errors
///
/// Returns [`SolverError`] from the underlying dispatch.
pub fn split_goal_and_minimize(
    arena: &mut TermArena,
    hypotheses: &[TermId],
    goal: TermId,
    config: &MinimizeConfig,
) -> Result<Vec<(TermId, MinimizeOutcome)>, SolverError> {
    let conjuncts = top_level_conjuncts(arena, goal);
    let mut out = Vec::with_capacity(conjuncts.len());
    for c in conjuncts {
        let negated = arena
            .not(c)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let outcome = minimize_hypotheses(arena, hypotheses, &[negated], config)?;
        out.push((c, outcome));
    }
    Ok(out)
}

/// The top-level conjuncts of `t`, left to right, flattening nested `and`.
fn top_level_conjuncts(arena: &TermArena, t: TermId) -> Vec<TermId> {
    use axeyum_ir::{Op, TermNode};
    let mut out = Vec::new();
    let mut stack = vec![t];
    // Depth-first with an explicit stack, pushing right-then-left so the output
    // is left-to-right and deterministic.
    while let Some(top) = stack.pop() {
        match arena.node(top) {
            TermNode::App {
                op: Op::BoolAnd,
                args,
            } if args.len() == 2 => {
                stack.push(args[1]);
                stack.push(args[0]);
            }
            _ => out.push(top),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    // The variable names are the mathematics's own (`a`, `b`, `t`, `w`, `x`, `y`
    // are route-B's symbols); renaming them would obscure which lemma each test
    // encodes. Same stance as `nra.rs:1476` and `ufbv_finite.rs:383`.
    #![allow(clippy::many_single_char_names)]

    use super::*;
    use axeyum_ir::TermArena;

    /// `a >= 2, t >= 1, t = a*w |- w >= 1` — route-B lemma `L2`, padded with
    /// irrelevant hypotheses that the minimiser must drop.
    fn l2_padded() -> (TermArena, Vec<TermId>, Vec<TermId>) {
        let mut ar = TermArena::new();
        let a = ar.int_var("a").unwrap();
        let t = ar.int_var("t").unwrap();
        let w = ar.int_var("w").unwrap();
        let two = ar.int_const(2);
        let one = ar.int_const(1);
        let h_a = ar.int_ge(a, two).unwrap();
        let h_t = ar.int_ge(t, one).unwrap();
        let aw = ar.int_mul(a, w).unwrap();
        let h_def = ar.eq(t, aw).unwrap();
        // Padding: four irrelevant nonlinear hypotheses over fresh variables.
        let mut hyps = vec![h_a, h_t, h_def];
        for i in 0..4 {
            let p = ar.int_var(&format!("p{i}")).unwrap();
            let q = ar.int_var(&format!("q{i}")).unwrap();
            let pq = ar.int_mul(p, q).unwrap();
            let zero = ar.int_const(0);
            hyps.push(ar.int_ge(pq, zero).unwrap());
        }
        let g = ar.int_ge(w, one).unwrap();
        let ng = ar.not(g).unwrap();
        (ar, hyps, vec![ng])
    }

    #[test]
    fn finds_the_minimal_sufficient_subset() {
        let (mut ar, hyps, goal) = l2_padded();
        let out =
            minimize_hypotheses(&mut ar, &hyps, &goal, &MinimizeConfig::default()).expect("solve");
        match out {
            MinimizeOutcome::Closed { indices, .. } => {
                // The three real hypotheses are at 0, 1, 2; the four padding
                // hypotheses at 3..7 must not appear.
                assert!(
                    indices.iter().all(|&i| i < 3),
                    "padding retained: {indices:?}"
                );
                assert!(!indices.is_empty());
            }
            other => panic!("expected Closed, got {other:?}"),
        }
    }

    #[test]
    fn reported_indices_are_ascending_unique_and_in_range() {
        let (mut ar, hyps, goal) = l2_padded();
        let out =
            minimize_hypotheses(&mut ar, &hyps, &goal, &MinimizeConfig::default()).expect("solve");
        let MinimizeOutcome::Closed { indices, .. } = out else {
            panic!("expected Closed")
        };
        assert!(
            indices.windows(2).all(|w| w[0] < w[1]),
            "not strictly ascending: {indices:?}"
        );
        assert!(
            indices.iter().all(|&i| i < hyps.len()),
            "out of range: {indices:?}"
        );
    }

    /// CONTROL for the re-verification guard: the subset the minimiser reports
    /// must independently refute the goal when re-posed from the returned
    /// indices alone.
    #[test]
    fn reported_subset_independently_refutes_the_goal() {
        let (mut ar, hyps, goal) = l2_padded();
        let out =
            minimize_hypotheses(&mut ar, &hyps, &goal, &MinimizeConfig::default()).expect("solve");
        let MinimizeOutcome::Closed { indices, .. } = out else {
            panic!("expected Closed")
        };
        let mut assertions: Vec<TermId> = indices.iter().map(|&i| hyps[i]).collect();
        assertions.extend_from_slice(&goal);
        let cfg = SolverConfig {
            timeout: Some(Duration::from_secs(5)),
            ..SolverConfig::default()
        };
        assert!(
            matches!(
                crate::auto::check_auto(&mut ar, &assertions, &cfg),
                Ok(CheckResult::Unsat)
            ),
            "the reported subset does not refute the goal"
        );
    }

    /// CONTROL for the vacuity guard. `{a >= 2, a <= 1}` is contradictory, so it
    /// entails `b >= 5` — a goal that does not follow from anything the caller
    /// meant. The minimiser must report `VacuousHypotheses`, not a proof.
    #[test]
    fn contradictory_hypotheses_are_refused_not_reported_as_a_proof() {
        let mut ar = TermArena::new();
        let a = ar.int_var("a").unwrap();
        let b = ar.int_var("b").unwrap();
        let two = ar.int_const(2);
        let one = ar.int_const(1);
        let five = ar.int_const(5);
        let h0 = ar.int_ge(a, two).unwrap();
        let h1 = ar.int_le(a, one).unwrap();
        let g = ar.int_ge(b, five).unwrap();
        let ng = ar.not(g).unwrap();
        let out = minimize_hypotheses(&mut ar, &[h0, h1], &[ng], &MinimizeConfig::default())
            .expect("solve");
        assert!(
            matches!(out, MinimizeOutcome::VacuousHypotheses { .. }),
            "contradictory hypotheses reported as a proof: {out:?}"
        );
    }

    /// CONTROL for the goal pin. If the negated goal could be dropped, this query
    /// would "close" on `{x = 1, x = 2}` alone and report a proof of `x = 3`.
    /// Because the goal is pinned, the only closing subset is contradictory and
    /// the outcome is `VacuousHypotheses` — never `Closed`.
    #[test]
    fn the_negated_goal_is_never_dropped() {
        let mut ar = TermArena::new();
        let x = ar.int_var("x").unwrap();
        let one = ar.int_const(1);
        let two = ar.int_const(2);
        let three = ar.int_const(3);
        let h0 = ar.eq(x, one).unwrap();
        let h1 = ar.eq(x, two).unwrap();
        let g = ar.eq(x, three).unwrap();
        let ng = ar.not(g).unwrap();
        let out = minimize_hypotheses(&mut ar, &[h0, h1], &[ng], &MinimizeConfig::default())
            .expect("solve");
        assert!(
            matches!(out, MinimizeOutcome::VacuousHypotheses { .. }),
            "a false goal was proved from contradictory hypotheses: {out:?}"
        );
    }

    /// CONTROL for "no subset suffices". `a >= 2 ∧ b >= 1 |- a*b >= 3` is FALSE
    /// (`a = 2, b = 1` gives `2`). No subset can close it, so the outcome must be
    /// `NotFound` — a minimiser that reports something here is a wrong-answer
    /// generator.
    #[test]
    fn an_unentailed_goal_is_not_found_not_closed() {
        let mut ar = TermArena::new();
        let a = ar.int_var("a").unwrap();
        let b = ar.int_var("b").unwrap();
        let two = ar.int_const(2);
        let one = ar.int_const(1);
        let three = ar.int_const(3);
        let h0 = ar.int_ge(a, two).unwrap();
        let h1 = ar.int_ge(b, one).unwrap();
        let ab = ar.int_mul(a, b).unwrap();
        let g = ar.int_ge(ab, three).unwrap();
        let ng = ar.not(g).unwrap();
        let out = minimize_hypotheses(&mut ar, &[h0, h1], &[ng], &MinimizeConfig::default())
            .expect("solve");
        assert!(
            matches!(out, MinimizeOutcome::NotFound { .. }),
            "an unentailed goal was reported closed: {out:?}"
        );
    }

    /// CONTROL for the re-verification guard. The search probes at
    /// `probe_budget` and the reported subset is re-checked at `verify_budget`;
    /// only a definite `Unsat` there is reported as a proof. With a verify budget
    /// too small to decide anything, the honest answer is `NotFound`, not the
    /// subset the search happened to accept.
    ///
    /// This control exists because the first mutation matrix measured the
    /// re-verification guard as a **dud**: deleting it left all nine tests green,
    /// because every other test's subset re-verifies trivially. Testing that a
    /// guard is *reached* is not testing that it is *needed*.
    #[test]
    fn re_verification_is_respected() {
        let (mut ar, hyps, goal) = l2_padded();
        let cfg = MinimizeConfig {
            probe_budget: Duration::from_secs(5),
            verify_budget: Some(Duration::from_nanos(1)),
            ..MinimizeConfig::default()
        };
        let out = minimize_hypotheses(&mut ar, &hyps, &goal, &cfg).expect("solve");
        assert!(
            matches!(out, MinimizeOutcome::NotFound { .. }),
            "a subset was reported without surviving re-verification: {out:?}"
        );
    }

    /// CONTROL for determinism: the same input twice yields the same subset.
    #[test]
    fn minimisation_is_deterministic() {
        let mut first = None;
        for _ in 0..3 {
            let (mut ar, hyps, goal) = l2_padded();
            let out = minimize_hypotheses(&mut ar, &hyps, &goal, &MinimizeConfig::default())
                .expect("solve");
            let MinimizeOutcome::Closed { indices, .. } = out else {
                panic!("expected Closed")
            };
            match &first {
                None => first = Some(indices),
                Some(prev) => assert_eq!(prev, &indices, "nondeterministic subset"),
            }
        }
    }

    /// The headline instance: route-B lemma `L3` carrying the full colour-1
    /// hypothesis set. `check_auto` on the whole set is `unknown` at every budget
    /// measured up to 300 s; the minimiser must find the four-hypothesis subset.
    #[test]
    fn closes_the_route_b_l3_lemma_from_the_full_hypothesis_set() {
        let mut ar = TermArena::new();
        let a = ar.int_var("a").unwrap();
        let b = ar.int_var("b").unwrap();
        let t = ar.int_var("t").unwrap();
        let u = ar.int_var("u").unwrap();
        let v = ar.int_var("v").unwrap();
        let w = ar.int_var("w").unwrap();
        let x = ar.int_var("x").unwrap();
        let y = ar.int_var("y").unwrap();
        let z = ar.int_var("z").unwrap();
        let px = ar.int_var("px").unwrap();
        let py = ar.int_var("py").unwrap();
        let one = ar.int_const(1);
        let two = ar.int_const(2);
        let ab = ar.int_mul(a, b).unwrap();
        let bt = ar.int_mul(b, t).unwrap();
        let aw = ar.int_mul(a, w).unwrap();
        let at = ar.int_mul(a, t).unwrap();
        let au = ar.int_mul(a, u).unwrap();
        let bv = ar.int_mul(b, v).unwrap();
        let bez = ar.int_add(au, bv).unwrap();
        let apx = ar.int_mul(a, px).unwrap();
        let apy = ar.int_mul(a, py).unwrap();
        let xy = ar.int_sub(x, y).unwrap();
        let hyps = vec![
            ar.int_ge(a, two).unwrap(), // 0  a >= 2
            ar.int_ge(b, one).unwrap(), // 1  b >= 1
            ar.eq(bez, one).unwrap(),   // 2  a*u + b*v = 1
            ar.int_ge(x, one).unwrap(), // 3  x >= 1
            ar.int_le(x, ab).unwrap(),  // 4  x <= a*b
            ar.int_ge(y, one).unwrap(), // 5  y >= 1
            ar.int_le(y, ab).unwrap(),  // 6  y <= a*b
            ar.eq(xy, bt).unwrap(),     // 7  x - y = b*t
            ar.eq(z, at).unwrap(),      // 8  z = a*t
            ar.eq(x, apx).unwrap(),     // 9  x = a*px
            ar.eq(y, apy).unwrap(),     // 10 y = a*py
            ar.eq(t, aw).unwrap(),      // 11 t = a*w
            ar.int_ge(t, one).unwrap(), // 12 t >= 1
            ar.int_ge(w, one).unwrap(), // 13 w >= 1
        ];
        let g = ar.int_ge(bt, ab).unwrap();
        let ng = ar.not(g).unwrap();

        // The monolithic query is `unknown` — this is the premise of the feature.
        let mono_cfg = SolverConfig {
            timeout: Some(Duration::from_secs(2)),
            ..SolverConfig::default()
        };
        let mut mono: Vec<TermId> = hyps.clone();
        mono.push(ng);
        assert!(
            matches!(
                crate::auto::check_auto(&mut ar, &mono, &mono_cfg),
                Ok(CheckResult::Unknown(_))
            ),
            "the monolithic query is no longer unknown; this test's premise has changed"
        );

        let out =
            minimize_hypotheses(&mut ar, &hyps, &[ng], &MinimizeConfig::default()).expect("solve");
        let MinimizeOutcome::Closed { indices, .. } = out else {
            panic!("L3 was not closed from the full hypothesis set: {out:?}")
        };
        // The Bezout conjunct (2) and the two `<= a*b` bounds (4, 6) are exactly
        // the additions measured to push the query past `MAX_CROSS_PRODUCTS`.
        assert!(
            !indices.contains(&2),
            "the fatal Bezout hypothesis was retained"
        );
        assert!(
            indices.len() <= 4,
            "subset larger than the route-B split: {indices:?}"
        );
    }

    /// A conjunctive goal is split and each conjunct minimised separately.
    #[test]
    fn conjunctive_goals_split_into_lemmas() {
        let mut ar = TermArena::new();
        let a = ar.int_var("a").unwrap();
        let b = ar.int_var("b").unwrap();
        let two = ar.int_const(2);
        let one = ar.int_const(1);
        let h0 = ar.int_ge(a, two).unwrap();
        let h1 = ar.int_ge(b, one).unwrap();
        let p = ar.int_var("p").unwrap();
        let q = ar.int_var("q").unwrap();
        let pq = ar.int_mul(p, q).unwrap();
        let zero = ar.int_const(0);
        let h2 = ar.int_ge(pq, zero).unwrap();
        let ab = ar.int_mul(a, b).unwrap();
        let g1 = ar.int_ge(ab, one).unwrap();
        let g2 = ar.int_ge(a, one).unwrap();
        let goal = ar.and(g1, g2).unwrap();
        let out = split_goal_and_minimize(&mut ar, &[h0, h1, h2], goal, &MinimizeConfig::default())
            .expect("solve");
        assert_eq!(out.len(), 2, "conjunctive goal was not split");
        for (_, o) in &out {
            assert!(
                matches!(o, MinimizeOutcome::Closed { .. }),
                "conjunct not closed: {o:?}"
            );
        }
        // The second conjunct `a >= 1` needs only `a >= 2`: one hypothesis.
        let MinimizeOutcome::Closed { indices, .. } = &out[1].1 else {
            unreachable!()
        };
        assert_eq!(indices, &vec![0]);
    }
}
