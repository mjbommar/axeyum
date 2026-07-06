//! Linear integer arithmetic (`QF_LIA`) on the **generic online CDCL(T) driver**
//! [`crate::cdclt::CdclT`] (ADR-0055 criterion 2, slice a — the
//! multiply-across-theories keystone).
//!
//! [`crate::euf_egraph::check_qf_uf_online_cdclt`] proved the generic driver drives
//! EUF; [`crate::string_theory`] drives strings through it. This module drives
//! **integer arithmetic** through the *same* [`CdclT`], establishing that the one
//! theory-agnostic search spine serves a third, arithmetic theory. It is the
//! CDCL(T)-driver counterpart to the self-contained [`crate::lia_online`] search
//! (whose `DPLL(T)` loop lives in [`crate::lra_online`]): the Boolean skeleton, the
//! Tseitin [`Encoder`], and the incremental [`LiaTheory`] are identical — only the
//! search loop differs.
//!
//! ## Wrap, don't rewrite
//! The heavy lifting is the already-validated [`LiaTheory`] from
//! [`crate::lia_online`]: it *is* a [`TheorySolver`] (`assert` re-decides integer
//! feasibility of the live asserted set via the trusted offline
//! [`crate::lra::check_with_lia_simplex`]; `push`/`pop` snapshot the assert stack in
//! lockstep; conflict cores are deletion-minimized subsets that stay
//! `check_with_lia_simplex`-`unsat`). So this slice adds **no** new arithmetic
//! reasoning. The only gap between [`LiaTheory`] and the generic driver is the
//! driver's documented *trigger-literal precondition*: its 1-UIP conflict analysis
//! requires every theory conflict to carry a current-decision-level literal (the
//! `c9d332c1` invariant). [`CdcltLiaTheory`] is a thin adapter that guarantees
//! exactly that — see its docs.
//!
//! ## Granularity & propagation
//! - **Per-assert consistency (eager).** The wrapped [`LiaTheory`] is built in eager
//!   mode ([`LiaTheory::new`]), so every theory-atom assignment re-decides integer
//!   feasibility of the live set. This makes the theory **complete per assert**
//!   (unlike the incomplete, non-monotone `StringTheory`): a wrong `sat` is
//!   impossible because every total Boolean assignment is theory-checked, and the
//!   driver terminates by the standard argument (each conflict, carrying its trigger
//!   literal, forces a strict backjump). The large-query *deferred* mode is **not**
//!   used here — it defers feasibility to `propagate`, which this route disables.
//! - **Propagation deferred.** [`CdcltLiaTheory::propagate`] returns no
//!   propagations this slice. Completeness comes from per-assert feasibility, not
//!   propagation, so nothing is lost for correctness; wiring the LP-relaxation
//!   entailment propagations (whose propagation-conflict cores would need the same
//!   trigger-literal guarantee threaded through the driver's `theory_propagate`
//!   path) is a separate, measured step.
//!
//! ## Soundness posture (no new trust surface over the offline route)
//! - `unsat` is a sound refutation. Its theory conflict clauses are `¬core` where
//!   `core` is a subset of asserted literals that the *same* trusted
//!   [`crate::lra::check_with_lia_simplex`] the offline route relies on re-decides
//!   `unsat`; 1-UIP resolution over the mixed clause database is standard,
//!   model-independent inference. Tests gate every online `unsat` against the
//!   offline [`crate::lia_online::check_qf_lia_online`] / `check_with_lia_simplex`.
//! - `sat` is **not** trusted from the driver: a candidate integer model is
//!   reconstructed from the live atoms ([`LiaTheory::integer_model`], re-running the
//!   trusted decider), Boolean skeleton leaves are injected from the driver trail,
//!   and the model is **replayed** against the original assertions — a non-replay
//!   yields [`CheckResult::Unknown`], never a wrong `sat`.
//! - Deadline-bounded (`config.timeout`) with the driver's step budget as the
//!   defense-in-depth backstop, so the search degrades to `Unknown` under a
//!   deterministic resource bound.
//!
//! Not wired into default dispatch this slice (ADR-0055's measured-first rule).

use std::collections::HashSet;
use std::time::Instant;

use axeyum_ir::{Sort, TermArena, TermId, TermNode, Value};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::cdclt::{CdclT, Lit as CdcltLit, Outcome};
use crate::euf_egraph::{TheoryLit, TheoryProp, TheorySolver};
use crate::lia_online::{Encoder, LiaTheory, collect_lia_atoms, replays_integer};
use crate::lra_online::Lit;
use crate::model::Model;

/// Adapts the validated online [`LiaTheory`] to the generic [`CdclT`] driver's
/// **trigger-literal precondition**.
///
/// [`LiaTheory`] already implements [`TheorySolver`], so it could in principle be
/// handed to [`CdclT`] verbatim. The one behavioural gap is the driver's documented
/// precondition (the `c9d332c1` invariant): its 1-UIP analysis
/// ([`CdclT`]) resolves the conflict clause against current-decision-level literals,
/// so **every theory conflict must contain the just-asserted literal**, which sits
/// at the current level. [`LiaTheory`]'s deletion-minimized cores almost always
/// retain it — a minimal `unsat` core over a set that was feasible before this
/// assert *must* include the new literal — but a rare `Unknown`→`Unsat` transition
/// in the underlying decider could minimize it away. This wrapper closes that gap
/// deterministically: on any conflict it ensures the trigger literal `(index,
/// value)` is present. Adding one more *currently-asserted* literal to an `unsat`
/// core keeps it `unsat` (a superset of an infeasible set is infeasible), so `¬core`
/// remains a valid theory lemma — the fix is sound and never widens a verdict.
///
/// Theory propagation is disabled on this route (returns no propagations); see the
/// module docs.
struct CdcltLiaTheory {
    inner: LiaTheory,
}

impl CdcltLiaTheory {
    /// Wraps a fresh **eager** [`LiaTheory`] over `atom_terms` (per-assert
    /// feasibility), bounded by the online driver's `deadline`.
    fn new(arena: &TermArena, atom_terms: &[TermId], deadline: Option<Instant>) -> Self {
        Self {
            inner: LiaTheory::new(arena, atom_terms).with_deadline(deadline),
        }
    }

    /// The wrapped theory, for model reconstruction after a `sat` verdict.
    fn inner(&self) -> &LiaTheory {
        &self.inner
    }
}

impl TheorySolver for CdcltLiaTheory {
    fn assert(&mut self, index: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        self.inner.assert(index, value).map_err(|mut core| {
            // Guarantee the driver's trigger-literal precondition: fold the
            // just-asserted (current-decision-level) literal into the core when
            // minimization dropped it. Sound — a currently-asserted literal added to
            // an unsat core keeps it unsat (see the type docs).
            if !core.iter().any(|l| l.atom == index) {
                core.push(TheoryLit { atom: index, value });
            }
            core
        })
    }

    fn push(&mut self) {
        self.inner.push();
    }

    fn pop(&mut self) {
        self.inner.pop();
    }

    fn propagate(&self) -> Vec<TheoryProp> {
        // Deferred this slice: completeness comes from the per-assert feasibility
        // check, not propagation (see the module docs).
        Vec::new()
    }
}

/// Decides a `QF_LIA` query (an arbitrary Boolean combination of linear integer
/// order/equality atoms) via the **generic online CDCL(T)** driver `CdclT` with
/// [`LiaTheory`] as the theory (ADR-0055 criterion 2, slice a). The CDCL(T)-driver
/// counterpart to [`crate::lia_online::check_qf_lia_online`]: the skeleton, the
/// Tseitin encoder, and the incremental theory are identical; the search is the
/// theory-agnostic `CdclT` that already drives EUF and strings.
///
/// Verdict discipline (see the module docs): `unsat` is a sound refutation carrying
/// no new trust surface over the offline route; `sat` is a driver assignment whose
/// reconstructed integer model is **replayed** against the original assertions (a
/// non-replay is `Unknown`, never a wrong `sat`); the search is deadline-bounded.
///
/// Returns [`CheckResult::Unknown`] when there are no `LIA` atoms or the Boolean
/// skeleton has structure the encoder does not cover — the same conservative
/// give-ups as [`crate::lia_online::check_qf_lia_online`]. Not wired into default
/// dispatch this slice.
///
/// # Errors
///
/// Never returns `Err` in this slice (every give-up is a conservative
/// [`CheckResult::Unknown`]); the [`SolverError`] return type matches the sibling
/// [`crate::lia_online::check_qf_lia_online`] for interchange.
pub fn check_qf_lia_online_cdclt(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    // Distinct integer atoms — the theory's atom indices and the first `atom_count`
    // skeleton variables.
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = HashSet::new();
    for &a in assertions {
        collect_lia_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.is_empty() {
        return Ok(CheckResult::Unknown(unknown(
            "no linear-integer atoms for the online CDCL(T) LIA path",
        )));
    }

    let mut enc = Encoder::new(&atom_terms);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    for &assertion in assertions {
        let Some(top) = enc.encode(arena, assertion, &mut clauses) else {
            return Ok(CheckResult::Unknown(unknown(
                "boolean skeleton outside the online CDCL(T) LIA encoder",
            )));
        };
        clauses.push(vec![Lit {
            var: top,
            positive: true,
        }]);
    }

    // The generic driver has its own literal type; the two are structurally
    // identical (var index + polarity).
    let driver_clauses: Vec<Vec<CdcltLit>> = clauses
        .iter()
        .map(|clause| {
            clause
                .iter()
                .map(|l| CdcltLit {
                    var: l.var,
                    positive: l.positive,
                })
                .collect()
        })
        .collect();

    let atom_count = atom_terms.len();
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let mut theory = CdcltLiaTheory::new(arena, &atom_terms, deadline);
    let mut solver = CdclT::new(enc.var_count, atom_count, driver_clauses, deadline);
    match solver.solve(&mut theory) {
        Outcome::Unsat => Ok(CheckResult::Unsat),
        Outcome::Unknown => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Timeout,
            detail: "timeout in the online CDCL(T) LIA driver".to_owned(),
        })),
        Outcome::Sat => {
            // Reconstruct an integer model from the live atoms (via the trusted
            // offline decider), inject Boolean skeleton leaves from the driver trail,
            // and replay against the originals — the soundness gate.
            let Some(mut model) = theory.inner().integer_model() else {
                return Ok(CheckResult::Unknown(unknown(
                    "online CDCL(T) LIA model did not replay (arithmetic outside the incremental engine)",
                )));
            };
            add_boolean_leaf_values(arena, &enc, atom_count, &solver, &mut model);
            if replays_integer(arena, assertions, &model) {
                Ok(CheckResult::Sat(model))
            } else {
                Ok(CheckResult::Unknown(unknown(
                    "online CDCL(T) LIA model did not replay (arithmetic outside the incremental engine)",
                )))
            }
        }
    }
}

/// Injects each genuine Bool skeleton leaf (a skeleton variable that is not a
/// registered `LIA` atom, so absent from the reconstructed integer model) from the
/// driver trail. Additive and replay-gated by the caller, so it cannot manufacture a
/// wrong `sat`. Visited in sorted `(TermId, var)` order for determinism (`term_var`
/// is a `HashMap`).
fn add_boolean_leaf_values(
    arena: &TermArena,
    enc: &Encoder,
    atom_count: usize,
    solver: &CdclT,
    model: &mut Model,
) {
    let mut term_vars: Vec<(TermId, usize)> = enc.term_var.iter().map(|(&t, &v)| (t, v)).collect();
    term_vars.sort_by_key(|(term, _)| *term);
    for (term, var) in term_vars {
        if var < atom_count {
            continue; // a registered LIA atom, handled by the integer model
        }
        if let TermNode::Symbol(symbol) = arena.node(term)
            && arena.sort_of(term) == Sort::Bool
            && let Some(value) = solver.value(var)
        {
            model.set(*symbol, Value::Bool(value));
        }
    }
}

/// A classified `unknown` reason for the online CDCL(T) LIA path.
fn unknown(detail: &str) -> UnknownReason {
    UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: detail.to_owned(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lra::check_with_lia_simplex;

    fn ivar(arena: &mut TermArena, name: &str) -> TermId {
        let s = arena.declare(name, Sort::Int).expect("declare int");
        arena.var(s)
    }

    /// The wrapper must always fold the just-asserted (current-level) literal into a
    /// conflict core — the driver's trigger-literal precondition.
    #[test]
    fn wrapper_conflict_core_carries_the_trigger() {
        // 0 < x  and  x < 1: integer-infeasible; the second assert triggers it.
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let gt = arena.int_gt(x, zero).expect("x>0");
        let lt = arena.int_lt(x, one).expect("x<1");

        let mut theory = CdcltLiaTheory::new(&arena, &[gt, lt], None);
        assert!(theory.assert(0, true).is_ok());
        let core = theory.assert(1, true).expect_err("integer-infeasible");
        assert!(
            core.iter().any(|l| l.atom == 1 && l.value),
            "conflict core must carry the just-asserted trigger literal (atom 1, true): {core:?}"
        );
    }

    /// A trigger the minimizer keeps is not duplicated by the wrapper.
    #[test]
    fn wrapper_does_not_duplicate_a_kept_trigger() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let gt = arena.int_gt(x, zero).expect("x>0");
        let lt = arena.int_lt(x, one).expect("x<1");

        let mut theory = CdcltLiaTheory::new(&arena, &[gt, lt], None);
        assert!(theory.assert(0, true).is_ok());
        let core = theory.assert(1, true).expect_err("infeasible");
        let occurrences = core.iter().filter(|l| l.atom == 1).count();
        assert_eq!(
            occurrences, 1,
            "trigger atom appears exactly once: {core:?}"
        );
    }

    /// The strict-integer-tightening `unsat` (`0<x ∧ x<1`) — the point of LIA over
    /// LRA — decided by the CDCL(T) driver, and confirmed `unsat` offline.
    #[test]
    fn strict_tightening_unsat_via_cdclt() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let gt = arena.int_gt(x, zero).expect("x>0");
        let lt = arena.int_lt(x, one).expect("x<1");
        let assertions = [gt, lt];

        assert_eq!(
            check_qf_lia_online_cdclt(&arena, &assertions, &SolverConfig::default())
                .expect("decidable"),
            CheckResult::Unsat,
        );
        assert_eq!(
            check_with_lia_simplex(&arena, &assertions).expect("offline decidable"),
            CheckResult::Unsat,
            "offline route agrees",
        );
    }

    /// A disjunctive refutation needing the Boolean search: `(x<0 ∨ x>0) ∧ x=0`.
    #[test]
    fn disjunctive_refutation_via_cdclt() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = arena.int_const(0);
        let lt0 = arena.int_lt(x, zero).expect("x<0");
        let gt0 = arena.int_gt(x, zero).expect("x>0");
        let disj = arena.or(lt0, gt0).expect("or");
        let eq0 = arena.eq(x, zero).expect("x=0");

        assert_eq!(
            check_qf_lia_online_cdclt(&arena, &[disj, eq0], &SolverConfig::default())
                .expect("decidable"),
            CheckResult::Unsat,
        );
    }

    /// A `sat` instance: the reconstructed integer model must replay.
    #[test]
    fn decides_sat_and_replays_via_cdclt() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let five = arena.int_const(5);
        let ten = arena.int_const(10);
        let ge = arena.int_ge(x, five).expect("x>=5");
        let le = arena.int_le(x, ten).expect("x<=10");

        let verdict = check_qf_lia_online_cdclt(&arena, &[ge, le], &SolverConfig::default())
            .expect("decidable");
        assert!(
            matches!(verdict, CheckResult::Sat(_)),
            "expected sat: {verdict:?}"
        );
    }

    /// A zero-duration deadline must degrade to `Unknown`, never a verdict.
    #[test]
    fn deadline_yields_unknown() {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let zero = arena.int_const(0);
        let one = arena.int_const(1);
        let gt = arena.int_gt(x, zero).expect("x>0");
        let lt = arena.int_lt(x, one).expect("x<1");
        let cfg = SolverConfig::default().with_timeout(std::time::Duration::ZERO);
        let r = check_qf_lia_online_cdclt(&arena, &[gt, lt], &cfg).expect("result");
        assert!(
            matches!(r, CheckResult::Unknown(_)),
            "zero-timeout → Unknown: {r:?}"
        );
    }

    /// Termination discipline: the eager [`LiaTheory`] is complete and monotone per
    /// assert, so the driver must decide within a tight, deterministic step budget —
    /// never trip it (a trip would signal a livelock). Runs several Boolean-structured
    /// shapes with a small budget and confirms each verdict matches the offline route.
    #[test]
    fn terminates_within_a_tight_step_budget() {
        // (shape assertions, offline conjunctive check applies only to conjunctions;
        // we cross-check the CDCL(T) verdict against the sibling online route.)
        let shapes: &[fn(&mut TermArena) -> Vec<TermId>] = &[
            // UNSAT strict tightening.
            |arena| {
                let x = ivar(arena, "x");
                let zero = arena.int_const(0);
                let one = arena.int_const(1);
                vec![
                    arena.int_gt(x, zero).unwrap(),
                    arena.int_lt(x, one).unwrap(),
                ]
            },
            // UNSAT disjunction ∧ pin.
            |arena| {
                let x = ivar(arena, "x");
                let zero = arena.int_const(0);
                let lt0 = arena.int_lt(x, zero).unwrap();
                let gt0 = arena.int_gt(x, zero).unwrap();
                let disj = arena.or(lt0, gt0).unwrap();
                let eq0 = arena.eq(x, zero).unwrap();
                vec![disj, eq0]
            },
            // SAT bounded range.
            |arena| {
                let x = ivar(arena, "x");
                let y = ivar(arena, "y");
                let five = arena.int_const(5);
                let ten = arena.int_const(10);
                vec![
                    arena.int_ge(x, five).unwrap(),
                    arena.int_le(y, ten).unwrap(),
                ]
            },
        ];

        for (i, build) in shapes.iter().enumerate() {
            let mut arena = TermArena::new();
            let assertions = build(&mut arena);

            // Replicate the entry point but drive with a tight step budget so a
            // livelock trips it deterministically rather than hanging.
            let mut atom_terms: Vec<TermId> = Vec::new();
            let mut seen = HashSet::new();
            for &a in &assertions {
                collect_lia_atoms(&arena, a, &mut atom_terms, &mut seen);
            }
            let mut enc = Encoder::new(&atom_terms);
            let mut clauses: Vec<Vec<Lit>> = Vec::new();
            for &a in &assertions {
                let top = enc.encode(&arena, a, &mut clauses).expect("encodable");
                clauses.push(vec![Lit {
                    var: top,
                    positive: true,
                }]);
            }
            let driver_clauses: Vec<Vec<CdcltLit>> = clauses
                .iter()
                .map(|c| {
                    c.iter()
                        .map(|l| CdcltLit {
                            var: l.var,
                            positive: l.positive,
                        })
                        .collect()
                })
                .collect();
            let atom_count = atom_terms.len();
            let mut theory = CdcltLiaTheory::new(&arena, &atom_terms, None);
            let mut solver = CdclT::new(enc.var_count, atom_count, driver_clauses, None)
                .with_step_budget(50_000);
            let outcome = solver.solve(&mut theory);
            assert!(
                !solver.step_budget_hit(),
                "shape {i}: LIA CDCL(T) driver tripped the step budget (livelock)"
            );
            assert_ne!(
                outcome,
                Outcome::Unknown,
                "shape {i}: Unknown with no deadline and no budget trip"
            );
            // Verdict must match the sibling online route on the same query.
            let sibling = crate::lia_online::check_qf_lia_online(
                &arena,
                &assertions,
                &SolverConfig::default(),
            )
            .expect("sibling decidable");
            match (&outcome, &sibling) {
                (Outcome::Unsat, CheckResult::Unsat) | (Outcome::Sat, CheckResult::Sat(_)) => {}
                (Outcome::Sat, CheckResult::Unsat) | (Outcome::Unsat, CheckResult::Sat(_)) => {
                    panic!("shape {i}: CDCL(T) {outcome:?} disagrees with sibling {sibling:?}")
                }
                other => panic!("shape {i}: unexpected pairing {other:?}"),
            }
        }
    }
}
