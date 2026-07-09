//! Linear real arithmetic (`QF_LRA`) on the **generic online CDCL(T) driver**
//! [`crate::cdclt::CdclT`] (ADR-0055 criterion 2, slice a-lra — the LRA companion
//! to the [`crate::lia_theory`] integer slice).
//!
//! [`crate::euf_egraph::check_qf_uf_online_cdclt`] proved the generic driver drives
//! EUF; [`crate::string_theory`] drives strings; [`crate::lia_theory`] drives integer
//! arithmetic. This module drives **linear real arithmetic** through the *same*
//! [`CdclT`], establishing that the one theory-agnostic search spine serves a fourth
//! theory. It is the CDCL(T)-driver counterpart to the self-contained
//! [`crate::lra_online::check_qf_lra_online`] search (whose `DPLL(T)` loop lives in
//! [`crate::lra_online`]): the Boolean skeleton, the Tseitin [`Encoder`], and the
//! incremental [`LraTheory`] are identical — only the search loop differs.
//!
//! ## Wrap, don't rewrite
//! The heavy lifting is the already-validated [`LraTheory`] from
//! [`crate::lra_online`]: it *is* a [`TheorySolver`] (`assert` re-decides real
//! feasibility of the live asserted set by exact-rational Fourier–Motzkin
//! elimination; `push`/`pop` snapshot the assert stack in lockstep; conflict cores
//! are the Farkas-participating subset of asserted atoms). So this slice adds **no**
//! new arithmetic reasoning. The only gap between [`LraTheory`] and the generic
//! driver is the driver's documented *trigger-literal precondition*: its 1-UIP
//! conflict analysis requires every theory conflict to carry a
//! current-decision-level literal (the `c9d332c1` invariant). [`CdcltLraTheory`] is
//! a thin adapter that guarantees exactly that — see its docs.
//!
//! ## Granularity & propagation
//! - **Per-assert consistency (eager).** The wrapped [`LraTheory`] re-decides
//!   feasibility of the live set on every theory-atom assignment. This makes the
//!   theory **complete per assert**: a wrong `sat` is impossible because every total
//!   Boolean assignment is theory-checked. Fourier–Motzkin always terminates under
//!   the deterministic row cap, but can still be expensive, so the caller's absolute
//!   deadline is threaded into every feasibility, propagation, and model-rebuild
//!   pass. Termination of the *driver* is the standard argument (each conflict,
//!   carrying its trigger literal, forces a strict backjump), with deadline/step
//!   budgets as backstops.
//! - **Propagation forwarded.** [`CdcltLraTheory::propagate`] forwards the
//!   already-validated [`LraTheory::propagate`] negation probes into the generic
//!   driver, so entailed order atoms can be assigned before a decision. Completeness
//!   still comes from per-assert feasibility; propagation is a pruning layer whose
//!   reasons are replayed as theory clauses by [`CdclT`].
//!
//! ## Soundness posture (no new trust surface over the offline route)
//! - `unsat` is a sound refutation. Its theory conflict clauses are `¬core` where
//!   `core` is a subset of asserted literals whose constraints carry a nonzero Farkas
//!   multiplier in the derived contradiction — the *same* explained-conflict
//!   machinery the offline [`crate::lra_online::check_qf_lra_online`] / the trusted
//!   [`crate::lra::check_with_lra`] route relies on; 1-UIP resolution over the mixed
//!   clause database is standard, model-independent inference. Tests gate every
//!   online `unsat` against those offline routes.
//! - `sat` is **not** trusted from the driver: a candidate real model is
//!   reconstructed from the live atoms ([`LraTheory::real_model`], re-running the
//!   trusted Fourier–Motzkin reconstruction), Boolean skeleton leaves are injected
//!   from the driver trail, and the model is **replayed** against the original
//!   assertions — a non-replay yields [`CheckResult::Unknown`], never a wrong `sat`.
//! - Deadline-bounded (`config.timeout`) with the driver's step budget as the
//!   defense-in-depth backstop, so the search degrades to `Unknown` under a
//!   deterministic resource bound.
//!
//! The pure `QF_LRA` front door now tries this generic route first (ADR-0060's
//! 2026-07-09 update). Budget exhaustion is terminal for that query; structural
//! or arithmetic-incompleteness declines retain the established mixed fallback.

use std::collections::HashSet;
use std::time::Instant;

use axeyum_ir::{Sort, TermArena, TermId, TermNode, Value};

use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::cdclt::{CdclT, Lit as CdcltLit, Outcome};
use crate::euf_egraph::{TheoryLit, TheoryProp, TheorySolver};
use crate::lra_online::{Encoder, Lit, LraTheory, collect_lra_atoms, replays};
use crate::model::Model;

/// The eager per-assert Fourier–Motzkin theory is not an efficient or stack-safe
/// online choice above this many distinct atoms. Larger formulas return a
/// first-class resource-limit result before atom normalization.
const MAX_ONLINE_LRA_ATOMS: usize = 1_024;

/// Adapts the validated online [`LraTheory`] to the generic [`CdclT`] driver's
/// **trigger-literal precondition**.
///
/// [`LraTheory`] already implements [`TheorySolver`], so it could in principle be
/// handed to [`CdclT`] verbatim. The one behavioural gap is the driver's documented
/// precondition (the `c9d332c1` invariant): its 1-UIP analysis ([`CdclT`]) resolves
/// the conflict clause against current-decision-level literals, so **every theory
/// conflict must contain the just-asserted literal**, which sits at the current
/// level. [`LraTheory`]'s Farkas-derived cores almost always retain it — a
/// refutation of a set that was feasible before this assert *must* involve the new
/// constraint — but a degenerate multiplier vector (or the `rows_to_core` fallback
/// to the full asserted set, which does include it) could in principle name a core
/// the trigger is absent from. This wrapper closes that gap deterministically: on
/// any conflict it ensures the trigger literal `(index, value)` is present. Adding
/// one more *currently-asserted* literal to an `unsat` core keeps it `unsat` (a
/// superset of an infeasible set is infeasible), so `¬core` remains a valid theory
/// lemma — the fix is sound and never widens a verdict.
///
/// Theory propagation forwards the wrapped [`LraTheory`]'s checked negation-probe
/// entailments; see the module docs.
struct CdcltLraTheory {
    inner: LraTheory,
}

impl CdcltLraTheory {
    /// Wraps a fresh [`LraTheory`] over `atom_terms` (per-assert exact-rational
    /// feasibility), bounded by the online driver's absolute `deadline`.
    fn new(arena: &TermArena, atom_terms: &[TermId], deadline: Option<Instant>) -> Option<Self> {
        Some(Self {
            inner: LraTheory::new_with_deadline(arena, atom_terms, deadline)?,
        })
    }

    /// The wrapped theory, for model reconstruction after a `sat` verdict.
    fn inner(&self) -> &LraTheory {
        &self.inner
    }
}

impl TheorySolver for CdcltLraTheory {
    fn assert(&mut self, index: usize, value: bool) -> Result<(), Vec<TheoryLit>> {
        self.inner.assert(index, value).map_err(|mut core| {
            // Guarantee the driver's trigger-literal precondition: fold the
            // just-asserted (current-decision-level) literal into the core when the
            // Farkas core dropped it. Sound — a currently-asserted literal added to
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
        self.inner.propagate()
    }
}

/// Decides a `QF_LRA` query (an arbitrary Boolean combination of linear real
/// order/equality atoms) via the **generic online CDCL(T)** driver `CdclT` with
/// [`LraTheory`] as the theory (ADR-0055 criterion 2, slice a-lra). The
/// CDCL(T)-driver counterpart to [`crate::lra_online::check_qf_lra_online`]: the
/// skeleton, the Tseitin encoder, and the incremental theory are identical; the
/// search is the theory-agnostic `CdclT` that already drives EUF, strings, and
/// integer arithmetic.
///
/// Verdict discipline (see the module docs): `unsat` is a sound refutation carrying
/// no new trust surface over the offline route; `sat` is a driver assignment whose
/// reconstructed real model is **replayed** against the original assertions (a
/// non-replay is `Unknown`, never a wrong `sat`); the search is deadline-bounded.
///
/// Returns [`CheckResult::Unknown`] when there are no `LRA` atoms or the Boolean
/// skeleton has structure the encoder does not cover — the same conservative
/// give-ups as [`crate::lra_online::check_qf_lra_online`]. This is the default
/// first route for pure `QF_LRA`; non-budget incompleteness can still fall back.
///
/// # Errors
///
/// Never returns `Err` in this slice (every give-up is a conservative
/// [`CheckResult::Unknown`]); the [`SolverError`] return type matches the sibling
/// [`crate::lra_online::check_qf_lra_online`] for interchange.
pub fn check_qf_lra_online_cdclt(
    arena: &TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    // Distinct real atoms — the theory's atom indices and the first `atom_count`
    // skeleton variables.
    let mut atom_terms: Vec<TermId> = Vec::new();
    let mut seen = HashSet::new();
    for &a in assertions {
        collect_lra_atoms(arena, a, &mut atom_terms, &mut seen);
    }
    if atom_terms.len() > MAX_ONLINE_LRA_ATOMS {
        return Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::ResourceLimit,
            detail: format!(
                "online CDCL(T) LRA atom cap exceeded ({} > {MAX_ONLINE_LRA_ATOMS})",
                atom_terms.len()
            ),
        }));
    }
    if atom_terms.is_empty() {
        return Ok(CheckResult::Unknown(unknown(
            "no linear-real atoms for the online CDCL(T) LRA path",
        )));
    }

    let mut enc = Encoder::new(&atom_terms);
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    for &assertion in assertions {
        let Some(top) = enc.encode(arena, assertion, &mut clauses) else {
            return Ok(CheckResult::Unknown(unknown(
                "boolean skeleton outside the online CDCL(T) LRA encoder",
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
    let Some(mut theory) = CdcltLraTheory::new(arena, &atom_terms, deadline) else {
        return Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Timeout,
            detail: "timeout in the online CDCL(T) LRA driver".to_owned(),
        }));
    };
    let mut solver = CdclT::new(enc.var_count, atom_count, driver_clauses, deadline);
    match solver.solve(&mut theory) {
        Outcome::Unsat => Ok(CheckResult::Unsat),
        Outcome::Unknown => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Timeout,
            detail: "timeout in the online CDCL(T) LRA driver".to_owned(),
        })),
        Outcome::Sat => {
            // Reconstruct a real model from the live atoms (via the trusted
            // Fourier–Motzkin reconstruction), inject Boolean skeleton leaves from
            // the driver trail, and replay against the originals — the soundness gate.
            let Some(mut model) = theory.inner().real_model() else {
                return Ok(CheckResult::Unknown(unknown(
                    "online CDCL(T) LRA model did not replay (arithmetic outside the incremental engine)",
                )));
            };
            add_boolean_leaf_values(arena, &enc, atom_count, &solver, &mut model);
            if replays(arena, assertions, &model) {
                Ok(CheckResult::Sat(model))
            } else {
                Ok(CheckResult::Unknown(unknown(
                    "online CDCL(T) LRA model did not replay (arithmetic outside the incremental engine)",
                )))
            }
        }
    }
}

/// Injects each genuine Bool skeleton leaf (a skeleton variable that is not a
/// registered `LRA` atom, so absent from the reconstructed real model) from the
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
            continue; // a registered LRA atom, handled by the real model
        }
        if let TermNode::Symbol(symbol) = arena.node(term)
            && arena.sort_of(term) == Sort::Bool
            && let Some(value) = solver.value(var)
        {
            model.set(*symbol, Value::Bool(value));
        }
    }
}

/// A classified `unknown` reason for the online CDCL(T) LRA path.
fn unknown(detail: impl Into<String>) -> UnknownReason {
    UnknownReason {
        kind: UnknownKind::Incomplete,
        detail: detail.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lra::check_with_lra;
    use axeyum_ir::Rational;

    fn rvar(arena: &mut TermArena, name: &str) -> TermId {
        let s = arena.declare(name, Sort::Real).expect("declare real");
        arena.var(s)
    }

    fn rconst(arena: &mut TermArena, n: i128) -> TermId {
        arena.real_const(Rational::integer(n))
    }

    #[test]
    fn oversized_atom_set_declines_before_online_theory_construction() {
        let mut arena = TermArena::new();
        let zero = rconst(&mut arena, 0);
        let mut assertions = Vec::with_capacity(MAX_ONLINE_LRA_ATOMS + 1);
        for index in 0..=MAX_ONLINE_LRA_ATOMS {
            let x = rvar(&mut arena, &format!("x{index}"));
            assertions.push(arena.real_ge(x, zero).expect("x>=0"));
        }

        let CheckResult::Unknown(reason) =
            check_qf_lra_online_cdclt(&arena, &assertions, &SolverConfig::default())
                .expect("result")
        else {
            panic!("oversized generic LRA query must decline");
        };
        assert_eq!(reason.kind, UnknownKind::ResourceLimit);
        assert!(reason.detail.contains("atom cap exceeded"));
    }

    /// The wrapper must always fold the just-asserted (current-level) literal into a
    /// conflict core — the driver's trigger-literal precondition.
    #[test]
    fn wrapper_conflict_core_carries_the_trigger() {
        // x < 0  and  x > 0: real-infeasible; the second assert triggers it.
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let lt = arena.real_lt(x, zero).expect("x<0");
        let gt = arena.real_gt(x, zero).expect("x>0");

        let mut theory = CdcltLraTheory::new(&arena, &[lt, gt], None).expect("unbounded theory");
        assert!(theory.assert(0, true).is_ok());
        let core = theory.assert(1, true).expect_err("real-infeasible");
        assert!(
            core.iter().any(|l| l.atom == 1 && l.value),
            "conflict core must carry the just-asserted trigger literal (atom 1, true): {core:?}"
        );
    }

    /// A trigger the Farkas core keeps is not duplicated by the wrapper.
    #[test]
    fn wrapper_does_not_duplicate_a_kept_trigger() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let lt = arena.real_lt(x, zero).expect("x<0");
        let gt = arena.real_gt(x, zero).expect("x>0");

        let mut theory = CdcltLraTheory::new(&arena, &[lt, gt], None).expect("unbounded theory");
        assert!(theory.assert(0, true).is_ok());
        let core = theory.assert(1, true).expect_err("infeasible");
        let occurrences = core.iter().filter(|l| l.atom == 1).count();
        assert_eq!(
            occurrences, 1,
            "trigger atom appears exactly once: {core:?}"
        );
    }

    /// The generic-driver wrapper must expose the underlying `LraTheory`
    /// propagation reasons unchanged: `x >= 1` entails `x > 0`.
    #[test]
    fn wrapper_forwards_lra_theory_propagation() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let one = rconst(&mut arena, 1);
        let ge_one = arena.real_ge(x, one).expect("x>=1");
        let gt_zero = arena.real_gt(x, zero).expect("x>0");

        let mut theory =
            CdcltLraTheory::new(&arena, &[ge_one, gt_zero], None).expect("unbounded theory");
        theory.assert(0, true).expect("x>=1 feasible");
        let props = theory.propagate();
        assert!(
            props.iter().any(|p| {
                p.lit.atom == 1 && p.lit.value && p.reason.iter().any(|r| r.atom == 0 && r.value)
            }),
            "expected propagation x>=1 entails x>0 with reason x>=1, got {props:?}"
        );
    }

    /// A strict-bound `unsat` (`x < 0 ∧ x > 0`) decided by the CDCL(T) driver, and
    /// confirmed `unsat` offline.
    #[test]
    fn strict_bounds_unsat_via_cdclt() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let lt = arena.real_lt(x, zero).expect("x<0");
        let gt = arena.real_gt(x, zero).expect("x>0");
        let assertions = [lt, gt];

        assert_eq!(
            check_qf_lra_online_cdclt(&arena, &assertions, &SolverConfig::default())
                .expect("decidable"),
            CheckResult::Unsat,
        );
        assert_eq!(
            check_with_lra(&arena, &assertions).expect("offline decidable"),
            CheckResult::Unsat,
            "offline route agrees",
        );
    }

    /// A disjunctive refutation needing the Boolean search: `(x<0 ∨ x>0) ∧ x=0`.
    #[test]
    fn disjunctive_refutation_via_cdclt() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let lt0 = arena.real_lt(x, zero).expect("x<0");
        let gt0 = arena.real_gt(x, zero).expect("x>0");
        let disj = arena.or(lt0, gt0).expect("or");
        let eq0 = arena.eq(x, zero).expect("x=0");

        assert_eq!(
            check_qf_lra_online_cdclt(&arena, &[disj, eq0], &SolverConfig::default())
                .expect("decidable"),
            CheckResult::Unsat,
        );
    }

    /// A `sat` instance: the reconstructed real model must replay.
    #[test]
    fn decides_sat_and_replays_via_cdclt() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let five = rconst(&mut arena, 5);
        let ten = rconst(&mut arena, 10);
        let ge = arena.real_ge(x, five).expect("x>=5");
        let le = arena.real_le(x, ten).expect("x<=10");

        let verdict = check_qf_lra_online_cdclt(&arena, &[ge, le], &SolverConfig::default())
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
        let x = rvar(&mut arena, "x");
        let zero = rconst(&mut arena, 0);
        let lt = arena.real_lt(x, zero).expect("x<0");
        let gt = arena.real_gt(x, zero).expect("x>0");
        let cfg = SolverConfig::default().with_timeout(std::time::Duration::ZERO);
        let r = check_qf_lra_online_cdclt(&arena, &[lt, gt], &cfg).expect("result");
        assert!(
            matches!(r, CheckResult::Unknown(_)),
            "zero-timeout → Unknown: {r:?}"
        );
    }

    /// Termination discipline: the eager [`LraTheory`] is complete and its
    /// Fourier–Motzkin feasibility check always terminates (no branch-and-bound), so
    /// the driver must decide within a tight, deterministic step budget — never trip
    /// it (a trip would signal a livelock). Runs several Boolean-structured shapes
    /// with a small budget and confirms each verdict matches the sibling online route.
    #[test]
    fn terminates_within_a_tight_step_budget() {
        let shapes: &[fn(&mut TermArena) -> Vec<TermId>] = &[
            // UNSAT strict bounds.
            |arena| {
                let x = rvar(arena, "x");
                let zero = rconst(arena, 0);
                vec![
                    arena.real_lt(x, zero).unwrap(),
                    arena.real_gt(x, zero).unwrap(),
                ]
            },
            // UNSAT disjunction ∧ pin.
            |arena| {
                let x = rvar(arena, "x");
                let zero = rconst(arena, 0);
                let lt0 = arena.real_lt(x, zero).unwrap();
                let gt0 = arena.real_gt(x, zero).unwrap();
                let disj = arena.or(lt0, gt0).unwrap();
                let eq0 = arena.eq(x, zero).unwrap();
                vec![disj, eq0]
            },
            // SAT bounded range.
            |arena| {
                let x = rvar(arena, "x");
                let y = rvar(arena, "y");
                let five = rconst(arena, 5);
                let ten = rconst(arena, 10);
                vec![
                    arena.real_ge(x, five).unwrap(),
                    arena.real_le(y, ten).unwrap(),
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
                collect_lra_atoms(&arena, a, &mut atom_terms, &mut seen);
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
            let mut theory =
                CdcltLraTheory::new(&arena, &atom_terms, None).expect("unbounded theory");
            let mut solver = CdclT::new(enc.var_count, atom_count, driver_clauses, None)
                .with_step_budget(50_000);
            let outcome = solver.solve(&mut theory);
            assert!(
                !solver.step_budget_hit(),
                "shape {i}: LRA CDCL(T) driver tripped the step budget (livelock)"
            );
            assert_ne!(
                outcome,
                Outcome::Unknown,
                "shape {i}: Unknown with no deadline and no budget trip"
            );
            // Verdict must match the sibling online route on the same query.
            let sibling = crate::lra_online::check_qf_lra_online(
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

    /// End-to-end through `CdclT`: the wrapper's forwarded propagation must assign
    /// an entailed theory atom before the driver needs to decide it.
    #[test]
    fn cdclt_driver_counts_forwarded_lra_propagation() {
        let mut arena = TermArena::new();
        let x = rvar(&mut arena, "x");
        let b_sym = arena.declare("b", Sort::Bool).expect("declare bool");
        let b = arena.var(b_sym);
        let zero = rconst(&mut arena, 0);
        let one = rconst(&mut arena, 1);
        let ge_one = arena.real_ge(x, one).expect("x>=1");
        let gt_zero = arena.real_gt(x, zero).expect("x>0");
        let clause = arena.or(gt_zero, b).expect("gt_zero or b");
        let assertions = [ge_one, clause];

        let mut atom_terms: Vec<TermId> = Vec::new();
        let mut seen = HashSet::new();
        for &a in &assertions {
            collect_lra_atoms(&arena, a, &mut atom_terms, &mut seen);
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
        let mut theory = CdcltLraTheory::new(&arena, &atom_terms, None).expect("unbounded theory");
        let mut solver = CdclT::new(enc.var_count, atom_count, driver_clauses, None);

        assert_eq!(solver.solve(&mut theory), Outcome::Sat);
        assert!(
            solver.theory_propagations() > 0,
            "expected the LRA propagation path to fire"
        );
        assert_eq!(solver.value(1), Some(true), "x>0 should be propagated");
    }
}
