#!/usr/bin/env python3
"""ZERO-INST -- insert the Boolean-skeleton refutation rung into auto.rs.

Kept in the repository rather than run from a scratch file so the edit that
produced the measured binary is itself reviewable, and so a re-run is a
no-op rather than a second insertion (every anchor is asserted to occur
exactly once).
"""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
AUTO = ROOT / 'crates/axeyum-solver/src/auto.rs'

LEVER = r'''
/// Whether the Boolean-skeleton refutation rung is armed.
///
/// **Polarity: OFF is the shipped arm.** Unset, empty, or anything other than
/// exactly `1` returns `false` and the rung does not run, so a typo, a stale
/// export or a malformed value all fail **closed** to shipped behaviour.
///
/// Read through a `OnceLock` so an armed A/B cannot be perturbed mid-run and a
/// disarmed build pays one cached load per call.
fn bool_skeleton_probe_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var("AXEYUM_ZERO_INST_SKELETON").is_ok_and(|v| v == "1"))
}

/// Replaces every **maximal** quantified subterm of `assertions` by an opaque
/// Boolean atom, yielding the query's Boolean skeleton.
///
/// Returns the rewritten assertions and how many quantified occurrences were
/// abstracted, or `None` if the deadline passed or a helper could not be minted.
///
/// # Why this is sound
///
/// The skeleton is a **weakening**: an atom is unconstrained where the formula
/// it replaced was not, so every model of the original extends to a model of the
/// skeleton. Hence `skeleton unsat ⟹ original unsat`, which is the only
/// direction the caller uses. The converse is false and is never assumed.
///
/// Two occurrences of the *same* subterm share one atom. That is sound **here**
/// and not in general: the arena is hash-consed, so one `TermId` is one formula,
/// and a *maximal* quantified subterm sits under no quantifier, so it has no
/// bound variable whose value could differ between occurrences. A text-level
/// version of this abstraction does **not** have that property — `let` can bind
/// one name to two values — and ADR-2025's reference measurement had to carry a
/// `--fresh-per-occurrence` control for exactly that reason. Here the sharing is
/// semantic.
///
/// Atoms are minted with `TermArena::declare_internal`, whose namespace is
/// disjoint from user symbols, so a benchmark that declares `qskel!7` itself
/// cannot alias an abstraction atom.
fn quantifier_boolean_skeleton(
    arena: &mut TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Option<(Vec<TermId>, usize)> {
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut abstracted = 0usize;
    let mut out = Vec::with_capacity(assertions.len());

    for &root in assertions {
        let mut stack: Vec<(TermId, bool)> = vec![(root, false)];
        while let Some((term, children_done)) = stack.pop() {
            if past_deadline(deadline) {
                return None;
            }
            if memo.contains_key(&term) {
                continue;
            }
            let TermNode::App { op, args } = arena.node(term) else {
                memo.insert(term, term);
                continue;
            };
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                // MAXIMAL: stop here and do not descend. Descending would
                // abstract a quantifier nested under a binder, and a constant
                // cannot track a bound variable — that abstraction is not a
                // weakening, and would not be sound.
                let name = format!("qskel!{}", term.index());
                let symbol = arena.declare_internal(&name, Sort::Bool).ok()?;
                let atom = arena.var(symbol);
                memo.insert(term, atom);
                abstracted += 1;
                continue;
            }
            let args: Vec<TermId> = args.to_vec();
            if children_done {
                let mut rebuilt_args = Vec::with_capacity(args.len());
                for arg in &args {
                    rebuilt_args.push(*memo.get(arg)?);
                }
                let rebuilt = arena.rebuild_with_args(term, &rebuilt_args);
                memo.insert(term, rebuilt);
                continue;
            }
            stack.push((term, true));
            for arg in args {
                stack.push((arg, false));
            }
        }
        out.push(*memo.get(&root)?);
    }
    Some((out, abstracted))
}

/// Tries to refute the query's **Boolean skeleton** — every maximal quantified
/// subformula replaced by an opaque atom — before any instantiation runs.
///
/// # Why this is not [`ground_subset_refutes_quantified_query`]
///
/// That sibling **drops** every top-level conjunct that *contains* a quantifier.
/// This one **keeps** such a conjunct and abstracts only the quantified
/// subformulas *inside* it. The difference is the whole point: measured for
/// ADR-2025 on the nine `UFLIA`/`UFNIA` files cvc5 refutes with zero
/// instantiation tuples, the refutation lives inside **one** assertion — the
/// last, the negated verification condition — and that assertion contains
/// quantifiers. Dropping it throws the refutation away, which is why the ground
/// assertions alone are `sat` on 8 of those 9 (cvc5 and z3 agreeing) and the
/// sibling correctly declines.
///
/// On the 129-row winnable population, 15 files have a skeleton two independent
/// solvers refute — 11.6 %, Wilson `[7.2 %, 18.3 %]`.
///
/// Only `Unsat` is propagated; every other outcome leaves the ordinary
/// quantified ladder in charge, and the probe takes a tenth of the budget so it
/// cannot starve the routes it precedes.
// dispatch-family fn: keeps `Result` for uniformity with sibling routes.
#[allow(clippy::unnecessary_wraps)]
fn skeleton_refutes_quantified_query(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    if !bool_skeleton_probe_enabled() {
        return Ok(false);
    }
    let Some(total) = config.timeout else {
        return Ok(false);
    };
    let probe_budget = total / 10;
    if probe_budget.is_zero() {
        return Ok(false);
    }
    let probe_deadline = Instant::now().checked_add(probe_budget);

    let Some((skeleton, abstracted)) = quantifier_boolean_skeleton(arena, assertions, probe_deadline)
    else {
        return Ok(false);
    };
    // Liveness, not an assumption: abstracting zero occurrences hands back the
    // original query, and refuting THAT here would be the ordinary QF route
    // wearing this rung's name. Such a run has measured nothing.
    if abstracted == 0 {
        return Ok(false);
    }
    // The skeleton is quantifier-free by construction. If it is not, the rewrite
    // missed something and the result is not the abstraction this rung's
    // soundness argument is about, so decline rather than solve it.
    if contains_quantifier_within(arena, &skeleton, probe_deadline) != Some(false) {
        return Ok(false);
    }

    let Some(probe) = config_with_remaining_timeout(config, probe_deadline) else {
        return Ok(false);
    };
    match check_auto(arena, &skeleton, &probe) {
        Ok(CheckResult::Unsat) => Ok(true),
        Ok(CheckResult::Sat(_) | CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {
            Ok(false)
        }
        // An optional accelerator must never turn a query the established
        // portfolio can handle into an operational error.
        Err(_) => Ok(false),
    }
}

'''

ANCHOR = ('/// Clones a query configuration with only the wall-clock time '
          'remaining before\n/// `deadline`. `None` means the shared query '
          'budget has already expired.')

CALL_OLD = '''        route_trace::record_quant_rung_declined(
            route_trace::quant_rung::GROUND_SUBSET,
            DeclineReason::NotApplicable,
        );
    }'''

CALL_NEW = '''        route_trace::record_quant_rung_declined(
            route_trace::quant_rung::GROUND_SUBSET,
            DeclineReason::NotApplicable,
        );
        if skeleton_refutes_quantified_query(arena, assertions, config)? {
            route_trace::record_quant_rung_result(
                route_trace::quant_rung::BOOL_SKELETON,
                &CheckResult::Unsat,
            );
            return Ok(CheckResult::Unsat);
        }
        route_trace::record_quant_rung_declined(
            route_trace::quant_rung::BOOL_SKELETON,
            DeclineReason::NotApplicable,
        );
    }'''


def main():
    s = AUTO.read_text()
    if 'fn skeleton_refutes_quantified_query' in s:
        print('already applied; nothing to do')
        return
    for name, needle in (('lever anchor', ANCHOR), ('call site', CALL_OLD)):
        n = s.count(needle)
        if n != 1:
            sys.exit(f'ABORT: {name} matched {n} times, expected exactly 1')
    s = s.replace(ANCHOR, LEVER.strip() + '\n\n' + ANCHOR, 1)
    s = s.replace(CALL_OLD, CALL_NEW, 1)
    AUTO.write_text(s)
    print(f'patched {AUTO}')


main()
