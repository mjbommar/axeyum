#!/usr/bin/env python3
"""ZERO-INST -- make the rung's remaining guards reachable by a test.

`mutation_controls.py` reported two things that are not results, and both are
fixed here rather than explained away:

  SURVIVED       the abstraction-liveness floor -- no test could reach it,
                 because the whole function early-returns on the OFF lever and
                 the tests cannot set process environment.  Split the env gate
                 from the body so the body is callable.

  AMBIGUOUS      the maximality rule -- the anchor `if matches!(op,
                 Op::Forall(_) | Op::Exists(_)) {` occurs three times in
                 auto.rs.  Name the rule, so there is one place to mutate and
                 the mutation is a *behaviour* change rather than a guess.
"""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
AUTO = ROOT / 'crates/axeyum-solver/src/auto.rs'

SPLIT_OLD = '''    if !bool_skeleton_probe_enabled() {
        return Ok(false);
    }
    let Some(total) = config.timeout else {'''

SPLIT_NEW = '''    if !bool_skeleton_probe_enabled() {
        return Ok(false);
    }
    skeleton_refutes_quantified_query_armed(arena, assertions, config)
}

/// [`skeleton_refutes_quantified_query`] with the env gate already passed.
///
/// Split out for the same reason as [`parse_bool_skeleton_lever`]: the rung's
/// own guards -- the liveness floor and the quantifier-free postcondition --
/// are unreachable from a test while the OFF lever short-circuits the whole
/// function, and a guard no test can reach is decoration.
/// `mutation_controls.py` reported the liveness floor as SURVIVED before this
/// split.
// dispatch-family fn: keeps `Result` for uniformity with sibling routes.
#[allow(clippy::unnecessary_wraps)]
fn skeleton_refutes_quantified_query_armed(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    let Some(total) = config.timeout else {'''

MAX_OLD = '''            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                // MAXIMAL: stop here and do not descend. Descending would
                // abstract a quantifier nested under a binder, and a constant
                // cannot track a bound variable — that abstraction is not a
                // weakening, and would not be sound.
                let name = format!("qskel!{}", term.index());'''

MAX_NEW = '''            // MAXIMALITY, named so it is one place to read and one place to
            // break. A quantifier is replaced WHOLE and its body is never
            // visited. Descending would abstract a quantifier nested under a
            // binder — replacing a formula that varies with the bound variable
            // by a constant that cannot — which is not a weakening, and so not
            // sound. `bool_skeleton_abstracts_only_the_outermost_quantifier`
            // is the test that fails if this stops being true.
            let stop_at_this_quantifier = matches!(op, Op::Forall(_) | Op::Exists(_));
            if stop_at_this_quantifier {
                let name = format!("qskel!{}", term.index());'''


def main():
    s = AUTO.read_text()
    if 'fn skeleton_refutes_quantified_query_armed' in s:
        print('already applied; nothing to do')
        return
    for name, needle in (('env-gate split', SPLIT_OLD), ('maximality block', MAX_OLD)):
        if s.count(needle) != 1:
            sys.exit(f'ABORT: {name} matched {s.count(needle)} times, expected 1')
    s = s.replace(SPLIT_OLD, SPLIT_NEW, 1)
    s = s.replace(MAX_OLD, MAX_NEW, 1)
    AUTO.write_text(s)
    print(f'patched {AUTO}')


main()
