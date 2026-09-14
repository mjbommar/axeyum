#!/usr/bin/env python3
"""ZERO-INST -- register the Boolean-skeleton rung's guards with
`scripts/tests/mutation_controls.py`.

Three mutations, each removing exactly one load-bearing guard:

  1. the lever FAILS OPEN            -- the polarity guard
  2. the liveness floor is removed   -- `abstracted == 0` no longer declines
  3. the maximality rule is removed  -- nested quantifiers get abstracted too,
                                        which is the one change that would make
                                        the abstraction UNSOUND

Mutation 3 is the important one: a constant cannot track a bound variable, so
abstracting a quantifier that sits under a binder is not a weakening and can
manufacture a wrong `unsat`.
"""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
CTRL = ROOT / 'scripts/tests/mutation_controls.py'

BLOCK = '''

# --------------------------------------------------------------------------
# `solver-bool-skeleton-rung` — the pre-instantiation Boolean-abstraction
# refutation rung (ADR-2025).
#
# Three guards, and they fail in three different directions.  The polarity
# guard failing OPEN would make an A/B measure the armed arm against itself and
# report the zero as a null.  The liveness floor failing would let a query with
# no quantifiers at all be refuted under this rung's name, which is the
# ordinary quantifier-free route wearing a costume.  And the maximality rule is
# the SOUNDNESS guard: abstracting a quantifier nested under a binder replaces a
# formula that varies with the bound variable by a constant that cannot, which
# is not a weakening and can forge a wrong `unsat`.
# --------------------------------------------------------------------------

SUITES["solver-bool-skeleton-rung"] = (
    "crates/axeyum-solver/src/auto.rs",
    Cargo(
        ("-p", "axeyum-solver", "--lib", "--features", "full", "bool_skeleton"),
        "solver-bool-skeleton-rung",
    ),
    [
        (
            # The lever fails OPEN: every spelling arms the rung.
            "the lever's exact-spelling polarity guard",
            '    raw == Some("1")',
            "    raw != Some(\\"\\\\0never\\")",
        ),
        (
            # A query that abstracted nothing is no longer declined.
            "the abstraction-liveness floor",
            "    if abstracted == 0 {\\n        return Ok(false);\\n    }",
            "    if false {\\n        return Ok(false);\\n    }",
        ),
        (
            # Maximality removed: descend into quantifier bodies as well, so a
            # nested quantifier under a binder is abstracted to a constant.
            "the maximality rule that keeps the abstraction a weakening",
            "            if matches!(op, Op::Forall(_) | Op::Exists(_)) {",
            "            if matches!(op, Op::Forall(_) | Op::Exists(_)) && children_done {",
        ),
    ],
)
'''


def main():
    s = CTRL.read_text()
    if 'solver-bool-skeleton-rung' in s:
        print('already applied; nothing to do')
        return
    if 'SUITES["solver-occurrence-pass-admission"]' not in s:
        sys.exit('ABORT: expected registry not found')
    CTRL.write_text(s.rstrip('\n') + '\n' + BLOCK)
    print(f'patched {CTRL}')


main()
