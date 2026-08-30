# Notes: l1-g0-module-baseline

Detail moved out of [`../status/l1-g0-module-baseline.md`](../status/l1-g0-module-baseline.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

All 9 guards (comment/string-literal decoy stripping, internal/external edge
classification, sink counting, the lexicographic degree tie-break, the three
absence cases, and the two drift-detection conditions) are mutation-verified
in `scripts/tests/test-module-baseline-mutations.sh`: each deleted in a
scratch copy (never the tracked worktree), each kills exactly one test in
`scripts/tests/test-module-baseline.py`, never zero, never more than one.
Getting to "exactly one" took two real fixes to the test fixture itself,
recorded in the commit message and ADR-0805 — an earlier fixture shared
modules between two checks and one mutation killed two tests at once, and a
"missing directory" guard turned out to be operationally subsumed by the
"no Mathlib/ subdirectory" guard for every input, so the test now
discriminates on the raised exception's message text rather than just its
type.

Registered as `just module-baseline` / `just module-baseline-controls` and
three `step` lines in `scripts/check.sh` (`module-baseline`,
`module-baseline-controls`, `module-baseline-mutations`), appended to
`check:`'s dependency list. `just --list` and
`AXEYUM_CHECK_LIST=1 scripts/check.sh` both parse cleanly and list the three
new steps.

**What the receipt does not pin, stated once and left in ADR-0805 rather than
repeated here:** it is silent on which declarations live inside each module,
their types, proofs, or any dependency finer than "this file imports that
file" — that is G1's job (declaration graph) and G2's (join to Axeyum
state), against `artifacts/library-artifact/`, a sibling lane's
(`l1-c0-artifact-contract`) contract that this lane did not touch.

**Next for whoever picks up G1:** build the declaration/type/proof graph
over the population this receipt's module set defines, joined against
`artifacts/library-artifact/` once that contract lands, per the roadmap's G1
exit criteria (complete selected-population coverage, resolved endpoints,
acyclicity where required, deletion mutations for rows and edges).
