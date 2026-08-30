# Lane: l1-g0-module-baseline — reproduce the Mathlib module-import baseline (G0)

<!-- plan-section: lane-status -->

**G0 exit criteria met (`DONE`, l1-g0-module-baseline, 2026-08-30).**
`docs/plan/graph-directed-library-roadmap-2026-08-30.md` phase G0 asked for a
compact, reproducible receipt of the Mathlib module-import graph without
vendoring a checkout, with source-or-parser drift failing the gate. Both are
in place: [ADR-0805](../../research/09-decisions/adr-0805-the-module-baseline-receipt-is-a-hash-and-a-parser-not-a-vendored-checkout.md)
records the design and evidence.

`scripts/gen-module-baseline.py` / `scripts/lib/module_baseline.py` parse
`Mathlib/**/*.lean` under whatever checkout `--mathlib-dir` names (default:
the pinned toolchain checkout `scripts/provision-lean-import-toolchain.sh`
provisions, commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`) into a
compact receipt at `artifacts/module-baseline/receipt.json`: source commit +
content tree hash, parser sha256, module/edge totals, top-indegree/outdegree
rows, no-importer sink count.

**This is the full parse over all 8,094 `.lean` files, not a bounded
subset** — it completes in roughly 7-9 s per invocation, so there was no
need to reduce scope. Measured totals match the roadmap's hand-measured
evidence baseline exactly: 8,094 modules, 25,495 internal edges, 1,476
no-importer sinks, `Mathlib.Init` 193 importers, `Mathlib.Tactic.Common` 69,
`Mathlib.Algebra.Ring.Defs` 43, `Mathlib.Tactic` outdegree 336.

`scripts/check-module-baseline.py` re-parses the source TWICE per invocation
(so "two runs reproduce the receipt" is a standing, mechanically-checked
property rather than a one-time human observation) and diagnoses SOURCE_DRIFT
and PARSER_DRIFT as independently-firing reasons — verified by two real
subprocess scenarios, not simulated: a fixture content change with the
commit label held fixed fires only SOURCE_DRIFT; a behaviour-preserving
parser edit (appended comment, same logic, different sha256) fires only
PARSER_DRIFT. Three absence cases (missing directory, no `Mathlib/`
subdirectory, zero `.lean` files parsed) each raise before any receipt is
written.

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

<!-- plan-section: landed-changes -->

| 2026-08-30 | `1ec34c8e1` | Initial module-import parser + receipt generator/checker, verified against the full pinned Mathlib checkout (8,094 modules, 25,495 internal edges, 1,476 sinks, matching the roadmap's evidence baseline exactly); two runs byte-identical. |
| 2026-08-30 | `8e337c9e5` | 12-test suite + 9-mutation harness against a synthetic fixture (all 9 guards kill exactly one test); registered `just module-baseline`/`module-baseline-controls` and three `check.sh` steps. |
