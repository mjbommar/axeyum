# Notes: 290-depends-producer

Detail moved out of [`../status/290-depends-producer.md`](../status/290-depends-producer.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. It is the command CLAUDE.md's Commands section lists **standalone** —
   the one a lane is actually told to run when it touches a fact — not only
   a step buried in the two heavy aggregate gates. The drift this lane fixes
   (1054 edges, then 109 more) accumulated specifically because those two
   gates are periodic and expensive; wiring the same-day command is what
   catches it before it piles up.
2. `check-fact-depends-derived.py` was *already* registered in both
   `scripts/check.sh` (line ~126) and `justfile` (line ~274) before this
   lane started — that registration is untouched, so the periodic sweep is
   unchanged and this is additive, not a replacement.
3. Staying inside `scripts/` (this task's file scope) ruled out adding a new
   `justfile` recipe or a `hooks/pre-push` conditional block, both of which
   live outside it; `validate-facts.py` is the only "runs everywhere,
   already gated in both aggregate sweeps" surface inside scope.

`--skip-depends-derived` is the escape hatch for a fast schema-only
iteration loop while drafting a fact's JSON (it skips the subprocess
entirely, so it's instant); it is documented in the function's own docstring
as not a substitute for running the validator without it before landing a
fact, and neither aggregate gate ever passes it.

Verified: `python3 scripts/validate-facts.py` now prints the
`DEPENDS_DERIVED|...` line and fails closed if the checker fails; a fake
failing/OK subprocess pair confirms the wiring propagates the exit code both
ways (unit-tested, not just eyeballed).

## Out of scope, explicitly

The ~120 "kernel-route facts whose checker command names no theorem (not
enforced)" facts printed by the checker are **unchanged and intentionally
unenforced** — this was already the checker's documented restraint before
this lane (its own module docstring: these are facts backed by a `cargo
test`/example-flag checker rather than a `nat_theorem_inventory --
<theorem>`-shaped one, so there is no theorem name to read a dependency out
of, and widening the name pattern would only make a guess look official).
`--fix` correctly produces no edges for them, for the same reason the
read-only check reports none — not because it was weakened to avoid them.

Two items the design-review doc filed as "also left open, and NOT
mechanical" (an `autogenesis-nursery` train/development crossing, and a
`development-partition` conflict between two gates) are untouched — they
need an ADR-0542 amendment and a new ADR respectively, not a producer.

## Mutation results

Controls added: `scripts/tests/test_check_fact_depends_derived.py` (14 new
tests across `MissingEdgesByFactMatchesEvaluate`,
`PatchDependsOnPreservesEverythingElse`, `MainDispatchesTheFixFlag`,
`FixWritesOnlyWhatIsMissing`) and `scripts/tests/test_validate_facts.py`
(7 new tests across `DependsDerivedGateIsWiredIntoTheValidator`,
`MainFailsWhenDependsOnDrifts`). Full suite: 72 tests, all green
(`python3 -m unittest scripts.tests.test_check_fact_depends_derived
scripts.tests.test_validate_facts`).

Mutated in a scratch `copytree` under `/tmp/.../depends-producer-mutation`
(symlinked `artifacts/`, copied only the four touched `scripts/` files),
never in this tracked checkout — `__pycache__` cleared before every run.
Seven mutations, each applied one at a time against a restored baseline:

| guard mutated | killed by |
| --- | --- |
| dedup filter in `_patch_depends_on` removed | `test_a_field_already_satisfying_the_request_is_untouched_byte_for_byte` (1) |
| early-return no-op guard removed | same test (1) |
| self-exclusion (`needed == ident`) removed in `missing_edges_by_fact` | `test_a_fact_does_not_need_itself_even_if_the_graph_says_so` (1) |
| `fix()`'s reload self-check deleted | `test_the_reload_self_check_fails_the_fix_if_a_patch_did_not_take` (1) |
| `main()`'s `--fix` dispatch line deleted | `test_main_with_fix_writes_the_missing_edge_and_returns_zero` (1) |
| multi-line entry indent hardcoded (ignores detected indent) | `test_multiline_array_keeps_its_own_entry_and_closing_indent` (1) |
| `_DEPENDS_ON_RE`'s non-nesting class widened to `[\s\S]*` (spans past the first `]`) | 4 tests (the dedicated regex test plus three integration tests whose fixtures have a second array elsewhere in the file — expected: nearly every realistic fact file has more than one array, so this guard's absence is broadly, not narrowly, visible) |

False-positive controls (a healthy/already-satisfied case must NOT be
flagged or rewritten): `test_a_fully_healthy_ledger_reports_nothing_to_fix_and_writes_nothing`
(byte-for-byte untouched files), `test_a_field_already_satisfying_the_request_is_untouched_byte_for_byte`
(no reformat even when semantically a no-op), `test_main_without_fix_on_the_same_regression_reports_failure_only`
(default path never writes), `DependsDerivedGateIsWiredIntoTheValidator.test_a_passing_checker_propagates_zero`.

No mutation was left un-killed; the one mutation killing more than one test
was independently confirmed to be a real, broad-impact removal (any fact file
with a second array anywhere — i.e. almost all of them, since `evidence` is
always an array — breaks), not a sign of redundant coverage.

## Handoff

Next lane touching `depends_on` drift: run `python3
scripts/check-fact-depends-derived.py --fix` after landing facts, review the
diff (it is a plain surgical edit, easy to `git diff`), then re-run
`python3 scripts/validate-facts.py` before committing. The self-check inside
`fix()` means a red exit from `--fix` itself is a real problem (not just an
unclosed edge) and should not be silently retried.
