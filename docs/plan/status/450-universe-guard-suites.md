# Lane: universe-guard-suites — three kernel suites have not run since ADR-1495's universe guard landed

<!-- plan-section: lane-status -->

**WIP, universe-guard-suites, 2026-09-03.** `scripts/lane-push.sh` was refused
on main at `76a8d109c`: `check-kernel-suites` runs three tests that fail with
`ConstructorFieldUniverseTooBig`, all from ADR-1495's guard (`c72fd281b`).
ADR-1495's measurement was aimed at three suites that did not include these,
and every lane since ran only its own `--lib` filter, so these three have not
run since the guard landed. The guard is a soundness fix and is not to be
weakened; each fixture is being decided against Lean 4's `check_constructor`
rule (field universe <= result universe, `Prop` exempt), not against what makes
the test pass.

<!-- plan-section: landed-changes -->

| 2026-09-03 | universe-guard-suites | Lane status stub: three kernel suites refused by ADR-1495's universe guard, under triage. |
