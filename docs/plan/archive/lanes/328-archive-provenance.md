# Lane: archive-provenance — an artifact citation is a caller, so a cited gate stays in `scripts/`

<!-- plan-section: lane-status -->

**Done (`archive-provenance`, 2026-08-30).** `98d17aeef` archived 346 `check-*` scripts on "no live
caller in `check.sh` or the justfile". That criterion could not see artifact
citations, which are callers of a different kind.

Measured before the fix: 212 distinct script names cited by files under
`artifacts/`; 87 resolved into `scripts/`, **125 only into `scripts/archive/`**,
0 nowhere. 111 of those pairs spell an explicit `scripts/check-X.py`, so 111
committed artifacts carried a false path.

The two surfaced failures were not check failures. Every archived script uses
`ROOT = ...resolve().parents[1]`, which is `scripts/` itself one level deeper —
**345 of 345** archived files (control: 256 live ones, where it is correct). The
sweep made every archived script unable to run.

**Restored 129, kept 217 archived.** 125 cited directly, 4 by transitive closure
through sibling invocation — a second caller class the census also missed
(capsule checkers invoke result checkers by path; control: 175 references that
resolve). Restoring makes `parents[1]` right *and* the artifacts' spelling true,
so no script and no artifact needed editing.

Running all 129: **103 pass, 26 fail**. The split is the finding — capsule
16/16, result 31/33, plan 52/76. Result and capsule checkers re-verify frozen
artifacts and should pass forever; plan checkers assert live-tree preconditions
and go stale by design. So the gate asserts **resolvability, not exit 0** —
requiring exit 0 would red on 24 correctly-stale plans.

`scripts/check-artifact-gate-provenance.py` (ADR-0621), registered in both
aggregate gates, green at `artifact_citations=578|sibling_references=183|
live=601|archived=216`. Seven guards, each mutation-verified to kill exactly one
of 11 controls, no survivors.

Cleared: `check-autogenesis-modeq-family.py` and
`check-autogenesis-bounded-induction-family.py` (exit 1 → `_OK`), plus three
sealed-capsule receipts nobody could re-check (`nat-fib-dvd`, `nat-fib-gcd`,
`int-fib-natcast`).

**Next:** a future archiving sweep needs "no live caller AND no artifact
citation"; the gate names the artifact and script when it fires. Open question
in ADR-0621: whether the 217 still-archived scripts should get a
location-independent root. Nothing claims they run today, and restoring one
self-heals the idiom.
