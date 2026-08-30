# Lane: red-drift — triaging the 12 detectors that were red on `main`

<!-- plan-section: lane-status -->

**Triaged all 12, fixed the one that was mine to fix, opt-out ceiling down by
one (`DONE`, red-drift, 2026-08-27).** `docs/plan/status/154-inert-controls.md`
measured 12 of the newly-registered 188 Python control suites as RED on
`main` (commit `a00924af0`) — drift detectors that had been firing into an
empty room because nothing invoked them. Task: classify each as (1) a real
regression the detector correctly caught, (2) a stale pin nobody updated after
a deliberate change, or (3) a broken detector, and fix what is mine to fix
(`scripts/tests/`) without touching `crates/`, `artifacts/`, or any other
lane's checker script.

Opt-out ceiling: **19 -> 18** (`OPTOUT_CEILING` in
`scripts/check-control-registration.sh`; `scripts/control-optout.tsv` now has
18 named entries). One suite left the exclusion list; the other 11 stay
excluded because the fix belongs to whoever owns the subject or the checker
script, per scope.

## Classification (all 12)

Detail moved to [`../notes/155-red-drift.md`](../notes/155-red-drift.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | (pending commit) | Triage the 12 red drift detectors from `docs/plan/status/154-inert-controls.md`: 1 test-mock bug fixed (`test_check_autogenesis_nat_fib_gcd_surface_plan`, mutation-verified), 11 root-caused and left excluded with precise reasons in `control-optout.tsv` (stale pins after legitimate refactors/doc changes, one over-broad Cargo.lock pin, one `git safe.directory` false negative, one genuine "target fact got proved" happy drift, one genuine shared-artifact drift). `OPTOUT_CEILING` 19 -> 18. Also repaired `scripts/check-shell-antipatterns.sh` (red on `main`): fixed the in-scope `grep -q` in `scripts/tests/test-lane-commit.sh`, baselined the out-of-scope one in `render/check.sh`. |
