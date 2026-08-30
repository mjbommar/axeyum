# Notes: 334-gate-termination

Detail moved out of [`../status/334-gate-termination.md`](../status/334-gate-termination.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The ledger sweep is bounded at three scales.** Its build probe had no timeout
at all; its per-row timeout was `subprocess.run(shell=True, timeout=N)`, which
kills only the direct child (measured: grandchild survives at all three command
shapes); and it had no whole-sweep budget, so the summed per-row budgets came to
993,952 s — 11.5 days. Now capped, tree-killed, and deadlined at 9,900 s,
deliberately under `check.sh`'s 10,800 s cap so the informative stop wins and
unreached facts are named as `NOT RUN`.

The caps are anchored to repository measurements, not chosen: 30 min default
(the whole non-cargo half extrapolates to ~45 min), 2 h for anything that builds
(worst measured cargo step 509 s, contention documented at 4–7x), 4 h for `test`
(never timed; nearest recorded artifact is the 6,588 s workspace nextest sweep).

Probe: 8 cases / 19 assertions, ~90 s, no cargo. Mutation sweep: 7 mutants, 6
killed; the survivor is a defensive guard whose precondition is unreachable on
this host and is reported rather than excused. **The probe caught two defects in
the fix it was written to verify** — the missing group kill, and a Python reaper
that broke out of its kill loop when the direct child was reaped and so never
sent SIGKILL.

Next for whoever picks this up: the process-substitution `read`s in
`check-autogenesis-apply-search.sh` (3 sites) and
`check-autogenesis-induction-search.sh` (1) are individually unbounded and only
bounded from outside by the step cap; and `check.sh` execs itself through
`cargo-serialized.sh`, so it can wait up to 90 minutes for the slot before any
step timing begins. Both are noted in ADR-0623 and neither is fixed here.
