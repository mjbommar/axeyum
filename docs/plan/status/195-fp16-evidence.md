# Lane: fp16-evidence — settle F:fp16-add-monotone-rne's evidence row (ADR-0613)

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, fp16-evidence, 2026-08-28).** ADR-0613 (LRAT
hint-following certification) landed on main within the hour and closed the
measured checking-throughput obstruction on this fact (fp16 certify: never
observed to finish -> 125.1s end to end). This lane's job is to reproduce
that run in its own worktree, attach a real `evidence` row with a
discriminating `checker_command`, and flip `epistemic_status` to `proved` --
or report precisely why it could not. In progress: building
`smtcomp_cli --release` to reproduce the numbers first-hand before touching
the fact JSON.

<!-- plan-section: landed-changes -->

| 2026-08-28 | fp16-evidence | what landed, in one line |
