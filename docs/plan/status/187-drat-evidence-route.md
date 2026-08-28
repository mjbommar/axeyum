# Lane: drat-evidence-route — route the `unsat` evidence path off the quadratic forward DRAT checker

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, drat-evidence-route, 2026-08-28).** Investigating why
the evidence/certificate path calls `check_drat` (the forward reference checker,
superlinear in proof length) when `check_drat_backward` and
`elaborate_drat_to_lrat_backward` (ADR-0382) exist and are ~66x faster.

Measured motivation (`F:fp16-add-monotone-rne`): decide 11.09 s, emit 827,048
proof steps, `drat_check` ~95 steps/sec, so ~2.4 h extrapolated and never
completed. "Finding is hard, checking is cheap" is inverted by ~3 orders of
magnitude.

Initial finding (pre-change): the choice is **historical, not deliberate**.
ADR-0382 is explicitly additive ("the new checker must be additive"), keeps
`check_drat` as the auditable *reference*, and its item 9 defers re-basing the
LRAT elaborator as "an obvious follow-on ... deliberately not in this slice".
No ADR, comment, or test pins the evidence path to the forward checker. The
pieces to close it already exist and are unused outside examples.

<!-- plan-section: landed-changes -->

| 2026-08-28 | drat-evidence-route | lane opened: audit of why the evidence path uses the slow DRAT checker |
