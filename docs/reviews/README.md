# Review archive

This directory preserves point-in-time code and architecture reviews. Review
reports and diaries are historical evidence: their file counts, benchmark
numbers, line references, findings, and recommendations describe the checkout
and scope named in the report, not the current tree.

For current project claims, use [Project State](../PROJECT-STATE.md), the
[capability matrix](../research/08-planning/capability-matrix.md), the
[support matrix](../research/08-planning/support-matrix.md), and the
[trust ledger](../research/08-planning/trust-ledger.md). For current priority
and disposition, use root [`PLAN.md`](../../PLAN.md). A later fix does not erase
the value of the review that found it.

## Reviews

| Date | Scope | Main artifact | Supporting record |
|---|---|---|---|
| 2026-07-17 | Axeyum core and architecture plus the Glaurung integration seam | [Ranked recommendations](multiagent-20260717/README.md) | [Core diary](multiagent-20260717/1-axeyum-core.md), [architecture diary](multiagent-20260717/2-axeyum-architecture.md), [integration-seam diary](multiagent-20260717/3-glaurung-seam.md), [breadth sweep](multiagent-20260717/4-axeyum-breadth.md) |
| 2026-06-20 | Axeyum design, implementation, benchmark artifacts, and targeted validation | [Codex report](codex-20260620/report.md) | [Review diary](codex-20260620/diary.md) |

## Reading a review safely

1. Read its date, scope, checkout assumptions, and validation method.
2. Treat numeric inventories and source line references as snapshot data.
3. Reproduce a finding on current `main` before acting on it.
4. Check ADRs and root `PLAN.md` for later decisions or disposition.
5. Keep the original report immutable; add a new dated review or a linked
   current-state note rather than rewriting history.

New reviews should include a concise verdict, exact scope and revision,
evidence-backed findings, ranked actions, validation status, and a diary when
the investigation is substantial.
