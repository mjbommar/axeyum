# Project-wide plan sections

The hand-authored parts of [`PLAN.md`](../../../PLAN.md) that are **not** any
one lane's: the header, Status, the ordered A1–A11 queue, Workstream state, the
resume protocol, the planning rules, the detail map, and the consolidation
record. They are emitted verbatim, in filename order, joined by one blank line.

Per-lane state lives in [`../status/`](../status/README.md) instead. Regenerate
with `python3 scripts/gen-plan.py`; `--check` is a gate.

## Deliberately still hand-authored

These sections are project-level statements — the priority order, the exit and
stop conditions, the rules — not lane reports. Two lanes do not append to them
in the course of ordinary work; changing one is a project decision. They kept
their existing shared-file form because splitting them per lane would fragment
the single ordering the queue exists to express.

The churn was elsewhere and that is what moved: the lane blocks in Next Actions
and the recent-landed-changes table, both of which grew by one entry per lane
per session.

## Placeholders

Two lines in these files are filled in by the generator:

| placeholder | filled with |
|---|---|
| `<!-- plan-generated: lane-status -->` | every lane's `lane-status` block, in lane-file order |
| `<!-- plan-generated: landed-changes -->` | every lane's landed rows, merged newest-first |

Each must appear exactly once across all sections; a missing one is an error,
because it would silently drop every lane's contribution.
