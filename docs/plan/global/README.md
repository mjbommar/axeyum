# Project-wide plan sections

The hand-authored parts of [`PLAN.md`](../../../PLAN.md) that are **not** any
one lane's: the header, Status, the five-track queue (Next Actions), the
families map, Workstream state, the resume protocol, the planning rules, the
detail map, and the consolidation record. They are emitted verbatim, in
filename order, joined by one blank line.

Per-lane state lives in [`../status/`](../status/README.md) while a lane is
active and moves to [`../archive/`](../archive/README.md) when it is done.
Regenerate with `python3 scripts/gen-plan.py`; `--check` is a gate.

## Deliberately hand-authored

These sections are project-level statements — the order, the exit criteria,
the rules — not lane reports. Changing one is a project decision. Because the
lane files are transient, these sections must carry the whole go-forward plan
on their own. `scripts/check-plan-authority.py` caps them at 32,000 bytes in
total (this README excluded).

## Placeholders

Two lines in these files are filled in by the generator:

| placeholder | filled with |
|---|---|
| `<!-- plan-generated: lane-status -->` | every active lane's `lane-status` block, in lane-file order |
| `<!-- plan-generated: landed-changes -->` | every active lane's landed rows, merged newest-first |

Each must appear exactly once across all sections; a missing one is an error,
because it would silently drop every lane's contribution.
