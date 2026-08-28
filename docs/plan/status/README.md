# Per-lane plan status

One file per lane. **Edit only your own.** These files, plus the project-wide
sections in [`../global/`](../global/README.md), are what
[`PLAN.md`](../../../PLAN.md) is generated from:

```sh
python3 scripts/gen-plan.py            # rewrite PLAN.md
python3 scripts/gen-plan.py --check    # gate: fails if PLAN.md was hand-edited
```

## Why

`PLAN.md` was touched **67 times in 24 hours** by concurrent lanes on
2026-08-13/14, and one lane's uncommitted edit was swept into another lane's
commit. Pathspec discipline does not help — it stops you sweeping files you did
not touch, not two lanes legitimately touching the same one. The session
protocol *instructed* every lane to edit `PLAN.md`, so the instruction was the
defect. Splitting the churning parts per lane removes the collision instead of
asking everyone to be careful.

## File format

```markdown
# Lane: <who you are> — <what you own>

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, your-id, YYYY-MM-DD).** What is true now, what is
next, what is blocked. This is emitted into PLAN.md's "Next Actions".

<!-- plan-section: landed-changes -->

| 2026-08-14 | `abc1234` | One row per landing, merged newest-first across lanes. |
```

- The `# ` heading is required and never appears in `PLAN.md`; it names the lane
  so the file reads on its own.
- Both sections are optional — a lane that has only landed rows omits the other.
- **Use `scripts/new-lane-status.sh <n> <lane>` rather than writing the skeleton
  by hand.** Both rules below were documented here before 2026-08-27 and **six
  lanes broke them that day**, in three distinct shapes: no markers at all (four
  lanes), text before the first marker, and a `| date | change | notes |` header
  row where `landed-changes` takes **data rows only**. Each blocks `PLAN.md`
  regeneration completely.

  The reason prose has not been enough is that the failure surfaces at the
  **coordinator**, when regeneration is refused — never at the lane that wrote
  the file, which sees nothing wrong. The script emits a skeleton that is
  correct by construction.

- **`gen-plan.py` only validates TRACKED files.** It prints
  `skipping … (untracked; git add them to include them)` and moves on, so a
  brand-new status file passes `--check` until it is staged. If you are testing
  whether your file is well-formed, `git add` it first — otherwise the check is
  not looking at it, and an unexamined file is indistinguishable from a valid
  one.

- Any text before the first `<!-- plan-section: … -->` marker is an error rather
  than being silently dropped.
- Landed rows must be `| YYYY-MM-DD | … | … |`. They are merged newest-first,
  ties broken by lane file name and then by order within the file, so the result
  is reproducible and two lanes landing on the same day never touch one line.
- The filename's numeric prefix orders the lane blocks inside `PLAN.md`. Pick a
  free number; duplicates are resolved by the rest of the name, not by anyone
  editing anyone else's file.

## Adding a lane

Add `NN-your-lane.md`, run `python3 scripts/gen-plan.py`, and commit your lane
file together with the regenerated `PLAN.md` (pathspec-only, as always).
