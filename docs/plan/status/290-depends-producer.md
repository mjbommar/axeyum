# Lane: depends-producer — `--fix` for `check-fact-depends-derived.py` and its enforcement point

<!-- plan-section: lane-status -->

**DONE (`depends-producer`, 2026-08-29).**

## What `--fix` does

`scripts/check-fact-depends-derived.py --fix` computes exactly the same
missing-edge set `evaluate()` would otherwise report as a failure (both now
share `_kernel_index`, and a new `missing_edges_by_fact()` collapses the
per-message traversal into a per-fact set), then patches each affected fact
file's `depends_on` array with a **surgical text substitution** — never a
JSON re-dump. `_patch_depends_on()` finds the file's own `"depends_on": [...]`
span via a non-nesting regex (`[^\[\]]*`, safe because no `depends_on` entry
in the whole ledger contains `[` or `]`), parses just that array, appends the
missing ids (sorted, deduped against what's already there), and re-emits it
in the array's OWN style: single-line stays single-line, multi-line keeps its
own entry indent and closing-bracket indent (read from the array itself, not
assumed — the committed ledger has dozens of distinct indent widths). If
nothing is missing, the function returns the input unchanged, byte for byte —
this is deliberately its own guard (see mutation results below), not an
accident of dict equality.

After writing, `fix()` **reloads every file from disk** (not from the
in-memory patch) and re-runs `evaluate()` as a self-check; if any edge is
still missing it reports the same `DEPENDS_DERIVED_ERROR|` lines and returns
1. This exists so a broken substitution is caught here, not by the next
process that reads these files.

Verified against the real ledger in a scratch copy (never the tracked
files): regressing `F-ml430-int-add-le-add-a76ad5ce.json`'s `depends_on` (both
a single-line and a hand-restored multi-line variant) and running the patch
restores exactly the missing edge, and a mask-diff (`depends_on` span blanked
out in both texts) is byte-identical outside that one field.

## Where the enforcement is wired, and why there

Enforcement lives in **`scripts/validate-facts.py`** (`run_depends_derived_gate`,
called from `main()` right after the structural-error check). Reasons, in
order:

Detail moved to [`../notes/290-depends-producer.md`](../notes/290-depends-producer.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | depends-producer | `check-fact-depends-derived.py --fix` mode: derives, surgically patches, and self-verifies `depends_on` edges; wired into `validate-facts.py` as the landing-time gate (`--skip-depends-derived` escape hatch); 21 new mutation-controlled tests. |
