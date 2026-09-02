# Lane: shape-dupes-at-merge

Status: IN PROGRESS (stub, first-ten-tool-calls commit)

## Goal

`scripts/check-shape-duplicates.py` — the gate that catches two declarations
proving one proposition — was red on `main` for ~25 hours and appears in 0 of
240 commit messages that day (lane `retrieval-audit-0901`). It needs a release
build of `examples/shape_search.rs --duplicates`, so it lives only in the
~10-minute full gate and nobody runs it. A literal duplicate landed 16 hours
after its twin inside that window.

Follow the pattern landed today, do not invent a third:

- ADR-1511: cheap checks go in `scripts/check-merge-hygiene.sh`; expensive
  ones get a no-cargo proxy there.
- `scripts/gen-py-prelude-fields.py --check` and `scripts/fact-frontier.py`
  use a PREBUILT release binary directly when it exists and is fresh, and
  report "cannot answer" (exit 2) rather than a false pass when it is absent
  or stale. `fact-frontier.py`'s `kernel_projection_is_stale` is the
  staleness test to reuse.

## Planned deliverables

1. `--prebuilt` mode on `check-shape-duplicates.py` (default when the binary
   exists): run `target/release/examples/shape_search --duplicates` directly,
   no cargo, no lock. Absent or stale -> exit 2 with a one-line reason.
2. Wire into `scripts/check-merge-hygiene.sh` under ADR-1511: exit 1 blocks,
   exit 2 is `shape_duplicates=skipped(stale-binary)` and does not block,
   exit 0 is `ok`.
3. Tests in `scripts/tests/test_check_merge_hygiene.py` (fail case + skipped
   case), mutation-verified in an isolated snapshot.
4. Dated amendment to ADR-1511 with the measured cost; regenerate the index.
5. End-to-end discrimination in an isolated snapshot: add a trivial duplicate
   declaration, rebuild `shape_search`, run the hygiene gate, show exit 1
   naming the pair. Restore.

## Landed changes

(none yet)
