# agent-adr-numbering — detail

## The brief

`origin/main` carries ADR-0471..0477 from a separate checkout; this branch had
independently allocated 0471..0474 for four unrelated decisions. A prior lane
(agent-capability-assurance) fixed that today (`61906c585`, `cd19e54ea`,
`de7e903d8`): renumbered to 0478..0481, four files. Task: make the collision
class either undetectable-to-land-silently, or impossible.

## What was measured, first

Before writing any code: `git fetch origin main` (fresh; `origin/main` at
`380267b2a`), then a plain filename diff between local and
`origin/main`'s `docs/research/09-decisions/`. The prior fix's own commit
message said "Next free number for this branch is 0482, and it is not safe
either until the gate compares against the remote" — that warning was
correct. The diff showed **three more numbers already collided**: 0468, 0469,
0470 — different content on each side, same numbers, live, on THIS run,
before any change of mine. This was not in the brief; it is new evidence the
defect is ongoing, not a one-time incident, and it directly motivated keeping
the fix detection-only rather than also attempting the renumber (below).

## Design chosen: detect, not prevent

Considered the non-sequential-numbering alternative (date-stamped or
hash-suffixed IDs). Rejected for THIS task: 477 files, an index generator,
hundreds of cross-references (`ADR-0468` appears as prose in ~50 files
including `.rs` doc comments), and it does not remove the need for a detector
during the multi-week migration window anyway. The brief itself says not to
start it without the detector landed first.

## Implementation

`scripts/gen-adr-index.py`:
- `remote_ref_commit(ref)` — `git rev-parse --verify --quiet`; `None` on any
  failure to resolve (no `origin`, never fetched, not a git checkout).
- `remote_adr_filenames(ref)` — `git ls-tree -r --name-only ref -- docs/research/09-decisions`,
  filtered to `adr-NNNN-*.md`.
- `fetch_head_age_seconds()` — mtime of `git rev-parse --git-path FETCH_HEAD`;
  `None` if never fetched. Chosen over remote-ref reflog because reflog for
  remote-tracking refs is not guaranteed enabled, and FETCH_HEAD is written by
  every `git fetch` unconditionally.
- `find_remote_collisions(local, remote)` — group filenames by 4-digit number
  on each side; a number is a collision iff EACH side has a filename the
  OTHER side lacks for that number (a number shared under the identical
  filename is ordinary merged history, not a collision).
- `next_free_number(local, remote)` — max numbered filename across both sides,
  plus one.
- `check_remote(remote_ref, max_staleness_hours, require_fresh)` — orchestrates
  the above; see its docstring for the fail-open trade (reproduced in the
  status file). Prints `ADR_REMOTE_COLLISION|status=...|...` always, and
  `adr-collision: ERROR/SKIP/ADVISORY` lines with specifics.
- CLI: `--check-remote`, `--remote-ref` (default `origin/main`),
  `--max-staleness-hours` (default 24.0), `--require-fresh`. When
  `--check-remote` is given, `main()` returns `check_remote(...)` directly and
  skips the index generation/`--check` path entirely — the two modes do not
  interact.

## Wiring

- `scripts/check.sh`: new `step adr-remote-collisions ...` beside `adr-index`.
  `step()` never aborts the run on failure (records and continues), so
  placement doesn't affect other steps' visibility.
- `justfile`: new standalone recipe `adr-remote-collisions:`, added as the
  LAST entry in `check:`'s dependency list (not folded into
  `generated-trackers:`). Reason: `just` aborts a recipe chain at the first
  failing DEPENDENCY, unlike `check.sh`'s soft-continue `step`. Folding it
  into `generated-trackers` (which runs early in the list) would have hidden
  every later recipe (`solver-module-graph`, `plan-authority`, `links`, ...)
  behind the SAME red this gate is expected to show right now. Last means
  everything else still visibly runs/reports before this one (possibly)
  fails.
- `scripts/check-aggregate-scope.sh` re-run after wiring: still 66 divergent
  steps (`check.sh` 122, `just check` 178) — unchanged, because the command
  text (`python3 scripts/gen-adr-index.py --check-remote`) is byte-identical
  on both sides after normalization, so it appears/cancels on both sides of
  the `comm` diff. No update to `.expected` needed.

## Mutation coverage (`scripts/tests/mutation_controls.py adr-index`)

Added 6 guards, each verified to kill EXACTLY one test (brief's
non-negotiable):

```
remote-collision: non-numbered filename is skipped, not crashed   killed 1
remote-collision: BOTH sides must have a file the other lacks     killed 1
check-remote: unresolvable ref is SKIPPED before comparing        killed 1
check-remote: staleness is measured, not assumed fresh            killed 1
check-remote: a found collision fails the gate                    killed 1
--check-remote CLI flag actually routes to check_remote           killed 1
```

Getting to exactly-1 took two redesigns, both instructive:
- First draft used the SAME overlapping fixture (`adr-0001-x.md` on both
  sides) across four different tests. Deleting the "both sides must differ"
  guard turned that shared fixture into a false collision and killed 4 tests
  at once — not because the tests were redundant, but because they were
  accidentally coupled through one fixture. Fix: give "clean" tests numbers
  that don't intersect the remote's numbers at all, so the guard's code path
  never runs for them; reserve the identical-both-sides fixture for exactly
  one dedicated test.
- The "a found collision fails the gate" guard legitimately protects TWO
  scenarios (fresh+collision, stale+collision) with one line of code. Two
  separate test methods asserting on it is correct per-scenario coverage but
  registers as 2 dead tests. Merged into one test method with two sequential
  assertions instead — same coverage, reports as exactly 1 failure.
- The end-to-end real-`git` SKIP-path CLI test was dropped rather than kept:
  it would have exercised the exact same guard as the pure-unit SKIP test.
  Real-git behavior for that path was instead verified manually (see below)
  and is not a permanent regression test, to avoid the same 1-guard/2-tests
  problem. The CLI test that remains (`test_flags_are_parsed_and_routed_to_check_remote`)
  targets a DIFFERENT guard — the `if args.check_remote:` routing line in
  `main()`, previously untested — found and added while doing this cleanup.

`python3 -m unittest scripts.tests.test_gen_adr_index` — 26 tests, all green.
`python3 scripts/gen-adr-index.py --check` — unaffected, still green,
`duplicate_numbers=0166,0167` unchanged (pre-existing, documented, not this
task's scope).

## Demonstration

### Against the real, live `origin/main` (`fetch_head_age_seconds` ~750s, fresh)

Created `docs/research/09-decisions/adr-0475-scratch-collision-demo-delete-me.md`
(0475 is used by `origin/main` for
`adr-0475-authoritative-kernel-b-operation-is-exact-and-source-bound.md`,
unused locally before this). `--check-remote` output (trimmed to the new
line; the pre-existing 0468-0470 collisions are also legitimately printed,
see below):

```
adr-collision: ERROR: ADR-0475 is claimed by both this checkout and origin/main for DIFFERENT decisions:
  local:         adr-0475-scratch-collision-demo-delete-me.md
  origin/main: adr-0475-authoritative-kernel-b-operation-is-exact-and-source-bound.md
adr-collision: next free ADR number is 0483 (highest used across local + origin/main at commit 380267b2abff)
ADR_REMOTE_COLLISION|status=collision|collisions=4|next_free=0483|...
exit=1
```

Removed the scratch file; re-ran:

```
ADR_REMOTE_COLLISION|status=collision|collisions=3|next_free=0483|...
exit=1
```

The 0475 finding is gone (as it should be); collisions=4 -> 3. **NOT green**,
honestly: the 3 pre-existing 0468-0470 collisions remain, because this task
did not renumber them (see status file — files at play had another lane's
uncommitted WIP in them). This is the gate correctly reporting a real,
already-existing defect it was never asked to fix.

### Isolated fixture, to also show a genuinely clean/green result

Built a throwaway two-repo git fixture in scratch (`upstream` == remote,
`local` == clone + independently-minted colliding ADR-0002), with a COPY of
`gen-adr-index.py` inside the fixture repo (so `ROOT`/`DECISIONS`, computed
from `__file__`, point at the fixture, not this repo). Sequence:

1. Collision: local `adr-0002-local-unrelated-decision.md` vs. upstream
   `adr-0002-upstream-second-decision.md` -> `ERROR ... ADR-0002 ...`,
   `next_free=0003`, exit 1.
2. `git mv` the local file to `adr-0003-...`, commit. Re-run:
   `status=clean|collisions=0|next_free=0004|...`, **exit 0**.
3. Unresolvable ref (`origin/no-such-branch`) -> SKIP, exit 0.
4. `touch -d '3 days ago' .git/FETCH_HEAD` + `--max-staleness-hours 1` ->
   `status=stale_clean`, exit 0 (advisory, not blocking).
5. Same staleness + `--require-fresh` -> exit 1.

Scratch fixture deleted after the demo; nothing under version control here.

## What in the brief turned out to be WRONG or incomplete

- The brief describes exactly 4 collided numbers (0471-0474). By the time
  this task ran (same day, hours later), the SAME class of defect had grown
  to 3 more (0468-0470), discovered by the very detector this task built.
  Not a brief error exactly, but a live confirmation the problem recurs
  faster than a human audit catches it.
- `just -n check 2>&1` needed for the aggregate-scope comparison (per
  CLAUDE.md's own note about `2>/dev/null` swallowing it) — used correctly
  here throughout; flagging because an early manual `grep` against `just -n
  check`'s raw command output (no recipe names appear, only shell lines) gave
  a false "0 matches" that was a grep-pattern mistake on my part, not a tool
  lie — resolved by re-reading the actual output before concluding anything.
