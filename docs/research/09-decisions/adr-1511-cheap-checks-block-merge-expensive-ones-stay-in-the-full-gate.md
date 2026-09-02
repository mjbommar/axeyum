# ADR-1511: Cheap ledger `--check`s block a merge directly; the two that need a release kernel build get a cheap cross-consistency ratchet instead

Date: 2026-09-01
Status: Accepted
Lane: `ledger-regen`

Index-summary: Four generated ledgers
(`theorem-production-ledger.md`, `production-provenance-ledger.md`,
`import-backlog.json`, `ledger-coverage.json`) were stale on main and their
`--check`s red, because none of the four was wired into anything a
coordinator actually runs before merging — only into `scripts/check.sh` /
`just check`, the ~10-minute gate. Regenerated all four (distinct theorems
1,448 -> 2,340; established facts 2,054 -> 2,343; import backlog 147 -> 213
rows; kernel_theorems 2,340 registered 2,063). Measured each `--check`'s
cost warm: `gen-import-backlog.py` and `gen-production-provenance-ledger.py`
are ~0.1s (no cargo, read only `artifacts/facts/*.json`); `gen-theorem-
production-ledger.py` and `gen-ledger-coverage.py` are ~40s warm / ~3 minutes
cold, because both shell out to `cargo run --release … prelude_theorem_
inventory`. Decision: the two cheap checks now run for real inside
`scripts/check-merge-hygiene.sh` (~2s gate, every merge); the two expensive
ones get a new cross-consistency ratchet there instead (comparing two
already-committed artifacts, no cargo) plus stay as the real `--check` in
`scripts/check.sh`/`just check`. Also fixed the actual staleness cause: the
kernel grew an `ipc` (intuitionistic propositional calculus) prelude group on
2026-08-31 that neither generator's coverage list knew about.
Index-status: Accepted

## Context

CLAUDE.md: "At N lanes the ledger IS the product, so a checker that cannot
fail is worse than no checker." The four ledgers below are precisely the
ledger CLAUDE.md means — theorem counts and provenance, read from the kernel,
never from source text. All four were measurably stale on 2026-09-01:

| generator | committed said | reality (this lane, 2026-09-01) | its `--check` |
|---|---|---|---|
| `gen-theorem-production-ledger.py` | 1,448 distinct theorems | 2,340 | red |
| `gen-production-provenance-ledger.py` | 2,054 established / 30 multi-target | 2,343 / 30 | red |
| `gen-import-backlog.py` | 147 rows | 213 rows | red |
| `gen-ledger-coverage.py` | ~1,521-theorem denominator (08-27) | kernel_theorems=2,340 | red |

`scripts/flywheel-status.sh` reprinted whatever `theorem-production-ledger.md`
said with no staleness signal, so a reader had no way to tell the number was
five days and ~900 theorems behind reality.

**Why the drift happened, not just that it did.** The proximate cause was not
neglect of the generators — `gen-theorem-production-ledger.py`'s own
fail-closed `EXPECTED_PRELUDES` guard is exactly the mechanism CLAUDE.md asks
for ("a checker that cannot fail is worse than no checker"), and it worked:
when this lane first ran it, it raised

    coverage changed: measured (..., 'ipc', ...), expected (..., without 'ipc')

rather than silently publishing a narrower distinct count. `prelude_theorem_
inventory` grew an `ipc` prelude group (`crates/axeyum-lean-kernel/examples/
prelude_theorem_inventory.rs:213`, the intuitionistic-propositional-calculus
soundness package) on 2026-08-31, and neither `gen-theorem-production-
ledger.py`'s `EXPECTED_PRELUDES` tuple nor `gen-ledger-coverage.py`'s
`prelude_of()` namespace map learned about it. Both are fixed in this change
(see Evidence). So the checker did its job the moment anyone ran it — the gap
was entirely that nobody had, because nothing between "a lane merges" and
"the ~10-minute full gate, run occasionally" required it.

**Where the four checks actually live today**, verified by reading the
files rather than assuming:

- `hooks/pre-push` (the ~10-minute pre-push battery): none of the four.
  Confirmed by grep — no `gen-theorem-production`, `gen-ledger-coverage`,
  `gen-import-backlog`, or `gen-production-provenance-ledger` reference
  anywhere in the file. It explicitly documents the precedent this ADR
  follows: `trust-closure` (`58s warm, and it shells out to a cargo run
  --release kernel example`) is deliberately NOT run in pre-push, and the
  file states why — "adding those here would put ~2.5 minutes in front of
  every push — including the docs-only pushes that currently cost zero —
  and a gate people reach for `--no-verify` to escape is worse than no gate."
- `.github/workflows/ci.yml`: none of the four (grepped for each generator
  name; zero matches).
- `scripts/check.sh` / `justfile`'s `check` recipe: **all four**, already
  wired as blocking steps (`step theorem-production-ledger …`, `step
  production-provenance-ledger …`, `step import-backlog …`, `step ledger-
  coverage …`). This is the ~10-minute gate CLAUDE.md itself says "is not run
  per merge."
- `scripts/check-merge-hygiene.sh` (the ~2-second script a coordinator
  actually runs before merging a lane branch, per its own header and
  CLAUDE.md's "Multi-agent hygiene" section): **none of the four**, before
  this change.

So the failure was structural, not a one-off oversight: the only place all
four checks blocked anything was a gate that is, by the project's own
documented workflow, not run at the point where staleness would be caught
before it lands.

## Decision

Split the four checks by measured cost, not by generator identity:

**1. Cheap, real, and now enforced in `scripts/check-merge-hygiene.sh`:**
`gen-import-backlog.py --check` and `gen-production-provenance-ledger.py
--check`. Both read only `artifacts/facts/*.json` (and, for the backlog,
`docs/curriculum/curriculum.toml`) — no cargo, no kernel build. Measured warm,
repeatably: ~0.09-0.11s each. Adding both to the ~2-second hygiene gate is
free relative to its own budget (measured baseline ~2-7s depending on load)
and they are the real check, not a proxy — they now genuinely block a merge
that leaves either ledger stale.

**2. Expensive, and NOT added whole to any per-merge gate.**
`gen-theorem-production-ledger.py --check` and `gen-ledger-coverage.py
--check` both shell out to `cargo run --quiet --release -p axeyum-lean-kernel
--example prelude_theorem_inventory -- --include-constructed`. Measured this
lane, same worktree:

- **Cold** (fresh worktree, empty `target/`): ~3 minutes wall clock to
  compile `axeyum-lean-kernel` in release and run the inventory once
  (18:11:xx start, 18:14:03 first output — the coverage-gap error that led
  to the `ipc` fix above).
- **Warm** (binary already built, unchanged since): `gen-theorem-production-
  ledger.py --check` 41.0s; `gen-ledger-coverage.py --check` 39.6s. Both
  numbers are the wrapped `scripts/cargo-serialized.sh --batch …` wall time
  (lock + nice 10 + ionice), not a bare `cargo run`.

A 2-second gate cannot absorb either number, warm or cold — 40s warm is 20x
the hygiene script's own baseline, and a coordinator merging several lane
branches in a row pays it every time. Adding it to `pre-push` would repeat
the exact reasoning the file already gives for excluding `trust-closure`: a
cargo-release-build gate does not distinguish a docs-only push from a
Rust-touching one, and this lane found nothing in `pre-push` that
path-conditions a step this way for a docs/JSON-only change (the four L0
gates that DO run unconditionally are all sub-2-second, no-cargo Python
checks — the same shape as the two moved into merge-hygiene above, not the
same shape as this pair).

Instead: a **cross-consistency ratchet**, added to `check-merge-hygiene.sh`
as a new point 6. `theorem-production-ledger.md`'s "N distinct theorems" and
`ledger-coverage.json`'s `counts.overall.kernel_theorems` are two committed
artifacts derived from the identical kernel measurement
(`prelude_theorem_inventory --include-constructed`'s distinct count) and must
agree exactly — verified: both currently read 2,340. Comparing two committed
files costs no cargo and no kernel build (measured: negligible, dominated by
one `python3 -c` JSON load). This is deliberately a **necessary, not
sufficient**, freshness signal: two artifacts regenerated together still
agree with each other while both are stale against the true kernel state.
What it DOES catch, cheaply, is exactly the failure mode that produced this
ADR's own investigation — one of the two ledgers regenerated and committed,
the other not, drifting apart. The real absolute-freshness check remains
`gen-theorem-production-ledger.py --check` / `gen-ledger-coverage.py --check`
in `scripts/check.sh` and `just check`, unchanged by this ADR, and the
ratchet's own failure message says so and names both commands.

## Evidence

- Fixed the actual staleness cause in `scripts/gen-theorem-production-
  ledger.py` (`EXPECTED_PRELUDES` gained `"ipc"`) and `scripts/gen-ledger-
  coverage.py` (`prelude_of()` gained an explicit `name.startswith("ipc_")`
  branch, the same shape as the pre-existing `axeyum.string.` special case,
  since `ipc_*` theorem names are flat and lowercase and would otherwise
  silently fall through to the `logic` bucket). Both regenerators re-run
  clean after the fix (`THEOREM_PRODUCTION|distinct=2340|axiom_free=2340|
  axiom_bearing=0|preludes=11|ties=32`, `LEDGER-COVERAGE|kernel_theorems=2340
  |registered=2063|curated=1036|unregistered=277`).
- All four `--check`s exit 0 against the regenerated artifacts (direct `$?`
  on each command, not read after a pipeline).
- Discriminating test on the new merge-hygiene checks, run in this worktree:
  corrupted `theorem-production-ledger.md`'s pinned count to `9999` ->
  `scripts/check-merge-hygiene.sh` exits **1** naming the mismatch (`9999`
  vs `ledger-coverage.json`'s `2340`); restored the file -> exits **0**.
  Same pattern for `artifacts/import-backlog.json` (`"count": 213` ->
  `999` -> gate exit **1** naming `gen-import-backlog.py --check`; restored
  -> exit **0**). `git status --porcelain` confirmed the tree was clean
  after each restore.
- `hooks/pre-push` grepped directly for all four generator names: zero
  matches. `.github/workflows/ci.yml` likewise: zero matches.

## Alternatives

- **Add all four to `hooks/pre-push` unconditionally.** Rejected: the file's
  own header already measures and rejects this shape for `trust-closure`
  (~2.5 minutes added to every push, including docs-only ones), and this
  pair is comparable in cost.
- **Add all four to `check-merge-hygiene.sh`.** Rejected for the two
  cargo-dependent ones: a 2-second gate absorbing a 40-second (warm) /
  3-minute (cold) step defeats the reason that script exists — CLAUDE.md and
  the script's own header are explicit that the ~10-minute full gate is *not*
  run per merge precisely because of costs in this range.
- **Path-condition the expensive checks in `pre-push`** (run only when a
  push touches `crates/axeyum-lean-kernel/**` or `artifacts/facts/**`, the
  same pattern the L0 gates and the heavier suites later in the file already
  use for other checks). Left for a follow-up: it is the more complete fix
  and mirrors an established pattern in the same file, but implementing and
  verifying it against `pre-push`'s existing path-range logic is a larger,
  separate change than this ADR's scope, and the cross-consistency ratchet
  already closes the specific gap this investigation found (two ledgers
  silently diverging) without it.
- **A ratchet reading cached kernel state without any committed
  cross-check** (e.g., comparing the ledger's mtime against `git log` on
  `crates/axeyum-lean-kernel/src/**`). Rejected in favor of the
  cross-consistency check: an mtime/git-log heuristic can be defeated by an
  unrelated commit touching the kernel tree, and does not verify anything
  about the ledgers' own content, whereas comparing two committed counts is
  a real (if partial) correctness statement and is exactly as cheap.

## Consequences

- A lane merge that regenerates one theorem-counting ledger but not its
  sibling is now caught at merge time (point 6), not only when someone next
  runs the full gate.
- A lane merge that lets the import backlog or production-provenance ledger
  drift is now caught for real at merge time (points 5), with the same
  ~0.1s cost either way.
- The absolute freshness of `theorem-production-ledger.md` and `ledger-
  coverage.json` against the true kernel state is still only checked by
  `scripts/check.sh` / `just check`, unchanged by this ADR — a coordinator
  who wants that guarantee before merging still has to run the full gate (or
  the two `--check`s by name) deliberately. The ratchet narrows the gap it
  can silently sit in; it does not close it.
- The next prelude group added to `prelude_theorem_inventory` will again
  need its name added to `EXPECTED_PRELUDES` (`gen-theorem-production-
  ledger.py`) and, if its theorem names are flat/lowercase rather than
  dotted, to `prelude_of()`'s explicit-prefix branches (`gen-ledger-
  coverage.py`) — this is unchanged by this ADR and remains the generators'
  existing fail-closed design, which worked exactly as intended this time.
- Path-conditioning the two expensive checks into `pre-push` (the Alternative
  left open above) remains available as follow-up work if a coordinator
  decides the cross-consistency ratchet's necessary-but-not-sufficient
  guarantee is not enough.
