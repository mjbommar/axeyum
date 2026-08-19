# The unblocking, verified against eleven concurrent lanes

Measured 2026-08-14, coordinator lane. This closes the "verify by running
concurrent lanes and measuring collisions" item: the day itself was the
experiment, so the numbers are observational rather than staged.

## What ran

**107 commits from 11 distinct lanes** in one shared checkout: `coordinator`
(33), `nat-shard` (13), `gates` (13), `int-keystone` (3), `quant-duality` (2),
`facts-number` (2), `append-points` (2), `telescoping-scale`, `telescoping`,
`facts-logic`, `agent-j` (1 each). Six lanes were live simultaneously at peak.

35 of the 107 carry no `Agent:` trailer, all of them from before the
`hooks/commit-msg` hook landed mid-morning. Attribution from that point on is
complete.

## Zero cross-lane clobbering, measured precisely

The five previous incidents all had the same shape: one lane's uncommitted hunks
swept into another lane's commit. The precise test for a recurrence is whether
any lane committed a *different* lane's per-lane state.

    # every commit, its lane, and any status file it touched
    git log --format='%H|%(trailers:key=Agent,valueonly)' | ... | grep '^docs/plan/status/'

**Result: none.** The only lane appearing against other lanes' status files is
`append-points`, which *authored* the split — it created all ten files from the
old monolithic PLAN.md in one commit. That is the migration, not a collision.

Every lane that committed the generated `PLAN.md` also committed exactly its own
status file. The single exception is one `coordinator` commit with zero status
files, which regenerated `PLAN.md` after a generator fix — legitimate and
intended.

## What actually worked, and why

| mechanism | effect observed |
|---|---|
| `Agent:` trailer via `hooks/commit-msg` | 72/72 post-hook commits attributable; three misattributions the previous day |
| per-lane `docs/plan/status/<lane>.md` | 11 lanes edited plan state with no contention |
| one file per fact in `artifacts/facts/` | 5 lanes wrote the ledger concurrently, no collisions — the resource was *designed* per-item |
| `nat_prelude` sharded into 10 modules | two kernel lanes worked without touching the same file |
| `AXEYUM_AGENT` in the environment | survives a shared checkout, unlike the repo-local git config it replaced |

The pattern is one rule: **per-lane state belongs in per-lane paths or
per-process environment.** Every mechanism above is an instance, and the two
that were *not* built that way are exactly where multi-writer pressure remains.

## What remains multi-writer

Counted by distinct lanes committing each file today:

| file | lanes | status |
|---|---|---|
| `PLAN.md` | 7 | generated; sources are per-lane, but the artifact is still a shared commit target |
| `scripts/check.sh` | 3 | **still an append point** |
| `CLAUDE.md` | 3 | **still an append point** |
| `justfile` | 2 | **still an append point** |

The `gates` lane predicted exactly this in its FEEDBACK F2 — `check.sh` and the
`justfile` are the next two append points of the same shape, since every gate
lane appends a step. Its proposed fix, a single authoritative step manifest that
generates both, remains the right one and is not done.

> **CONFIRMED 2026-08-19, and it cost something.** The prediction was right and
> the fix is still not done. `scripts/check-aggregate-scope.sh` was built to
> *detect* the divergence rather than to remove it, and it now reports
> `check.sh` at **203** steps against `just check`'s **278**, with **32** steps
> that `main` ships recorded as accepted in neither — every one of them a lane
> appending to one file and not the other.
>
> The cost was not the divergence. `just` aborts its dependency chain at the
> first failure, and the red `aggregate-scope` sat at **#18 of 41**, so
> `just check` died there and **23 gates never ran** — including `test`,
> `frontier`, `gate-liveness`, `lean-gate` and `doc`. `check.sh` accumulates
> instead of aborting, so for that window the *fallback* was the more complete
> gate. Detection at an early position in an aborting chain is worse than
> detection at the tail; the three expected-red gates were moved to #39–#41 in
> `51fdc0ae6`. **The manifest that generates both is still the right fix.**

One residual risk observed as *possible* but not *realised*: `gen-plan.py` reads
every status file from the worktree, so a lane regenerating `PLAN.md` while
another lane's status file is present-but-uncommitted would commit that lane's
block. It did not happen today. The mitigation is the same discipline the
hygiene rules already state — `git diff <file>` before `git add` — and the
stronger fix would be for the generator to read committed state rather than the
worktree.

## The failure that did happen, and it was not a collision

`systemd-oomd` killed the session cgroup at 14:18 — *"68.36% > 50.00% for > 20s
with reclaim activity"*, 27 processes, 83.6 GB peak — taking a 2¼-hour solve and
two watchers with it. Not a kernel OOM; a pressure-based userspace killer that
acts on **cgroups**, so `nohup` is irrelevant and bystanders die with the cause.

The trigger was three concurrent `--all-features` workspace builds plus an 18 GB
solve on one box. So the binding constraint on lane concurrency here is **memory
pressure, not source contention** — which is the opposite of what this whole
workstream was built to fix, and worth stating plainly: the append points were
real and are mostly gone, and the thing that actually stopped work today was
resource scheduling.

Mitigations now in every lane brief: `-p <crate>` builds rather than workspace,
`CARGO_BUILD_JOBS` capped, and long runs offloaded to `s1`/`s4`/`s5`/`s6`/`s7`
as transient `systemd --user` services with `MemoryHigh`/`MemoryMax` set, so a
runaway throttles itself instead of taking down the slice.
