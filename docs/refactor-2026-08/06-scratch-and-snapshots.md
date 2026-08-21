# 06 — Where work goes: scratch, snapshots, and results

**Status:** landed as policy; the freshness guard it depends on already exists.

This is the smallest item in the folder and it exists because the day it was
missing cost a 2¼-hour solve, a 90-minute test sweep, and two watchers.

## The measured storage map

| filesystem | device | free | right for |
|---|---|---|---|
| `/` | nvme ext4 | ~727 G | **nothing large** — it carried 328 G of build artifacts and is what pressure kills |
| `/data0/axeyum` | sata ext4 | **853 G** | **build and scratch**: `CARGO_TARGET_DIR`, snapshot extractions, per-lane temp |
| `/nas3/data/axeyum` | nfs4 | 15.2 T | **results and evidence**: certificates, corpora, campaign logs |
| `/nas4/data` | nfs4 | 24.5 T | overflow for the same |

**`/tmp` is missing from that table on purpose, and that was not enough.** It is a
**62 G tmpfs — i.e. RAM**, and `mktemp -d` is what everyone types. Measured
2026-08-15: `/tmp` at 81% (50 G), `Shmem` 45.1 G of a 123 G box, `MemAvailable`
57 G. Fifteen abandoned axeyum snapshots were sitting there holding **9.3 GB of
RAM** between them, four of them 15–20 h old, none held open by any process. A
tmpfs page is not reclaimable under pressure the way page cache is, so this is a
standing contributor to the OOM kills that have taken out sessions on this box —
and a `git archive` of this repo is ~640 MB **a time**. The largest single
consumer was 33 G of agent-session directories, which is not ours to reclaim; the
snapshots were.

Three traps in that table, all paid for:

- **The NFS mount point is `/nas3/data`, not `/nas3`.** `/nas3` is a local ext4
  directory that merely *hosts* the mountpoint, so `df /nas3` reports the root
  filesystem and answers a different question confidently. Probe the path you
  actually write to, or use `findmnt -T <path>`.
- **`/data0` itself is root-owned.** It was recommended as the scratch disk
  before anyone checked. `/data0/axeyum/{scratch,target}` now exists and is
  user-writable; `/data0/winlab` shows the same pattern was already in use.
- **The agent session scratchpad is shared by every lane** (added 2026-08-18).
  `/tmp/claude-1000/<project>/<session>/scratchpad` is per **session**, not per
  lane, and every lane is told to use it. One lane kept its snapshot path in a
  fixed-name `W.txt` there; another overwrote it, and the first lane's next `cp`
  loop wrote 13 files into the second lane's `/data0` snapshot tree. Committed
  content was recoverable; an uncommitted edit inside that snapshot would not
  have been.

  It is also on the tmpfs measured above, so it is RAM. Name files
  `$AXEYUM_AGENT.<something>`, prefer passing a path in a variable within one
  invocation over persisting it, and prefer `lane-snapshot.sh`, which stamps its
  directories with an owner. Neither `git status` nor any gate can see a write
  that lands outside the repository.

## The policy

**Build and scratch → `/data0/axeyum`.** Build churn is small-random I/O, which
NFS serves badly and which fills root. A lane doing an A/B or a snapshot build
should point `CARGO_TARGET_DIR` there.

**Results and evidence → `/nas3/data/axeyum`.** Large sequential writes, shared
across every host, and the place a 19.9 GB certificate belongs. Both NFS mounts
use `nconnect=8`, 128 K rsize/wsize and `noatime`, which suits that and suits a
cargo target directory not at all.

**Long runs → a memory-bounded transient unit on an idle host**, never `nohup`.
`systemd-oomd` kills by **cgroup** under *pressure* — not on absolute
exhaustion — so a `nohup`'d job dies with whatever session it was launched from,
along with every bystander in that scope. The recipe is in
[`00-parallel-work.md`](00-parallel-work.md); `loginctl enable-linger` is set on
s4 and s5.

## The snapshot trap this pairs with

`git archive HEAD | tar -x` stamps every file with the **commit** time, and
cargo decides freshness by mtime. Extracting a *newer* commit is safe. Extracting
an **earlier** one into a warm target directory — an A/B, a bisect — puts the
content's clock behind the cache, and then `clippy -D warnings` and `cargo test`
pass over code they never compiled. Measured: `touch -d 2020-01-01 src/lib.rs`
makes `cargo test` print `1 passed` for a test that must fail.

`scripts/check-source-freshness.sh` content-hashes the build inputs and touches
what changed; the wrappers `check-clippy-complete.sh` and
`check-workspace-tests.sh` use it and report how many targets they examined.

## Stop typing the recipe: `scripts/lane-snapshot.sh`

Prose did not work. Of the ~60 `git archive` recipes in tracked files — in gate
scripts, in `CLAUDE.md`, in the `justfile`, in a dozen lane diaries, several of
them in comments *whose entire subject is this trap* — exactly **one** used
`tar --touch`. Every other copy sends the next lane to a RAM-backed tmpfs with
commit-time mtimes. So the recipe is now a script:

```sh
W=$(scripts/lane-snapshot.sh)          # HEAD
W=$(scripts/lane-snapshot.sh <ref>)    # a bisect or A/B point
(cd "$W" && CARGO_TARGET_DIR=$(scripts/lane-snapshot.sh --target) cargo test …)
scripts/lane-snapshot.sh --list        # who owns what, and is it complete
scripts/lane-snapshot.sh --gc [hours]  # reclaim YOUR OWN, default 24 h
```

It extracts to `/data0`, passes `--touch`, prints only the path so it composes,
**refuses a tmpfs scratch root** with the measurement in the error, and stamps
`.lane-owner`/`.lane-ref` so a snapshot is attributable. `--gc` reclaims only
your own: another lane's tree sitting idle between two cargo invocations is
indistinguishable from an abandoned one, and guessing wrong destroys a running
build.

Two of those properties come from the script's own controls catching it out.
Ownership is stamped **before** extraction, not after, because a 5-minute test
timeout killed a 127-second extraction and the orphan it left had no owner file —
unreclaimable by `--gc`, which is precisely the anonymous-orphan problem the
script exists to end. And reuse is gated on a `.lane-complete` sentinel written
only after `tar` returns, because the first draft handed back *any* existing
directory: a truncated checkout would have been built against and measured as if
it were the commit. That one is worse than a leak — it is a wrong number with no
symptom.

## Why this is a roadmap item rather than a wiki page

Every element above was learned by losing something. The scratch path was
recommended unwritable; the NFS mount was probed one directory too high; the
solve that died was `nohup`'d because `nohup` is what one reaches for; and the
freshness hole was found only because a lane re-extracted an earlier commit four
times in one afternoon. None of it is inferable from the tools' documentation,
and all of it is cheap once written down.
