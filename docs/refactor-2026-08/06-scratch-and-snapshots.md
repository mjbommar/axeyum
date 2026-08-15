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

Two traps in that table, both paid for:

- **The NFS mount point is `/nas3/data`, not `/nas3`.** `/nas3` is a local ext4
  directory that merely *hosts* the mountpoint, so `df /nas3` reports the root
  filesystem and answers a different question confidently. Probe the path you
  actually write to, or use `findmnt -T <path>`.
- **`/data0` itself is root-owned.** It was recommended as the scratch disk
  before anyone checked. `/data0/axeyum/{scratch,target}` now exists and is
  user-writable; `/data0/winlab` shows the same pattern was already in use.

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
Use `tar --touch` if extracting by hand.

## Why this is a roadmap item rather than a wiki page

Every element above was learned by losing something. The scratch path was
recommended unwritable; the NFS mount was probed one directory too high; the
solve that died was `nohup`'d because `nohup` is what one reaches for; and the
freshness hole was found only because a lane re-extracted an earlier commit four
times in one afternoon. None of it is inferable from the tools' documentation,
and all of it is cheap once written down.
