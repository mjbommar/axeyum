# Full-library candidate selection and failed distributed-run handoff

Status: first run frozen incomplete; no result credit
Date: 2026-07-21

## Purpose

This is the operator/reviewer handoff for G1's first complete-tree experiment.
It records the useful selection artifact, the exact failed execution state, and
the prerequisite before another large run. It is not a benchmark result and is
not included in the generated measurement-provenance matrix.

## Code boundary

Commit `d9e71e2119287d11f4d5f11968838a5a325c9af3` adds:

- `scripts/smtcomp_repro/select_library.py`: per-logic cap plus seeded
  directory-family sampling over a complete tree;
- `scripts/smtcomp_repro/compete.py --file-list`: execution over an explicit
  selected list; and
- `scripts/smtcomp_repro/distribute_run.sh`: 52 background shards across
  s4-s7.

That commit was local and not yet on `origin/repro/smtcomp-scoring` when this
snapshot was taken. Any later handoff must identify the pushed descendant, not
assume the short hash is remotely available.

## Candidate selection snapshot

External paths (not committed evidence):

| Item | Value |
|---|---|
| Corpus root | `/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental` |
| Selection seed | `20260721` |
| Logic directories | 84 |
| Pool files | 438,631 |
| Selected files | 64,345 |
| Manifest | `/nas3/data/axeyum/harness/full-inventory/selection_manifest.json` |
| Manifest SHA-256 | `964693be6cd1953b815c24ab8411d0ee234bc74608c8713c2b41a7f93cfe31b5` |
| Selected list | `/nas3/data/axeyum/harness/full-inventory/selected.txt` |
| Selected-list SHA-256 | `1f988de6efd8b0dd47ccbc14d7c61739f6e47f55a675fc705e7f58c7baf47609` |

The line count is exactly 64,345 and matches `total_selected`. This proves the
cap/family sampler emitted a deterministic candidate list for that external
tree. It does not establish official SMT-COMP selection.

### Missing selection identities

The current manifest does not bind:

- a canonical SMT-LIB release archive/tree digest;
- the official competition seed or the 2026 rules' preceding-year release;
- eligibility/status filtering per track;
- the past-solver difficulty/easy exclusion and its source result set;
- per-selected-file SHA-256, size, logic, family, status, and exclusion reason;
- a hash of the selector code/toolchain; or
- an eligible-versus-selected-versus-excluded file ledger.

Until those fields are versioned, call this `cap-family-candidate-2024`, not
official, competition-faithful, representative, or source-balanced.

## First execution attempt

The 52-shard run used a 300-second wall ceiling and one shard process per
declared worker. The output directory is
`/nas3/data/axeyum/harness/full-inventory/raw_selection`.

Snapshot at `2026-07-21T18:23:47-04:00`:

| Observation | Value |
|---|---:|
| Expected shard logs | 52 |
| Present shard logs | 52 |
| Expected raw JSON shards | 52 |
| Present raw JSON shards | 0 |
| Total expected selected cases | 64,345 |
| Completed progress lines retained in logs | 2,041 |
| Minimum completed cases in one shard | 36 |
| Maximum completed cases in one shard | 44 |
| Mean completed cases per shard | 39.25 |
| Live `compete.py` or solver workers on s4-s7 | 0 |
| Remote kernel OOM visibility | unavailable (`dmesg`: permission denied) |

Every log ends on an ordinary per-case progress line. Searches found no
traceback, explicit exception, killed/terminated message, or structured footer.
Remote `dmesg` is permission-denied on all four hosts, so kernel OOM state is
unavailable. OOM is unverified, not ruled out. The cause could also be an
external stop, a remote session policy, or another signal.

**Result classification:** unexplained external termination, incomplete,
non-mergeable, zero benchmark credit. Do not reconstruct a performance result
from the human progress logs.

## Architectural failure exposed

`compete.py --dump-raw` serializes the shard only after the entire shard
returns. With 1,237-1,238 cases per shard and a 300-second ceiling, one late
termination discards every structured result already completed by that shard.
The distributor also records no PID/exit-status manifest and has no resume
contract. Fifty-two logs therefore retain partial human-readable observations,
but `inventory.py` has zero raw inputs to merge.

This is measurement architecture, not a reason to rerun unchanged. The next
producer must make partial state durable without changing benchmark semantics.

## Prerequisite before any rerun

Preregister and test a resumable raw-result protocol with these minimum gates:

1. Write one atomic result record after every benchmark (or a small fixed
   batch), keyed by normalized benchmark ID plus exact input hash.
2. On resume, validate run identity and skip only records whose benchmark,
   solver binary, limits, selector/list, corpus, and schema identities match.
3. Emit a shard manifest at launch and a terminal footer containing PID,
   host, assigned count, completed count, exit/signal/status, wall/RSS peak,
   output hash, and missing IDs.
4. Make central merge fail on duplicate conflicting records, missing expected
   IDs, identity drift, malformed/truncated lines, or a nonterminal shard.
5. Prove interruption recovery on a tiny fixture by killing workers after fixed
   record counts, resuming, and comparing the final canonical merged JSON
   byte-for-byte with an uninterrupted run.
6. Bound aggregate memory and concurrency per host; record the actual cgroup or
   equivalent enforcement rather than only a per-child requested limit.
7. Preserve completed partial artifacts after failure. Never overwrite the
   first negative attempt or report partial coverage as a completed inventory.

Only after that protocol passes should the 64,345-file candidate be rerun. The
first rerun objective is artifact completeness and resumability, not a solver
headline.

## Safe resume checks

Read-only checks for the next session:

```sh
sha256sum /nas3/data/axeyum/harness/full-inventory/{selection_manifest.json,selected.txt}
find /nas3/data/axeyum/harness/full-inventory/raw_selection -maxdepth 1 -name 'log_*.log' | wc -l
find /nas3/data/axeyum/harness/full-inventory/raw_selection -maxdepth 1 -name 'raw_*.json' | wc -l
for host in s4 s5 s6 s7; do ssh "$host" "ps -eo pid,etime,rss,cmd | grep -E '[c]ompete.py|[a]xeyum-smtcomp'"; done
```

If external state changed, record a new timestamped attempt directory and
handoff. Do not edit this frozen first-attempt account in place.
