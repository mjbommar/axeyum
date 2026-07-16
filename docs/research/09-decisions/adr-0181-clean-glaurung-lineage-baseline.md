# ADR-0181: Clean Glaurung lineage regression baseline

Status: accepted
Date: 2026-07-16

## Context

ADR-0179 made the held-out lineage run reproducible and fail-closed, and
ADR-0180 supplied its regression alarms. Neither dirty exploratory evidence nor
a self-comparison is a durable per-commit reference. GQ9 automatic admission
must not be fitted until one clean full artifact fixes the exact source,
binary, driver, environment, work, finding, timing, and memory identity.

## Decision

Accept Glaurung's committed `lineage-baseline-v1.json` as the first clean
same-environment baseline for the ADR-0180 comparator.

- The release client is rebuilt from clean detached Glaurung `a0e5f9f` and
  Axeyum `486b7e28` revisions. Both artifact dirty-path arrays are empty.
- The compact atomic JSON is committed; process logs remain local, with their
  finding hashes and parsed time/RSS measurements retained in the artifact.
- Future candidates must first pass schema, environment, policy, driver,
  exact-work, finding, agreement, unknown, lifecycle, fallback, and resource
  validation. Only then do the 3% Axeyum, 3% ratio, 5% RSS, and 2% absolute Z3
  alarms apply.
- This baseline authorizes GQ9 topology/cost fitting. It does not enable
  lineage by default, authorize GQ8 caching, or weaken model/proof replay.

## Evidence

The six hard-4-GiB processes execute 92,721 shadow checks, all agreed with Z3,
with zero disagreements or unknown splits and exact expected warm/fallback
traffic.

- SurfacePen: Axeyum mean 1.063 seconds, Z3 mean 4.395 seconds, ratio 0.242x,
  Axeyum population CV 0.50%, median RSS 82,432 KiB.
- Fixed-budget NETwtw10: Axeyum mean 18.751 seconds, Z3 mean 52.149 seconds,
  ratio 0.360x, Axeyum population CV 0.09%, median RSS 257,632 KiB.

Standalone validation and baseline-to-capture comparison pass with zero
deltas. Four focused runner tests, Python compilation, Ruff lint/format, and
whitespace validation pass. Glaurung `51666a9` publishes the exact 7,986-byte
artifact. Its SHA-256 is
`ba615467b3956d21b512841335e6bb495e88f586fbb10cfdf8159cfd3153ff5b`;
the rebuilt release binary hash is
`721b435ef0cb98857db8fb1f5ec25c054670ae6b4e9d93bbda3b4a3428a41659`.

## Alternatives

Keeping the baseline only in `/tmp` was rejected because it cannot gate later
commits. Committing all process logs was rejected because the JSON already
contains the enforced hashes and measurements. Treating earlier dirty or
wall-deadline runs as the baseline was rejected because they fail source or
exact-work identity.

## Consequences

The GQ10 per-commit gate now has a versioned clean reference, and GQ9 may begin
with an explicit detected-reuse topology/cost selector measured against fixed
off and lineage policies. The first selector remains opt-in until repeated
candidate artifacts pass the clean baseline alarms on both held-out families.
GQ4 stays off; GQ8 needs its own bounded replay-safe cache decision.
