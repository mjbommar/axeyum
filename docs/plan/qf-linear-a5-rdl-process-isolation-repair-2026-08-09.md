# QF linear A5 RDL process-isolation repair result — 2026-08-09

## Outcome

QF_RDL attempt 001's exit 101 is a corpus-driver address-space retention
failure, not a row-local solver crash. The candidate repair runs each frozen
file through one sequential child of `explain_corpus`, preserving order,
identity, solver configuration, and query timeout while reclaiming every
child's allocations at process exit.

The first exact uncommitted isolated-worker candidate completed 200/200 QF_RDL
rows under the unchanged 24,000 ms query timeout and 8 GiB inherited
per-process `RLIMIT_AS`: 64 SAT, 42 UNSAT, and 94 typed unknown, with ordered
identities, nonempty route traces, zero stderr, and exit 0. This is repair
evidence, not a credited V2 census capture. A later hardening made the internal
single-file CLI flag, rather than an inherited environment marker, the sole
recursion boundary. Its focused gates pass; its quiet-host exact trigger remains
required before V2 capture.

## Failure boundary

The retained
[`QF_RDL-attempt-001.failure.json`](evidence/qf-linear-a5/failures/QF_RDL-attempt-001.failure.json)
binds the old 11,730,816-byte release binary (SHA-256
`f88c9dede3957a8730b5adbe77ad62babf397e56daa712b38f40401632976c6d`),
exact pushed commit `e996afd839c0dd076673cea861ea59dda329f344`, and frozen
200-row list. It records 196 emitted rows, exit 101, zero stderr, 2,108,059 ms,
and no credit.

The apparent row 197 trigger, the final four rows, and the complete final 21
rows all exit 0 in smaller processes. Each relevant hard scheduling row returns
typed budget `unknown`. Therefore benchmark content alone does not reproduce
the failure.

## Memory diagnosis

An external `/proc/<pid>/status` sampler observed the old exact-list process:

- rows 1--24 grew gradually from about 9 MiB to 25 MiB RSS;
- an early 363 MiB peak returned to about 98 MiB;
- rows 57--64 raised retained RSS through about 0.64, 0.97, 1.14, and 1.30 GiB;
- rows 64--85 remained pinned near 1.39 GiB despite completed queries; and
- the retained baseline made the later multi-gigabyte rows exceed the 8 GiB
  address-space limit.

Two allocator-policy controls were rejected. A 128 KiB mmap threshold still
retained about 1.17 GiB by row 63; a 16 KiB threshold retained about 1.14 GiB
across only rows 57--64. Neither is a deterministic or portable release
contract.

## Repair contract

[ADR-0379](../research/09-decisions/adr-0379-sequential-isolated-corpus-workers.md)
accepts one ordered parent and one active inherited-limit child per file. The
parent validates one identity-matching JSON record, zero stderr, and successful
exit before forwarding and flushing output. A child failure stops the complete
stream; no partial record receives credit. The capture metadata records the
topology, worker limit, per-process address-space scope, and absence of an
aggregate cgroup-memory claim.

The focused example suite has six passing tests, including stderr, empty,
multiple-record, and identity-drift negatives; strict example Clippy is green.
The 200-row candidate release binary SHA-256 was
`928478c96573779ec09fae2c2aaf6b949cd95aa8470403b5e42d00233a7fbf59`.
The hardened release binary SHA-256 is
`18ef76d6f94c8619062dc44c69f1fa75f3d477d9ed146eb555202248efbe9af6`.

## Measurement consequence

The topology change invalidates combination with V1 captures. The
[V2 preregistration](qf-linear-a5-cross-division-census-v2-preregistration-2026-08-09.md)
retains every frozen population, semantic validator, correctness control,
timeout, and ceiling, but makes the worker boundary and memory scope explicit.
After exact commit/push and the complete gate, capture restarts at QF_LRA row 1.

## Exact pushed verification and census disposition

Exact pushed repair `5a53012e1` passed the complete external-frontier
`just check` gate. Its hardened 11,859,024-byte release binary (SHA-256
`18ef76d6f94c8619062dc44c69f1fa75f3d477d9ed146eb555202248efbe9af6`)
first completed a quiet-host 200-row QF_RDL confirmation with zero stderr,
directly crossing the old row-196 boundary. The subsequent credited-topology V2
sequence completed QF_RDL atomically in 2,127,949 ms: 63 SAT, 42 UNSAT, and 95
typed unknown, preserving all 105 historical decisions. Its JSONL SHA-256 is
`5af6091b75367fdc337dc4026335f0fd95abdd10e3965677b79425d47c5bee76`.

That RDL result proves the process-isolation repair, but the complete V2 census
is non-credited because cross-division derivation found an independent
historical QF_LRA UNSAT loss. The retained failure record is
[`V2-census-attempt-001.failure.json`](evidence/qf-linear-a5/failures/V2-census-attempt-001.failure.json).
The bounded LRA repair changes behavior again, so all three divisions must
restart; no RDL row is reused.
