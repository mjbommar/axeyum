# ADR-0211: Accept native timeout-continuation default

Status: accepted
Date: 2026-07-17

## Context

ADR-0209 implements exactly one fresh-deadline check on the same synchronized
Glaurung direct-delta session after an initial `Unknown`, but keeps it explicit
and off. ADR-0210 accepts the mechanism on one exact public ordered stream while
requiring a repeated production-topology gate before downstream default
admission. Glaurung ADR-019 now captures and replays the missing native facts:
typed expression-DAG packs, source-prefix identity, direct persistent/temporary
work, adaptive fallbacks, and serial owner share/release order.

The admission result must not conflate two independent policies. Direct delta
itself remains explicit pending its wider-driver decision. This ADR decides only
whether a caller that already selected direct delta receives the bounded
continuation by default.

## Decision

Accept one same-session continuation as the Glaurung direct-delta default.
Glaurung `9ace064` treats a missing
`GLAURUNG_AXEYUM_WARM_TIMEOUT_CONTINUE` as enabled. `0`, `off`, or `false`
provides the preserved control, and an unrecognized value fails closed to off.

Keep all other boundaries unchanged:

- `GLAURUNG_AXEYUM_DIRECT_DELTA` remains separately opt-in;
- continuation occurs only after a synchronized warm check returns `Unknown`;
- at most one fresh-deadline check runs on the same solver;
- a repeated `Unknown`, error, or unavailable solver preserves the original
  `Unknown` and remains counted;
- fresh cold retry remains off; and
- generic Axeyum constructors, one-shot solving, snapshot reuse, proof policy,
  strict sorts, and public APIs do not change.

## Evidence

### Exact production artifact

Clean Glaurung `33191ac89d00befd1f330198c642568d3477b616` completes
156/338 tcpip functions under a 4 GiB process cap in 14m45s. It reaches the work
limit rather than the analysis deadline, emits 794 stable finding rows, and
records 71,136/71,136 shadow checks with zero decided disagreement. Axeyum has
55 bounded nondecisions and Glaurung preserves them as `Unknown`; no fast
failure is scored as a win.

The published trace contains 326,364 ordered events, 15,501 paths, 50,687
unique queries, 71,136 checks, 10,515 public assertions, 10,515 native packs,
15,501 owner releases, 7,663 owner shares, and 27,940 model reads. The producer
validator accepts the complete artifact. Its manifest, event-stream, and query
index SHA-256 values are respectively
`a97727d00e01645ca10f6fb98b68c44ddbceb313b112edf66c5a10b41860c657`,
`cf189a96fde81e7114b3a75f8958a20ab4439c6f6c22f3d53d18166588325cd5`, and
`2935b9c3d4a3e89487666352fb858e35a7e4c11a0a685a676d6e8d5689330a18`.
The finding stream SHA-256 is
`72ae4787fe57be8f76be41f1955bc84a9968a83e7da67e34344ab5cd1a95e6f5`.

### Independent public replay

Axeyum `ddb368b7fcf5e4a93fbfd570f2abb349bd965d31` independently parses and
validates all 50,687 unique queries under a 5 s per-query alarm, then replays
all 27,940 model reads against original terms. It observes 28,834 SAT and
21,853 UNSAT unique queries and all 71,136 recorded occurrences, with no parse,
verdict, or model-replay failure. The 18m54s process peaks at 1,050,664 KiB,
below the 4 GiB cap. Report SHA-256 is
`3a9a6b45b2b86148c197b4f20918b65093f249fcbf523a4347d91d63b72b3387`.

### Repeated native policy comparison

Glaurung `c1a56351a34114f0a035b4fc408fb43a4223f72a` and replay
executable SHA-256
`ad69f9d115eceb22d7f3c43156f61ee31640ef6e582bb92fde74f4934ae1f666`
run three interleaved fresh-process control/candidate pairs. Every report binds
the trace, finding stream, independent replay, executable, and clean Glaurung/
Axeyum revisions.

All six processes reproduce 70,656 synchronized warm checks and 480
assertion-cap fallbacks, 13,933 exact reuses, 7,067,382 prefix assertions,
42,908 additions, 37,436 pops, and the complete owner lifecycle. Every run has
zero opposite decisions, synchronization mismatches, operational errors,
resets, cache replay failures, or terminal live paths/owners/references.

Across candidates, 29 continuations partition into 18 recovered decisions,
11 repeated `Unknown`s, and zero errors. Control/candidate Axeyum-time p50 is
98.175/100.166 seconds, a +2.027% candidate cost within the 3% alarm. Maximum
RSS p50 is 356,840/360,484 KiB, +1.021% within the 5% alarm. Axeyum-time CV is
0.192%/0.365%, below the 3% variance alarm. The fail-closed comparison passes;
its SHA-256 is
`0f27afce0b691e977ebf9aa66b67f4bb8744e1c0cc3eb90c2f832b196d1adbc3`.

Focused Glaurung default-parser and 46-test Axeyum-backend groups pass. The
native pack, producer lifecycle/tamper, independent compatibility, smoke, and
comparison-script tests also pass. The downstream repository retains its known
baseline warnings and unrelated rustfmt drift; this change introduces neither.

## Alternatives

- Default-enable direct delta too: rejected because that is a distinct
  wider-driver admission decision and the native replay covers tcpip only.
- Raise every warm timeout: rejected because it taxes the common decided path
  rather than continuing only observed nondecisions.
- Retry in a fresh solver: rejected by ADR-0208's +10.46% RSS result.
- Continue repeatedly or without a deadline: rejected because it breaks the
  bounded deterministic resource contract.
- Convert residual nondecisions to an error or fallback verdict: rejected
  because `Unknown` is a first-class sound outcome.

## Consequences

The native production-topology blocker from ADR-0209/0210 is closed for the
bounded continuation policy. Direct-delta users gain additional decisions
without rebuilding the arena/AIG/CNF or weakening replay, and explicit controls
remain available for every future gate.

This is a downstream policy admission, not a new Axeyum-wide default and not a
general QF_BV completeness claim. Continue GQ10 with the zero-query `win32k`
frontend gap and wider direct-delta admission; continue the pure-solver lane
with measured cold term-to-AIG-to-CNF work before SAT tuning. Preserve all ten
[Glaurung consumer feedback invariants](../../../PLAN.md#glaurung-consumer-feedback-invariants-2026-07-16),
including strict/actionable sort errors, warm/cold separation, warm-only
configured preprocessing, lean scalar models, bounded shared replay, honest
cause-partitioned nondecisions, self-rechecked proof paths, the pure-Rust
default, and exact-work measurement that rejects fast failure.
