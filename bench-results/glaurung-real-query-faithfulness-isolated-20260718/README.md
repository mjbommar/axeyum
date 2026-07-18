# Glaurung real-query QF_BV process-isolated faithfulness — 2026-07-18

Status: accepted corrected-representative whole-certificate denominator

This bundle repeats ADR-0234's complete corrected five-driver denominator with
artifact-v34's killable subprocess boundary. Every primary UNSAT launches the
same pinned executable as a one-query worker. The worker re-reads and hashes
the exact source, parses it, constructs both proof routes, and self-rechecks
both stored certificate texts. The parent retains every row and kills/reaps a
worker that crosses the declared whole-process wall.

## Contract

- clean Axeyum source: `e1be4bd19efdc650dcea974469cd269a9270b436`
- artifact schema: v34
- manifest: `glaurung-qfbv-2026-07-16-corrected-wide-v3`, 162 exact
  content-hashed rows from ADR-0187's accepted five-driver capture
- manifest SHA-256:
  `7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064`
- accepted policy: 1000 ms cooperative proof-search deadline nested inside a
  1500 ms whole-worker timeout
- execution: raw/full query, proof-producing SAT core, in-process Z3,
  deterministic resources, one worker, CPU 3
- repetitions: two independent clean processes with identical source,
  configuration, environment, manifest, and per-query outcomes
- fatal: manifest/oracle disagreement, missing CNF proof, source drift, worker
  crash or malformed protocol, satisfiable contradiction, certificate recheck
  failure, operational error, identity drift, or per-query drift

A hard timeout is an accepted `not-certified` coverage miss, never a solver
verdict or dropped row. The parent starts the budget before spawning the worker;
observed return can exceed the nominal wall by scheduler, one-millisecond poll,
kill, and reap overhead. Certificate-process time remains separate assurance
work and is excluded from cold/warm solver comparisons.

## Accepted result

Both clean repetitions produce the same complete population:

| Population | Per run | Result |
|---|---:|---|
| Exact manifest rows | 162 | 162 decided, 0 Unknown/unsupported/error |
| SAT | 88 | 88 original-query model replays, 0 failures |
| UNSAT CNF DRAT | 74 | 74 checked, 0 missing |
| Process-isolated end-to-end attempts | 74 | 74 certified, 0 not-certified |
| Hard whole-worker timeouts | 74 | 0 |
| Z3 and manifest comparisons | 324 | all agree, 0 disagreement/skip |

The certified family split is 26 `register-slice`, 24 `slice-partial`, 18
`arithmetic`, 5 `comparison`, and 1 `mixed`.

Whole-worker assurance telemetry is descriptive, not solver performance:

| Run | p50 | p95 | max | total |
|---|---:|---:|---:|---:|
| 1 | 3.457 ms | 60.108 ms | 155.685 ms | 0.929 s |
| 2 | 3.534 ms | 59.098 ms | 157.768 ms | 0.927 s |

## Kill-path control

A separate clean run keeps the same 162-query source, manifest, solver, and
1000 ms cooperative search policy but sets the whole-worker wall to 1 ms. It
still decides all 162 primary queries, replays all 88 SAT models, and rechecks
all 74 primary CNF DRAT proofs. All 74 UNSAT rows then enter exactly one
end-to-end bucket as `not-certified` plus `hard_timeout`; zero row is omitted,
and zero contradiction, recheck failure, worker error, or other alarm occurs.

The kill-control elapsed distribution is p50 1.172 ms, p95 1.299 ms, and max
1.456 ms including process scheduling, kill, and reap. Its raw SHA-256 is
`485c19d0237ff00f51a1035514d6d419cb233bc7fd2d802ce18cc13ad84b1026`.

## Artifacts and reproduction

- [`analysis.json`](analysis.json) is the fail-closed two-run join.
- [`raw/artifact-v34.json`](raw/artifact-v34.json) and
  [`raw/artifact-v34-run2.json`](raw/artifact-v34-run2.json) are the accepted
  repeated artifacts.
- [`raw/hard-timeout-control-v34.json`](raw/hard-timeout-control-v34.json) is
  the deliberate 1 ms kill-path control.

Run the accepted policy from a clean source tree:

```sh
just bench-glaurung-qfbv-real-faithfulness \
  /path/to/corrected-wide-v3/representative \
  /path/to/corrected-wide-v3/representative/manifest-v1.json \
  representative \
  1000 \
  1500 \
  /tmp/faithfulness-isolated.json
```

Join at least two identity-matched accepted runs:

```sh
python3 scripts/analyze-qfbv-faithfulness.py \
  --out analysis.json run-1.json run-2.json
```

## Claim boundary and next step

This closes the previously explicit whole-certificate isolation gap on the
corrected 74-row representative UNSAT denominator. It does not cover the
30,628-query corrected full corpus, produce an externally standardized proof
format, or change any performance conclusion. Wider real manifests, independent
fuzz seeds plus another neutral implementation, and timeout-sensitive/wider
sole-authority findings remain publication work.
