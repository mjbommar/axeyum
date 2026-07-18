# Glaurung real-query QF_BV faithfulness — 2026-07-18

Status: accepted representative real-query assurance denominator

This bundle extends ADR-0230's CNF-only assurance method by running the
independent-reference bit-blast miter and final CNF DRAT refutation over every
UNSAT row in the current corrected 162-query Glaurung representative manifest.
No row is selected after execution and an expiry would remain in the denominator as
`not-certified`.

## Contract

- clean Axeyum source: `21738d4291735bd1986c9cce40ade4f0816dbc50`
- artifact schema: v33
- manifest: `glaurung-qfbv-2026-07-16-corrected-wide-v3`, 162 exact
  content-hashed rows from the accepted five-driver capture
- manifest SHA-256:
  `7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064`
- policy: raw rewrite-off, full query, proof-producing SAT core, in-process Z3,
  deterministic resource bounds, one worker, CPU 3
- end-to-end deadline: 1000 ms shared by the faithfulness-miter and final-UNSAT
  proof searches for each primary UNSAT
- repetition boundary: two independent clean processes with identical source,
  configuration, environment, manifest, and per-query outcomes
- fatal: manifest/oracle disagreement, missing CNF proof, end-to-end
  satisfiable contradiction, certificate recheck failure, operational error,
  identity drift, or per-query certification drift

The deadline is cooperative proof-search policy. Independent-reference/AIG/CNF
construction and checking of a completed certificate remain outside the hard
wall-clock guarantee; whole-process isolation is still open.

## Result

Both clean repetitions produce the same complete assurance population:

| Population | Per run | Result |
|---|---:|---|
| Exact manifest rows | 162 | 162 decided, 0 Unknown/unsupported/error |
| SAT | 88 | 88 original-query model replays, 0 failures |
| UNSAT CNF DRAT | 74 | 74 checked, 0 missing |
| UNSAT end-to-end attempts | 74 | 74 certified, 0 not-certified |
| Z3 comparisons | 162 | 162 agree, 0 disagreement/skip |
| Manifest comparisons | 162 | 162 agree, 0 disagreement |

End-to-end coverage is therefore **74/74 (100%)** over the complete declared
real-query UNSAT denominator in both runs. The certified family split is 24
`slice-partial`, 26 `register-slice`, 18 `arithmetic`, 5 `comparison`, and 1
`mixed`.

The certificate-work distributions are descriptive assurance telemetry, not
solver performance:

| Run | p50 | p95 | max | total |
|---|---:|---:|---:|---:|
| 1 | 0.930 ms | 55.101 ms | 152.718 ms | 0.679 s |
| 2 | 1.167 ms | 55.445 ms | 154.163 ms | 0.692 s |

The observed maximum leaves headroom under the declared 1000 ms proof-search
policy; ADR-0231 separately retains generated rows that do expire under its
tighter policy. These timers include completed-proof rechecking and must not be
added to, or compared with, the ordinary cold/warm solver map.

## Artifacts and reproduction

- [`analysis.json`](analysis.json) is the fail-closed two-run join.
- [`raw/artifact-v33.json`](raw/artifact-v33.json) and
  [`raw/artifact-v33-run2.json`](raw/artifact-v33-run2.json) retain every query
  hash, result, manifest/oracle comparison, CNF-proof state, end-to-end state,
  policy, resource identity, and timing field.

Run the manifest-bound recipe from a clean source tree:

```sh
just bench-glaurung-qfbv-real-faithfulness \
  /path/to/corrected-wide-v3/representative \
  /path/to/corrected-wide-v3/representative/manifest-v1.json \
  representative \
  1000 \
  /tmp/faithfulness-run.json
```

Join at least two identity-matched runs:

```sh
python3 scripts/analyze-qfbv-faithfulness.py \
  --out analysis.json run-1.json run-2.json
```

## Claim boundary and next step

This closes term-to-CNF faithfulness on the current corrected representative
74-row real UNSAT denominator. It does not cover the 30,628-query corrected
full corpus, guarantee a 1000 ms whole-call wall time, produce an externally
standardized proof format, or change any performance conclusion. Next proof
work is whole-certificate process isolation and wider real manifests; the next
independent correctness blocker is new fuzz seeds plus another neutral
implementation.
