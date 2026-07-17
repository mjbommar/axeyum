# Glaurung real-query DRAT coverage — 2026-07-17

This artifact runs the committed fail-closed proof recipe over the 128-query
representative Glaurung QF_BV corpus. Axeyum and Z3 decide all 128 queries,
agree with each other and the manifest on every row, and replay all 64 SAT
models. Every one of the 64 UNSAT rows carries an inline proof-producing-core
DRAT certificate that independently rechecks; none is missing.

| Population | Rows | Checked result |
|---|---:|---|
| Representative real Glaurung QF_BV queries | 128 | 128 decided, 0 Unknown/error |
| SAT | 64 | 64 original-query model replays, 0 failures |
| UNSAT | 64 | 64 inline DRAT rechecks, 0 missing |
| Z3 comparisons | 128 | 128 agree, 0 disagree/skip |
| Manifest comparisons | 128 | 128 agree, 0 disagree |

The UNSAT family split is 24 `register-slice`, 24 `slice-partial`, 11
`arithmetic`, and 5 `comparison` queries. Thus the proof result is a concrete
client-derived use case rather than a synthetic proof smoke.

## Identity and command

- Axeyum revision: `0e6287646d026c37c1cf456e2872a32830c598ff`,
  measured from a clean detached worktree.
- Corpus manifest: `glaurung-qfbv-2026-07-v1`, 128 exact content-hashed
  members, SHA-256
  `0556f77bad1ca74e49f57ef0ad01d2967391c9937fbe0cfd805e24d8fce2e68d`.
- Report SHA-256:
  `88a33fd2644ec81b043f59780db4a28b8c164bb91332e5c0033be68a3e4a7df8`.
- Configuration hash: `34284b3831fbb7cb`.
- Environment hash:
  `83bf3161219d530aa28d371cdea9596c0292978b883f5d67ac82540394ce4543`.

The semantic recipe is the `bench-glaurung-qfbv-raw-proof-check` target:

```sh
cargo run --release -p axeyum-bench --features z3 -- \
  CORPUS_DIR --corpus-manifest MANIFEST --corpus-tier representative \
  --backend sat-bv --rewrite off --prove-unsat --compare-z3 \
  --require-in-process-z3 --require-reproducible-run \
  --require-deterministic-resources --timeout-ms 30000 \
  --resource-limit 2000000 --node-budget 300000 \
  --cnf-var-budget 3000000 --cnf-clause-budget 8000000 \
  --jobs 1 --min-decided-percent 100 --logic QF_BV --out report.json
```

[`report.json`](report.json) retains every per-query content hash, expected and
observed result, formula/AIG/CNF size, proof-replay state and time, model
replay, oracle comparison, resource configuration, toolchain, and source
identity. It is a compact projection of the benchmark's machine report; proof
recheck time is nested inside solve time and is not added twice to the pipeline
total.

## Claim boundary

This establishes 64/64 rechecked CNF DRAT coverage over the declared real-query
UNSAT denominator. It does not establish end-to-end term-to-CNF faithfulness:
plain DRAT checks the emitted CNF refutation, while ADR-0226's stronger route
also certifies bit-blast faithfulness on a separate generated subset. These
denominators must remain distinct.

The report's performance fields are incidental proof-gate measurements, not a
paper speed comparison: the proof-producing core and 30-second proof recipe do
not match the four-cell Glaurung topology. The corpus is a content-hashed
capture whose source manifest identifies three Glaurung drivers; this artifact
does not claim coverage of all 9,526 accepted live checks or the fourth fair-map
driver.
