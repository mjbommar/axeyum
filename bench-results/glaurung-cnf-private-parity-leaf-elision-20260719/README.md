# Glaurung private parity-leaf elision — 2026-07-19

Status: rejected at the preregistered structural gate; timing not run

ADR-0261 selected one bounded interpretation of ADR-0260's dominant origin
cell: normalize private parity leaves within one positive direct-root AND tree
and elide later identical keys before clause generation. The implementation
was committed before observation as Axeyum `8b95d42a` and measured from clean
detached revision `8b95d42aa264c94c30df14fb9d114a6973b6a62c`.

## Population and correctness

The run uses the unchanged corrected-wide-v3 representative manifest SHA-256
`7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064`:

- 162 raw QF_BV queries: 88 SAT and 74 UNSAT;
- family counts 36 arithmetic, 12 comparison, 7 mixed, 52 register-slice,
  54 slice-partial, and 1 trivial;
- 162/162 manifest agreements and 162/162 in-process Z3 agreements;
- all 88 SAT original-model replays; and
- zero Unknown, unsupported, error, disagreement, or replay failure.

The retained files are:

- [`artifact.json`](artifact.json), SHA-256
  `33638089305423bb3e4eb1877b713f5480087593d929f8cec8eb5958f47f6621`;
- [`analysis.json`](analysis.json), SHA-256
  `17134ac51497b024303435b42884a3817e1654fcb3a88ba9b5668786447c0066`.

Artifact identity remains version 36, config hash `3031046d19deeb81`, and
corpus hash `23932b876da74bd1`.

## Structural result

The candidate changes none of ADR-0261's preselected counters:

| Counter | Baseline `1bce10fd` | Candidate `8b95d42a` | Required delta | Observed delta |
|---|---:|---:|---:|---:|
| Clause attempts | 396,270 | 396,270 | -107,000 | 0 |
| Exact duplicates | 119,260 | 119,260 | -107,000 | 0 |
| Canonical attempted literals | 894,543 | 894,543 | -214,000 | 0 |
| Emitted clauses | 271,991 | 271,991 | 0 | 0 |

Every per-query outcome, DAG/AIG construction record, CNF variable count,
emitted-clause count, attempt count, duplicate count, and canonical-literal
count is identical. The independent analysis is byte-identical to ADR-0260's
accepted analysis and therefore has the same SHA-256.

ADR-0260 identified equal clauses from the same owner and emission template;
it did not establish that the enclosing parity leaves had identical normalized
keys. ADR-0261's stronger mechanism inference is false on this population.
Under the preregistered rule, a non-exact structural delta rejects the
candidate. The unprofiled six-pair timing protocol was not run, and the
candidate must not be retained or described as an optimization.

## Command

```sh
MEM_LIMIT_GB=8 CARGO_BUILD_JOBS=2 scripts/mem-run.sh \
  cargo run --release -j1 -p axeyum-bench --features z3 -- \
  /nas4/data/workspace-infosec/glaurung-captures/2026-07-16-corrected-wide-v3/representative \
  --corpus-manifest /nas4/data/workspace-infosec/glaurung-captures/2026-07-16-corrected-wide-v3/representative/manifest-v1.json \
  --corpus-tier representative --backend sat-bv --rewrite off \
  --profile-cnf-construction --compare-z3 --require-in-process-z3 \
  --require-reproducible-run --require-deterministic-resources \
  --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 \
  --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 \
  --min-decided-percent 100 --logic QF_BV --out artifact.json
```
