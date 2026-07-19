# Glaurung cold CNF construction profile — 2026-07-19

Status: accepted fixed-population diagnostic; no optimization selected

ADR-0259 preregistered one opt-in, production-zero-overhead-off detailed CNF
construction profile before any corrected-wide-v3 query was executed through
that profile. The measurement then ran from clean detached Axeyum commit
`d29470cfe02696a7675efeff295030597a183c10`.

## Population and gates

- corrected-wide-v3 representative manifest SHA-256
  `7818686bc26c56646775eb2f557e1e4edb36e4e8254a8c410fe0333da1ba2064`;
- 162 raw QF_BV queries: 88 SAT and 74 UNSAT;
- exact family counts: arithmetic 36, comparison 12, mixed 7,
  register-slice 52, slice-partial 54, trivial 1;
- `sat-bv`, rewrite off, in-process Z3, one worker, deterministic resource
  limits, and a 10-second safety wall; and
- 162/162 manifest agreements, 162/162 Z3 agreements, 88/88 original-model
  replays, zero Unknown/unsupported/error/disagreement, and all six profile
  identities true.

The retained files are:

- [`artifact.json`](artifact.json), SHA-256
  `7125de24e81a32e3847acb92d2b15450317f121cdccd733d28d4821ab426003b`;
- [`analysis.json`](analysis.json), SHA-256
  `e7c8bcdab62b52b5ec4feb07a4e3f7d63dd5bd53de2e37f98927a410a877116f`.

Artifact identity is version 35, config hash `18d81c58b58db304`, and corpus hash
`23932b876da74bd1`.

## Exact result

The encoder attempted 396,270 clauses. Of 391,251 non-tautological attempts,
271,991 were emitted and 119,260 were exact duplicates, a 30.4817% duplicate
rate. Every duplicate was an exact hit in the primary fingerprint entry:
collision-bucket comparisons, collision duplicates, and genuine fingerprint
collisions were all zero. Repeated-literal drops and complementary-literal
tautologies were also zero.

The profile visited all 1,085,685 declared literals and dropped 186,123 false
constants (17.1434%). All 5,019 tautologies came from a true constant. The
391,251 canonical attempts were 34 empty, 22,730 unit, 255,330 binary, 112,144
ternary, and 1,013 larger clauses.

| Family | Non-taut attempts | Exact duplicates | Duplicate rate | Share of all duplicates |
|---|---:|---:|---:|---:|
| arithmetic | 32,111 | 128 | 0.3986% | 0.1073% |
| comparison | 1,305 | 492 | 37.7011% | 0.4125% |
| mixed | 132 | 0 | 0% | 0% |
| register-slice | 137,078 | 31,035 | 22.6404% | 26.0230% |
| slice-partial | 220,625 | 87,605 | 39.7076% | 73.4572% |
| trivial | 0 | 0 | n/a | 0% |

Slice-partial SAT rows contain 87,525 of their family's 87,605 duplicates;
register-slice SAT/UNSAT rows contain 16,718/14,317. That outcome concentration
is descriptive, not a causal or performance claim.

## Decision and limits

This result rejects another collision-table/index redesign for this population:
the collision path performed no work. It also gives no support to optimizing
repeated-literal or complementary-literal canonicalization. The material
residual is upstream generation of exact duplicate clauses, concentrated in
slice-partial and register-slice queries.

Counts are not time. In particular, removing 30.4817% of non-tautological
attempts must not be presented as a 30% wall-time opportunity. ADR-0259 selects
no optimization. ADR-0260 preregisters a profile-only first-origin/duplicate-
origin measurement before any generator-elision change is considered.

## Command

```sh
scripts/mem-run.sh env CARGO_BUILD_JOBS=2 cargo run --release -j1 \
  -p axeyum-bench --features z3 -- \
  /nas4/data/workspace-infosec/glaurung-captures/2026-07-16-corrected-wide-v3/representative \
  --corpus-manifest /nas4/data/workspace-infosec/glaurung-captures/2026-07-16-corrected-wide-v3/representative/manifest-v1.json \
  --corpus-tier representative --backend sat-bv --rewrite off \
  --profile-cnf-construction --compare-z3 --require-in-process-z3 \
  --require-reproducible-run --require-deterministic-resources \
  --timeout-ms 10000 --resource-limit 2000000 --node-budget 300000 \
  --cnf-var-budget 3000000 --cnf-clause-budget 8000000 --jobs 1 \
  --min-decided-percent 100 --logic QF_BV --out artifact.json
```
