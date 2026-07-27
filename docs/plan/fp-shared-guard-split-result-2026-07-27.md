# Narrow shared-guard split on the QF_BVFP hard tail — 2026-07-27

## Bounded verdict

The pure-Rust SAT-BV backend now recognizes one measured counterexample shape:
a large single disjunction whose unique non-false leaves are all
`not(implies(A, C_i))` for the same antecedent `A`. It solves those leaves in
deterministic order under one shared deadline. All-branch UNSAT transfers to the
original disjunction; a SAT branch is accepted only after model completion and
replay against the complete original root.

On the exact 34-file public `QF_BVFP/ramalho/esbmc` population at a five-second
per-instance budget, the pure-Rust backend moves from 30/34 to 34/34 decided.
All 34 results are the declared and Z3 4.13.3 `unsat` verdict, with zero
disagreement, errors, or model-replay failures. This closes the selected
population's four-row hard tail; it does not close the broader selected
QF_FP/QF_BVFP/QF_ABVFP full-library rerun.

## Selection and rejected alternatives

The four predecessor timeouts were:

- `Float4-main.smt2`;
- `Float4_1-main.smt2`;
- `Float-no-simp2-main.smt2`; and
- `Float-no-simp2_1-main.smt2`.

Post-policy preprocessing was already cheap. The two no-simp formulas produced
identical 439,234-clause / 118,037-variable CNFs; the two Float4 formulas
produced identical 921,561-clause / 247,458-variable CNFs. SAT search dominated.
At 20 seconds on a representative no-simp row, the default finished in 9.672 s,
vivification in 10.670 s, inprocessing in 18.076 s, and the native core remained
undecided at the tested limit. Those results rejected a default knob change.

Flattening the post-policy top-level `or` exposed five unique non-false branches
for the no-simp pair and a bounded repeated-obligation set for Float4. Direct
branch probes were cheaper in aggregate than the monolithic CNF. ADR-0065's
earlier broad-split regression ruled out general disjunction splitting, so
ADR-0367 admits only this exact shared-antecedent form, 4--16 unique branches,
and at least 5,000 reachable DAG nodes.

## Implementation

Implementation commit:
`b6c3d486f110f449b75958614d6a5a4831340d7c`.

The route is local to `SatBvBackend`. It requires a configured timeout, declines
when an internal query replay plan is present, removes only literal-false leaves,
deduplicates deterministically by `TermId`, and disables recursive splitting in
branch backends. Each branch receives a fair share of the remaining global
deadline. One unknown makes the aggregate unknown; errors stay errors.

For SAT, missing symbols are completed with sort-correct well-founded defaults
and the returned assignment must evaluate the original assertion to `true`.
This maintains the project's original-term replay rule. For UNSAT, the transfer
is the exact equivalence that a disjunction is UNSAT iff every disjunct is
UNSAT; it does not add proof-producing assurance beyond the existing BatSat
route.

## Population result

The authoritative current-host run used one worker to avoid conflating solver
behavior with a concurrent external multi-process workload:

```text
files=34 sat=0 unsat=34 unknown=0 unsupported=0 errors=0
agree=34 DISAGREE=0 model_replay_failures=0
decided_percent=100.00 par2_mean_s=0.490
```

The four former residual cold totals were 1.609 s, 1.624 s, 3.752 s, and
3.948 s. The immediate predecessor artifact used four workers and reported
30 UNSAT / four timeout unknowns with PAR-2 1.348 s. Because worker count and
host load differ, the decide-rate delta and exact current timings are retained,
but no aggregate parallel speedup ratio is claimed.

Two attempted four-worker current runs exceeded outer ceilings while another
workspace was consuming multiple cores; neither produced an artifact. A
temporary single-row trace, removed before commit, showed five branch decisions,
no recursion, and a 1.812 s total. These observations are disclosed as
load-sensitive diagnostics, not accepted benchmark evidence.

Local artifact:
`/tmp/axeyum-qfbvfp-esbmc-shared-guard-split-j1-20260727.json`, SHA-256
`6470e79d4bb3207aac3dca91f8487148582307ba73a1178a49226d245c60436c`
(not committed, so not durable evidence by itself). The exact release benchmark
binary used for that artifact has SHA-256
`52136133642cbb29bdc79f6f1452a1651447a6ff548b7348fab3bae55f1f78b9`.

## Verification

- `cargo test -p axeyum-solver --all-features shared_guard_split`: two passed;
- `cargo clippy -p axeyum-solver --all-targets --all-features -- -D warnings`:
  passed;
- `cargo fmt --all --check`: passed;
- `./scripts/check-links.sh`: passed;
- the serial 34-file Z3 comparison above: 34/34 agreement.

The focused tests cover structural admission and decline, all-branch UNSAT,
SAT model completion, and replay of the original disjunction. Full `just check`,
remote CI, push, origin/main integration, proof-producing UNSAT, parallel
throughput, and credited full-library completion are not claimed here.

## Next bounded step

Return to the selected SMT-LIB residue map rather than widen this route. The
next increment should select a different measured cluster, preserve the 34/34
ESBMC population as a no-loss gate, and keep proof-producing UNSAT and full-run
resume evidence separate from decide-rate progress.
