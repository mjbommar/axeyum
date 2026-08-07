# QF_NIA A3 large-core cluster v1 result — 2026-08-07

## Verdict

The diagnostic hypothesis is **confirmed** for the preregistered pair. Both
rows repeatedly produce hundreds of broad arithmetic conflict cores because
the exact inconsistent set exceeds the existing 128-atom deletion-minimization
guard. Deadline-only admission is not the common cause.

No solver policy changed in this increment. The diagnostic only splits the
existing `Large` source by reason and reports fixed size buckets when
`AXEYUM_NIA_LARGE_CORE_DIAGNOSTIC` is set. The ordinary production summary is
unchanged.

This result authorizes mechanism selection under the original preregistration;
it does not by itself authorize a retained solver change. The separately
preregistered v2 experiment tests deterministic, sound group deletion.

## Bound inputs and protocol

- integrated baseline:
  `bd413357cd967aed0f2f5a1281ca0a6a8f9a276b`;
- diagnostic documentation checkpoint:
  `cd98b98958b141d84da74fb9b39e26970765af23`;
- target-list SHA-256:
  `09d46491340903af0181bde3cf8f08af073268b1b62bc937349d4eab5aecde17`;
- routing-control-list SHA-256:
  `df0e044140a72a4e8fa0eb733745e9d7b91e2f6b014b586fb0302ee34403a05b`;
- diagnostic release-binary SHA-256:
  `405d6cc3557fafbb5168366c4598cb7093d2c2d1c0e70caa4542fb26f29c4dc4`;
- per-query memory limit: 8 GiB;
- query timeout: 24,000 ms;
- direct observations: three per target, serialized on CPU 4 to reduce
  interference from unrelated host work.

The exact command shape was:

```sh
AXEYUM_NIA_LARGE_CORE_DIAGNOSTIC=1 MEM_LIMIT_GB=8 timeout 40 \
  ./scripts/mem-run.sh taskset -c 4 \
  target/release/examples/explain_corpus \
  --list <one-row-preregistered-list> 24000 --json
```

CPU affinity changes scheduling only; the registered memory and wall-clock
limits remained unchanged.

## Direct observations

| Target | Run | Terminal path | Large cores | Admission reason | Length bucket |
|---|---:|---|---:|---|---|
| `SAT14/1051.smt2` | 1 | warm SAT skeleton timeout after 202 rounds | 179 | 178 size-only, 1 size+deadline | 179 in 513–1,024 |
| `SAT14/1051.smt2` | 2 | warm SAT skeleton timeout after 192 rounds | 170 | 170 size-only | 170 in 513–1,024 |
| `SAT14/1051.smt2` | 3 | warm SAT skeleton timeout after 202 rounds | 179 | 179 size-only | 179 in 513–1,024 |
| `SAT14/1280.smt2` | 1 | lazy-loop timeout after 391 rounds | 363 | 362 size-only, 1 size+deadline | 363 in 257–512 |
| `SAT14/1280.smt2` | 2 | warm SAT skeleton timeout after 397 rounds | 369 | 369 size-only | 369 in 257–512 |
| `SAT14/1280.smt2` | 3 | reconstruction deadline | n/a | route did not enter the measured loop | n/a |

For `1051`, the repeated core maxima were 653 and the representative average
lengths were 449.3–454.3. For `1280`, the repeated core maxima were 490 and the
representative averages were 308.3–309.6. Neither repeated path attempted an
arithmetic support model or full fallback; each conflict batch added another
broad blocking clause to the same warm Boolean skeleton.

## Causal conclusion

The required threshold is met: `1051` reproduces size-admission large cores in
3/3 observations and `1280` in 2/3. Across those five reproductions, deadline-
only admission occurs zero times. The common actionable downstream mechanism
is repeated insertion of broad, valid but low-quality theory-conflict clauses
into a warm SAT skeleton until either that solver or the shared lazy loop
exhausts the query budget.

The third `1280` observation is retained as route-instability evidence rather
than discarded. It does not negate the 2/3 threshold, and it forbids claiming
that every run reaches the cluster.

Arbitrary truncation, sampling, or literal dropping would be unsound. A smaller
core may replace the broad clause only after the same deadline-bounded theory
oracle independently proves the retained subset unsatisfiable. That observation
selects bounded group deletion as the v2 experiment.

## Gate state

The diagnostic instrumentation passed:

- `cargo test -p axeyum-solver --all-features
  dpll_lia::tests::arith_core_stats_report_source_counts` — 1 passed;
- `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --all-features` — exit 0;
- `cargo fmt --all --check` and `git diff --check` — exit 0.

Routing controls, retained-decision controls, and the aggregate gate belong to
the v2 implementation experiment. No 200-row measurement is authorized before
the v2 two-target A/B and mandatory controls pass.
