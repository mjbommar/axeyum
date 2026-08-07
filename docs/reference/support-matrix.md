# Support Matrix

The authoritative table is the
[generated support matrix](../research/08-planning/support-matrix.md). It keeps
these layers separate for each feature/fragment:

- typed IR;
- ground evaluator;
- SMT-LIB parser/writer;
- native oracle;
- pure-Rust decision route; and
- evidence/model/proof support.

Do not duplicate the rows here. The source table is rendered from
`axeyum_solver::support_matrix` and protected by a golden test:

```sh
cargo test -p axeyum-solver --test support_matrix --features full
```

When intentionally changing the source ledger, follow the regeneration command
printed by the failing golden test, inspect the full diff, and update capability,
trust, limitations, and benchmark claims in the same change.

## How to read it

“Done” in one column does not imply end-to-end support. Examples:

- parser support without a pure-Rust route can still end in `Unsupported`;
- an evaluator without model lifting cannot justify `sat`;
- an oracle comparison validates a verdict but is not per-query evidence;
- a solver route without a checked proof may have lower-assurance `unsat`; and
- bounded support must retain its bound and return `unknown` beyond it.

For assurance detail, use the [Trust ledger](trust-ledger.md). For what was
measured rather than merely implemented, use
[Benchmark results](../../bench-results/README.md).

