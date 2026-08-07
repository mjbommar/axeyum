# QF_NIA A3 clause-estimate attribution v1 result — 2026-08-07

## Verdict

V1 stopped fail-closed on both frozen targets. The exact structural-demand
transfer table generated 8,000,001 term-bit requests and tripped the
preregistered 8,000,000-request ceiling before serialization. No AIG, CNF,
solver, model, or verdict path ran; no production edit or target credit is
authorized.

This is a diagnostic-algorithm rejection, not evidence that structural demand
is intrinsically too large. The copied production transfer table redundantly
requests every child bit once for every demanded output bit of a non-local
arithmetic operator. Its fixed point can be computed equivalently by scheduling
each unique term bit once and propagating each full arithmetic barrier once.
That deduplication requires a separately frozen v2 protocol; the v1 work bound
must not be raised retrospectively.

## Exact boundary and observations

The preregistration is
[`qf-nia-a3-clause-estimate-attribution-v1-preregistration-2026-08-07.md`](qf-nia-a3-clause-estimate-attribution-v1-preregistration-2026-08-07.md).
Its clean source boundary is
`6d881816c5669d049a97b62d6e495109b53b876b`; the preregistration commit is
`0d77f0fd9`. The release diagnostic built after format, focused tests, and
warning-denied example Clippy has SHA-256
`77fbc553c009463575e670a91d22b2d8f80ff2c3ed22049f02a8ca539d82e7bf`.

Both frozen source digests passed before analysis. Both exact runs then exited
1 with:

```text
clause_estimate_attribution: structural-demand request limit exceeded: 8000001 > 8000000
```

| Target | Exit | Elapsed | Maximum RSS | Serialized bytes |
|---|---:|---:|---:|---:|
| `p31818` | 1 | 0.03 s | 6,228 KiB | 0 |
| `p6984` | 1 | 0.02 s | 7,260 KiB | 0 |

The empty outputs are intentional: the preregistration requires a nonzero exit
and no partial artifact after any work-limit failure. Exact estimate and grouped
attribution were computed before demand, but are not accepted as a v1 result
because the complete-record contract failed.

## Retained diagnostic and gates

`crates/axeyum-bench/examples/clause_estimate_attribution.rs` remains a
non-production reproducer. It accepts only the two frozen basenames, verifies
their source SHA-256 values, parses the ordinary flat view, blasts at width 32,
recomputes the production estimator over the shared DAG, classifies immediate
constant multipliers, and copies the existing structural-demand transfer rules.
It contains no call to a lowerer or solver.

Focused evidence:

- `cargo test -p axeyum-bench --example clause_estimate_attribution`: 2/2 pass;
- `cargo clippy -p axeyum-bench --example clause_estimate_attribution -- -D warnings`: pass;
- `cargo fmt --all -- --check`: pass after formatting; and
- `git diff --check`: pass.

No broader or 200-row gate is authorized because no target observation was
admissible.

## Next bounded action

Preregister v2 before changing the diagnostic. Preserve the same sources,
width, production estimate formula, source digests, 64,000,000 production
ceiling, and prohibition on lowering/solving. Replace redundant request-stack
accounting with an exact monotone fixed point that schedules each unique
term-bit once and propagates a full arithmetic barrier once, with independent
caps on unique term bits and transfer edges. If that bounded computation still
cannot produce two complete records, close the estimate-attribution route and
move to the next canonical work item without a solver edit.
