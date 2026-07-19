# Glaurung real-query proof populations

This directory contains committed, machine-readable selections for QF_BV proof
and end-to-end faithfulness measurements. These are assurance denominators, not
solver-performance corpora.

## Corrected-wide-v3 proof holdout v1

[`corrected-wide-v3-proof-holdout-v1-registration.json`](corrected-wide-v3-proof-holdout-v1-registration.json)
preregisters the exact sources, selection policy, execution bounds, acceptance
gates, and claim limits. The selected
[`corrected-wide-v3-proof-holdout-v1.json`](corrected-wide-v3-proof-holdout-v1.json)
contains 1,024 queries: 515 SAT and 509 UNSAT.

The selector excludes all 162 hashes in the accepted corrected representative,
then takes the lowest content hashes under fixed family/verdict quotas. It does
not inspect proof completion, certificate status, or timing. Reproduce it with:

```sh
python3 scripts/select-glaurung-proof-holdout.py \
  --full-manifest /nas4/data/workspace-infosec/glaurung-captures/2026-07-16-corrected-wide-v3/full/manifest-v1.json \
  --representative-manifest /nas4/data/workspace-infosec/glaurung-captures/2026-07-16-corrected-wide-v3/representative/manifest-v1.json \
  --out /tmp/corrected-wide-v3-proof-holdout-v1.json
```

The committed manifest SHA-256 is
`67c7f14f5f2f8db1eaa1bb17649cf3623e268e3f7ea678cbe53326bfa8cd899b`.
ADR-0251 requires execution from its clean detached preregistration commit and
retains every resource-bounded `not-certified` row in the denominator.

ADR-0252 preserves the first full-root membership rejection and preregisters an
exact materialization boundary. Reproduce the execution corpus in a new path:

```sh
python3 scripts/materialize-glaurung-proof-holdout.py \
  --source-root /nas4/data/workspace-infosec/glaurung-captures/2026-07-16-corrected-wide-v3/full \
  --full-manifest /nas4/data/workspace-infosec/glaurung-captures/2026-07-16-corrected-wide-v3/full/manifest-v1.json \
  --selected-manifest corpus/glaurung-proof-populations/corrected-wide-v3-proof-holdout-v1.json \
  --out /tmp/corrected-wide-v3-proof-holdout-v1-corpus
```

The materializer verifies both manifest hashes, exact full-manifest membership,
all source and destination query bytes, byte-identical destination manifest,
and exact destination `.smt2` membership. It refuses an existing destination.
Its machine-readable preregistration is
[`corrected-wide-v3-proof-holdout-v1-materialization-registration.json`](corrected-wide-v3-proof-holdout-v1-materialization-registration.json).
