# ADR-0188: Corrected Glaurung shard variance and alarms

Status: accepted
Date: 2026-07-16

## Context

ADR-0187 accepted one clean full-corpus composite but explicitly did not treat
its four child shards as statistical repetitions. GQ10 still required an
identical second complete composite and an executable cross-commit comparator
before the corrected corpus could control performance regressions.

## Decision

Accept two same-revision complete raw and canonical composites as the initial
corrected-corpus variance baseline. Each repetition contains all four
deterministic process shards and all 30,628 queries. Retain the existing
same-environment alarms for corrected full-tier comparisons:

- maximum 3% Axeyum mean regression;
- maximum 3% normalized Axeyum/Z3 ratio regression;
- maximum 5% maximum-child-RSS regression; and
- maximum 2% absolute Z3 control drift.

`summarize-glaurung-shard-repetitions.py` recomputes every source composite,
requires exact capture/source/configuration/outcome/rewrite/construction/shard
identity, and reports statistics only over whole composites.
`compare-glaurung-shard-repetitions.py` then permits a different clean source
revision and code-induced deterministic construction changes, but rejects
corpus, environment, toolchain, solver-policy, or resource drift before
applying the explicit alarms. Raw Axeyum, Z3, normalized ratio, peak child RSS,
and every stage remain visible.

These are conservative regression alarms, not a significance test or a
hardware-independent performance promise. More repetitions may refine them;
they may not be weakened merely to admit a candidate.

## Evidence

Both composites use clean Axeyum `f7f174c5`, environment hash
`b0f5781b8c70707448fec92aba7d68bdb8fed9b245c55926b1156bc038e7aa7a`,
the ADR-0187 capture/shard identities, jobs=1, manifest jobs=8, deterministic
resource limits, in-process Z3, original-model replay, and a hard 4 GiB child
envelope. All 122,512 policy/query executions decide and agree, and canonical
construction is byte-count deterministic across repetitions.

Raw complete-composite results:

- Axeyum 30.802801 / 31.003068 seconds; mean 30.902934, sample CV 0.458%;
- Z3 69.126627 / 69.674081 seconds; mean 69.400354, CV 0.558%;
- ratio 0.445600 / 0.444973; mean 0.445286, CV 0.100%;
- maximum child RSS 1,445,304 / 1,407,176 KiB; CV 1.890%; and
- every nonzero attributed stage has CV at most 0.526%.

Canonical-v4 complete-composite results:

- Axeyum 18.470722 / 18.266163 seconds; mean 18.368442, sample CV 0.787%;
- Z3 68.556019 / 68.701218 seconds; mean 68.628618, CV 0.150%;
- ratio 0.269425 / 0.265878; mean 0.267652, CV 0.937%;
- maximum child RSS 1,424,500 / 1,425,284 KiB; CV 0.039%; and
- the largest stage CV is word preprocessing at 1.362%; all other nonzero
  stages are at most 0.803%.

The fail-closed raw/canonical repetition-summary SHA-256 values are
`58c85262eddc68b2b4241d1f5c3da6b610cabc9150bf79e1e35cd89bd4568fb2`
and
`34873d2ce0e823c4f1be869816652c08f4bf4630053bb2e01516d43242812d70`.
Forty-six benchmark-infrastructure tests cover source recomputation,
deterministic-work drift, capture drift, clean-revision identity, and passing
and failing alarm outcomes.

## Consequences

GQ1/GQ10 capture, widening, clean full baseline, variance, and guarded
per-commit comparison are complete for the current five-driver cold corpus.
The 3%/3%/5%/2% alarms are comfortably outside observed two-run spread while
remaining sensitive to material regressions.

The next cold implementation must start from fresh causal attribution on the
canonical distribution: mean word/CNF/bit-blast/SAT times are approximately
4.295/4.415/3.655/3.390 seconds. No stage dominates enough to justify an
unmeasured broad rewrite, lowering, encoding, or SAT change. GQ4 remains off.
In parallel, GQ8 may proceed only from a written bounded cache identity,
eviction, invalidation, and mandatory model/proof replay contract.

## Alternatives

Using child shards as eight samples was rejected because each shard covers a
different deterministic query subset. Comparing only the two aggregate ratios
was rejected because Z3 drift and RSS regressions could masquerade as solver
wins. Requiring five complete composites before any alarm was rejected as
unnecessary for a conservative initial gate: observed spread is already well
inside the retained thresholds, and the alarms can be refined with additional
complete repetitions.
