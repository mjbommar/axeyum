# ADR-0159: Paired rewrite-ablation attribution

Status: accepted
Date: 2026-07-14

## Context

GQ3 asks which exact word-level rewrites actually help Glaurung's captured
QF_BV workload. A rule's fire count and the final rewritten query size cannot
answer that question: several rules fire in the same query, later rules may
consume an earlier result, and structural hashing can erase a word-level
difference before it reaches AIG or CNF.

Artifact v31 records stable per-rule applications and affected query/family
sets, and can build a validated default-minus-one-rule manifest. The remaining
question is how to compare those artifacts without accepting configuration,
corpus, environment, correctness, or path-pairing drift as rule impact. This
closes the causal-measurement part of GQ3 in the
[Glaurung execution plan](../08-planning/glaurung-qfbv-execution-plan.md).

## Decision

Accept same-revision, repeated, manifest-path-paired default-minus-one-rule
ablation as the only performance attribution for an individual rewrite.

The comparison tool must fail closed unless:

- base and ablation use artifact v31, a clean identical source revision,
  identical environment/corpus/manifest, one worker, deterministic resource
  bounds, and the same non-rewrite configuration;
- the base enables the complete named default manifest and the ablation differs
  by exactly one disabled rule and its derived configuration identity;
- every query decides, agrees with both the manifest and in-process Z3, retains
  the same outcome under ablation, and has zero errors, disagreements, or model
  replay failures; and
- both artifacts contain exactly the same unique instance paths.

Pair instances by manifest path. Determine the affected set from the base
artifact's fire counts, and report `ablation - base` deltas for that set.
Positive work or time therefore means the enabled rule avoided that work or
time. Report exact structural deltas separately from repeated wall-clock
distributions, retain every timing sample, and include whole-corpus timing as
a drift control. At least two fresh-process repetitions are mandatory; five is
the default recipe.

## Evidence

Five same-revision rounds at clean revision `06750219` compare the unchanged v4
default against four structural ablations on the pinned 128-query producer
representative capture. All 25 artifacts decide and agree on 128/128 queries
with zero errors, disagreements, or replay failures.

| Disabled rule | Affected queries / families | Applications | Extra term bits | Extra AIG nodes | Extra CNF clauses | Affected cold delta, mean |
|---|---:|---:|---:|---:|---:|---:|
| `bv.extract_extend.v1` | 45 (25 register-slice, 20 slice-partial) | 65 | +6,259 | 0 | 0 | +1.657 ms |
| `bv.extract_nested.v1` | 9 register-slice | 44 | +4,140 | 0 | 0 | +0.106 ms |
| `bv.extract_concat.v1` | 4 register-slice | 4 | +635 | 0 | 0 | +0.074 ms |
| `bv.extract_bitwise.v1` | 12 register-slice | 84 | -1,728 | 0 | 0 | +0.156 ms |

`extract_extend` is the only material member of this tranche: all five affected
cold deltas are positive (0.789--2.220 ms), and disabling it adds 0.907 ms mean
bit-blast time. It reduces lift-map/materialization work rather than the final
gate cone. `extract_nested` and `extract_concat` have small consistent lowering
effects. `extract_bitwise` is timing-neutral at this scale (0.026 ms median
cold delta with mixed-sign samples), and its changed materialization direction
does not reach AIG nodes or clauses.

The result corrects the dirty exploratory interpretation. The four rules do
fire, but none causally reduces AIG nodes or CNF clauses on this capture because
the lowerer and AIG structural hashing already collapse their residual wiring.

## Alternatives

- **Rank by applications or affected queries.** Rejected: reach is useful for
  experiment selection but says nothing about downstream saved work.
- **Attribute each rule the selected policy's complete query reduction.**
  Rejected: that double-counts interacting rules and is not counterfactual.
- **Compare unpaired corpus totals.** Rejected: family mix and query-level
  variance can hide the causal direction; path pairing is exact and cheap.
- **Use one timing process because structure is deterministic.** Rejected for
  timing claims. Exact structural deltas need one pair, but sub-millisecond
  timing requires repeated fresh processes with samples retained.
- **Remove every rule without an AIG/CNF reduction.** Rejected: exact cheap
  rules can still reduce lowering cost, as `extract_extend` demonstrates, and
  no ablation establishes an end-to-end default win from removal.

## Consequences

The repository now has one executable causal contract:
`bench-glaurung-qfbv-rewrite-ablation-repeated` produces alternating base and
ablation artifacts and `compare-glaurung-rewrite-ablation.py` validates and
summarizes them.

Keep all four exact rules enabled. Stop proposing more extract rewrites for
this capture solely from lexical opportunity or fire count: the current
structural tranche does not remove a gate or clause. Reopen GQ3 when a new
residual shape has a specific downstream hypothesis, then require this same
ablation boundary. The immediate client-performance priority moves to GQ1's
native Glaurung entry-path attribution and, from that evidence, either GQ5's
incremental gate-fusion gap or a purpose-built one-shot client boundary.
