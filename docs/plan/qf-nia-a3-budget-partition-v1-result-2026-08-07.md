# QF_NIA A3 typed-budget partition v1 result — 2026-08-07

## Verdict

The 52-row `nia-linearize = budget` population is now partitioned by the
downstream typed stop that actually ends each retained trace. It is not one
mechanism and must not be optimized as one:

| Downstream stop | Reference SAT | Reference UNSAT | Total | Disposition |
|---|---:|---:|---:|---|
| integer width-ladder timeout | 24 | 13 | 37 | mixed; diagnose a bounded SAT cluster before policy changes |
| pre-lowering CNF-clause estimate above 64,000,000 | 11 | 0 | 11 | first implementation-candidate population |
| combined-theory timeout after scalar backend | 0 | 3 | 3 | secondary UNSAT symptom; not a width-ladder target |
| exact replay model overflow at width 32 | 0 | 1 | 1 | sound replay rejection; not permission to accept or widen |
| **Total** | **35** | **17** | **52** | — |

This closes the coarse 52-row repartition. No cap, deadline, route order,
clause ceiling, width ladder, or solver code changed. The next bounded action
is diagnostic attribution over the two smallest all-SAT clause-estimate rows,
not raising the 64,000,000 safety ceiling.

## Authority and classification

The source is the complete retained
[`causal-census-v2.json`](evidence/qf-nia-a3/causal-census-v2.json), SHA-256
`2585b9627fb851b06428455eb1e0754e01083c0cb17b2c24c6404087c105203a`,
joined by basename to
[`retained-sidecar-v1.tsv`](evidence/qf-nia-a3/retained-sidecar-v1.tsv),
SHA-256
`392e6cc33423518a44015a98cb1c7fdf867ea1c33ffd1cb77f761316acb5d524`.
Every counted row has `nia-linearize` as its first causal decline with reason
`budget`; the category is the detail on the final route-trace attempt. The
four categories are mutually exclusive and sum to all 52 rows.

The 11 estimate refusals are all reference-SAT. Their two lowest retained
estimates are:

- `From_AProVE_2014__juHashMapCreateContainsKey.jar-obl-11__p31818_safety_0`
  at 81,482,280 clauses;
- `From_AProVE_2014__juHashMapCreateRemove.jar-obl-11__p6984_safety_0`
  at 82,590,729 clauses.

They exceed the ceiling by about 27% and 29%, respectively. That proximity is
only a selection signal: the estimator is deliberately conservative because
lowering an unexpectedly large multiplier circuit can exhaust memory. A repair
must reduce or prove the demanded encoding, retain the same absolute fail-closed
ceiling, and preserve original-term replay; this result does not authorize
simply admitting either estimate.

## Fresh exact-baseline discrimination

Fresh direct observations used current integrated source
`a28560f81db34248413f27382b706ab7c5b9b60f`, release `explain_corpus`
SHA-256
`b4c55749c5cfd25c89422f3e3251cd083563d84d2cac6ab30c3c7aeed78ad77e`,
an 8 GiB process limit, a 24,000 ms query budget, serialized execution, and CPU
4 affinity.

The three combined-timeout rows are all reference-UNSAT:

| Row suffix | Atoms | Lazy rounds | Initial / blocking lemmas | Terminal detail |
|---|---:|---:|---:|---|
| `ex36.t2__p29986_safety_0` | 524 | 55 | 38 / 118 | combined-theory timeout after scalar backend |
| `s1-striped.t2_fixed__p11698_safety_0` | 275 | 72 | 218 / 98 | combined-theory timeout after scalar backend |
| `s1.t2__p18409_safety_0` | 333 | 36 | 278 / 79 | combined-theory timeout after scalar backend |

Each scalar backend returned only after the shared deadline. The later bounded
integer blast is SAT-only for unbounded integer queries: a replaying model could
be accepted, but modular `unsat` cannot prove integer `unsat`. Moving or widening
that ladder therefore does not address the reference verdict and would consume
more time after the owning search stop.

The single model-overflow row,
`aproveSMT7795667227375240089`, is also reference-UNSAT. Its retained width-32
candidate falsifies original assertion 299 under exact semantics. This is the
replay checker working as intended, not a model that may be accepted.

Finally, the reference-UNSAT width-timeout row
`From_AProVE_2014__Test6.jar-obl-13__terminationS_36_0` was rechecked because it
has a different upstream shape. It declined from NIA linearization after
QF_LIA branch-and-bound passed the wall deadline at its 20,000,000-node cap,
then the width ladder also reached the wall deadline. The second stop is again
downstream of the owning exact-search exhaustion and cannot establish UNSAT.

## Next bounded boundary

Start with the two smallest all-SAT clause-estimate rows above. Before solver
edits, preregister a diagnostic that attributes the conservative estimate by
shared term and operator and compares it with a memory-bounded demanded-lowering
projection. Any implementation candidate must:

1. retain the 64,000,000 absolute pre-allocation safety boundary;
2. avoid materializing a circuit merely to discover that it is too large;
3. be additive and fail closed when the tighter bound cannot be proved;
4. accept SAT only after replay against the original integer assertions;
5. decide at least one target in two of three observations before controls or a
   200-row gate are authorized; and
6. be removed completely if the target gate fails.

Do not use the combined-timeout or model-overflow UNSAT tail as a width-policy
target, and do not raise the general clause, node, width, or wall-clock caps.
