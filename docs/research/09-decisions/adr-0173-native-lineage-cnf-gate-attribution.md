# ADR-0173: Native lineage CNF gate attribution

Status: accepted
Date: 2026-07-15

## Context

ADR-0172 attributes 43.78% of the bounded native-lineage profile to
incremental CNF construction, but its v1 records report only aggregate clause
and variable deltas. That is enough to rank phases, not to choose another
encoding change. Earlier cold and fresh-incremental profiles selected direct
positive-root fusion and exact root-context deduplication; retained path-owned
sessions can have materially different root reuse, polarity, and definition
traffic, so those distributions cannot be assumed to carry over.

The required boundary remains diagnostic-only. Ordinary incremental solvers
must not pay gate recognition, clause fingerprinting, phase clocks, query
rendering, or JSON output costs. Glaurung remains an opt-in downstream workload
and does not become an Axeyum architecture dependency.

## Decision

Accept Glaurung `21c01ce` and the Axeyum v2 summarizer as the causal warm-CNF
attribution boundary:

1. add the exact per-check delta of every existing `IncrementalCnfStats` field
   to `glaurung-axeyum-warm-profile-v2` records;
2. retain v1 as accepted historical input, but emit aggregate gate totals only
   for a homogeneous v2 stream;
3. validate the complete field set, nonnegative values, the five-family
   half-definition partition, fused-opportunity bounds, and root-dedup bounds
   before summarizing;
4. preserve one exact query hash, path owner, phase sum, and structural delta
   per record so gate totals cannot be detached from the decided stream;
5. reject another root-dedup or broad positive-root-fusion tranche on this
   stream: every measured positive-root opportunity is already fused, while
   duplicate and tautology counters are zero; and
6. select internal positive AND-tree half flattening as the next bounded
   experiment. Its acceptance requires fewer clauses and lower repeated,
   unprofiled, same-stream native time with identical decisions, replay,
   scopes, resource limits, root traffic, and findings.

The selected experiment must not assume that an AIG node remains private in a
growing solver. A sound candidate may replace one positive implication
`v -> tree` by the equivalent clauses from `v` to the flattened conjunction
leaves while leaving ordinary definitions available if a bypassed helper is
used later under another polarity or assertion. The aggregate v2 family count
does not cross-tab shape by polarity, so implementation telemetry must report
the actual eligible and flattened positive halves rather than treating every
AND-tree hit as savings.

## Evidence

The producer's focused release test verifies that all 38 counters are exported
and that untouched fields remain zero. The Axeyum summarizer tests cover v2
aggregation, exact rejection of a malformed shape partition, and v1 backward
compatibility. The same three release shadow processes used by ADR-0172 produce
exactly 6,986 records: 4,753 `vwififlt`, 561 Dptf, and 1,672 IntcSST checks.
Every check decides and agrees with Z3; all 2,103 paths close; cap fallbacks,
warm resets, deadline hits, disagreements, and unknown splits remain zero.

The structural totals are unchanged: 88,476 added roots, 8,758,247 added AIG
nodes, 8,848,809 added CNF variables, and 11,734,335 added clauses. The v2
profile's 7.194-second internal total remains diagnostic overhead. Its phase
shares reproduce ADR-0172 within run variance: CNF 43.58%, bit blast 22.98%,
SAT 17.50%, replay 5.69%, translation 3.77%, model lift 3.37%, unattributed
2.87%, session creation 0.19%, and model extraction 0.05%.

| Clause source | Count | Share of added clauses |
|---|---:|---:|
| primitive definitions | 8,419,041 | 71.75% |
| guarded roots | 3,313,208 | 28.24% |
| synchronized constants | 2,086 | 0.02% |

The 5,697,696 emitted implication halves partition exactly:

| Local AIG family | Half-definitions | Share |
|---|---:|---:|
| positive-child AND tree | 3,070,411 | 53.89% |
| complemented-child AND | 1,452,816 | 25.50% |
| XOR/XNOR | 705,066 | 12.37% |
| primitive binary AND | 469,403 | 8.24% |
| not-ITE | 0 | 0.00% |

All 34,377 direct positive-AND roots, 1,966,961 exposed positive-AND nodes,
and 1,257,771 structural XOR leaves take the existing fusion path. All 88,476
roots are selector-guarded. Their 3,313,208 clauses contain 797,666 unit
payloads and 2,515,542 binary payloads, with no wide payload. Exact definition,
root, prior-root, and root-versus-non-root duplicates are all zero; definition
and root tautologies are also zero. There are 42,364 cross-context literal
reuses, but no repeated same-context assertion for the production dedup key.

## Alternatives

Another root-context or clause-dedup index was rejected because this stream
contains no matching duplicate opportunity, and ADR-0163 already showed that
a stronger production clause index can regress native time. Extending direct
positive-root fusion was rejected because its eligible counters are already
saturated. Leading with XOR or primitive binary-AND work was rejected because
their measured half populations are 4.4x and 6.5x smaller than the AND-tree
family. Treating the aggregate AND-tree count as positive-half eligibility was
rejected because v2 does not cross-tab family and polarity. Enabling any
candidate from profiled timing was rejected because diagnostic clocks and
clause indexing materially change the measured path.

## Consequences

GQ1/GQ5 gate/root attribution is complete for the bounded three-driver native
lineage tier. The next implementation slice is one semantically exact,
future-reuse-safe positive internal AND-tree flattening experiment, with its
own eligible/applied/clause delta counters. Review the foundational dependency
DAG before changing the encoder, preserve AIG-to-CNF/model replay maps, and run
the full incremental semantic suite before the real-client gate.

If the candidate does not reduce repeated unprofiled native time, revert or
defer it even when clauses fall. AIG construction per node remains next after
this bounded CNF slice; SAT remains third at 17.50% on the diagnostic rerun.
GQ4 stays explicit and off. GQ7 memory admission, GQ10 driver widening, and the
separate trust-ledger/proof work remain open.
