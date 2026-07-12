# Pareto Dominance Readiness

> **Auto-generated. Do not edit by hand.** Regenerate with `python3 scripts/gen-dominance-scoreboard.py`.

This is the conservative companion to `bench-results/SCOREBOARD.md`. It does not replace the decide-rate scoreboard; it adds the proof-route axis needed by PLAN.md's four-constraint Pareto-dominance metric.

## What This Measures

A row is Pareto-dominant only when it satisfies all four constraints: decided within budget, DISAGREE = 0, every `unsat` has a re-checked trust-hole-free Lean certificate, and the route is pure-Rust, deterministic, and unsafe-free.

The current benchmark JSONs record decide-rate, disagreement, and PAR-2, but they do **not** yet record per-instance Lean certificate coverage. Rows with a complete committed audit under `bench-results/dominance/` report exact audited `dominant%(D)`; rows without one remain readiness queue entries.

## Headline

- 35 measured division rows, 992 files, 746 decided, 628 oracle-compared.
- 35/35 rows have DISAGREE = 0; any nonzero row must preempt dominance work.
- 25 rows are decide-strong (Decide% >= 80). 21 have a current Lean route worth auditing now; the others need proof-route work before dominance measurement is meaningful.
- Complete committed dominance audits with exact audited `dominant%(D)`: 35. Remaining rows are readiness or partial-audit entries.

## Audit Harness

The per-instance evidence/Lean audit entry point now exists:

```text
cargo run --release -p axeyum-bench --example audit_dominance -- <baseline.json> [timeout_ms] [limit] [out.json]
```

It re-runs baseline-decided instances through `produce_evidence`, re-checks the evidence, attempts `prove_unsat_to_lean_module` for `unsat`, and emits `evidence_certified`, `evidence_checked`, `lean_fragment`, `lean_checked`, `trust_holes`, and `dominant_candidate`. Local smoke runs already exposed both a positive `QfUfBv` Lean-certified unsat and real gaps where baseline-decided instances still lack transferable evidence.

## Exact Audit Results

Complete audit rows have one audit record for every baseline-decided instance in the row. `Dominant%` is exact for the audited row under the current evidence/Lean routes.

| Division | Slice | Decided | Dominant% | Lean unsat | Gaps | Artifact |
| --- | --- | ---: | ---: | ---: | --- | --- |
| BV | `bv-bitwuzla-regress-clean-quantified` | 5 | 80% (4/5) | 75% (3/4) | Lean unsat 3/4 | `bench-results/dominance/bv-bitwuzla-regress-clean-quantified-dominance-audit.json` |
| BV | `bv-cvc5-regress-clean-quantified` | 47 | 85% (40/47) | 53% (8/15) | Lean unsat 8/15 | `bench-results/dominance/bv-cvc5-regress-clean-quantified-dominance-audit.json` |
| LIA | `lia-cvc5-regress-clean-quantified` | 0 | 0% (0/0) | 100% (0/0) | none | `bench-results/dominance/lia-cvc5-regress-clean-quantified-dominance-audit.json` |
| QF_ABV | `qf-abv-cvc5-bitwuzla-regress-clean` | 169 | 100% (169/169) | 100% (85/85) | none | `bench-results/dominance/qf-abv-cvc5-bitwuzla-regress-clean-dominance-audit.json` |
| QF_ALIA | `qf-alia-cvc5-regress-clean` | 6 | 100% (6/6) | 100% (5/5) | none | `bench-results/dominance/qf-alia-cvc5-regress-clean-dominance-audit.json` |
| QF_AUFBV | `qf-aufbv-bitwuzla-regress-clean` | 41 | 100% (41/41) | 100% (20/20) | none | `bench-results/dominance/qf-aufbv-bitwuzla-regress-clean-dominance-audit.json` |
| QF_AUFBV | `qf-aufbv-cvc5-regress-clean` | 5 | 100% (5/5) | 100% (0/0) | none | `bench-results/dominance/qf-aufbv-cvc5-regress-clean-dominance-audit.json` |
| QF_AUFLIA | `qf-auflia-cvc5-regress-clean` | 5 | 60% (3/5) | 0% (0/2) | Lean unsat 0/2, evidence certified 3/5 | `bench-results/dominance/qf-auflia-cvc5-regress-clean-dominance-audit.json` |
| QF_AX | `qf-ax-cvc5-regress-clean` | 8 | 100% (8/8) | 100% (5/5) | none | `bench-results/dominance/qf-ax-cvc5-regress-clean-dominance-audit.json` |
| QF_BV | `qf-bv-curated-bvred` | 6 | 100% (6/6) | 100% (2/2) | none | `bench-results/dominance/qf-bv-curated-bvred-dominance-audit.json` |
| QF_BVFP | `qf-bvfp-bitwuzla-regress-clean` | 7 | 100% (7/7) | 100% (3/3) | none | `bench-results/dominance/qf-bvfp-bitwuzla-regress-clean-dominance-audit.json` |
| QF_DT | `qf-dt-cvc5-regress-clean` | 3 | 100% (3/3) | 100% (3/3) | none | `bench-results/dominance/qf-dt-cvc5-regress-clean-dominance-audit.json` |
| QF_FF | `qf-ff-cvc5-regress-clean` | 24 | 100% (24/24) | 100% (10/10) | none | `bench-results/dominance/qf-ff-cvc5-regress-clean-dominance-audit.json` |
| QF_FP | `qf-fp-bitwuzla-regress-clean` | 16 | 100% (16/16) | 100% (7/7) | none | `bench-results/dominance/qf-fp-bitwuzla-regress-clean-dominance-audit.json` |
| QF_LIA | `qf-lia-cvc5-regress-clean` | 10 | 100% (10/10) | 100% (4/4) | none | `bench-results/dominance/qf-lia-cvc5-regress-clean-dominance-audit.json` |
| QF_LRA | `qf-lra-cvc5-regress-clean` | 9 | 100% (9/9) | 100% (3/3) | none | `bench-results/dominance/qf-lra-cvc5-regress-clean-dominance-audit.json` |
| QF_NIA | `qf-nia-curated-iand` | 3 | 100% (3/3) | 100% (2/2) | none | `bench-results/dominance/qf-nia-curated-iand-dominance-audit.json` |
| QF_NIA | `qf-nia-synthetic-graduated` | 32 | 100% (32/32) | 100% (16/16) | none | `bench-results/dominance/qf-nia-synthetic-graduated-dominance-audit.json` |
| QF_NIA | `qf-nia-cvc5-regress-clean` | 33 | 61% (20/33) | 13% (2/15) | errors 2, Lean unsat 2/15, evidence certified 23/33, evidence checked 31/33 | `bench-results/dominance/qf-nia-cvc5-regress-clean-dominance-audit.json` |
| QF_NRA | `qf-nra-synthetic-graduated` | 30 | 100% (30/30) | 100% (16/16) | none | `bench-results/dominance/qf-nra-synthetic-graduated-dominance-audit.json` |
| QF_NRA | `qf-nra-cvc5-regress-clean` | 32 | 59% (19/32) | 14% (2/14) | Lean unsat 2/14, evidence certified 19/32 | `bench-results/dominance/qf-nra-cvc5-regress-clean-dominance-audit.json` |
| QF_S | `qf-s-cvc5-regress-clean` | 87 | 9% (8/87) | 29% (8/28) | Lean unsat 8/28, evidence certified 67/87, evidence checked 8/87 | `bench-results/dominance/qf-s-cvc5-regress-clean-dominance-audit.json` |
| QF_SEQ | `qf-seq-cvc5-regress-clean` | 26 | 81% (21/26) | 20% (1/5) | Lean unsat 1/5, evidence certified 25/26, trust holes bit-blast | `bench-results/dominance/qf-seq-cvc5-regress-clean-dominance-audit.json` |
| QF_SLIA | `qf-slia-cvc5-regress-clean` | 18 | 11% (2/18) | 25% (2/8) | Lean unsat 2/8, evidence certified 12/18, evidence checked 2/18 | `bench-results/dominance/qf-slia-cvc5-regress-clean-dominance-audit.json` |
| QF_UF | `qf-uf-cvc5-regress-clean-overbound-uninterp-sorts` | 4 | 100% (4/4) | 100% (3/3) | none | `bench-results/dominance/qf-uf-cvc5-regress-clean-overbound-uninterp-sorts-dominance-audit.json` |
| QF_UF | `qf-uf-cvc5-regress-clean-bounded` | 44 | 100% (44/44) | 100% (15/15) | none | `bench-results/dominance/qf-uf-cvc5-regress-clean-bounded-dominance-audit.json` |
| QF_UF | `qf-uf-cvc5-regress-clean-bounded-uninterp-sorts` | 44 | 100% (44/44) | 100% (15/15) | none | `bench-results/dominance/qf-uf-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json` |
| QF_UFBV | `qf-ufbv-bitwuzla-regress-clean` | 2 | 100% (2/2) | 100% (1/1) | none | `bench-results/dominance/qf-ufbv-bitwuzla-regress-clean-dominance-audit.json` |
| QF_UFBV | `qf-ufbv-cvc5-regress-clean` | 4 | 100% (4/4) | 100% (2/2) | none | `bench-results/dominance/qf-ufbv-cvc5-regress-clean-dominance-audit.json` |
| QF_UFFF | `qf-ufff-cvc5-regress-clean` | 8 | 100% (8/8) | 100% (6/6) | none | `bench-results/dominance/qf-ufff-cvc5-regress-clean-dominance-audit.json` |
| QF_UFLIA | `qf-uflia-curated-named` | 2 | 100% (2/2) | 100% (2/2) | none | `bench-results/dominance/qf-uflia-curated-named-dominance-audit.json` |
| QF_UFLIA | `qf-uflia-cvc5-regress-clean` | 8 | 75% (6/8) | 50% (2/4) | Lean unsat 2/4, evidence certified 6/8 | `bench-results/dominance/qf-uflia-cvc5-regress-clean-dominance-audit.json` |
| QF_UFLIA | `qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts` | 6 | 100% (6/6) | 100% (2/2) | none | `bench-results/dominance/qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts-dominance-audit.json` |
| QF_UFLIA | `qf-uflia-cvc5-regress-clean-overbound-uninterp-sorts` | 2 | 0% (0/2) | 0% (0/2) | Lean unsat 0/2, evidence certified 0/2 | `bench-results/dominance/qf-uflia-cvc5-regress-clean-overbound-uninterp-sorts-dominance-audit.json` |
| UF | `uf-cvc5-regress-clean-quantified` | 0 | 0% (0/0) | 100% (0/0) | none | `bench-results/dominance/uf-cvc5-regress-clean-quantified-dominance-audit.json` |

## First Audit Queue

These rows are the best immediate candidates: they are already decide-strong and have a non-empty Lean reconstruction route. The task is to measure how many decided unsats in the row actually fall inside that route.

| Division | Slice | Files | Decide% | DISAGREE | PAR-2 (s) | Lean route | Audit task |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- |
| - | - | 0 | - | - | - | - | - |

## All Rows

`Dominance action` is intentionally conservative: it is an audit label, not a certification claim.

| Division | Slice | Files | Decided | Decide% | Band | DISAGREE | Audit | Dominant% | Lean unsat | Dominance action | Next action |
| --- | --- | ---: | ---: | ---: | --- | ---: | --- | ---: | ---: | --- | --- |
| BV | `bv-bitwuzla-regress-clean-quantified` | 5 | 5 | 100% | strong | 0 | complete | 80% (4/5) | 75% (3/4) | close Lean unsat gaps | audit quantified-BV rows with per-instance Lean reconstruction |
| BV | `bv-cvc5-regress-clean-quantified` | 54 | 47 | 87% | strong | 0 | complete | 85% (40/47) | 53% (8/15) | close Lean unsat gaps | audit quantified-BV rows with per-instance Lean reconstruction |
| LIA | `lia-cvc5-regress-clean-quantified` | 12 | 0 | 0% | weak | 0 | complete | 0% (0/0) | 100% (0/0) | dominant on audited row | separate guarded finite-Int unsats from unsupported infinite-domain cases |
| QF_ABV | `qf-abv-cvc5-bitwuzla-regress-clean` | 193 | 169 | 88% | strong | 0 | complete | 100% (169/169) | 100% (85/85) | dominant on audited row | classify array unsats by ROW/congruence vs general ArrayElim |
| QF_ALIA | `qf-alia-cvc5-regress-clean` | 6 | 6 | 100% | strong | 0 | complete | 100% (6/6) | 100% (5/5) | dominant on audited row | move solve frontier to AUFLIA scalar search depth |
| QF_AUFBV | `qf-aufbv-bitwuzla-regress-clean` | 44 | 41 | 93% | strong | 0 | complete | 100% (41/41) | 100% (20/20) | dominant on audited row | split direct ROW/congruence wins from general array elimination |
| QF_AUFBV | `qf-aufbv-cvc5-regress-clean` | 9 | 5 | 56% | mid | 0 | complete | 100% (5/5) | 100% (0/0) | dominant on audited row | split direct ROW/congruence wins from general array elimination |
| QF_AUFLIA | `qf-auflia-cvc5-regress-clean` | 7 | 5 | 71% | mid | 0 | complete | 60% (3/5) | 0% (0/2) | close Lean unsat gaps | finish decide frontier before spending cert budget beyond narrow refuters |
| QF_AX | `qf-ax-cvc5-regress-clean` | 8 | 8 | 100% | strong | 0 | complete | 100% (8/8) | 100% (5/5) | dominant on audited row | broaden beyond this small cvc5 slice with neutral QF_AX arrays |
| QF_BV | `qf-bv-curated-bvred` | 6 | 6 | 100% | strong | 0 | complete | 100% (6/6) | 100% (2/2) | dominant on audited row | add per-instance BV operator classifier; close mul/rem/shift Lean gap |
| QF_BVFP | `qf-bvfp-bitwuzla-regress-clean` | 8 | 7 | 88% | strong | 0 | complete | 100% (7/7) | 100% (3/3) | dominant on audited row | separate pure-BV certs from FP-to-BV trust-hole cases |
| QF_DT | `qf-dt-cvc5-regress-clean` | 3 | 3 | 100% | strong | 0 | complete | 100% (3/3) | 100% (3/3) | dominant on audited row | witness the general DatatypeElim dispatch end to end |
| QF_FF | `qf-ff-cvc5-regress-clean` | 30 | 24 | 80% | strong | 0 | complete | 100% (24/24) | 100% (10/10) | dominant on audited row | broaden finite-field audits beyond the cvc5 slice and grow algebraic certificates |
| QF_FP | `qf-fp-bitwuzla-regress-clean` | 16 | 16 | 100% | strong | 0 | complete | 100% (16/16) | 100% (7/7) | dominant on audited row | keep FP as measured-competitive, not Lean-dominant, until Fpa2Bv certs grow |
| QF_LIA | `qf-lia-cvc5-regress-clean` | 11 | 10 | 91% | strong | 0 | complete | 100% (10/10) | 100% (4/4) | dominant on audited row | audit unsats by Diophantine/IntInequality/general LIA route |
| QF_LRA | `qf-lra-cvc5-regress-clean` | 11 | 9 | 82% | strong | 0 | complete | 100% (9/9) | 100% (3/3) | dominant on audited row | run per-instance Lean reconstruction over the committed LRA slice |
| QF_NIA | `qf-nia-curated-iand` | 3 | 3 | 100% | strong | 0 | complete | 100% (3/3) | 100% (2/2) | dominant on audited row | separate Diophantine/interval unsats from bit-blasted bounded boxes |
| QF_NIA | `qf-nia-synthetic-graduated` | 32 | 32 | 100% | strong | 0 | complete | 100% (32/32) | 100% (16/16) | dominant on audited row | separate Diophantine/interval unsats from bit-blasted bounded boxes |
| QF_NIA | `qf-nia-cvc5-regress-clean` | 39 | 33 | 85% | strong | 0 | complete | 61% (20/33) | 13% (2/15) | fix audit errors | separate Diophantine/interval unsats from bit-blasted bounded boxes |
| QF_NRA | `qf-nra-synthetic-graduated` | 33 | 30 | 91% | strong | 0 | complete | 100% (30/30) | 100% (16/16) | dominant on audited row | measure SOS-covered unsats separately from general nonlinear search |
| QF_NRA | `qf-nra-cvc5-regress-clean` | 38 | 32 | 84% | strong | 0 | complete | 59% (19/32) | 14% (2/14) | close Lean unsat gaps | measure SOS-covered unsats separately from general nonlinear search |
| QF_S | `qf-s-cvc5-regress-clean` | 134 | 87 | 65% | mid | 0 | complete | 9% (8/87) | 29% (8/28) | close Lean unsat gaps | decider/front-end work first; proof lane later |
| QF_SEQ | `qf-seq-cvc5-regress-clean` | 33 | 26 | 79% | mid | 0 | complete | 81% (21/26) | 20% (1/5) | close Lean unsat gaps | decider/front-end work first; proof lane later |
| QF_SLIA | `qf-slia-cvc5-regress-clean` | 50 | 18 | 36% | weak | 0 | complete | 11% (2/18) | 25% (2/8) | close Lean unsat gaps | migrate strings to solver StrTerm API before proof investment |
| QF_UF | `qf-uf-cvc5-regress-clean-overbound-uninterp-sorts` | 6 | 4 | 67% | mid | 0 | complete | 100% (4/4) | 100% (3/3) | dominant on audited row | remeasure after first-class uninterpreted sorts, then run Lean audit |
| QF_UF | `qf-uf-cvc5-regress-clean-bounded` | 82 | 44 | 54% | mid | 0 | complete | 100% (44/44) | 100% (15/15) | dominant on audited row | remeasure after first-class uninterpreted sorts, then run Lean audit |
| QF_UF | `qf-uf-cvc5-regress-clean-bounded-uninterp-sorts` | 82 | 44 | 54% | mid | 0 | complete | 100% (44/44) | 100% (15/15) | dominant on audited row | remeasure after first-class uninterpreted sorts, then run Lean audit |
| QF_UFBV | `qf-ufbv-bitwuzla-regress-clean` | 2 | 2 | 100% | strong | 0 | complete | 100% (2/2) | 100% (1/1) | dominant on audited row | audit whether measured unsats avoid BV mul/rem/shift holes |
| QF_UFBV | `qf-ufbv-cvc5-regress-clean` | 4 | 4 | 100% | strong | 0 | complete | 100% (4/4) | 100% (2/2) | dominant on audited row | audit whether measured unsats avoid BV mul/rem/shift holes |
| QF_UFFF | `qf-ufff-cvc5-regress-clean` | 8 | 8 | 100% | strong | 0 | complete | 100% (8/8) | 100% (6/6) | dominant on audited row | broaden UFFF audits beyond the cvc5 finite-field+UF slice |
| QF_UFLIA | `qf-uflia-curated-named` | 2 | 2 | 100% | strong | 0 | complete | 100% (2/2) | 100% (2/2) | dominant on audited row | audit UFLIA unsats by integer-fragment route and UF congruence shape |
| QF_UFLIA | `qf-uflia-cvc5-regress-clean` | 8 | 8 | 100% | strong | 0 | complete | 75% (6/8) | 50% (2/4) | close Lean unsat gaps | audit UFLIA unsats by integer-fragment route and UF congruence shape |
| QF_UFLIA | `qf-uflia-cvc5-regress-clean-bounded-uninterp-sorts` | 6 | 6 | 100% | strong | 0 | complete | 100% (6/6) | 100% (2/2) | dominant on audited row | audit UFLIA unsats by integer-fragment route and UF congruence shape |
| QF_UFLIA | `qf-uflia-cvc5-regress-clean-overbound-uninterp-sorts` | 2 | 2 | 100% | strong | 0 | complete | 0% (0/2) | 0% (0/2) | close Lean unsat gaps | audit UFLIA unsats by integer-fragment route and UF congruence shape |
| UF | `uf-cvc5-regress-clean-quantified` | 5 | 0 | 0% | weak | 0 | complete | 0% (0/0) | 100% (0/0) | dominant on audited row | decider/model-finding work first |

## Certification Route Legend

- `strong-partial`: a real Lean reconstruction route exists for an important subfragment, and the measured row is plausibly close enough to audit immediately.
- `partial`: some proof/checking route exists, but the measured row must be split by operator/reduction shape before a dominance percentage can be claimed.
- `none`: no broad Lean-kernel route exists for the measured row; push decider/front-end work or build a proof route first.

## Next Generator Step

The first `audit now` queue is clear. The next dominance movement comes from reducing the concrete proof/evidence gaps reported above, then regenerating the affected exact audit artifacts.

## Provenance

Generated by [`scripts/gen-dominance-scoreboard.py`](../scripts/gen-dominance-scoreboard.py) from the same committed baseline JSONs consumed by [`scripts/gen-scoreboard.py`](../scripts/gen-scoreboard.py), committed `bench-results/dominance/*.json` audit artifacts, and the conservative proof-route map embedded in the generator.
