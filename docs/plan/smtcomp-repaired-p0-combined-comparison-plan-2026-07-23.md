# SMT-COMP repaired P0 combined-comparison plan

Status: preregistered; implementation and generated comparison not yet accepted
Date: 2026-07-23
Parent: [Bitwuzla closure result](smtcomp-repaired-p0-v2-bitwuzla-closure-result-2026-07-23.md)
Durability authority: [ADR-0344](../research/09-decisions/adr-0344-preregister-resumable-distributed-benchmark-execution.md)

## Purpose and bounded claim

Derive one deterministic, fail-closed comparison from the three completed
repaired-P0 external result roots. The comparison is a correctness and decision-
coverage map over exact selected populations. It is not an official SMT-COMP
ranking, a full-library result, or a general solver-performance claim.

The population boundary is mandatory:

- Axeyum and cvc5 each contain the same 1,810 rows from `QF_ABVFP`,
  `QF_AUFLIA`, `QF_BVFP`, and `QF_FP`;
- Bitwuzla contains the exact 1,305-row FP-family subset from `QF_ABVFP`,
  `QF_BVFP`, and `QF_FP`; and
- the 505 excluded rows must be exactly the complete `QF_AUFLIA` population.

No total, percentage, PAR-2 score, timing sum, or rank may combine Bitwuzla's
1,305-row scope with the 1,810-row scope. The first artifact deliberately omits
performance ranking: the cells were run sequentially, and Bitwuzla includes a
registered recovery lifecycle even though the per-case resource identities are
equal.

## Frozen input authority

Preparation root:
`/nas3/data/axeyum/harness/official-selection-2026-sq/repaired-p0-prep-20260723-75e544a8-v2`

| Input | File SHA-256 | Record SHA-256 / rows |
|---|---|---|
| Preparation completion | `8d9145b2673ee10bf7c38990c20301f13323cfe4ab02c9946b403d0d2e4f4261` | `d3ae8e7cd870c48c19417495aeb99b53ed1a797db58092b79d0828b9255b5f7b` |
| Axeyum external completion | `28402ac34a91715ab60ad2ff6dd1f1774ec60b5594131592da317dd23faa33ca` | `97f27a480f9694e97765d669823b05c34ced8825f2f598c16e00ea301b1c4a57` |
| Axeyum raw export | `9424ab09f44c63b7370e3472b299eeab051b1e7d66cfe2de967cb05088581820` | 1,810 |
| cvc5 external completion | `4abde0a6b3d02be1a4e4aa80bda32e2808e78e32db3e1e71336bc6e304bd32f8` | `e6fbc654535c82bb5d9fa9460ba802cf41d128c28778b859f990df2160a37faf` |
| cvc5 raw export | `0465d0aea6929bdf42c37f5aaa7e3ba24eca67f960a322ad6c8735a8f0d9e010` | 1,810 |
| Bitwuzla external completion | `4e0c9682931154b6455d02e00ed5a6cc3ec6b58635e7c808de703023c72dcf20` | `7ec879514032b00ed5d8fffd119d126df90681a6b0ed4e2bf9ea737ae94df6f3` |
| Bitwuzla raw export | `390e113f1d6291402e2ae6a59a09e174cfb2d978727a01432b7f6a016b265dd4` | 1,305 |

The generator must first run `validate_preparation(..., require_empty=False)`
and `validate_cell_result` for every cell. It must then bind the exact
preparation, external completion, raw-export, run-identity, selection-list, and
selection-manifest hashes. Reading only the legacy raw export is insufficient:
comparison identity comes from the validated immutable result records.

## Comparison identity and terminology

One benchmark identity is the ordered pair
`(benchmark_id, benchmark_sha256)`. `result_key` is solver-configuration-
specific and must never be used to join cells.

For every shared benchmark, the logic, expected status, benchmark ID, and
benchmark content hash must agree exactly. Duplicate identities, missing rows,
unknown logics, unexpected status/termination values, or a mismatch between a
record and its selected population reject generation.

The generated artifact keeps three axes separate:

1. **Reported status:** `sat`, `unsat`, `unknown`, or `no-verdict` when the
   admitted status is null.
2. **Decision:** only `sat` and `unsat` are decisions. `unknown` is an observed
   response but not a decision; `no-verdict` is neither.
3. **Termination:** the exact typed `termination_class`, counted independently
   from reported status.

Decision/expected-status classification is:

- `known-correct`: a `sat`/`unsat` decision matching known `:status`;
- `known-contradiction`: a `sat`/`unsat` decision opposing known `:status`;
- `unadjudicated-decision`: a `sat`/`unsat` decision where expected status is
  absent; and
- `no-decision`: `unknown` or `no-verdict`.

The term "correct" must not be applied to the 90 absent-status rows. Any known
contradiction or cross-solver `sat`/`unsat` disagreement rejects publication.

## Required populations and projections

The machine artifact schema is
`axeyum.smtcomp-repaired-p0-comparison.v1`. It must contain these independently
sealed projections:

1. **Per-cell native scope**: status, decision/expected-status, and termination
   counts, both overall and per logic, for Axeyum 1,810, cvc5 1,810, and
   Bitwuzla 1,305.
2. **Axeyum/cvc5 all-scope pair**: exact 1,810-row intersection and no exclusive
   rows.
3. **Three-solver FP scope**: exact 1,305-row intersection, with no Bitwuzla-
   exclusive rows and exactly 505 Axeyum/cvc5 rows outside it.
4. **QF_AUFLIA two-solver scope**: exactly 505 rows for Axeyum and cvc5 and no
   Bitwuzla rows.
5. **Pairwise decision projection** on each exact intersection:
   `both-decide-agree`, `left-only-decides`, `right-only-decides`,
   `neither-decides`, and `disagreement`.
6. **Three-way FP decision projection**: `three-decide-agree`,
   `two-decide-agree`, `one-decides`, `none-decide`, and `disagreement`, plus
   solver-attributed counts for the sole decider or sole non-decider.

Every projection must account for its full population exactly. The generator
must prove that the FP selection is exactly the all-selection restriction to
`QF_ABVFP`, `QF_BVFP`, and `QF_FP`, not merely a same-sized subset.

## Outputs and self-check

Implementation targets:

- `scripts/smtcomp_repro/p0_compare.py` for pure derivation and validation;
- `scripts/generate-smtcomp-repaired-p0-comparison.py` for the bounded CLI;
- `scripts/tests/test_smtcomp_p0_compare.py` for fixture/mutation coverage;
- `docs/plan/generated/smtcomp-repaired-p0-comparison.json`; and
- `docs/plan/generated/smtcomp-repaired-p0-comparison.md`.

The JSON is canonical and contains a `record_sha256` over every other field.
The Markdown is rendered only from the validated JSON and names its file and
record hashes. `--check` must reject stale generated bytes. Neither mode may
mutate the preparation or any NAS artifact.

Required tests cover deterministic reproduction, every population boundary,
status/decision/termination separation, expected-status drift, missing and
duplicate benchmark identities, wrong logic membership, known contradiction,
cross-solver disagreement, stale external completion identity, unaccounted
projection rows, JSON self-seal mutation, and Markdown drift.

## Exit gate

This milestone is complete only when:

1. the exact three live external results independently validate;
2. focused tests and the generated-artifact check pass;
3. the JSON and Markdown reproduce byte-identically in a fresh process;
4. all population accounting identities hold with zero known contradiction and
   zero cross-solver disagreement;
5. link and foundational-resource checks pass;
6. the result document records exact output hashes and bounded conclusions; and
7. the topic branch is green and pushed for integrator-controlled landing.

No solver execution, retry, lease operation, coordinator finalization, or NAS
write is authorized by this plan.
