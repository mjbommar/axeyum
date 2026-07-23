# SMT-COMP harness admission S5 plan

Status: complete
Date: 2026-07-23
Decision: [accepted ADR-0356](../research/09-decisions/adr-0356-preregister-official-smtcomp-selection-identity.md)

## Bounded objective

Bind the E1b resumable-run preflight to an accepted S4 selection artifact
before any credited solver execution. This increment admits no large run and
does not change solver, scoring, sharding, checkpoint, or resource-enforcement
semantics.

The accepted S4 root remains immutable. S5 adds a path-independent execution
ledger that consumes its identities and proves the same handoff on a tiny
fixture.

## Admission contract

An admitted selection-input manifest has a new schema and contains:

- the SHA-256 and payload SHA-256 of canonical `complete.json`;
- the exact byte count and SHA-256 of `official-selected.txt`;
- the exact byte count, row count, and SHA-256 of `selected-files.jsonl`;
- the existing ordered physical-path, benchmark-ID, byte-count, and SHA-256
  execution ledger.

Construction and every preflight independently require all of the following:

1. `complete.json` is canonical JSON, reports `status=complete`,
   `selection_observed=true`, and has a valid payload hash.
2. The accepted directory is named `accepted-<sha256(complete.json)>`.
3. The completion artifact map binds the exact selected list and selected-file
   ledger bytes.
4. `official-selected.txt` is UTF-8, LF-terminated, strictly sorted, unique,
   and contains canonical non-incremental benchmark IDs.
5. `selected-files.jsonl` is canonical JSONL with the exact S4 row shape; its
   rows occur in official-list order and its count equals `selected_files` in
   the completion.
6. The execution file list has the same order and benchmark IDs, and every
   physical file has the exact byte count and SHA-256 recorded in the ledger.
7. The run identity continues to bind the complete execution manifest and the
   absolute execution list. The execution manifest transitively binds the S4
   completion, official list, and selected-file ledger.

Legacy `axeyum.smtcomp-selection-input.v1` manifests remain valid only for
explicit no-credit fixtures. Real cgroup-backed E2/E3 preflight rejects them
unless the caller supplies a deliberately named fixture-only override. This
preserves the accepted E1--E3 mechanism tests without allowing their old five
selection tests to masquerade as S5 admission.

## Preregistered rejecting mutations

The tiny fixture must reject before creating a run directory when any one of
these mutations is present:

| ID | Mutation |
|---|---|
| S5-M01 | completion status, observation flag, or schema differs |
| S5-M02 | completion payload hash differs |
| S5-M03 | accepted-directory content address differs |
| S5-M04 | selected-list bytes differ from the completion artifact map |
| S5-M05 | selected-file ledger bytes differ from the completion artifact map |
| S5-M06 | selected-list order, uniqueness, or benchmark ID differs |
| S5-M07 | ledger row shape, order, count, byte count, or digest differs |
| S5-M08 | physical execution path order, ID, bytes, or digest differs |
| S5-M09 | a cgroup-backed run presents only the legacy fixture manifest |

Every mutation test also asserts that the target run directory does not exist.

## Gates

The implementation is complete only after:

```sh
python3 -m unittest scripts.tests.test_smtcomp_resume_runner
python3 -m unittest scripts.tests.test_smtcomp_cgroup_host
python3 -m unittest scripts.tests.test_smtcomp_multi_host
python3 -m unittest scripts.tests.test_smtcomp_multi_host_live
./scripts/check-smtcomp-resume.sh
./scripts/check-links.sh
just foundational-resources
```

The accepted 45,905-file root receives one read-only admission-manifest build
and validation pass after the tiny fixture is green. No solver is launched by
that pass.

Completed result:
[S5 harness-admission result](smtcomp-harness-admission-s5-result-2026-07-23.md).

## Stop conditions

Stop without a large run if the accepted S4 root fails any admission check, if
the tiny mutation matrix does not fail closed, or if binding admission would
require changing E1--E3 execution semantics. Any such change needs a separately
preregistered correction.
