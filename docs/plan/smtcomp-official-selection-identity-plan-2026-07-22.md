# SMT-COMP 2026 Single Query selection-identity plan

Status: S0/S1a complete; S1b live selection-free input audit pending
Date: 2026-07-22
Owner: SMT-COMP measurement/full-library lane
Decision: [proposed ADR-0356](../research/09-decisions/adr-0356-preregister-official-smtcomp-selection-identity.md)

## Bounded objective

Produce one content-addressed, independently checked selection artifact for the
SMT-COMP 2026 Single Query track. It must bind the exact official inputs, the
matching SMT-LIB 2025 release bytes, every eligibility/exclusion decision, the
official producer output, and the selected file bytes. This milestone ends at
selection identity. It does not execute a solver or award benchmark credit.

## Frozen authority

| Item | Frozen value |
|---|---|
| Competition / track | SMT-COMP 2026 / Single Query |
| Rules | `https://smt-comp.github.io/2026/rules.pdf` |
| Rules SHA-256 | `268e5c579ee9dd82bcf470f6c66f637c0656bf44f9488dd6347d1f25a2fb4974` |
| Organizer repository | `https://github.com/SMT-COMP/smt-comp.github.io` |
| Organizer commit | `401302678311593efcef8a79b614b33a3b853eac` |
| `selection.py` SHA-256 | `e4d5c9f9c8fc15ec500714f24e2c63aa439408109c9c9cc51b8243391223cdfb` |
| `defs.py` SHA-256 | `5c500314b6604fc763bede8de92cc4f9f913e42f771053ad737688e5f010bdc6` |
| `pyproject.toml` SHA-256 | `d3bcbdb9a058444d8720ae3c4aeefc923c0834ad105aa9e7a4091575d7083226` |
| `poetry.lock` SHA-256 | `8f57e76984579d949d2679eddab2b5cda5c63740d4ca656637390966b1791e4b` |
| Polars | 1.39.2 from the pinned lockfile |
| Benchmark metadata SHA-256 | `ba855e47e1ed88e2e6bb26272e84a20a0e8f0c320adc704b062f4c287e586a54` |
| Corpus | SMT-LIB 2025 non-incremental release `2025.08.04` |
| Zenodo record / DOI | `16740866` / `10.5281/zenodo.16740866` |
| Metadata population | 450,472 non-incremental rows, 89 logics |
| New rows | 3,445 with first family component prefixed `2025` |
| Historical years | 2018 through 2024 inclusive |
| Seed | `(9,684,066,201 mod 2^30) + 2,341,289 = 22,731,074` |

The historical Single Query inputs are:

| Year | Bytes | SHA-256 |
|---:|---:|---|
| 2018 | 20,889,194 | `f1b6353c1a20fd7856d584166ce619c8b0b901f7b4fd88057328e6b123bbb0e5` |
| 2019 | 11,770,723 | `c3807ed94bc85a6be13bf443f334412e74984505dade028de08c63487f581e48` |
| 2020 | 8,755,041 | `847a7335111b7018b4a32b2c1ec033c4971a056f321b3cf0c7b17bd9fce39590` |
| 2021 | 14,590,540 | `a62a892549e069cef3b1f6df34ae343d815e2049741622e0bed2c29bb578365b` |
| 2022 | 11,096,210 | `3794b37f84851c3f0404b3bfa3966dec1e051b4608a84ab2cd5fa2b0b96d7cfd` |
| 2023 | 12,636,621 | `b3c0a11cf7cbf4aef8d6a93c81c8da018aadf7603b425d4a95f16efdabd1f680` |
| 2024 | 14,070,472 | `bd2208c644b2f18520f08df49a797e2f8dbf1a829004c7eab76b4500b8cb5e99` |

These values are pre-observation authority facts. Selection contents and
per-logic selected counts are deliberately not copied into this plan before the
registered producer and auditor exist.

## Artifact contract

The external attempt directory contains:

| Artifact | Required contents |
|---|---|
| `authority.json` | schema, all URLs/hashes/sizes, organizer commit/toolchain, policy constants, ordered submissions and seed derivation |
| `archives.json` | all 90 Zenodo names, sizes, published MD5 values, local SHA-256 values, verified state |
| `corpus.jsonl` | one row per metadata benchmark with normalized ID, metadata, archive, bytes, SHA-256 |
| `historical.jsonl` | normalized per-file/year evidence needed to audit coherence, competitive-year admission, result, and triviality |
| `decisions.jsonl` | one terminal selection/exclusion decision per metadata row with every intermediate policy fact |
| `official-selected.txt` | normalized LF-terminated official producer paths |
| `selected-files.jsonl` | selected paths with size and SHA-256 in `official-selected.txt` order |
| `summary.json` | per-logic counts/digests at each stage and global artifact digests |
| `producer.json` | exact official invocation/environment plus both repetition outputs and equality result |
| `audit.json` | independent invariant results and mutation-matrix result |
| `complete.json` | self-hashed completion-last root over every required artifact |

Normalized IDs are POSIX paths of the form
`non-incremental/<logic>/<family...>/<name>`. Absolute paths never enter a
canonical digest. Every row must map back to one regular extracted file below
the registered root without symlink traversal.

`decisions.jsonl` uses terminal reasons from a closed enum:

- `selected-new`;
- `selected-old`;
- `excluded-explicit-removal`;
- `excluded-noncompetitive-logic`;
- `excluded-trivial`;
- `excluded-cap-new`; and
- `excluded-cap-old`.

An eligible row is either selected or excluded by its new/old cap. An ineligible
row has exactly one earlier exclusion reason. Counts at every transition must
balance.

## Milestones and stop conditions

### S0 — authority manifest and fixture contract

- Commit a small machine-readable authority manifest for all upstream, result,
  submission, and Zenodo inputs.
- Commit schemas, canonicalization rules, and a tiny synthetic fixture.
- Add the authority/fixture checks to the bounded SMT-COMP gate.

Stop if any pinned hash, submission count, derived seed, release count, or
fixture expectation differs. Correct the plan in a new pre-implementation
commit; do not explain drift away after observing a selection.

**Result:** complete. The canonical
[`authority-v1.json`](smtcomp-official-selection-authority-v1.json) freezes 29
organizer source/config files, 51 direct-child submissions, seven historical
result inputs, 90 Zenodo entries, 450,472 metadata rows, and seed `22,731,074`. The
[`contract-v1.json`](smtcomp-official-selection-contract-v1.json) freezes 18
invariants and 18 rejecting mutations. Nine exact fixture files plus generated
300/450/800/1200-row populations exercise the registered policy without
observing the official sample. Eight tests pass.

### S1 — independent eligibility auditor

- Implement metadata/path normalization and duplicate rejection.
- Reconstruct submission participation and competitive logics without importing
  organizer code.
- Reconstruct the historical coherence/competitive-year/triviality reduction.
- Compute exact caps and new/old quotas, then validate an externally supplied
  official selected list.
- Pass every ADR-0356 fixture and mutation.

The auditor may validate selected-set membership, counts, and completeness. It
must not generate a replacement pseudorandom sample.

**S1a result:** fixture-complete. A standard-library AST reader extracts the
Single Query division/logic table from pinned `defs.py` without importing it.
Strict gzip/JSON adapters normalize official benchmark and historical-result
documents, including all organizer answer enums, and expand official
submission divisions plus explicit logics with Pydantic-compatible integer seed
coercion. Eleven tests now include unknown division/logic, wrong incremental
identity, unknown answer, and the executable's non-`Unknown` (rather than
sat/unsat-only) historical predicate. No official selected set has been
produced or observed.

**S1b implementation:** committed before and exercised by the live audit. The independent
runner downloads and rechecks all 89 pinned organizer/rules/data/submission
inputs (29 source/config files, 51 direct-child submissions, benchmark metadata,
seven historical files, and the rules PDF), streams the multi-million-row gzip
JSON
without Polars or organizer imports, and publishes a selection-free
`eligibility.jsonl`, per-logic caps/quotas, summary, and completion-last input
audit. A bounded-memory historical accumulator is differential-tested against
the batch fixture result. Fourteen offline tests pass. The official selected
set remained unobserved throughout this selection-free stage.

**S1b first live attempt:** retained negative. The audit at
`/nas3/data/axeyum/harness/official-selection-2026-sq/input-audit-1784743920768303217-16764d04`
verified and retained its then-registered inputs, then stopped before metadata
reduction with `official divisions/logics are not lists`. The official
Pydantic `Logics` root accepts either a list or regexp. Investigation also
proved that `Config.submissions` uses the non-recursive
`../submissions/*.json` glob, excluding the two `submissions/template/`
examples. S0 is corrected to 51 submissions, 36 competitive submissions, and
seed `22,731,074` before any official sample was generated or observed. A
fresh-directory rerun is required.

**S1b second live attempt:** retained negative. The audit at
`/nas3/data/axeyum/harness/official-selection-2026-sq/input-audit-1784744315286061407-0c81f06d`
verified all 89 corrected inputs, then stopped before metadata reduction on
`QF_AUFBVLIA`. It is a valid organizer `Logic` but does not occur in the
Single Query division table. The exact producer first expands list/regexp
values against every `Logic`, then `Participation.get` filters them through
the selected track's divisions. The independent adapter and fixture now
reproduce that two-stage behavior. No official sample was generated or
observed; another fresh-directory rerun is required.

**S1b third live attempt:** retained negative. The audit at
`/nas3/data/axeyum/harness/official-selection-2026-sq/input-audit-1784744522957943433-eb81e506`
verified all 89 inputs and streamed all 450,472 metadata rows, then stopped
before historical reduction because neither configured removal ID occurs in
the pinned metadata. This matches the official anti-join semantics: both rows
are accepted configuration, and the join removes zero current rows. The
contract and independent audit now distinguish configured removals from matched
removals and freeze the exact zero-match fact. No official sample was generated
or observed; another fresh-directory rerun is required.

**S1b fourth live attempt:** retained negative. The audit at
`/nas3/data/axeyum/harness/official-selection-2026-sq/input-audit-1784744715221056942-32ecd649`
verified all 89 inputs, streamed all 450,472 metadata rows, and reduced all
5,345,294 historical rows across 2018--2024. It then stopped because organizer
metadata is not already in strict normalized-path order. Canonical ledger order
is an Axeyum artifact requirement, not an upstream input-order requirement. The
runner now performs a standard-library bounded external merge sort during its
second metadata pass; a retained-input check produced exactly 450,472 strictly
ordered rows. No official sample was generated or observed; another
fresh-directory rerun is required.

**S1 result:** complete. The fifth fresh audit at
`/nas3/data/axeyum/harness/official-selection-2026-sq/input-audit-1784744992636593932-5051dfbc`
verified all 89 inputs, 450,472 metadata rows across 89 logics, and 5,345,294
historical rows. It emitted 450,472 strictly path-ordered eligibility rows:
3,445 eligible new, 249,915 eligible old, and 197,112 excluded trivial. The two
configured removals match zero metadata rows. Aggregate cap is 45,905, split
into 2,709 new and 43,196 old quota slots. A fresh-process audit rehashed every
input and completion dependency and reconstructed all counts. The compact
[S1b result](smtcomp-official-selection-input-audit-s1b-2026-07-22.md) records
the artifact roots and retained negatives. `selection_observed=false`; S2 is
next.

### S2 — verified corpus acquisition

- Download all 90 files from Zenodo record `16740866` into a fresh staging
  directory, recording redirects and transport failures.
- Check published size and MD5, compute SHA-256, then extract without path
  traversal or symlinks.
- Build `corpus.jsonl`; require the 450,472-row metadata/tree bijection.
- Preserve the prior SMT-LIB 2024 tree unchanged.

Stop before official production on any archive or tree mismatch. No partial
tree may be relabeled as the release.

### S3 — pinned official producer

- Materialize the organizer source/data/submission bundle at the registered
  commit without its Git history.
- Verify all source and data bytes before running it.
- Create caches and export the complete Single Query selection with locked
  Polars 1.39.2.
- Repeat in a fresh environment and compare normalized selected bytes and
  per-logic counts.

Any non-identical repetition is a selection blocker, not an invitation to pick
one output.

### S4 — full independent audit and publication

- Join official output, corpus bytes, metadata, submissions, and historical
  results into the complete decision ledger.
- Run the full mutation matrix against copies of the tiny fixture and bounded
  full-artifact metadata mutations.
- Publish completion last, move the complete attempt to its content-addressed
  accepted path, and verify it read-only from a fresh process.
- Commit the compact result document with all counts and digests; consider
  ADR-0356 for acceptance only after every registered gate passes.

### S5 — execution handoff

- Extend E1b preflight to consume the accepted `complete.json`,
  `official-selected.txt`, and `selected-files.jsonl` identities.
- Run a tiny harness fixture with that contract before the repaired P0 slices.
- Do not alter E1--E3 semantics unless a failing mutation proves a required
  correction and the change is separately preregistered.

## Verification commands

The implementation will add focused commands here without weakening the
existing gate. The minimum retained checks are:

```sh
python3 -m unittest scripts.smtcomp_repro.tests.test_official_selection
./scripts/check-smtcomp-resume.sh
./scripts/check-links.sh
just foundational-resources
```

Live corpus acquisition and official production are explicit required gates in
S2--S4, not ordinary offline CI jobs.

## Current next action

Commit and push the S1b runner, then execute it into a fresh directory below
`/nas3/data/axeyum/harness/official-selection-2026-sq/` and publish the compact
selection-free result. Do not download/extract the full Zenodo release or
observe the official selected population until that audit passes.
