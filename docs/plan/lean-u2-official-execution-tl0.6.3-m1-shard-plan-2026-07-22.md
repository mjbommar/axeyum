# Lean U2 TL0.6.3 M1 child-shard derivation plan

Status: **preregistered; derivation not yet run; no execution or parity credit**

Date: 2026-07-22

Target: Lean `v4.30.0` at
`d024af099ca4bf2c86f649261ebf59565dc8c622`, using only the already accepted
U2 registration and official-CI-profile authorities.

This document freezes the first breadth-expansion step after the completed M0
singleton history. It defines how the active official U2 selections are
partitioned into deterministic child shards. It does **not** execute Lean,
Axeyum, CTest, a workflow, or a provider, and it cannot create an outcome,
pair, performance row, coverage percentage, or parity claim.

## 1. Decision and boundary

M1 will derive a complete, bounded scheduling projection over every case in
every official selection set. Exact duplicate ordered memberships will share
one physical membership plan, while all eight selection-set identities and all
111 declared official attempts remain explicit bindings.

The partition rule is deliberately mechanical:

- preserve the committed `selected_case_ids` order exactly;
- split each distinct ordered membership into contiguous chunks of at most 64
  case IDs;
- assign every selected case to exactly one chunk in that membership;
- do not reorder, sample, stratify, cherry-pick, or remove the previously
  observed M0 case;
- keep every generated attempt and child shard in `not-run` state.

Contiguous chunks are scheduling units, not representative samples. Shard
ordinal zero, any individual shard, and any prefix of the order may not be used
to estimate a pass, failure, support, performance, or parity rate.

This is an evidence-only projection under
[ADR-0345](../research/09-decisions/ADR-0345-versioned-lean-export-import-boundary.md):
it strengthens identity and fail-closed accounting without changing the Lean
wire format, importer, kernel, supported construct set, or public solver
surface. No new ADR is required for this preregistered derivation.

## 2. Frozen inputs

The implementation must reject any physical-byte or semantic-validation drift
in these committed authorities before it derives a row:

| Input | Physical SHA-256 | Required semantic validation |
|---|---|---|
| `docs/plan/lean-u2-test-authority-v1.json` | `d7446e7965bac100ac6b5c607cbb7c87b5b80063fc23b3ec998fff2736d5d18e` | `gen-lean-u2-test-authority.py::validate_manifest` returns no failure |
| `docs/plan/lean-u2-official-ci-profiles-v1.json` | `4817d177828797f9dab9e62cf7647732d2b9c3788db7b7b4e3461bc868948548` | `gen-lean-u2-official-ci-profiles.py::validate_manifest` returns no failure |
| `docs/plan/lean-u2-official-execution-tl0.6.3-m0-r3-v1.json` | `fe04cd96fb9f08c8a0e834ec11f954c3c8172912332da28fc2a92adf0cedb475` | amended R3 result validator returns no failure |

The corresponding validator source bytes are also frozen for this first
derivation:

| Validator | SHA-256 |
|---|---|
| `scripts/gen-lean-u2-test-authority.py` | `2c173c2621c374179ee346aa8cc710a84e8c37792b2ead25d4e80f8144ad34ba` |
| `scripts/gen-lean-u2-official-ci-profiles.py` | `4b4b2d0fca8acaee1f90e8a7f143067db6596e6aa7d558e9a877639db878e246` |
| `scripts/lean_u2_official_execution_r3_result.py` | `955f91838debb65b939492108d8a5cd66a0cb5834f9b1e03a69d80a8afbe3f73` |

The parent authorities currently declare 3,678 default registrations, 3,723
full-Lake registrations, eight factored selection sets, and 111 official CTest
attempts. Those are input facts, not results of M1. M1 must recompute and
validate them rather than trusting this prose.

## 3. Output artifacts

The implementation commit will add:

- `scripts/gen-lean-u2-official-child-shards.py`;
- `scripts/tests/test_lean_u2_official_child_shards.py`;
- `docs/plan/lean-u2-official-child-shards-v1.json`, the canonical authority;
- `docs/plan/generated/lean-u2-official-child-shards.json`, the bounded
  generated report; and
- `docs/plan/generated/lean-u2-official-child-shards.md`, the human-readable
  report.

The generator will support ordinary regeneration and `--check`. It may read
only committed source authorities and validator code. It may not inspect a
Lean checkout, execute CTest, inspect local M0 evidence directories, call a
network service, or infer outcome from filesystem residue.

## 4. Canonical derivation

The derivation order is frozen as follows.

1. Read each authority as UTF-8 JSON and verify its exact physical SHA-256.
2. Load the three frozen validators and require all semantic checks to pass.
3. Build the registration case map from U2 `cases`; reject duplicate IDs,
   missing per-case seals, or an ID referenced by a selection but absent from
   the registration authority.
4. Traverse official selection sets in their committed, already validated
   order. Recompute each selected-list digest and count.
5. Deduplicate only when two selections have byte-for-byte equal ordered
   `selected_case_ids`. A matching digest with unequal content is a fatal
   collision; equal content with unequal committed digests is drift.
6. Give each distinct ordered membership the ID
   `membership-<selected_ids_sha256>`. Sort membership plans by that full ID.
7. For each membership, enumerate slices `[0:64]`, `[64:128]`, and so on.
   The final slice may contain 1 through 64 cases. Empty membership is valid
   only as an explicit zero-shard plan; the current authorities are not
   assumed to contain one.
8. Give a shard the ID
   `<membership-id>--shard-<zero-padded-four-digit-ordinal>`. More than 10,000
   shards in one membership is a fatal schema-capacity error rather than an ID
   format change.
9. Bind every selection-set ID to exactly one membership plan. Preserve the
   selection identity and seal even when its membership is shared.
10. Bind every official attempt ID to its original selection-set ID and the
    selected membership's ordered shard IDs. Preserve attempt identity and
    seal. Every attempt outcome remains `not-run`.
11. Resolve the amended R3 case against the registration map and record it in
    a separate historical-observation annotation. Its two official outcomes
    for one unique case do not complete an M1 shard, an official profile, or an
    official-provider attempt. The case remains in every applicable complete
    membership partition.
12. Seal every record and every ordered record list with domain-separated
    SHA-256 over canonical JSON (`UTF-8`, sorted object keys, compact
    separators, no NaN/infinity). Seal the top-level authority last with its
    `record_sha256` field empty during digest calculation.

No current derived count—distinct memberships, physical shards,
selection-expanded shards, or attempt-expanded shard occurrences—is frozen in
this preregistration. Those are M1 observations and will be published only by
the committed generator result.

## 5. Required authority model

The canonical authority must retain these layers rather than flattening them:

### Source identities

- exact target repository, tag, version, and commit;
- path, physical SHA-256, schema, and top-level logical seal for each parent
  authority;
- path and SHA-256 for each validator used;
- fixed `max_cases_per_shard = 64` and the canonicalization/domain names.

### Membership plans

Each distinct ordered membership records:

- full digest-derived ID;
- selected count and selected-list digest;
- all selection-set IDs sharing the membership;
- ordered shard IDs, shard count, and shard-list digest; and
- a per-record seal.

### Child shards

Each shard records:

- ID, membership-plan ID, ordinal, half-open start/end offsets;
- exact ordered case IDs, count, case-list digest, first ID, and last ID;
- historical-observation IDs as annotation only;
- `outcome = not-run`, zero execution/completion credit, and a per-record seal.

Every case ID is resolved through the frozen registration authority; copying
the several-thousand-record case catalog into every overlapping membership is
forbidden. Parent authority identities plus exact case IDs and closure checks
provide the source binding without uncontrolled duplication.

### Selection and attempt bindings

Each selection binding records the original selection ID and seal, membership
ID, selected count/list digest, ordered shard IDs, and its own seal. Each
attempt binding records the original attempt ID and seal, phase, cell ID,
selection ID, membership ID, ordered shard IDs, `not-run`, and its own seal.

### Historical observation

The separate M0/R3 annotation records the amended result authority identity,
case ID and registration seal, four process attempts, two completed process
attempts, two official outcomes, one pass, one failure, zero completed parent
profiles, zero Axeyum outcomes, zero pairs, and zero performance rows. It must
state `credit_scope = historical-local-singleton-only` and
`completes_m1_shard = false`.

### Summary, claims, and residuals

The summary reports both unique and expanded quantities:

- distinct membership plans and their case occurrences;
- physical child shards;
- selection-expanded shard occurrences;
- attempt-expanded shard occurrences;
- union of selected registration cases;
- historical unique observed cases; and
- all execution, completion, Axeyum, pair, performance, and parity counts as
  zero.

Only derivation claims may be true: complete partition of each parent
membership, exact selection binding, exact attempt binding, and explicit
historical annotation. `official_execution_complete`,
`official_provider_reproduced`, `axeyum_observed`, `matched_pair_formed`,
`performance_measured`, and `lean_parity_established` must all be false.

## 6. Fail-closed invariants

Validation and `--check` must reject at least:

- input physical digest, schema, logical seal, or validator-source drift;
- a parent validator failure;
- duplicate, missing, extra, or reordered selection, attempt, membership,
  shard, or case reference;
- selected count/list digest disagreement;
- membership deduplication by count, set equality, or digest alone rather than
  exact ordered-list equality;
- a shard with zero cases, more than 64 cases, a non-contiguous offset, a
  wrong ordinal/ID, or a bad first/last case;
- a membership case missing from shards, appearing twice, appearing in the
  wrong order, or added from outside the selected list;
- a selection or attempt bound to a non-equivalent membership;
- attempt or shard outcome other than `not-run`;
- historical M0 observations counted as M1 shard, parent-profile,
  official-provider, Axeyum, pair, performance, or parity completion;
- stale generated JSON or Markdown; or
- any record/list/top-level seal mismatch.

The focused test module will include positive regeneration/check tests and
mutations for every invariant class above. Mutation tests must reseal the
modified outer structure where necessary so that semantic validators, rather
than only the first digest check, are exercised.

## 7. Acceptance and next step

M1 is accepted only after:

1. this preregistration is committed and pushed by itself;
2. implementation and tests are committed from that fixed boundary;
3. the generator publishes and validates its canonical authority;
4. focused mutation tests, generated-output checks, parity-doc tests, and the
   repository link checker pass, apart from any separately documented
   pre-existing branch-skew failure; and
5. the parity registry, contract, roadmap, implementation plan, project state,
   `PLAN.md`, and `STATUS.md` link the accepted result without changing any
   terminal claim.

The next execution milestone must be preregistered separately. It may select
one or more derived child shards and define provider, executable,
configuration, environment, resource, attempt, completion, JUnit/log, retry,
and invalid-run identities. M1 itself authorizes no execution.
