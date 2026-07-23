# Lean U2 TL0.6.5 R4 result — typed normalized observables

Date: 2026-07-23

Status: **accepted bounded schema correction; no process or parity credit**

Plan: [R4 typed-observable plan](lean-u2-matched-execution-tl0.6.5-typed-observables-r4-plan-2026-07-23.md)

Preregistration: `7418ba95`

Typed projection checkpoint: `7ef93b57`

Complete-parity integration checkpoint: `92d30d38`

## Result

R3's field-name allowlist no longer accepts arbitrary deterministic JSON as a
valid normalized observation. R4 validates every field value against a sealed
schema before projection. An object in `stdout_bytes_sha256`, a list in
`termination_class`, a Boolean collector sequence, or an empty evidence path
now rejects instead of receiving a normalized digest.

The current [v2 machine authority](lean-u2-normalization-contracts-v2.json)
versions the authority schema, all nine normalization IDs, the contract digest
domain, and the normalized-projection domain. The
[v1 authority](lean-u2-normalization-contracts-v1.json) remains immutable R3
history and is not a current normalizer.

## Accepted typed authority

The v2 authority and generated
[summary](generated/lean-u2-normalization-contracts.md) bind 86 typed field
occurrences:

- 65 lowercase 64-hex SHA-256 identities;
- three enums: two exact twelve-member termination taxonomies and one
  three-member kernel admission taxonomy;
- nine nonnegative JSON integers for `collector_sequence`, with Booleans
  rejected; and
- nine nonempty strings for `evidence_storage_path`.

The 68 compared-field and 18 ignored-rule denominators are unchanged. Four
formerly untyped semantic labels now name digests of their future canonical
payloads: `cleanup_state_sha256`, `completion_state_sha256`,
`expected_exit_policy_sha256`, and `execution_route_sha256`.

The two termination enums are checked against the exact ordered taxonomy in
the accepted [execution-evidence authority](lean-execution-evidence-v1.json).
The validator permits no coercion, trimming, case folding, repair, or default.
No registered field schema admits an array or object.

## Complete-parity integration

The [terminal registry](lean-complete-parity-v1.json) now requires the v2
authority. Its paired-cell validator resolves only a registered v2 ID and
requires the exact same-layer v2 contract seal. A paired cell carrying the
authentic v1 kernel normalizer ID and seal still rejects after the comparison,
cell, and population authority are fully resealed.

The v1 authority remains a content-identified historical source in the
generated complete-parity report. It cannot be silently interpreted with v2
semantics.

## Controls

Eight focused normalization tests establish:

1. all 86 field-schema occurrences accept a valid constructed value and reject
   a malformed same-field mutation;
2. every one of the 68 valid semantic-field mutations changes the projection
   digest;
3. every one of the 18 valid ignored-field mutations preserves the projection
   digest;
4. uppercase, short, long, and non-hex digest strings reject;
5. empty, duplicate, reordered, and non-string enum definitions reject;
6. negative and Boolean collector sequences plus empty storage paths reject;
7. missing, extra, object, array, numeric, null, v1-ID, and invented-ID inputs
   reject; and
8. top-level object insertion order does not change the canonical projection.

The 24 complete-parity tests retain all prior population, axis, pair,
authority, seal, and terminal-claim controls while adding the v2 snapshot and
fully resealed v1 rejection.

## Validation checkpoint

The accepted checkpoints passed:

- `python3 -m unittest scripts.tests.test_lean_u2_normalization_contracts` —
  eight tests;
- `python3 -m unittest scripts.tests.test_lean_complete_parity` — 24 tests;
- both generators under `--check`;
- `just parity-docs`, including the complete registered Lean/SMT evidence
  suite;
- `just links`; and
- a differently rooted detached replay at
  `/tmp/axeyum-lean-r4-replay.KfMzuT` of all 32 focused tests and both
  generator checks.

The normalization truth line is:

```text
LEAN_U2_NORMALIZATION|contracts=9|compared_fields=68|ignored_rules=18|typed_fields=86|sha256=65|enum=3|nonnegative_integer=9|nonempty_string=9|raw_extractors=0|semantic_canonicalizers=0|paired_cells=0|parity_credit=0
```

The terminal truth remains:

```text
LEAN_COMPLETE_PARITY|populations=10|complete_populations=0|axes=12|complete_axes=0|paired_cells=0|gates_satisfied=0|terminal_ready=false
```

No M2.1 native-header process or M2.2-M2.7 external process was launched.

## Portability integration boundary

The root-relative portability repair remains present and validated on this
Lean branch. It is not yet on `main`. At the final R4 check, remote `main` was
`2a04d8f0ae79a862975dde5fb78773d39064fc05`, and docs run
[`30027546161`](https://github.com/mjbommar/axeyum/actions/runs/30027546161)
still failed with:

```text
LEAN_PROCESS_ATTEMPT_ERROR|exit-zero-4g: run/spec attribution drift
```

Therefore R4 does not claim that the shared integration branch, its docs gate,
or downstream workstreams blocked by that gate are repaired. The branch-local
portability result remains documented separately in the
[R1 result](lean-complete-parity-worktree-portability-r1-result-2026-07-23.md).

## Research basis

JSON Schema 2020-12's
[validation vocabulary](https://json-schema.org/draft/2020-12/json-schema-validation)
separates instance types, enumerations, integer bounds, and string constraints.
R4 implements only its smaller sealed four-kind vocabulary; it does not claim
general JSON Schema support. [RFC 8785](https://www.rfc-editor.org/rfc/rfc8785.html)
defines deterministic JSON canonicalization, but canonical bytes do not prove
that an instance satisfies an application schema. R4 therefore validates
before projection and hashing.

## Truth boundary and next work

R4 is typed contract/projection evidence only. A syntactically valid digest is
not proof that a raw Lean or Axeyum adapter computed it from the right artifact
or used the correct semantic canonicalizer. Raw extractors, semantic
canonicalizers, complete comparison obligations, official/native matched
outcomes, pairs, performance rows, U2 promotion, completed axes/gates, and
parity credit remain zero.

The next TL0.6.5 work remains gated on complete accepted TL0.6.3 and TL0.6.4
parents. After those parents exist, M0 must derive the exact layer-expanded
obligation authority and M1 must validate each raw-to-canonical adapter before
M2 may authorize a native attempt.
