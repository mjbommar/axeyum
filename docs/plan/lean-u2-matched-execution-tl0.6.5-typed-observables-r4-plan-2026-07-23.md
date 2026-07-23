# Lean U2 TL0.6.5 R4 plan — typed normalized observables

Date: 2026-07-23  
Status: **preregistered offline schema correction; no process or parity credit**  
Owner: complete Lean parity lane, TL0.6.5 M1

## 1. Defect and boundary

R3 binds nine layer-specific field allowlists and rejects missing/unknown
fields, but it validates only that every value is some deterministic JSON
primitive. A field named `stdout_bytes_sha256` can therefore contain an object,
`termination_class` can contain a list, and ignored `collector_sequence` can
contain a mapping. Those malformed values still receive a normalized digest.

The defect is structural even before raw adapters exist: a sealed name is not a
typed value. R4 closes that gap with a versioned authority and executable value
schemas. It does not implement raw extractors or semantic canonicalizers,
consume TL0.6.3/TL0.6.4 parents, derive comparison obligations, launch a
process, or create an outcome, pair, performance row, axis/gate completion, or
parity credit.

## 2. Version migration

R4 publishes `lean-u2-normalization-contracts-v2.json`. It changes:

- authority schema from `axeyum-lean-u2-normalization-contracts-v1` to `v2`;
- contract digest domain from `axeyum-lean-normalization-contract-v1` to `v2`;
- projection schema/domain from `axeyum-lean-normalized-observation-v1` to
  `v2`; and
- every normalization ID from `lean-*-v1` to `lean-*-v2`.

The v1 authority and R3 result remain immutable history. Because there are zero
paired cells, migration does not rewrite any observation. A v1 ID must become
unregistered in the terminal validator; accepting it under v2 semantics would
silently reinterpret an old digest.

## 3. Field value schemas

Every compared and ignored field record carries a sealed schema. R4 admits only
four exact schema kinds:

| Kind | Accepted value |
|---|---|
| `sha256` | lowercase 64-hex string |
| `enum` | string equal to one sealed member of a nonempty ordered set |
| `nonnegative-integer` | JSON integer `>= 0`; booleans reject |
| `nonempty-string` | nonempty string |

The 68 compared fields become 65 SHA-256 identities and three enum values:

- process/harness and compiler/runtime `termination_class` use the twelve
  accepted TL0.7.1 termination classes in their registered order; and
- kernel/assurance `admission_class` uses `admitted`, `rejected`, or
  `declined`.

Four formerly untyped semantic labels become digest identities of their future
canonical payloads without changing the 68-field denominator:

- `cleanup_state` -> `cleanup_state_sha256`;
- `completion_state` -> `completion_state_sha256`;
- `expected_exit_policy` -> `expected_exit_policy_sha256`; and
- `execution_route` -> `execution_route_sha256`.

This avoids freezing an underspecified label vocabulary before the raw adapters
exist while still requiring exact typed identities. The 18 ignored fields
become nine `nonnegative-integer` collector sequences and nine nonempty storage
paths. Compared and ignored fields remain disjoint and exact.

## 4. Projection behavior

The projection kernel validates every value against its sealed schema before
omitting ignored fields or hashing selected fields. Invalid values reject with
the contract ID, field, schema kind, and bounded reason. The projection retains
the normalization ID and the same exact selected values; R4 does not coerce,
repair, trim, case-fold, or invent defaults.

The complete-parity validator must require the v2 authority path, v2 ID, exact
layer, and v2 contract seal. A fully resealed v1 cell, malformed v2 value, or v2
ID with a v1 seal rejects.

## 5. Required controls

The implementation checkpoint must include:

1. exact v2 authority and deterministic contract sealing;
2. valid-value construction from every one of the 86 field-schema occurrences;
3. every one of the 68 semantic fields changing the digest under a valid
   same-schema mutation;
4. all 18 ignored fields preserving the digest under a valid same-schema
   mutation;
5. every schema occurrence rejecting at least one wrong-type/value mutation;
6. booleans rejecting as nonnegative integers;
7. uppercase, short, long, and non-hex digest strings rejecting;
8. empty, duplicate, unsorted, or non-string enum members rejecting;
9. v1 ID, wrong layer, stale/v1 seal, and invented ID rejecting after complete
   resealing;
10. deterministic generation and differently rooted replay; and
11. unchanged zero extractors, semantic canonicalizers, outcomes, paired cells,
    complete authorities, satisfied gates, and parity credit.

## 6. Research basis

- JSON Schema 2020-12's [validation vocabulary](https://json-schema.org/draft/2020-12/json-schema-validation)
  distinguishes instance `type`, `enum`, integer bounds, string patterns, and
  required object members. R4 implements only the smaller frozen vocabulary
  above and does not claim general JSON Schema support.
- [RFC 8785](https://www.rfc-editor.org/rfc/rfc8785.html) requires invariant
  data representation before hashing. Canonical bytes alone do not make an
  instance valid against its application schema, so R4 validates first and
  hashes second.
- The accepted [TL0.7.1 execution authority](lean-execution-evidence-v1.json)
  is the repository authority for the twelve termination classes; R4 imports
  their exact values into the sealed v2 contracts rather than inventing a
  second process taxonomy.

## 7. Exit and nonclaims

R4 exits only when the v2 authority, typed validator, exhaustive controls,
complete-parity integration, generated artifacts, full parity-document gate,
link gate, and detached-root replay pass. It is still a contract/projection
checkpoint. A syntactically valid digest is not evidence that a raw adapter
computed it correctly; future post-parent adapters must bind and validate the
canonical payload and its provenance.
