# Lean U2 TL0.6.5 R5 plan — normalization axis coverage

Date: 2026-07-23

Status: **preregistered offline authority correction; no process or parity credit**

Owner: complete Lean parity lane, TL0.6.5 contract/projection boundary

## 1. Defects and boundary

R4 validates every selected field value before projection, but two relational
defects remain in the terminal registry:

1. each normalization contract seals `applicable_axes`, yet paired-cell
   validation checks only the normalization ID, layer, and contract seal; and
2. the union of the nine current contracts covers A0--A9 and A11, but no
   current normalizer covers terminal axis A10, `mathlib ecosystem`.

A direct fully resealed control changed a valid kernel/assurance cell from A1
to A0 while retaining the same layer and v2 normalizer. The terminal validator
returned no failure:

```text
RESEALED_WRONG_AXIS_ACCEPTED=True
```

The first defect means a sealed applicability rule is currently inert. The
second means A10 has no registered semantic projection route even though the
[complete-parity contract](lean4-complete-parity-contract-2026-07-22.md#6-complete-parity-axes)
requires a complete pinned-mathlib profile and separately defines mathlib
equivalence.

R5 closes both defects before any paired cell exists. It does not create a
mathlib population, inspect or execute mathlib, implement raw extractors or
semantic canonicalizers, consume TL0.6.3/TL0.6.4 parents, launch a process, or
create an outcome, pair, completed axis/gate, or parity credit.

## 2. Versioned authority migration

R5 publishes `lean-u2-normalization-contracts-v3.json` and preserves v1/R3 and
v2/R4 as immutable history. It versions:

- the authority schema to `axeyum-lean-u2-normalization-contracts-v3`;
- the contract digest domain to `axeyum-lean-normalization-contract-v3`;
- the normalized projection schema/domain to
  `axeyum-lean-normalized-observation-v3`; and
- every normalization ID from `lean-*-v2` to `lean-*-v3`.

The complete-parity validator must require the v3 authority path and reject a
fully resealed v1 or v2 paired cell. Because paired-cell count remains zero,
the migration rewrites no observation or credited evidence.

## 3. Complete axis coverage

The v3 registry contains ten contracts. The existing nine retain their R4
field schemas and applicable axes. A new `lean-mathlib-ecosystem-v3` contract
owns layer `mathlib-ecosystem`, applies only to A10, and selects eight exact
SHA-256 identities:

1. `axiom_trust_closure_sha256`;
2. `build_outcomes_sha256`;
3. `declaration_closure_sha256`;
4. `failure_classification_sha256`;
5. `module_outcomes_sha256`;
6. `runtime_tests_sha256`;
7. `tactic_results_sha256`; and
8. `test_outcomes_sha256`.

These fields are the minimum direct projection of A10's existing terminal
contract: complete module/build/test/tactic outcomes, declaration and axiom
closures, runtime tests, and zero unclassified failures. Source and dependency
identity remain common paired-cell fields. Commands, resources, attempts,
completion, assurance, and performance remain independently sealed side-record
properties; resource or timing differences do not silently become functional
semantic differences.

Like every other contract, the mathlib contract ignores only a typed
`collector_sequence` and typed `evidence_storage_path`, with sealed reasons.
The v3 derived totals must be exact:

- ten contracts;
- 76 compared fields;
- 20 ignored rules;
- 96 typed field occurrences;
- 73 SHA-256 fields, three enums, ten nonnegative integers, and ten nonempty
  strings;
- twelve covered axes; and
- fifteen exact contract/axis applicability occurrences.

The validator must reject a registry whose applicability union is not exactly
A0--A11. Contract-local axis lists remain nonempty, unique, numeric-order
sorted, and content sealed.

## 4. Paired-cell relational rule

After resolving a registered normalizer, the terminal validator must require:

```text
cell.axis in normalization_contract.applicable_axes
```

This check is independent of the existing same-layer and exact-seal checks.
The cell, comparison, and population-authority hashes may all be valid and the
record must still reject if the axis/normalizer relation is invalid. No axis is
inferred from layer name, population, source family, or outcome.

## 5. Required controls

The R5 implementation checkpoint must include:

1. exact deterministic v3 authority sealing and rendering;
2. exact A0--A11 union coverage and fifteen positive applicability pairs;
3. all 105 invalid contract/axis pairs rejecting after full cell,
   comparison, and bounded-population resealing;
4. every valid pair passing the same fully resealed control;
5. direct A10/mathlib positive coverage;
6. missing A10, duplicate/unsorted axis, unknown axis, stale seal, wrong layer,
   invented ID, authentic v1 ID/seal, and authentic v2 ID/seal controls;
7. all 76 semantic-field mutations changing their projection digests;
8. all 20 ignored-field mutations preserving projection digests;
9. malformed-value rejection across all 96 typed occurrences;
10. deterministic generation and differently rooted replay; and
11. unchanged zero extractors, canonicalizers, outcomes, paired cells,
    complete populations/axes, satisfied gates, and parity credit.

## 6. Research basis

The JSON Schema 2020-12
[applicator vocabulary](https://json-schema.org/draft/2020-12/draft-bhutton-json-schema-00#section-10.2.2)
distinguishes per-property validation from conditions that validate an entire
object. R5 implements only the repository's explicit axis/normalizer relation;
it does not claim general JSON Schema support.

Lean's [Lake reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
separates packages, transitive dependencies, modules, build artifacts,
targets/facets, test drivers, and runtime test execution. The pinned mathlib
[README](https://github.com/leanprover-community/mathlib4/blob/v4.30.0/README.md)
requires `lake test` for the full test path. These separate observable classes
support a profile-level A10 projection rather than treating file presence or a
single build exit as mathlib parity.

## 7. Exit and nonclaims

R5 exits only when the v3 authority, missing A10 route, axis-applicability
validator, exhaustive pair matrix, typed projection controls, complete-parity
integration, generated artifacts, parity-document gate, link gate, and
detached-root replay pass.

This is still an offline authority checkpoint. A registered A10 normalizer is
not a mathlib denominator, execution, result, or parity claim. Future
post-parent work must freeze the complete pinned mathlib population and prove
that raw official/Axeyum evidence produces each selected identity before any
A10 cell receives credit.
