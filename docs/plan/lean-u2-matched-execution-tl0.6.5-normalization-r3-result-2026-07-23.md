# Lean U2 TL0.6.5 R3 result — normalization contracts and projection kernel

Date: 2026-07-23  
Status: **accepted bounded contract/projection correction; no process or parity credit**  
Plan: [R3 normalization plan](lean-u2-matched-execution-tl0.6.5-normalization-r3-plan-2026-07-23.md)  
Implementation checkpoint: `b1b3efd5`

## Result

TL0.6.5 comparisons can no longer name an invented or stale normalizer. The
new machine authority registers nine exact layer contracts, and the paired-cell
validator requires every comparison to cite a registered normalizer whose
layer and content seal match the cell.

The executable projection kernel is allowlist based. It rejects missing and
unknown fields, floating-point or non-JSON values, and malformed nested values;
it retains original array order and canonicalizes object-key order. Only fields
with a sealed ignored-field rule are omitted from the normalized projection.

## Accepted authority

The [machine authority](lean-u2-normalization-contracts-v1.json) and generated
[summary](generated/lean-u2-normalization-contracts.md) bind:

- nine contracts: process/harness, parser/macro, elaboration,
  kernel/assurance, module/cache, tactic, compiler/runtime, server/RPC, and
  Lake/project;
- 68 exact semantic compared fields;
- 18 ignored-field rules: `collector_sequence` and
  `evidence_storage_path`, each with a per-layer sealed reason;
- UTF-8 compact JSON with sorted object keys, original array order, no
  floating-point numbers, and domain-separated SHA-256;
- unknown-field policy `reject`; and
- zero raw extractors, semantic canonicalizers, official outcomes, Axeyum
  outcomes, paired cells, and parity credit.

The ignored rules do not erase semantic order or identity. Attempt/completion,
syntax, declaration, dependency, effect, transcript, version, cancellation,
graph, job, cache, and incremental order remain inside selected records or
selected observable identities.

## Controls

Six focused normalization tests cover:

- all 68 semantic-field mutations changing the projection digest;
- all 18 ignored-field mutations preserving the projection digest;
- exact-field, malformed nested-value, float, and unknown-ID rejection;
- object-key order equivalence and array-order sensitivity;
- contract seal, overlap, order, and false-credit mutations; and
- deterministic registry rendering.

The complete-parity module now has 24 tests. Its added paired-cell controls
fully reseal the comparison, cell, and population authority after inventing a
normalizer ID, crossing layers, or substituting a stale contract seal; each
still rejects for the semantic registry defect rather than only for an outer
hash mismatch.

## Validation checkpoint

The final checkpoint passed:

- `python3 -m unittest scripts.tests.test_lean_u2_normalization_contracts` —
  six tests;
- `python3 -m unittest scripts.tests.test_lean_complete_parity` — 24 tests;
- both normalization and complete-parity generators under `--check`;
- `just parity-docs`, including the complete registered Lean/SMT evidence
  suite;
- `just links`; and
- differently rooted detached-checkout replay of the two generators, the six
  normalization tests, the three paired normalizer controls, and link
  validation.

The complete-parity truth line remained:

```text
LEAN_COMPLETE_PARITY|populations=10|complete_populations=0|axes=12|complete_axes=0|paired_cells=0|gates_satisfied=0|terminal_ready=false
```

No M2.1 native header process or M2.2-M2.7 external process was launched.

## Research basis

Lean's [elaboration and compilation reference](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
separates syntax, macro expansion, elaboration metadata, kernel checking,
compiler input/output, serialized environments, editor indexes, and
initialization. Its [module reference](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
makes visibility and multi-part environments observable. The pinned
[test-suite contract](https://github.com/leanprover/lean4/blob/v4.30.0/tests/README.md)
separates expected/ignored output and compile, interpreter, server, Lake,
package, and benchmark behavior. Lean's [`FileWorker` API](https://lean-lang.org/doc/api/Lean/Server/FileWorker.html)
also makes document versions, cancellation, worker state, and stale-notification
filtering explicit. These boundaries justify layer-specific contracts instead
of one process-output hash.

## Truth boundary and next work

R3 implements the registry and selected-field projection kernel, **not** the
raw-to-selected-field adapters or semantic canonicalizers for actual Lean and
Axeyum artifacts. It creates no official/native comparison obligation,
execution, outcome, pair, performance row, U2 promotion, completed axis/gate,
or parity credit.

TL0.6.3 and TL0.6.4 remain incomplete parents. After their acceptance, M0 must
derive the complete layer-expanded obligation authority. M1 must then implement
and validate each raw extractor and semantic canonicalizer against real frozen
artifacts before M2 may authorize a native attempt.
