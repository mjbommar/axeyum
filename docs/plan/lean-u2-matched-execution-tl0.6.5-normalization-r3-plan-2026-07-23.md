# Lean U2 TL0.6.5 R3 plan — normalization contracts and projection kernel

Date: 2026-07-23  
Status: **preregistered offline contract increment; no process or parity credit**  
Owner: complete Lean parity lane, TL0.6.5 M1

## 1. Defect and boundary

R1 content-bound execution, comparison, cell, and population records. R2 made
the comparison outcome a deterministic function of typed side results and two
normalized-observable identities. Neither revision proves that a
`normalization_id` names a registered rule set, that its digest is correct,
that it belongs to the paired cell's layer, or that its selected fields obey an
allowlist.

R3 closes that structural gap before any real paired cell exists. It freezes a
nine-layer normalization-contract registry and a small executable projection
kernel. It does **not** implement the future raw Lean/Axeyum extractors or the
layer-specific semantic canonicalizers that must produce each selected field.
It does not consume TL0.6.3/TL0.6.4 parent evidence, derive M0 comparison
obligations, launch a process, or grant any outcome, population, axis, gate,
performance, or parity credit.

## 2. Registered layers

The registry contains exactly one first-version contract for each layer already
required by the TL0.6.5 observable contract:

1. `process-harness`;
2. `parser-macro`;
3. `elaboration`;
4. `kernel-assurance`;
5. `module-cache`;
6. `tactic`;
7. `compiler-runtime`;
8. `server-rpc`; and
9. `lake-project`.

Each record binds a stable ID, layer, applicable axes, nonempty sorted semantic
field allowlist, sorted ignored-field rules with nonempty reasons, canonical
encoding, unknown-field policy, and a domain-separated content seal. Compared
and ignored fields must be disjoint. The registry order and summary are
derived, not editorial.

This is a contract registry, not a claim that every U2 case has nine
obligations. The future post-parent M0 authority selects the applicable layers
for each exact case/variant/axis and records exclusions.

## 3. Projection kernel

For a selected contract, the kernel accepts one JSON observation only when its
top-level fields are **exactly** the union of the registered compared and
ignored fields. Unknown and missing fields reject. Values are restricted to
deterministic JSON primitives: null, booleans, integers, strings, arrays, and
string-keyed objects recursively; floating-point values reject.

The canonical projection contains the schema, normalization ID, and every
compared field. Ignored fields are omitted only because their names and reasons
are sealed in the contract. Canonical bytes use UTF-8 JSON with sorted object
keys, original array order, no insignificant whitespace, non-ASCII retained,
and no NaN/infinity. A domain-separated SHA-256 identifies the projection.

The initial ignored fields are deliberately narrow:

- `evidence_storage_path`, because raw evidence content and reachability are
  independently sealed while an absolute/local storage spelling is not a
  semantic observable; and
- `collector_sequence`, because local ingestion order is not semantic while
  attempt, completion, transcript, and evidence ordering remain selected in
  their owning records.

Paths, ordering, versions, platform, resources, attempts, completion, and
assurance are **not** generally normalized away. Only the two exact fields
above receive this R3 ignored-field treatment.

## 4. Paired-cell enforcement

The complete-parity validator must resolve every comparison's
`normalization_id` through the registered authority, require the paired cell's
`layer` to equal the contract layer, and require `normalization_sha256` to equal
the recomputed contract seal. An invented ID, cross-layer reuse, or stale seal
must fail even when every enclosing execution/comparison/cell/population seal
is recomputed correctly.

R2's outcome derivation remains unchanged. Equal projection digests still mean
canonical-byte equality only; R3 does not add an opaque semantic-equivalence
escape hatch.

## 5. Required controls

The implementation checkpoint must include:

1. exact validation and deterministic sealing of all nine contracts;
2. one semantic-field mutation per field in every contract changing the
   normalized digest;
3. one ignored-field mutation per ignored rule in every contract preserving
   the normalized digest;
4. missing, extra, overlapping, duplicate, unsorted, floating-point, and
   malformed nested values rejecting;
5. object-key insertion order normalizing identically while array order remains
   significant;
6. unknown normalization ID, wrong layer, and stale normalization seal rejecting
   after all enclosing paired-record seals are recomputed;
7. deterministic generated JSON/Markdown and differently rooted checkout
   replay; and
8. unchanged zero native outcomes, zero paired cells, zero complete paired
   authorities, zero satisfied terminal gates, and false terminal claim.

## 6. Primary references

- Lean's [elaboration and compilation reference](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
  separates parsing, macro expansion, elaboration metadata/info trees, kernel
  checking, compiler input, serialized environments, editor indexes, native
  artifacts, and initialization state.
- Lean's [source-file and module reference](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
  makes import visibility and multi-part module environments observable rather
  than treating a module as one source/output byte string.
- Lean v4.30.0's pinned [test-suite contract](https://github.com/leanprover/lean4/blob/v4.30.0/tests/README.md)
  distinguishes expected output, ignored output, expected failure,
  compile/interpreter, server, Lake, package, and benchmark behavior.
- Lean's [`FileWorker` API](https://lean-lang.org/doc/api/Lean/Server/FileWorker.html)
  records document-version tracking, cancellation, worker state, and filtering
  of outdated notifications; these cannot be erased from server comparison.
- [RFC 8785](https://www.rfc-editor.org/rfc/rfc8785.html) motivates invariant
  JSON serialization for hashing. R3 freezes its narrower internal encoding and
  does not claim full JCS compatibility.

## 7. Exit and nonclaims

R3 exits when the registry, projection kernel, paired-cell enforcement,
exhaustive mutation controls, generated artifacts, parity documentation gate,
link gate, and detached-root replay pass. The result must describe this as a
bounded contract/projection checkpoint. Raw-to-selected-field adapters,
semantic canonicalizers, the post-parent obligation authority, and every live
execution milestone remain open.
