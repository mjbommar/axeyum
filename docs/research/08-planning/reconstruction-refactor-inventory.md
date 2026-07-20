# Reconstruction refactor inventory

Status: active; R1, R2, and the equality/datatype slices of R3 complete
Date: 2026-07-20
Baseline: Axeyum `852ec4790411a7fbf89c48dd1aa4a952f0cb5fa0`

## Purpose

Reduce the artifact-review cost of `axeyum-solver`'s proof reconstruction code
without weakening its trust boundary or changing generated Lean source. This is
an internal organization and duplication project, not a new proof rule, solver
capability, or public API project.

The non-negotiable identity is still **untrusted fast search, trusted small
checking**. Moving a reconstructor must not move certificate validation into an
untrusted layer, replace kernel inference with an assertion, or widen the set of
accepted terms.

## Measured baseline

| Surface | Current size / shape |
|---|---:|
| `reconstruct.rs` | 18,517 lines / 804,247 bytes before R1; 16,999 lines / 743,551 bytes after R2; 16,476 lines / 720,714 bytes after equality; 14,189 lines / 618,110 bytes after datatype |
| `reconstruct/direct.rs` | 1,406 lines / 52,407 bytes after R2 |
| `reconstruct/equality.rs` | 534 lines / 23,244 bytes after the first R3 family extraction |
| `reconstruct/datatype.rs` | 2,313 lines / 103,818 bytes after the second R3 family extraction |
| `reconstruct/tests.rs` | 4,670 lines / 190,715 bytes |
| `reconstruct/quant_bv_instance_set_lean.rs` | 3,665 lines / 135,043 bytes |
| `int_reconstruct.rs` | 8,876 lines / 371,286 bytes |
| `reconstruct_*_to_lean_module` functions in `reconstruct.rs` | 43 |
| `ProofFragment` variants in the general dispatcher | 61 |
| direct structural variants in the pre-dispatch seam | 34 |

The file is large for two different reasons that should not be conflated:

1. it contains several genuinely different proof calculi and kernel encodings;
2. its direct structural lane repeats one small checked-wrapper emitter around
   many different certificate validators.

Only the second is safe for immediate parameterization.

## Direct structural lane

`reconstruct_direct_structural_fragment_to_lean_module` owns 34 variants. They
fall into three groups:

| Group | Count | Treatment |
|---|---:|---|
| Custom constructive encodings | 5 | Keep explicit: finite-domain pigeonhole, reflexive disequality, term identity, array axiom, finite-array extensionality |
| Checked certificate plus the same opaque-proposition emitter | 26 | Keep each named validator and error contract; route only its final emission through one helper |
| Already routed through that helper | 3 | Keep: const-array default mismatch, store-chain readback, cross-store array disequality |

The 29 shared-emitter rows all construct the same kernel-checked shape:

```text
axiom asserted : P
axiom refuter : Not P
exact refuter asserted
```

This is not permission to table-drive the certificate checks. Their validation
rules, failure details, recheck requirements, and source modules remain distinct.
Only the final deterministic Lean wrapper is common.

## File families

The remaining monolith divides into reviewable ownership families:

| Family | Approximate current region | Natural destination |
|---|---|---|
| Shared context, names, equality reconstruction | start through direct-certificate helpers | `reconstruct/core.rs` and `reconstruct/equality.rs` |
| Direct structural certificate adapters | finite-domain/direct lane through line 3,665 | `reconstruct/direct.rs` |
| Fragment selection and top-level dispatch | normalization and lines around 3,805--4,236 | keep in `reconstruct/mod.rs` |
| ABV and structural datatype source | starts around 4,237 and 4,885 | `reconstruct/array.rs`, `reconstruct/datatype.rs` |
| Quantifier and Skolem evidence | starts around 7,339 | `reconstruct/quantifier.rs` plus the existing BV instance-set module |
| Resolution/RUP/CNF introduction | starts around 8,236 and 10,813 | `reconstruct/resolution.rs`, `reconstruct/cnf.rs` |
| Bit-blast and QF_BV evidence | starts around 12,292 and 12,745 | `reconstruct/bitblast.rs` |
| LRA/SOS evidence | starts around 15,833 | `reconstruct/arithmetic.rs` |

These are ownership targets, not a command to move all regions at once. Private
cross-family dependencies must be made explicit before each extraction; broad
`pub(crate)` visibility is not an acceptable shortcut.

## Required gates

Every extraction or parameterization increment must preserve all of the
following:

1. the public `prove_unsat_to_lean_module` and `ProofFragment` surface;
2. exact fragment selection for accepted and rejected inputs;
3. validator order, recheck calls, error variant, rule string, and detail text;
4. byte-for-byte generated Lean source for every affected accepted row;
5. successful independent kernel inference of `False`;
6. deterministic naming and declaration order;
7. the `qfbv` default feature boundary and native-free default build; and
8. no new trusted axiom shape, unsafe code, or public re-export.

The ordinary full-profile solver suite is necessary but insufficient for item
4. Shared-emitter work therefore needs a test that compares the helper against
the pre-refactor emission algorithm over every registered `(proposition stem,
refuter role)` pair. Later file moves should add source snapshots or equivalent
before/after byte comparisons for their affected fixtures.

## Staged sequence

1. **R1 — emitter parameterization (complete).** The exhaustive
   legacy-equivalence test covers all 29 registered stem/role pairs; all 26
   formerly inline adapters now use the shared helper, while every validator
   remains named and unchanged. This removes 130 lines / 8,924 bytes from
   `reconstruct.rs`. All 884 full-profile solver tests and clippy `-D warnings`
   pass.
2. **R2 — direct-lane ownership (complete).** The 34 direct adapters, five
   constructive encodings, shared emitter, and explicit dispatcher now live in
   `reconstruct/direct.rs`. The parent keeps one dispatch call and one narrow
   finite-domain certification predicate used by fragment scanning; no
   certificate type or broad private surface was exposed. `reconstruct.rs`
   drops from 18,387 to 16,999 lines. All 884 tests, byte-equivalence checks,
   and clippy pass.
3. **R3 — one proof family per commit (active; equality complete).** The first
   slice moves the nine equality-owned entry/build/helper functions into
   `reconstruct/equality.rs`: reflexivity, clause and premise symmetry,
   binary/n-ary transitivity, and n-ary congruence. Shared `as_positive_eq`,
   `as_negated_eq`, and `check_against` remain parent-owned because resolution,
   quantifier, CNF, and bit-blast routes also consume them. The parent imports
   only the three private helpers used by its clausal walk and publicly re-exports
   the unchanged `reconstruct_eq_step`. Deterministic FNV-1a snapshots fix the
   transitivity module at 1,480 bytes / `16524372807544528002` and the congruence
   module at 1,558 bytes / `9142307883420495535`; kernel inference also remains
   explicit. All 885 full-profile solver tests and clippy `-D warnings` pass.
   The second slice's dependency census shows that datatype is one cohesive
   2,313-line family, while direct array adapters already belong to R2 and the
   remaining `reconstruct_qf_abv_to_lean_source` is a 44-line orchestrator.
   Datatype therefore moves alone. The parent imports only its four specialized
   routes and retains datatype-aware Alethe term translation; eight Nat-lemma
   builders are visible only to the existing unit tests. FNV-1a snapshots pin
   tester at 2,057 bytes / `12042421301549597275`, distinctness at 3,069 bytes /
   `15726968749404357215`, injectivity at 2,640 bytes /
   `1434913494449130936`, and acyclicity at 3,940 bytes /
   `2520869314195085188`. All 886 full-profile tests, clippy, and rustdoc pass.
   Next census and extract quantifier, resolution/CNF, bit-blast, and arithmetic
   regions separately, with the same per-family gates. Do not create an array
   module solely to relocate the thin orchestration function.
4. **R4 — visibility audit.** After the files settle, narrow private imports and
   only then evaluate the separate root-API namespacing work.

Do not combine R1--R4 with solver behavior, proof-rule additions, or public API
renaming. Small reviewable commits are the artifact-readiness objective.
