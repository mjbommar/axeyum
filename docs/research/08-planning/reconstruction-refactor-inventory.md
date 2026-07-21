# Reconstruction refactor inventory

Status: active; R1, R2, and R3 complete; R4a--R4f namespaces complete
Date: 2026-07-20
Baseline: Axeyum `852ec4790411a7fbf89c48dd1aa4a952f0cb5fa0`

## Purpose

Reduce the artifact-review cost of `axeyum-solver`'s proof reconstruction code
without weakening its trust boundary or changing generated Lean source. This is
an internal organization and duplication project followed by a measured
public-API organization pass, not a new proof rule or solver capability.

The non-negotiable identity is still **untrusted fast search, trusted small
checking**. Moving a reconstructor must not move certificate validation into an
untrusted layer, replace kernel inference with an assertion, or widen the set of
accepted terms.

## Measured baseline

| Surface | Current size / shape |
|---|---:|
| `reconstruct.rs` | 18,517 lines / 804,247 bytes before R1; 16,999 lines / 743,551 bytes after R2; 16,476 lines / 720,714 bytes after equality; 14,189 lines / 618,110 bytes after datatype; 13,350 lines / 580,831 bytes after quantifier; 11,225 lines / 498,127 bytes after resolution; 9,680 lines / 433,992 bytes after CNF; 7,748 lines / 346,174 bytes after bit-blast; 2,793 lines / 122,834 bytes after arithmetic |
| `reconstruct/direct.rs` | 1,406 lines / 52,407 bytes after R2 |
| `reconstruct/equality.rs` | 534 lines / 23,244 bytes after the first R3 family extraction |
| `reconstruct/datatype.rs` | 2,313 lines / 103,818 bytes after the second R3 family extraction |
| `reconstruct/quantifier.rs` | 853 lines / 37,900 bytes after the third R3 family extraction |
| `reconstruct/resolution.rs` | 2,150 lines / 83,697 bytes after the fourth R3 family extraction |
| `reconstruct/cnf.rs` | 1,578 lines / 64,950 bytes after the fifth R3 family extraction |
| `reconstruct/bitblast.rs` | 1,956 lines / 88,950 bytes after the sixth R3 family extraction |
| `reconstruct/arithmetic.rs` | 4,970 lines / 224,046 bytes after the seventh R3 family extraction |
| `reconstruct/tests.rs` | 4,885 lines / 199,052 bytes |
| `reconstruct/quant_bv_instance_set_lean.rs` | 3,665 lines / 135,043 bytes |
| `int_reconstruct.rs` | 8,876 lines / 371,286 bytes |
| `reconstruct_*_to_lean_module` functions in `reconstruct.rs` | 4 after R3 |
| `ProofFragment` variants in the general dispatcher | 61 |
| direct structural variants in the pre-dispatch seam | 34 |

## R4 public API census

The post-R3 rustdoc root was measured before selecting a namespace. Counts are
from warning-denied rustdoc in both supported solver profiles, not from source
text or the older approximate review number.

| Profile / surface | Before R4a | After R4a | After R4b | After R4c | After R4d | After R4e | After R4f |
|---|---:|---:|---:|---:|---:|---:|---:|
| all-feature documented crate-root items | 549 | 442 | 338 | 276 | 211 | 172 | 148 |
| minimal-`qfbv` documented crate-root items | 36 | 26 | 26 | 26 | 26 | 26 | 26 |
| entries organized in the `proofs` subtree | 0 | 113 | 115 | 115 | 115 | 115 | 115 |
| entries organized in the `certificates` subtree | 0 | 0 | 105 | 105 | 105 | 105 | 105 |
| entries organized in the `theories` subtree | 0 | 0 | 0 | 70 | 70 | 70 | 70 |
| entries organized in the `verification` subtree | 0 | 0 | 0 | 0 | 72 | 72 | 72 |
| entries organized in the `optimization` subtree | 0 | 0 | 0 | 0 | 0 | 43 | 43 |
| entries organized in the `smtlib` module | 0 | 0 | 0 | 0 | 0 | 0 | 25 |

ADR-0305 makes `proofs` the canonical documentation facade for minimal proof
export plus full-profile Alethe, end-to-end certification, evidence,
faithfulness, and Lean reconstruction. Historical root paths remain callable
and type-identical but are `#[doc(hidden)]`; this is a source-compatible
documentation and ownership change. Glaurung already selects the minimal
`qfbv` profile, and its existing root imports continue to compile. Theory and
certificate surfaces require separate consumer/collision censuses before they
receive equivalent facades. ADR-0306 completes the certificate-catalog census
for the two exact leak families identified by the review: 31 array entries and
72 quantified entries now live under `certificates::{arrays, quantifiers}`.
The two finite-quantifier Alethe emitters join `proofs::alethe`; general
`check_model` replay and array decision procedures intentionally remain visible
at the root for the separate theory/API census. ADR-0307 completes that census:
63 direct theory contracts and procedures now live under seven semantic
`theories` submodules. The facade deliberately excludes model replay,
auto-dispatch, SMT-LIB, optimization, interpolation, symbolic execution,
verification, proofs, and certificates. The next root-API pass must measure
those remaining cross-cutting domains independently rather than stretching the
three accepted facades. ADR-0308 then moves 66 existing verification-facing
contracts under `verification`: transition systems, Horn clauses, IMC, PDR,
symbolic execution, and the tiny-BV reference VM. That application layer is
not a solver theory or proof format. Its historical root paths remain callable,
and the next census keeps optimization, SMT-LIB, interpolation, and general
refutation utilities separate. ADR-0309 then groups 40 model-minimization,
MaxSAT, and objective-optimization entries under `optimization`. It deliberately
excludes the Pbls satisfiability backend, SMT-LIB textual commands, and the
consumer-facing `Solver` methods. ADR-0310 then exposes the existing `smtlib`
module because its exact 25 public items already equal the complete root-owned
text-front-door surface; no helper or internal state becomes public.

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
8. no new trusted axiom shape, unsafe code, or unmeasured public re-export.

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
3. **R3 — one proof family per commit (complete).** The first
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
   The third census keeps the specialized quantified-BV instance-set module
   separate and moves the cohesive general universal-instantiation and
   existential-elimination family into `reconstruct/quantifier.rs`. Its shared
   clause, resolution, equality-literal, and kernel-check machinery remains
   parent-owned; the two public reconstruction entry points are re-exported
   unchanged, and only `declare_forall_axiom` gains a test-only parent seam.
   FNV-1a snapshots pin the universal module at 921 bytes /
   `17229612914579886985` and the combined existential/universal module at
   2,685 bytes / `12920678261632022537`. All 887 full-profile tests, clippy,
   and rustdoc pass. The fourth census confirms that propositional
   resolution/RUP and CNF gate introduction are separate proof families even
   though bit-blast consumes both. Resolution therefore moves alone into
   `reconstruct/resolution.rs`. Four shared context methods, two clausal types,
   and thirteen clausal helper seams are visible only to the parent, each with an
   existing CNF, quantified-BV, direct-certificate, or bit-blast consumer; the
   public `reconstruct_resolution_proof` entry point is re-exported unchanged.
   A representative multi-step resolution module remains fixed at 1,651 bytes /
   `3433224910840366031`. All 888 full-profile tests, clippy, and rustdoc pass.
   The fifth slice moves CNF gate introduction alone into `reconstruct/cnf.rs`.
   Eight shared context methods, one assignment type/constructor, and six proof
   helpers are parent-visible only because resolution tests, quantified-BV,
   direct certificates, or bit-blast already consume them; all other CNF
   implementation details remain private. The public
   `reconstruct_cnf_intro_rule` entry point is re-exported unchanged. FNV-1a
   snapshots pin the specialized n-ary `and_pos` module at 3,358 bytes /
   `14531428178443531371` and the general `xor_neg1` module at 4,504 bytes /
   `11358181693276788078`. All 889 full-profile tests, clippy, and rustdoc pass.
   The sixth slice moves the complete bit-blast/QF_BV family into
   `reconstruct/bitblast.rs`. Its five public entry points are re-exported
   unchanged. Five parent-visible production helpers serve CNF or quantified-BV,
   while one congruence-block type and two helpers remain parent-visible only for
   the existing datatype-projection no-assumed-axiom audit. There is no
   arithmetic dependency. FNV-1a snapshots pin the pointwise BVAND module at
   6,171 bytes / `6475695101939760022` and the width-2 ripple-carry-add module at
   19,619 bytes / `1281267001421498970`. All 890 full-profile tests, clippy, and
   rustdoc pass. The seventh census finds one cohesive arithmetic family rather
   than separate LRA/SOS projects: exact-linear forms, the arithmetic kernel
   context, Farkas folds, SOS ring normalization, and disjunctive-LRA scanning
   share the same invariants. The complete family now lives in
   `reconstruct/arithmetic.rs`; the three public LRA/SOS entry points are
   re-exported unchanged. Four production-only functions plus the private
   exact-linear form serve parent classification/dispatch, and two Farkas
   helpers remain parent-visible only to existing tests. FNV-1a snapshots pin
   the linear module at 7,747 bytes / `232852107906522853` and the single-square
   SOS module at 1,088 bytes / `9042568084332375518`. All 891 full-profile
   tests, clippy, and rustdoc pass. The parent is now 2,793 lines / 122,834
   bytes; the thin ABV orchestration remains parent-owned rather than becoming
   an artificial array module.
4. **R4 — visibility and root-API audit (active).** R4a introduces a curated
   `proofs` facade after measuring both feature profiles. It adds no previously
   private item: every facade entry was already public at the crate root, and
   every historical path remains available as a rustdoc-hidden alias. Dedicated
   default-`qfbv` and all-feature gates prove representative type and function
   identity. The documented all-feature root falls from 549 to 442 items and the
   minimal root from 36 to 26, with 113 entries organized below `proofs`. All
   891 solver-library tests, strict all-target clippy, and warning-denied
   rustdoc pass. ADR-0305 owns the compatibility policy. Next, census
   `theories` and `certificates` independently; do not turn R4 into a broad
   breaking rename or mix it with solver behavior. R4b then groups the measured
   array and quantified certificate catalogs under
   `certificates::{arrays, quantifiers}` while keeping every historical root
   alias and leaving general model/theory entry points documented at the root.
   The all-feature root falls again from 442 to 338 items; the certificate
   subtree owns 105 entries, and the proof subtree grows to 115 after accepting
   the two finite-quantifier Alethe emitters. Minimal `qfbv` remains 26 items and
   does not compile the full-only catalog. The compatibility tests now cover
   both catalogs; all 891 library tests, clippy, and both strict rustdoc profiles
   pass. ADR-0306 owns this boundary. Next, perform the separate theory API
   census rather than grouping APIs by source-file accident. R4c then groups 63
   direct theory contracts and procedures under seven full-only semantic
   submodules: arrays, arithmetic, datatypes, quantifiers, strings,
   uninterpreted functions, and combination. It leaves general model replay,
   auto-dispatch, SMT-LIB, optimization, interpolation, symbolic execution,
   verification, proofs, and certificates outside the facade. The all-feature
   root falls from 338 to 276 items; the `theories` subtree contains 70 entries
   including its seven grouping modules, while minimal `qfbv` remains 26 and
   has no `theories` module. Historical paths remain callable and type-identical.
   Dedicated compatibility tests, all 891 library tests, strict all-target
   clippy, and both warning-denied rustdoc profiles pass. ADR-0307 owns this
   boundary. Next, census the remaining cross-cutting root domains independently
   before deciding whether R4 needs another facade; do not use `theories` as a
   catch-all. R4d selects the first such domain from a measured census: 66
   transition-system verification, Horn, IMC, PDR, symbolic-execution, and
   tiny-BV reference-VM entries now live under six full-only `verification`
   submodules. The all-feature root falls from 276 to 211 items and the new
   subtree contains 72 entries including the six grouping modules. Minimal
   `qfbv` remains 26 and has no `verification` module. Historical paths stay
   callable and type-identical; all 891 library tests, strict all-target clippy,
   compatibility gates, and both warning-denied rustdoc profiles pass. ADR-0308
   owns the boundary. Continue with independently measured optimization,
   SMT-LIB, interpolation, and general-refutation domains; do not sweep every
   remaining item into one miscellaneous namespace. R4e then groups 40 existing
   model-minimization, MaxSAT, and scalar/multi-objective contracts under three
   full-only `optimization` submodules. The all-feature root falls from 211 to
   172 items and the new subtree contains 43 entries including the three
   grouping modules. Minimal `qfbv` remains 26 and has no `optimization` module.
   Pbls remains a SAT backend; textual optimization commands remain with
   SMT-LIB; and `Solver` remains a compact consumer facade. Historical paths
   stay callable and type-identical. All 891 library tests, strict all-target
   clippy, compatibility gates, and both warning-denied rustdoc profiles pass.
   ADR-0309 owns the boundary. Next, census the SMT-LIB textual front door
   independently, followed by interpolation and general-refutation utilities.
   R4f confirms that the existing `smtlib.rs` boundary already contains exactly
   the 25 root-exported public contracts and no additional public helpers. The
   module is now public directly; duplicate root aliases remain callable and
   type-identical but are hidden from rustdoc. The all-feature root falls from
   172 to 148 items, the `smtlib` module contains 25, and minimal `qfbv` remains
   26 with no SMT-LIB surface. All 891 library tests, strict all-target clippy,
   compatibility gates, and both warning-denied rustdoc profiles pass. ADR-0310
   owns the boundary. Next, census interpolation independently, followed by the
   remaining general-refutation utilities.

Do not combine R1--R4 with solver behavior or proof-rule additions. R4 may add
measured canonical facades only while preserving historical source paths; any
removal or breaking rename requires its own decision. Small reviewable commits
are the artifact-readiness objective.
