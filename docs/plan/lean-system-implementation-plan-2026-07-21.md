# Lean 4.30 system implementation plan

Status: active execution plan

Date: 2026-07-21

Last updated: 2026-07-22

Pinned compatibility target: Lean `v4.30.0`
(`d024af099ca4bf2c86f649261ebf59565dc8c622`) and `lean4export` format
`3.1.0` (`a3e35a584f59b390667db7269cd37fca8575e4bf`)

Parent design:
[`lean-system-compatibility-roadmap-2026-07-21.md`](lean-system-compatibility-roadmap-2026-07-21.md)

Terminal parity definition:
[`lean4-complete-parity-contract-2026-07-22.md`](lean4-complete-parity-contract-2026-07-22.md)

Current evidence:
[`lean-system-roadmap-completion-audit-2026-07-21.md`](lean-system-roadmap-completion-audit-2026-07-21.md),
[`lean4export-rust-import-prototype-2026-07-21.md`](lean4export-rust-import-prototype-2026-07-21.md),
and
[`lean4export-official-blocker-census-2026-07-21.md`](lean4export-official-blocker-census-2026-07-21.md)

Accepted decisions:
[ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md)
and [ADR-0167](../research/09-decisions/adr-0167-prover-track-entry.md)

## 1. Outcome

Implement a versioned Lean-compatible system around Axeyum's independent Rust
kernel. The completed program must support all of the following as separately
measured capabilities:

1. import official Lean declarations and check them independently;
2. accept Lean source through a native parser, macro expander, and elaborator;
3. represent goals, holes, constraints, and proof states;
4. execute certificate-producing tactics and kernel-check their results;
5. load modules, caches, packages, and Lake projects reproducibly;
6. provide incremental editor and language-server services;
7. evaluate and compile Lean definitions and metaprograms;
8. load, build, and check pinned mathlib releases;
9. preserve the pure-Rust checker profile, deterministic behavior, explicit
   resource limits, and a countable axiom/trust boundary throughout.
10. publish a complete content-identified official population and paired
    A0-A11/U0-U9 outcome matrix before using the unqualified phrase “complete
    Lean 4.30 parity.”

The implementation is staged, but no named subsystem is left without an owner,
task sequence, artifact, and exit condition.

## 2. Task and status conventions

- Lean-system phases are `L0` through `L10`.
- Tasks owned by this plan are `TL<phase>.<task>`; for example `TL2.3`.
- Existing Track 6 tasks retain their `T6.*` IDs and are referenced rather than
  duplicated.
- Status is one of `DONE`, `PARTIAL`, `TODO`, or `BLOCKED`.
- Size follows repository convention: `S` up to two days, `M` about one week,
  `L` two to four weeks, `XL` multi-month.
- A task is not `DONE` because code exists. Its stated positive, negative,
  provenance, determinism, resource, and documentation gates must all pass.

## 3. Capability profiles

Every artifact reports one of these profiles. Passing a lower profile never
silently grants a higher one.

| Profile | Required behavior |
|---|---|
| `K0 checker` | Pure-Rust kernel checks native terms; no source or official Lean required. |
| `K1 import` | Pinned `lean4export` records parse, translate, and independently admit or decline with a stable reason. |
| `K2 source` | Native source parsing, macros, and elaboration produce independently admitted core declarations. |
| `K3 proof` | Goals, holes, unification, and tactics produce independently checked proof terms and replayed counterexamples. |
| `K4 workflow` | Modules, caches, packages, Lake projects, and editor requests reproduce under fixed identities. |
| `K5 runtime` | Definitions and metaprograms evaluate or compile with differential execution evidence. |
| `K6 ecosystem` | A pinned mathlib release builds, imports, checks, and runs the declared tactic/test profile. |

The machine-readable capability row must separately record `parsed`,
`translated`, `admitted`, `official_admitted`, `source_elaborated`,
`proof_checked`, `workflow_reproduced`, and `runtime_reproduced`.

K0-K6 are independently useful release profiles. The terminal full-system
claim is stronger than their union as currently sampled: it additionally
requires complete upstream population authority, exact paired outcomes,
toolchain/bootstrap and supported-platform evidence, and zero unexplained or
unexecuted cells under the
[complete-parity contract](lean4-complete-parity-contract-2026-07-22.md).

## 4. Non-negotiable definition of done

The following gate applies to every task unless its row explicitly strengthens
it:

1. **Semantics:** the supported fragment and version are written down.
2. **Positive control:** at least one pinned official input succeeds.
3. **Negative control:** malformed or semantically invalid mutations reject.
4. **Independent admission:** parsing or official acceptance never sets
   `admitted=true`; only the Rust kernel can do that.
5. **Axiom accounting:** every admitted axiom has a stable name and type digest;
   additions fail closed.
6. **Determinism:** two identical runs produce byte-identical canonical output.
7. **Resources:** time, memory, depth, count, and recursion limits are explicit;
   exhaustion is a typed result.
8. **No panic boundary:** untrusted source, export, project, cache, and protocol
   inputs cannot panic the process.
9. **Differential evidence:** supported behavior is compared with pinned
   official Lean; disagreement is retained and triaged rather than normalized.
10. **Documentation:** capability matrices, decline codes, commands, and the
    next residual blocker update in the same commit.
11. **Population identity:** source/test/project/request/runtime selections are
    complete for the claimed profile, content-addressed, dependency-bound, and
    generated from the pinned upstream authority.
12. **Paired outcomes:** official and Axeyum runs use the same registered input
    and retain `agree-success`, `agree-reject`, one-sided, mismatch,
    unadjudicated, not-run, and invalid-run denominators rather than only totals.
13. **Completion evidence:** attempts, raw artifacts, resource termination,
    and final completion are retained; an interrupted or preflight-invalid run
    earns zero parity credit.

Standard local work runs under 4 GiB. The official Lean exporter may use the
measured 8 GiB lane. Large jobs checkpoint progress and never retain only an
end-of-run result.

## 5. Ownership and crate boundaries

| Boundary | Owner | Rule |
|---|---|---|
| Core terms, environments, reduction, admission | `axeyum-lean-kernel` | Zero dependencies; no JSON, source parser, solver, tactic, package, or LSP dependency. |
| Official wire format | `axeyum-lean-import` | Depends on the kernel; malformed-input and version logic stays outside the kernel. |
| CIC/IR translation | Track 6 `axeyum-bridge` boundary | Translator is untrusted; kernel checks UNSAT proofs and model replay checks SAT. |
| Goals, holes, constraints, tactics | Track 6 `axeyum-goal` boundary | One goal engine; this plan does not create another. Checkers may depend on the kernel, never on tactic search. |
| Native syntax and elaboration | staged Lean frontend boundary | Syntax objects do not enter the kernel; crate split requires an exercised prototype and ADR-0001 review. |
| Modules, packages, server, compiler | workflow/runtime boundaries | No dependency back-edge into the kernel. Cache and compiler outputs receive no proof credit without admission/replay. |

ADR-0167 owns the native goal/tactic layer. ADR-0345 and this plan own Lean
source, declaration/library import, project/editor/compiler compatibility, and
mathlib. Selected imported mathlib declarations may feed Track 6 tactics; Track
6 does not maintain a competing native theorem library.

## 6. Dependency graph and parallel lanes

```text
                              +-> TL6.1-TL6.6 syntax substrate --------+
                              |                                        v
TL0 contracts -> TL1 importer +-> TL2 kernel breadth -> TL3 libraries -> TL4B elaborator
       |                      |             |                |               |
       |                      |             |                +-> TL5 tactics <-+
       |                      |             |
       +-> T6.0 hardening ----+             +-> P6.1 bridge -> P6.2 goals -> P6.3 base tactics
                                                                      |
TL1 + TL6 source adapter -> TL7 modules/packages ----------------------+-> TL8 LSP
TL4B elaborator + TL7 modules -> TL9 compiler/runtime ---------------------> TL7 Lake DSL
TL3 + TL5 + TL6 + TL7 + TL9 ----------------------------------------------> TL10 mathlib
```

Safe parallel lanes after `TL0`:

- **Lane A — checker/import:** TL1, TL2, T6.0.
- **Lane B — proof construction:** P6.1, P6.2, base P6.3 tactics.
- **Lane C — library/axioms:** TL3 after each required TL2 slice.
- **Lane D — source/workflow:** TL6 syntax substrate, then TL4B/TL7/TL8.
- **Lane E — runtime/ecosystem:** TL9, then the full TL10 gate.

Shared hotspots requiring single-owner coordination are
`axeyum-lean-kernel/src/expr.rs`, `tc.rs`, `inductive.rs`, `lean_pp.rs`,
`axeyum-lean-import/src/lib.rs`, reconstruction modules in `axeyum-solver`, and
the future goal/metavariable state.

## 7. Phase L0 — contracts, ledgers, and executable status

Goal: make all later claims machine-checkable and remove contradictions between
the interoperability and Track 6 plans.

| ID | Status | Task | Depends | Size | Exit artifact/gate |
|---|---|---|---|---|---|
| TL0.1 | DONE | Accept or revise ADR-0345 and ADR-0167 together; record ownership of imports, mathlib, source, goals, and tactics. | — | S | Both ADRs use the ownership table in this plan; research question is closed. |
| TL0.2 | DONE | Add `lean-compatibility-v1.json` schema with the eight assurance states and stable decline codes. | TL0.1 | M | Six mutation/contract tests reject illegal credit; the 12-row [generated matrix](generated/lean-compatibility.md) is byte-stable. |
| TL0.3 | PARTIAL | Pin Lean, exporter, source hashes, fixture hashes, commands, limits, host-independent options, and the executable path used from every test working directory. The first corrected remote job failed before its representative sweep because `AXEYUM_LEAN_BIN` resolved to an unconfigured elan shim outside the repository directory. | — | S | One manifest drives exporter, importer, and official-check tests; a retained remote run reaches the exact 71/71 attestation. |
| TL0.4 | DONE | Add a machine-checked axiom ledger: name, type digest, source, owner, classification, discharge status. | TL0.2 | M | The [65-row manifest](lean-axiom-ledger-v1.json), generated [ledger](generated/lean-axiom-ledger.md), runtime inventory, and seven mutation/contract tests make added, removed, renamed, or type-mutated assumptions fail the normal gate. All rows remain explicitly `unclassified`/`unreviewed` for TL3.2. |
| TL0.5 | TODO | Add `just lean-kernel`, `lean-import`, `lean-source`, `lean-workflow`, and `lean-system` tiers. | TL0.2 | M | Small per-commit, nightly corpus, and release-full gates are distinct. |
| TL0.6 | TODO | Add generated A0-A11 construct, declaration-root, source, tactic, project, editor, runtime, ecosystem, and platform scoreboards over content-identified U0-U9 populations. | TL0.2 | M | Every profile has exact raw/normalized denominators, paired overlap, blocker categories, assurance, attempts, resources, and completion. |
| TL0.7 | TODO | Freeze resource envelopes and checkpoint policy, including 4 GiB default and 8 GiB official-export lanes. | TL0.3 | S | OOM/signal/timeout/limit outcomes are typed and retained. |
| TL0.8 | TODO | Correct or archive older conflicting scope prose and wire link checks to this plan. | TL0.1 | S | No live document says both “import nothing” and “import mathlib.” |

L0 exits when status is generated from evidence rather than hand-copied prose.

## 8. Phase L1 — production `lean4export` reader

Goal: complete deterministic, streaming, fail-closed format-3.1 ingestion before
broadening kernel semantics.

| ID | Status | Task | Depends | Size | Exit artifact/gate |
|---|---|---|---|---|---|
| TL1.1 | DONE | Parse metadata, names, levels, expressions, declarations, and group records into a separate Rust wire layer. | — | M | Flat and direct-recursive official fixtures inventory exactly. |
| TL1.2 | DONE | Enforce dense IDs, backward references, exact fields/version, integer bounds, safety flags, and line/record limits. | — | M | Fourteen Rust tests retain stable first errors and projection wire mutations. |
| TL1.3 | DONE | Make whole-environment publication transactional rather than only declaration-transactional. | TL1.1 | M | [Owned completed publication](lean-import-transactional-publication-tl1.3-2026-07-22.md) stages in a private kernel and returns a field-private `CompletedImport` only after full success; late JSON, kernel, unsupported, record-limit, and I/O failures expose no environment. |
| TL1.4 | DONE | Generate truncation-at-every-record, duplicate-ID, forward-reference, unknown-field, deep-JSON, Unicode, integer, cycle, and version mutations. | TL0.2 | L | The [226-case deterministic corpus](lean-import-mutation-corpus-tl1.4-2026-07-22.md) runs twice byte-identically without panic and freezes exact JSON/malformed/kernel/unsupported/published/unsealed classes; all 65 record bodies reject truncation while 64 complete-record prefixes are explicitly unsealed under the upstream no-footer contract. |
| TL1.5 | TODO | Add property fuzzing for wire topology and semantic erasure of metadata. | TL1.4 | M | Fuzzer covers every record discriminant and metadata path. |
| TL1.6 | TODO | Add streaming large-input checkpoints, aggregate byte/depth limits, and completion-last publication. | TL0.7 | M | Forced termination resumes without duplicate admission or lost provenance. |
| TL1.7 | DONE | Record axiom name/type digests and declaration content/dependency digests during import. | TL0.4 | M | [Canonical v1 identities](lean-declaration-identity-tl1.7-2026-07-22.md) retain TL0.4-compatible axiom type hashes and structurally bind all declaration variants plus sorted direct dependencies; repeated/reordered imports agree, while valid type/body/binder mutations change exactly their intended content/dependency cone. |
| TL1.8 | PARTIAL | Differentially inventory every supported/declined construct with an independent Python reader. The [official construct-matrix plan](lean-official-construct-matrix-plan-2026-07-22.md) freezes source cases, then official wire observations, before current-product measurement. [M0/Stage A](lean-official-construct-matrix-stage-a-2026-07-22.md) freezes seven ordered cases and exact sources; [Stage B](lean-official-construct-matrix-stage-b-2026-07-22.md) adds five byte-identical retained streams and complete independent group metadata; [M3](lean-official-construct-matrix-product-2026-07-22.md) freezes two exact typed current-product outcomes per row with ten positive controls and no publication on decline; [M4](lean-official-construct-matrix-m4-2026-07-22.md) generates the assurance-separated selected-family result; [M5](lean-official-construct-matrix-final-2026-07-22.md) closes bounded validation and handoff. The complete format/root population remains open. | TL0.6 | M | Python/Rust counts agree over the complete fixture set. |
| TL1.9 | TODO | Publish the 570,807-byte String stream and future large closures in a content-addressed artifact store. | TL1.6 | S | Source, command, exact bytes, hash, and retrieval path are durable. |
| TL1.10 | TODO | Stabilize the public reader API, error codes, fresh-kernel contract, and examples for files/stdin/streams. | TL1.3 | M | Rustdoc examples and downstream misuse tests pass. |

L1 exits when every format-3.1 construct is recognized, every unsupported
construct declines stably, and parsing cannot publish a partially checked world.

## 9. Phase L2 — kernel compatibility breadth

Goal: close core semantic gaps in measured dependency order. Each slice lands
with an official positive, invalid mutation, independent admission, and
official comparison.

| ID | Status | Task | Depends | Size | Exit artifact/gate |
|---|---|---|---|---|---|
| TL2.1 | DONE | Admit existing core expressions/declarations plus flat, parametric-recursive, and direct-recursive non-indexed inductives. | TL1.2 | L | Official fixtures admit 8 and 11 declarations; recursor mutations reject. |
| TL2.2 | DONE | Add first-class `Proj` representation to interning, metadata, de Bruijn operations, substitution, level substitution, traversal, hashing, and printers. Importer translation remains deliberately fail-closed. | TL0.2, TL1.2 | L | [Four integration tests plus renderer coverage](lean-projection-representation-tl2.2-2026-07-21.md) exhaust the structural payloads/operations and rollback boundary. |
| TL2.3 | DONE | Preserve checked single-constructor parameter/index metadata and infer universe-polymorphic, indexed, and dependent projection types with Lean's Prop-elimination restriction. | TL2.2 | L | [Four integration families plus an injected-metadata mutation](lean-projection-inference-tl2.3-2026-07-21.md) reject wrong names/shapes/arity/fields and infer dependent second fields. |
| TL2.4 | DONE | Reduce projections of constructor applications, including universe-polymorphic and parameterized structures; translate validated format-3.1 projection records. | TL2.3 | M | [Native reduction tests plus the exact official projection closure](lean-projection-reduction-tl2.4-2026-07-21.md) independently admit nine declarations, compute the selected field, and reject name/index mutations. |
| TL2.5 | DONE | Add structure eta as a separate definitional-equality slice, restricted to exactly saturated constructors of checked one-constructor, zero-index, non-recursive inductives. | TL2.4 | M | [Seven native families plus the required pinned-Lean positive/rejecting differential](lean-structure-eta-tl2.5-2026-07-21.md) cover symmetry, zero-field and multi-constructor boundaries, wrong fields/types, parameters, universes, dependencies, and indexed/recursive exclusions. |
| TL2.6 | DONE | Replace `Lit::Nat(u128)` with arbitrary-precision storage before enabling literal typing. | TL1.2 | M | [Canonical `NatLit(BigUint)` storage](lean-nat-literal-storage-tl2.6-2026-07-22.md) round-trips below/at/above `2^128`; importer mutations prove the decimal wire path does not narrow while inference remains fail-closed. The former TL1.7 dependency was removed because declaration digests do not govern expression payload representation. |
| TL2.7 | DONE | Type Nat literals and implement constructor/literal conversion. | TL2.6, TL2.4 | M | [Checked literal semantics](lean-nat-literal-semantics-tl2.7-2026-07-22.md) admit the exact official Nat closure as ten declarations with zero axioms; canonical-bootstrap mutations reject, arbitrary-precision unary/literal forms are definitionally equal, and a required pinned-Lean differential passes. |
| TL2.8 | TODO | Implement accelerated Nat operations behind independently checked reductions or guarded trusted primitives. | TL2.7, TL0.4 | L | Per-operation mutation tests and large-value differential corpus pass. |
| TL2.9 | TODO | Type and reduce String literals through `String.mk`/character/list constructors. | TL2.7 | L | String root advances past literals with exact next blocker reported. |
| TL2.10 | TODO | Add the fixed quotient package and `Quot.lift`/`Quot.ind` reductions. | TL1.7 | M | Official quotient closure admits; relation/proof mutations reject. |
| TL2.11 | DONE | Implement and fuzz strict positivity before widening recursive admission. [Accepted ADR-0352](../research/09-decisions/adr-0352-preregister-lean-strict-positivity.md) and the [final result](lean-strict-positivity-final-2026-07-22.md) close the pre-insertion Lean 4.30 rule, exact typed failures, twelve-row public matrix, repeated 840-case grammar, eight pinned-Lean observations, mandatory CI, synthetic importer propagation, unchanged construct matrix, and all bounded gates without widening admission. | T6.0.3 | L | **Met:** known non-positive and invalid families reject transactionally before environment mutation. |
| TL2.12 | DONE | Generalize direct, recursive-indexed, and reflexive/higher-order fields through [accepted ADR-0353](../research/09-decisions/adr-0353-preregister-lean-recursive-induction-hypotheses.md)'s one telescope-based IH/rule construction. [M0-M3](lean-recursive-induction-hypotheses-m3-2026-07-22.md) freeze the targets, close fourteen native rows/twelve mutation classes/768 recursive profiles, and complete both construct targets with exact recursor comparison. [M4](lean-recursive-induction-hypotheses-m4-2026-07-22.md) confirms pinned Lean and Axeyum computations twice at the exact registered normal forms. The [M5 result](lean-recursive-induction-hypotheses-final-2026-07-22.md) closes all bounded gates and hands off to TL2.13. | TL2.11 | L | **Met:** `Vector`- and `Acc`-shaped official streams complete twice, exact generated recursors compare, selected recursor applications compute, direct recursion/840-case positivity remain controlled, and all rollback/resource gates pass. |
| TL2.13 | DONE | Admit mutual inductive groups through [accepted ADR-0354](../research/09-decisions/adr-0354-preregister-lean-mutual-inductive-groups.md)'s one atomic ordered group gate. [M0-M4](lean-mutual-inductive-groups-m4-2026-07-22.md) freeze the sources/wire order, preserve singleton behavior, land complete-group semantics, repeat 720 unique cases, import all three official streams twice, confirm both computations, and close 22 rejecting importer/publication mutation classes while retaining the 768/840 controls. The [M5 result](lean-mutual-inductive-groups-final-2026-07-22.md) adds the history-preserving assurance overlay, removes the obsolete live decline, and closes every bounded gate. | TL2.12 | L | **Met:** the frozen two-family official fixture and separate non-indexed/indexed computation streams agree with independently generated recursors; 720 group cases repeat byte-identically; 768 recursive/840 positivity controls and all rollback/resource gates pass. |
| TL2.14 | DONE | Implement pinned Lean 4.30 nested-inductive elimination inside atomic kernel admission under [accepted ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md): derive specialized auxiliary container families, check the expanded mutual group, restore surface declarations/rules, and publish exact `.rec_N` auxiliary recursors. The [dependency audit](lean-post-tl2.13-dependency-audit-2026-07-22.md) separates this kernel task from TL4.10 source recursion; the [P0-M6 plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md) binds the boundary. M0 freezes three explicit computations, one exact negative diagnostic, and 114,596 bytes of twice-identical wire evidence without Axeyum observation. M1 establishes typed non-admission. M2 lands rollback-aware native expansion/restoration. M3 repeats the exact 640-case grammar twice and closes 16 transactional restoration mutations. M4 imports the construct and all three streams twice with exact comparison and closes 20 wire/publication classes. M5 checks the registered 3/3/5-successor normal forms twice, appends the history-preserving 7/6/4/0 assurance overlay, and removes only the obsolete live nested decline. The [M6 result](lean-nested-inductive-elimination-final-2026-07-22.md) closes exits 1--11 and all non-publication final gates; containing-commit push/ref equality completes exit 12. | TL2.13 | XL | **Met:** frozen construct and explicit nested-computation streams agree with independently derived declarations and exact normal forms; 640 nested plus retained 720/768/840 and well-founded controls pass; private auxiliaries never leak; all failures remain transactional. |
| TL2.15 | PARTIAL | Run seam-first kernel fuzzing across Prop/elimination, universes/inductives, proof irrelevance/iota, literals/reduction, projections/eta, and quotients. The [T6.0.3 seed](lean-kernel-seam-fuzz-seed-2026-07-21.md) covers four semantic seams with 768 unique generated cases and deterministic summary replay. TL2.3-TL2.5 add direct semantic projection-inference/reduction/eta positives and mutations, but not the generated projection/reduction/eta family. | TL2.2-TL2.13 as applicable | L | Current four-seam `kernel accepts False` class is live; generated projection/reduction/eta and quotient semantic cases remain mandatory as those constructs land. |
| TL2.16 | PARTIAL | Generate the parsed/translated/admitted/dual-admitted construct and root matrix. The [selected-family seed](generated/lean-official-construct-matrix.md) is generated from exact source, wire, and product freezes with implication tests; its [completed milestone handoff](lean-official-construct-matrix-final-2026-07-22.md) preserves the broader population as open. | TL0.6 | M | Matrix is generated from tests and exact fixtures, never hand-maintained. |

L2 exits when the pinned construct matrix has no accidental parser-to-checker
credit, every unsupported kernel construct has a stable decline, and the
selected core corpus agrees with official Lean on admission and computation.

## 10. Phase L3 — Prelude, `Init`, `Std`, and mathlib theorem bases

Goal: replace Axeyum-created assumptions with checked theorems and establish
dependency-closed library compatibility.

| ID | Status | Task | Depends | Size | Exit artifact/gate |
|---|---|---|---|---|---|
| TL3.1 | TODO | Export and content-digest the exact logic, real, integer, and string reconstruction preludes. | TL1.7 | M | Complete dependency and axiom inventory is reproducible. |
| TL3.2 | TODO | Classify all 65 ledgered assumptions (real 30, integer 34, string 1) as primitive interface, external assumption, derivable theorem, or defect. | TL0.4, TL3.1 | M | Every row has an accepted semantic class and concrete discharge target or retained-boundary rationale. |
| TL3.3 | TODO | Namespace and make all preludes fallible/idempotent so logic/Real/Int/String coexist in one kernel; this fulfills T6.0.8 rather than duplicating it. | TL3.1 | M | Combined build has no collision or panic. |
| TL3.4 | TODO | Discharge the first five derivable axioms using imported theorem dependencies or explicit kernel terms. | TL3.2 | M | Axiom count falls and official/Axeyum checks agree. |
| TL3.5 | TODO | Discharge every derivable prelude axiom; retain irreducible assumptions only as explicit profile inputs. | TL3.4 | XL | Ledger has zero unclassified rows and no hidden additions. |
| TL3.6 | TODO | Export minimal `Init` roots selected to maximize construct coverage; record complete dependency closures. | TL2.4, TL2.7, TL2.10 | L | Exact admitted/declined root matrix and next blocker ranking. |
| TL3.7 | TODO | Expand through `Init.Prelude`, core datatypes, equality, arithmetic, strings, arrays, and metaprogramming foundations. | TL3.6, TL2.12 | XL | Declared `Init` profile independently checks with zero unexpected axioms. |
| TL3.8 | TODO | Import selected `Std` roots required by parser, elaborator, compiler, server, and package implementations. | TL3.7 | XL | Dependency-closed `Std` profile checks and is versioned. |
| TL3.9 | TODO | Select and import the smallest mathlib theorem bases for `norm_num`, `ring`, `linarith`, and current axiom discharge. | TL3.5-TL3.8 | L | Selection manifest binds every theorem and transitive dependency. |
| TL3.10 | TODO | Translate one CAS certificate family into proof terms using the imported generic algebraic theorem basis. | TL3.9, T6.1a | L | One end-to-end theorem checks in Axeyum and official Lean without new axioms. |
| TL3.11 | TODO | Give all 56 canonical rewrite rules theorem provenance, orientation, side conditions, and checked explanation conversion. | TL3.9 | XL | Every enabled theorem-backed rule can emit a kernel-checked equality proof; T6.3.3 consumes this result. |
| TL3.12 | TODO | Generate declaration-root coverage by dependency closure, not file or leaf-declaration counts. | TL0.6 | M | Dashboard reports exact roots, records, axioms, blockers, and resources. |

L3 exits when a selected `Init`/`Std`/mathlib profile independently checks,
the axiom ledger is classified and shrinking, and at least one generic CAS
certificate becomes a theorem through imported foundations.

## 11. Phase L4 — bridge, goals, unification, and elaboration

L4A reuses the existing Track 6 goal plan over API-built core terms. L4B adds
native source elaboration after the syntax substrate exists.

### L4A — one bridge and one goal engine

| Existing ID | Status | Task | Depends | Size | Exit artifact/gate |
|---|---|---|---|---|---|
| T6.1a | TODO | Extract IR-to-CIC reconstruction into a reusable bridge. | T6.0 | M | Existing reconstruction output is byte/behavior stable through the bridge. |
| T6.1b | TODO | Translate a published CIC-to-IR Bool/BV/Nat/Int starter fragment and decline the rest. | T6.1a | L | Golden capability row and differential corpus pass. |
| T6.1c | TODO | Replay lifted SAT models against the original CIC goal. | T6.1b | L | Deliberate mistranslation cannot produce a trusted counterexample. |
| T6.1d | TODO | Reconcile every divergent SMT/Lean totality convention. | T6.1b | M | Degenerate-argument fuzz class per operator. |
| T6.2.1-T6.2.3 | TODO | Add external obligation objects, canonical `Goal` data, and forkable/resumable proof states. | T6.1a | L | Identical goals serialize identically; branches do not alias. |
| T6.2.4-T6.2.5 | TODO | Implement delayed assignment, depth invariants, metavariable kinds, and explicit coupling. | T6.2.1 | L | Nested `intro` cannot assign sibling or opaque holes. |
| T6.2.6 | TODO | Implement higher-order pattern unification and explicit decline beyond the fragment. | T6.2.4 | L | Miller-pattern corpus passes; flex-flex/non-pattern cases remain typed constraints or declines. |
| T6.2.7 | TODO | Make holes legal, visible, serializable states that cannot close without evidence. | T6.2.1 | S | No open-hole state can publish a theorem. |

### L4B — native elaborator

| ID | Status | Task | Depends | Size | Exit artifact/gate |
|---|---|---|---|---|---|
| TL4.1 | TODO | Build an elaboration context with environment, local context, options, source maps, messages, metavariable state, and cancellation. | TL6.5, T6.2.1-T6.2.7 | L | Context snapshots are deterministic and rollback-clean. |
| TL4.2 | TODO | Add typed constraint queues, postponed constraints, synthetic opaque goals, wake-up dependencies, and occurs/scope checks. | TL4.1 | L | Constraint mutations cannot escape scope or solve opaque goals. |
| TL4.3 | TODO | Extend unification with universe constraints, reducibility modes, coercion/typeclass postponement, and bounded flex-rigid search. | TL4.2 | XL | Published fragment matches official normalized core; budget exhaustion declines. |
| TL4.4 | TODO | Elaborate identifiers, universes, literals, applications, named/positional arguments, lambdas, foralls, lets, annotations, and holes. | TL4.3, TL6.5 | XL | Term differential corpus produces definitionally equal core expressions. |
| TL4.5 | TODO | Implement implicit/instance argument insertion and expected-type propagation. | TL4.4 | L | Omitted argument corpus agrees with official Lean. |
| TL4.6 | TODO | Implement coercion discovery/insertion with loop and ambiguity controls. | TL4.5, TL3.8 | L | Coercion chains agree or decline deterministically. |
| TL4.7 | TODO | Implement typeclass synthesis, instance priorities/scopes, caching, out-parameters, and recursion/resource bounds. | TL4.5, TL3.8 | XL | Selected `Init`/`Std` instance corpus agrees with traceable search. |
| TL4.8 | TODO | Elaborate declarations, namespaces, sections, variables, attributes, modifiers, open/scoped commands, and options. | TL4.4, TL6.10 | XL | Source modules elaborate to independently admitted environments. |
| TL4.9 | TODO | Elaborate structures, inductives, constructors, projections, patterns, matches, and equations. | TL2.13, TL4.8 | XL | Official/source/exported core declarations are definitionally equivalent. |
| TL4.10 | TODO | Elaborate structural, mutual, nested, well-founded, and partial recursive source definitions with termination evidence. This owns `termination_by`/`decreasing_by`, `WellFounded.fix` construction, pattern/equation compilation, and source metadata; TL2.14 kernel admission does not satisfy it. | TL4.9 | XL | Positive/negative source and termination corpus elaborates to definitionally equal checked core and agrees with official Lean. |
| TL4.11 | TODO | Produce information trees, tactic states, goal/source ranges, hover data, and declaration ranges during elaboration. | TL4.1, TL8.1 | L | Every diagnostic and goal maps to stable syntax/core IDs. |
| TL4.12 | TODO | Differentially test parser+macro+elaboration against pinned official Lean using normalized export digests. | TL4.4-TL4.11 | XL | Supported corpus has zero unexplained core-term differences. |

L4 exits when both API-built and native-source goals can elaborate, fork,
unify, decline, and close without capture, hidden assignment, or open holes.

## 12. Phase L5 — tactics and proof construction

Goal: implement the tactic runtime and turn Axeyum's solver, CAS, rewriting,
e-graph, and induction assets into checked proof steps.

| ID | Status | Task | Depends | Size | Exit artifact/gate |
|---|---|---|---|---|---|
| TL5.1 | TODO | Define tactic state, step/certificate envelopes, focus/combinator semantics, tracing, cancellation, and rollback. | T6.2.1-T6.2.7 | L | Failed tactics leave state unchanged; traces are deterministic. |
| TL5.2 | TODO | Implement `exact`, `assumption`, `rfl`, `intro`, `apply`, `refine`, `have`, `show`, `revert`, `clear`, and `rename`. | TL5.1 | L | Each tactic has positive, negative, open-hole, and tamper tests. |
| T6.3.1 | TODO | Implement `decide` through CIC-to-IR translation, solver evidence, reconstruction, and kernel admission. | T6.1b, TL5.1 | M | Supported goal closes end-to-end without `sorry`. |
| T6.3.2 | TODO | Implement checked counterexamples/refutation only after the SAT replay gate. | T6.1c | M | Model falsifies the untouched source goal and maps to source variables. |
| T6.3.3 | TODO | Implement theorem-backed `simp` from e-graph explanations and imported rewrite theorems. | TL3.11, TL5.1 | L | Every equality/congruence/transitivity step checks independently. |
| TL5.3 | TODO | Implement `rw`, `change`, `unfold`, `delta`, `subst`, `congr`, and conversion-mode tactics. | TL3.9, TL5.1 | L | Tactic-term and direct-term paths are definitionally equal. |
| TL5.4 | TODO | Implement `norm_num` from exact arithmetic/CAS certificates. | TL3.10 | L | Closed numerical corpus checks with no new axioms. |
| TL5.5 | TODO | Implement `ring`/polynomial normalization and factor/Groebner side-condition proofs. | TL3.9 | XL | Generic semiring/ring corpus checks in both kernels. |
| TL5.6 | TODO | Implement selected `linarith`, `nlinarith`, `omega`, BV, array, UF, and string tactics from existing evidence routes. | T6.3.1, TL3.9 | XL | Each tactic publishes exact fragment, evidence route, and decline matrix. |
| T6.3.4 | TODO | Implement structural `cases` and `induction` over admitted recursors. | TL2.13, TL5.2 | L | Motives/minors/IHs check for indexed and recursive families. |
| TL5.7 | TODO | Implement tactic combinators: sequence, alternatives, repeat, first, all-goals, focus, try, solve, and bounded search. | TL5.1 | L | Depth invariant and branch rollback hold under nesting. |
| TL5.8 | TODO | Add source tactic parsing/elaboration and term-mode/tactic-mode transitions. | TL6.5, TL4.11 | L | Tactic scripts produce the same checked step stream as API calls. |
| TL5.9 | TODO | Execute user tactic macros and metaprograms in the bounded runtime. | TL6.8, TL9.12 | XL | Selected official tactic extensions run reproducibly. |
| T6.3.6 | TODO | Add symbol-renaming/assertion-order/resource instability ratchets. | T6.3.1 | M | Resource-count CV is measured and gated. |
| TL5.10 | TODO | Differentially run a pinned tactic corpus against official Lean and compare final theorem/core digests, goals, axioms, and diagnostics. | TL5.2-TL5.9 | XL | Zero unexplained theorem or open-goal differences in profile. |

L5 exits when the declared tactic profile closes the same goals with the same
axiom boundary under Axeyum and official Lean, while tactic search remains
outside the TCB.

## 13. Phase L6 — native parser, syntax extensions, and macros

Goal: parse the pinned Lean source language, including extensible syntax and
hygienic macro expansion, into source-mapped syntax trees.

Primary references are Lean 4.30's `Lean/Parser`, `Lean/Parser.lean`,
`Lean/Syntax.lean`, `Lean/Hygiene.lean`, `Lean/Elab/Macro*.lean`, and
`Lean/Elab/Quotation` modules.

| ID | Status | Task | Depends | Size | Exit artifact/gate |
|---|---|---|---|---|---|
| TL6.1 | TODO | Implement source files, UTF-8 positions, spans, substrings, line maps, and deterministic file/module identities. | TL0.3 | M | Unicode and newline mutation corpus preserves official ranges. |
| TL6.2 | TODO | Implement lexer primitives: whitespace/comments, identifiers, escaped identifiers, numerals, strings/chars, tokens, antiquotations, and recovery tokens. | TL6.1 | L | Token corpus agrees with official categories and spans. |
| TL6.3 | TODO | Implement Lean-compatible syntax objects, atoms, identifiers, nodes, missing nodes, source info, hygiene scopes, and canonical serialization. | TL6.2 | L | Syntax round-trip and scope identity golden tests pass. |
| TL6.4 | TODO | Implement parser categories, precedence, leading/trailing parsers, Pratt composition, parser tables, and deterministic extension registration. | TL6.3 | XL | Ambiguity/precedence differential corpus agrees. |
| TL6.5 | TODO | Implement builtin module/import, command, term, tactic, pattern, level, attribute, and do-syntax parsers. | TL6.4 | XL | Selected `Init` source parses with zero unclassified failures. |
| TL6.6 | TODO | Implement `syntax`, `macro`, `macro_rules`, parser aliases, notation, scoped syntax, priorities, and category extension compilation. | TL6.4 | XL | User-defined syntax changes subsequent parsing like official Lean. |
| TL6.7 | TODO | Implement quotations, antiquotations, syntax quotations, and prechecks. | TL6.3, TL6.6 | L | Nested quotation/hygiene differential tests pass. |
| TL6.8 | TODO | Implement hygienic macro expansion, expansion stacks, recursion limits, macro scopes, and deterministic errors. | TL6.6, TL6.7 | XL | Capture-avoidance and recursive macro corpus agrees. |
| TL6.9 | TODO | Implement namespace/open/scoped notation resolution and syntax/attribute environments across modules. | TL6.6, TL7.1 | L | Module-order and scope tests agree with official Lean. |
| TL6.10 | TODO | Implement parser error recovery and partial syntax trees suitable for editor use. | TL6.5 | L | Single-edit corpus retains unaffected syntax IDs and useful diagnostics. |
| TL6.11 | TODO | Implement canonical/failsafe pretty-printing and Pollack-consistency checks. | TL6.3, T6.0.9 | L | `parse(print(core/syntax))` preserves normalized identity. |
| TL6.12 | TODO | Generate parser/macro differential fixtures from `Init`, `Std`, mathlib, and adversarial standalone sources. | TL6.5-TL6.11 | L | Coverage reports every parser and macro kind in the selected profile. |
| TL6.13 | TODO | Bootstrap parser-extension and macro modules through the native frontend. | TL6.8, TL4.8 | XL | Selected frontend modules compile using their own extension machinery. |

L6 exits when supported source parses and expands to the same normalized syntax
as official Lean, with stable errors and incremental identities.

## 14. Phase L7 — modules, caches, packages, and Lake

Goal: reproduce Lean project builds, first through the official adapter and then
through native module/package machinery.

| ID | Status | Task | Depends | Size | Exit artifact/gate |
|---|---|---|---|---|---|
| TL7.1 | TODO | Implement module names, imports, dependency DAGs, environment deltas, initialization order, and cycle detection. | TL1.7, TL6.5 | L | Multi-module source/export environments reproduce exactly. |
| TL7.2 | TODO | Define a content-addressed Axeyum environment cache with schema/version/tool/options/source/dependency identities. | TL7.1 | L | Cold/warm builds are byte-identical; stale inputs invalidate. |
| TL7.3 | TODO | Implement the pinned official Lean/Lake/exporter adapter with sandbox, resource limits, structured termination, and output hashes. | TL0.7 | M | Two projects export reproducibly and failures cannot masquerade as success. |
| TL7.4 | TODO | Ship `axeyum check-lean-project` with module/root selection, progress checkpoints, declines, and evidence manifests. | TL7.3, TL1.10 | M | CLI checks a project without manual fixture preparation. |
| TL7.5 | TODO | Parse `lean-toolchain`, `lake-manifest.json`, and declarative `lakefile.toml`; reproduce package/workspace/dependency configuration. | TL6.2 | L | TOML/manifest differential corpus agrees with Lake. |
| TL7.6 | TODO | Implement package resolution, Git/path dependencies, revisions, lockfiles, reservoirs/registries, materialization, and offline reproducibility. | TL7.5 | XL | Fresh and offline rebuilds select identical sources. |
| TL7.7 | TODO | Implement build targets, facets, traces, jobs, module artifacts, extern libraries, scripts, and topological scheduling. | TL7.1, TL7.6 | XL | Selected multi-package project build graph agrees with Lake. |
| TL7.8 | TODO | Elaborate/evaluate `lakefile.lean` configuration and Lake DSL through the native frontend/runtime. | TL4.8, TL9.12 | XL | Lean and TOML configurations produce equivalent native build graphs where intended. |
| TL7.9 | TODO | Specify and implement a version-specific `.olean` compatibility reader in the untrusted cache/adapter layer, translating into the same checked wire/environment model. | TL1.10, TL7.2 | XL | `.olean` and `lean4export` paths yield equal declaration digests; malformed cache fuzzing cannot affect the kernel directly. |
| TL7.10 | TODO | Reproduce two pinned ordinary projects and one selected mathlib project through official-adapter and native paths. | TL7.4-TL7.9 | XL | Clean/incremental/offline matrices have no stale-cache acceptance. |

L7 exits when project and package identity, dependency resolution, caches, and
build scheduling reproduce under the declared native profile.

## 15. Phase L8 — editor and language server

Goal: provide snapshot-correct incremental parsing, elaboration, goals, and
navigation through Lean-compatible LSP/RPC services.

Primary references are Lean 4.30's `Lean/Server`, `FileWorker`, `Snapshots`,
`Requests`, `Rpc`, `Completion`, `GoTo`, `References`, and cancellation tests.

| ID | Status | Task | Depends | Size | Exit artifact/gate |
|---|---|---|---|---|---|
| TL8.1 | TODO | Define LSP/RPC protocol types, server capabilities, document/version IDs, request IDs, progress, cancellation, and structured errors. | TL0.2 | L | Protocol golden transcripts and malformed-message tests pass. |
| TL8.2 | TODO | Implement immutable document snapshots, edit application, task ownership, cancellation, watchdogs, and stale-result suppression. | TL8.1 | L | Cancel/edit race corpus never publishes an old result. |
| TL8.3 | TODO | Incrementally re-lex, reparse, and reuse stable syntax outside changed ranges. | TL6.10, TL8.2 | XL | Edit corpus matches clean reparse while reusing unchanged IDs. |
| TL8.4 | TODO | Incrementally rebuild module/environment/elaboration snapshots and invalidate dependent declarations. | TL4.11, TL7.2 | XL | Incremental result equals clean elaboration and rejects stale caches. |
| TL8.5 | TODO | Publish diagnostics, goals, messages, traces, evidence IDs, counterexamples, and axiom/trust information. | TL8.4, TL5.1, TL5.8, T6.3.2 | L | Every result maps to current source and stable core/evidence IDs. |
| TL8.6 | TODO | Implement hover, definition, declaration, references, document symbols, and workspace symbols from information trees. | TL4.11, TL8.4 | L | Navigation corpus agrees with official Lean on supported source. |
| TL8.7 | TODO | Implement completion, completion resolution, signature help, import suggestions, and expected-type-aware candidates. | TL4.5-TL4.7 | XL | Ranked candidate/profile corpus has recorded parity and differences. |
| TL8.8 | TODO | Implement semantic tokens/highlighting, inlay hints, code lenses, formatting hooks, and declaration ranges. | TL8.4 | L | Token/range updates are snapshot-correct. |
| TL8.9 | TODO | Implement code actions, custom Axeyum proof RPC, widgets/interactive goals, and tactic execution requests. | TL5.8, TL8.5 | XL | Editor can fork/attempt/check a goal without parsing rendered text. |
| TL8.10 | TODO | Run official-vs-native transcript, cancellation, edit, and latency/RSS suites. | TL8.2-TL8.9 | L | Selected request matrix has zero stale results and bounded resources. |

L8 exits when a selected Lean project can be edited incrementally with correct
goals, diagnostics, navigation, completions, and proof actions.

## 16. Phase L9 — evaluator, compiler, runtime, and metaprogram execution

Goal: run Lean definitions, build scripts, tactics, and executables without an
official Lean runtime in the native profile.

Primary references are Lean 4.30's `Lean/Compiler/IR`, `Lean/Compiler/LCNF`,
`ToIR`, `ToLCNF`, pass manager, closure/RC/boxing passes, and C/LLVM emitters.

| ID | Status | Task | Depends | Size | Exit artifact/gate |
|---|---|---|---|---|---|
| TL9.1 | TODO | Freeze executable semantics, erasure boundary, supported effects, runtime values, object layout, exception behavior, and FFI boundary. | TL0.1 | L | Runtime semantics document and differential fixtures land. |
| TL9.2 | TODO | Implement a bounded interpreter for closed core definitions and metaprograms. | TL3.8, TL4.8 | XL | Selected pure `Init` functions and frontend metaprograms reproduce. |
| TL9.3 | TODO | Implement proof/type erasure, irrelevance, recursor lowering, partial/unsafe handling, and executable declaration selection. | TL9.1 | L | Erasure mutation corpus preserves observable results. |
| TL9.4 | TODO | Define checked compiler IR and LCNF-like normalized representation with deterministic names and type checker. | TL9.3 | XL | Core-to-IR translation and IR checker reject malformed programs. |
| TL9.5 | TODO | Implement lambda lifting, closure conversion, join points, fixed parameters, SCC splitting, and arity reduction. | TL9.4 | XL | Higher-order program corpus reproduces interpreter results. |
| TL9.6 | TODO | Implement monomorphization/specialization, boxing/unboxing, irrelevant-value removal, CSE, simplification, and dead-code elimination. | TL9.5 | XL | Pass-by-pass validator and mutation corpus pass. |
| TL9.7 | TODO | Implement explicit reference counting, borrow inference, reset/reuse, object allocation, and runtime primitives. | TL9.6 | XL | Lifetime/alias stress corpus is leak/UAF clean. |
| TL9.8 | TODO | Emit portable C and native/LLVM objects, reusing existing Axeyum LLVM infrastructure where compatible. | TL9.7 | XL | Compiled binaries match interpreter and official Lean outputs. |
| TL9.9 | TODO | Emit WASM with deterministic imports, memory limits, and browser/runtime harnesses. | TL9.7 | XL | Closed certified functions and selected tools run in browser. |
| TL9.10 | TODO | Implement controlled FFI, extern attributes, dynamic/static libraries, name mangling, and platform profiles. | TL9.8 | XL | ABI fixtures reproduce on supported targets; unsafe boundary is explicit. |
| TL9.11 | TODO | Execute source macros, tactic extensions, deriving handlers, `lakefile.lean`, and build scripts in a sandboxed bounded runtime. | TL9.2, TL4.8 | XL | Selected extensions and Lake DSL run reproducibly. |
| TL9.12 | TODO | Differentially execute interpreter/C/WASM/native outputs against official Lean across pure, effectful, exception, recursion, and allocation corpora. | TL9.2-TL9.11 | XL | Zero unexplained observable differences in the runtime profile. |
| TL9.13 | TODO | Bootstrap selected frontend/compiler modules through the native compiler. | TL9.11, TL7.7 | XL | Rebuilt module hashes and tests reproduce under the native toolchain. |

L9 exits when the selected language/runtime profile builds and executes without
official Lean, and every optimization is covered by interpreter/differential
validation.

## 17. Phase L10 — mathlib compatibility and release maintenance

Goal: progress from selected theorem bases to a complete pinned mathlib build
and maintain versioned Lean/mathlib compatibility.

| ID | Status | Task | Depends | Size | Exit artifact/gate |
|---|---|---|---|---|---|
| TL10.1 | DONE | Pin mathlib v4.30.0 tree identity and exact 8,606-file inventory. | — | S | Commit and directory counts reproduced from Git tree. |
| TL10.2 | TODO | Generate file/module/declaration/dependency/construct/tactic/axiom/resource inventories for the full tagged tree. | TL7.3, TL1.6 | XL | Every root has complete provenance and a first blocker. |
| TL10.3 | TODO | Prioritize blockers by dependency-closed declarations and roots unlocked, then execute TL2/TL4/TL6/TL9 slices in that order. | TL10.2 | ongoing | Ranked queue regenerates after every admitted slice. |
| TL10.4 | TODO | Grow theorem-basis profiles: logic, algebra, arithmetic, order, data, topology/analysis foundations, category theory, and tactics. | TL3.9, TL10.3 | XL | Each profile independently admits with exact axiom ledger. |
| TL10.5 | TODO | Run mathlib tactic tests and selected theorem files through native parsing, elaboration, tactics, kernel admission, and runtime. | TL4.12, TL5.10, TL6.13, TL9.12 | XL | Theorem/core/axiom/test result matrix agrees with official build. |
| TL10.6 | TODO | Build the full pinned mathlib release through native module/package/compiler paths. | TL7.10, TL9.13, TL10.5 | XL | All modules either succeed or have zero unclassified failures; final exit requires all succeed. |
| TL10.7 | TODO | Add current/current-minus-one Lean and mathlib release profiles, format migrations, and compatibility deprecation policy. | TL10.6 | ongoing | Upgrade/downgrade matrix and migration tests pass. |
| TL10.8 | TODO | Publish declaration-root, theorem, tactic, axiom, performance, memory, and regression dashboards per release. | TL0.6, TL10.6 | M | No aggregate “mathlib percentage” without exact denominator partitions. |
| TL10.9 | TODO | Package reproducible source, cache, binary, WASM, and checker-only distributions. | TL7.10, TL9.13, TL10.6 | L | Fresh/offline install and smoke projects pass on supported targets. |

L10 exits only when the pinned mathlib release builds and checks through the
declared native profile. Partial profiles remain useful milestones but do not
receive the full exit label.

## 18. Milestones

| Milestone | Required exits | User-visible result |
|---|---|---|
| M0 — controlled boundary | TL0.1-TL0.8 | Generated, non-contradictory capability and trust status. |
| M1 — robust declaration checker | L1 + projection slice TL2.2-TL2.5 | Official structure declarations import and check independently. |
| M2 — core/library base | TL2.6-TL2.13 + TL3.1-TL3.9 | Selected `Init`/`Std`/mathlib roots check; axiom ledger shrinks. |
| M3 — API proof assistant | L4A + basic L5 | API-built goals, holes, `intro`/`apply`/`decide`, checked counterexamples. |
| M4 — native source | L6 + L4B + source tactics | Lean source parses, expands, elaborates, and proves under the native profile. |
| M5 — project/editor | L7 + L8 | Projects build incrementally and editors expose correct live goals. |
| M6 — native runtime | L9 | Metaprograms, build scripts, tactics, and executables run natively. |
| M7 — ecosystem | L10 | Pinned mathlib builds and checks through the native stack. |

### Terminal complete-parity exit

M7 is necessary but not sufficient for the unqualified full-system claim. A
published **complete Lean 4.30 parity** result additionally requires the
[terminal contract](lean4-complete-parity-contract-2026-07-22.md): complete
content-addressed U0-U9 populations, native A0-A11 exits, exact official/native
paired outcomes, zero one-sided/mismatch/unadjudicated/not-run/invalid cells,
independent admission and axiom/trust closure, clean/incremental/offline and
failure-recovery evidence, and the declared tiered platform
install/build/runtime matrix.

The optional official adapter may satisfy its own workflow profile but cannot
substitute for a native terminal cell. Functional, assurance, and performance
results are published separately; a performance aggregate cannot hide a
semantic mismatch or an unexecuted case.

## 19. Immediate execution queue

Execute in this order unless a task's explicit dependency says it may run in a
parallel lane:

1. **DONE:** TL0.1 — reconcile and accept ADR-0345 and ADR-0167.
2. **DONE:** TL0.2 — land the machine-readable capability schema and generated matrix.
3. **DONE:** TL0.4 — land the axiom ledger schema and current 65-row inventory.
4. **DONE:** T6.0.3/TL2.15 seed — establish the seam-fuzz harness before new kernel cases.
5. **DONE:** TL2.2 — add `Proj` representation and exhaustive traversal tests.
6. **DONE:** TL2.3 — add checked structure metadata and dependent projection inference.
7. **DONE:** TL2.4 — add constructor projection reduction.
8. **DONE:** translate official projection records and close the committed projection root; the Nat root then advanced to literal typing at line 125.
9. **DONE:** TL2.5 — add structure eta as its own differential slice.
10. **DONE:** TL2.6 — replace `u128` Nat storage with canonical arbitrary precision.
11. **DONE:** TL2.7 — type Nat literals, implement checked constructor/literal conversion, and close the exact official Nat closure.
12. **DONE:** TL1.3 — publish only owned completed environments after full-stream success.
13. **DONE:** TL1.4 — generate and freeze the 226-case record/structural mutation corpus.
14. **DONE:** TL1.7 — add axiom and declaration dependency digests.
15. **DONE:** Generate and assurance-classify the selected recursive-indexed,
    reflexive, mutual, nested, and well-founded official fixtures.
16. **DONE:** TL2.11--TL2.14 — land strict positivity first, then complete the
    recursive-IH, mutual-group, and nested expansion/restoration admission
    spine under accepted ADR-0352 through ADR-0355 and all retained gates.
17. TL0.3 — correct the remote Lean executable identity across changed working
    directories and retain the first true remote 71/71 attestation.
18. TL0.6 — freeze generated U0-U9 population authorities and A0-A11 paired
    scoreboards before promoting another broad parity claim.
19. TL3.1-TL3.3 — inventory/digest/classify and namespace all preludes.
20. TL3.4 — discharge the first five axioms.
21. TL3.6 — export minimal `Init` roots and regenerate blocker priority.
22. T6.1a — extract the reusable IR-to-CIC bridge in the parallel proof lane.
23. T6.2.1-T6.2.5 — establish one goal/metavariable state with delayed assignment.
24. TL6.1-TL6.4 — establish the source/syntax/parser substrate in the parallel
    frontend lane.
25. Recompute the critical path from the generated construct/root and
    complete-parity matrices.

## 20. Session resume protocol

Before work:

1. read `PLAN.md`, `STATUS.md`, this file, and the owning ADR/task file;
2. verify branch/local/tracking/remote identity and preserve unrelated changes;
3. select the first unblocked queue item, its positive fixture, negative
   mutation, resource limit, and exact exit artifact;
4. record the task ID in the commit message or commit body.

During work:

1. add/commit/push each independently reviewable slice;
2. update the machine-readable matrix and generated docs with the code;
3. never batch multiple trusted-kernel semantic changes into one measurement;
4. checkpoint large official exports and publish progress before terminal work;
5. keep standard processes under 4 GiB and use the registered 8 GiB exporter
   exception only where required.

Before ending:

1. run the task-specific positive/negative/differential gates;
2. run formatting, focused Clippy/tests, docs links, parity/docs consistency,
   and `git diff --check`;
3. update `STATUS.md` with exact evidence and the next unblocked task;
4. stage only owned paths, commit, push, and verify local/tracking/remote heads;
5. leave unsupported states and remaining blockers explicit.
