# Lean-system roadmap objective: completion audit

Status: research/design/prototype/documentation objective complete; implementation
program remains staged

Date: 2026-07-21

Roadmap:
[`lean-system-compatibility-roadmap-2026-07-21.md`](lean-system-compatibility-roadmap-2026-07-21.md)

Active execution plan:
[`lean-system-implementation-plan-2026-07-21.md`](lean-system-implementation-plan-2026-07-21.md)

Decision:
[ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md)

Terminal definition added 2026-07-22:
[`lean4-complete-parity-contract-2026-07-22.md`](lean4-complete-parity-contract-2026-07-22.md)

The terminal contract does not reopen this audit's completed
research/design/prototype objective. It makes the continuing implementation
claim stricter: complete Lean 4.30 parity requires native A0-A11 exits over
content-identified U0-U9 populations, exact official/native paired outcomes,
and zero adapter or incomplete-run substitution. The current matrix remains
K0 1/1, K1 4/5, and K2-K6 0 satisfied rows.

## 1. Scope of this audit

The requested objective was to research the distance between Axeyum's
independent Lean-compatible checker and the complete Lean environment, design
and prototype a route across that distance, and write a detailed roadmap under
`docs/`. The objective explicitly named:

- parser and macro expansion;
- elaboration and unification;
- tactics;
- compilation;
- Lake and package workflows;
- language-server/editor workflows;
- mathlib;
- `.olean` or `lean4export` declaration import;
- an evidence-based comparison with the CAS, rewrite rules, curriculum, and
  other machinery Axeyum already has.

Completing that objective does **not** mean that Axeyum now implements all of
Lean. It means that the current implementation has been inventoried, the
missing systems have explicit architectures/dependencies/sizes/exits, a real
interchange seam has crossed independent admission, and the remaining work is
an executable implementation program rather than an undifferentiated claim of
"Lean parity."

This audit treats that distinction as part of the requirement. A document that
called the roadmap complete by quietly narrowing the target to the kernel or to
source printing would fail.

## 2. Requirement-by-requirement result

| Requested surface | Evidence about current state | Closing design and measured exit | Audit result |
|---|---|---|---|
| Lean parser and macro system | Roadmap sections 1 and 3 distinguish extensible syntax/macros from core checking and record the native frontend as absent | TL6.1-TL6.13 cover lexer/syntax, Pratt extension tables, builtin and user syntax, quotations, hygiene, recovery, printing, differential fixtures, and bootstrap | covered by active plan; implementation open by design |
| Elaborator and unifier | Sections 2.2 and 3 distinguish existing solver automation from metavariable elaboration; Track 6 already owns goals/holes/delayed assignment | L4A reuses Track 6; TL4.1-TL4.12 add constraints, universe/coercion/typeclass handling, terms/declarations/inductives/recursion, information trees, and official-core differential tests | covered by active plan; implementation open |
| Tactics | Section 2.2 inventories solver reconstruction, e-graph explanations, CAS certificates, and 56 default rewrite rules without calling them Lean tactics | L5 orders `exact`/`intro`/`apply`, `decide`, counterexamples, `norm_num`, `ring`, `linarith`/`nlinarith`, theorem-backed `simp`, induction, and instantiation; every step must emit a tamper-tested kernel term | covered by roadmap; existing engines reused rather than ignored |
| Compiler/runtime | Section 3 separates optional compilation from kernel admission; no native Lean compiler is claimed today | TL9.1-TL9.13 stage interpreter, erasure, checked IR/LCNF, passes, RC/runtime, C/native/WASM, FFI, metaprograms, differential execution, and bootstrap outside the proof TCB | covered by active long-horizon plan |
| Lake/package ecosystem | Section 3 records Lake as a Lean-aware build/package system rather than a configuration-file parser | TL7.1-TL7.10 stage the official adapter, module/cache identity, manifests/resolution/build facets, native Lake DSL, `.olean`, and clean/incremental/offline project reproduction | covered by adapter-first native plan |
| Language server/editor | Section 3 records the dependency on elaboration information trees rather than treating JSON-RPC as compatibility | TL8.1-TL8.10 cover snapshots/cancellation, incremental syntax/elaboration, diagnostics, navigation, completion, semantic data, actions/widgets, and transcript/resource gates | covered by dependency-correct native plan |
| Mathlib | Section 2.3 compares actual Axeyum assets with the pinned mathlib tree and explicitly rejects a coverage percentage | L3 orders axiom classification/discharge and selected bases; TL10.1-TL10.9 then require blocker inventories, native tactic tests, a full pinned build, release maintenance, dashboards, and distributions | covered by source-backed full-build plan |
| `.olean` / `lean4export` reader | The original state had no reader. Section 4 rejects direct `.olean` parsing as the first or trusted interchange and selects pinned `lean4export` 3.1 NDJSON | L1's reader and L2 admission remain first; TL7.9 later allows a version-specific untrusted cache reader only with export-digest equivalence and malformed-input gates | prototype crossed the seam; both production paths open |
| Detailed roadmap under `docs/` | The main roadmap has target definitions, current inventory, primary-source model, architecture, dependency graph, L0-L10 phases, sizes, exits, assurance states, negative gates, performance reporting, risks/non-claims, and ten immediate actions | This audit plus the prototype and blocker reports bind each claim to code, fixtures, commands, or pinned upstream trees | satisfied |
| Research what Axeyum actually has | The comparison covers the independent kernel, proof reconstruction, Track 6, CAS, rewrite/e-graph layers, curriculum, foundational resources, and current axiom surface | Counts below were rederived from the current worktree; capability relationships are expressed as missing proof bridges, not as superficial LOC/file ratios | satisfied |

## 3. Current Axeyum inventory, revalidated

The following commands were rerun against the current source parent
`7a6e6953` before this documentation-only audit commit.

| Inventory | Command/evidence | Result |
|---|---|---:|
| CAS Rust source | `find crates/axeyum-cas/src -type f -name '*.rs' -print0 \| xargs -0 wc -l` | 13,929 lines |
| Default canonical rewrites | count top-level `rule(` entries in `default_rules()` | 56 |
| Curriculum state | exact `status` census in `docs/curriculum/curriculum.toml` | 23 nodes: 19 `covered`, 4 `lean-horizon` |
| Foundational concepts | `python3 scripts/query-foundational-resources.py summary` | 137 rows |
| Non-template math packs | same query | 173 |
| Expected-result rows | same query | 1,131 |
| Proof-status split | same query | 399 checked, 596 replay-only, 136 Lean-horizon |
| Solver-reuse disposition | same query | 173 promoted packs |
| Learning documents | `find docs/learn/math -type f` | 249 files |

These are meaningful assets for tactics and theorem selection, but they do not
measure mathlib coverage:

- the CAS primarily computes over explicit domains and returns specialized
  values/certificates;
- mathlib theorems are commonly generic over structures, universes,
  typeclasses, coercions, and dependent arguments;
- rewrite application reports are not proof terms until every rule has theorem
  provenance and a checked explanation translation;
- finite/computable curriculum packs are regression and target material, not a
  replacement for generic theorem libraries.

The roadmap's crosswalk therefore asks for reification, theorem-basis import,
certificate translation, hypothesis provenance, and kernel checking. It does
not propose reimplementing mathlib file by file.

## 4. Pinned upstream inventory, revalidated

The upstream comparison was rerun from shallow, no-checkout clones so the
counts come from Git trees rather than a web-interface estimate.

### Lean

- tag: `v4.30.0`;
- commit: `d024af099ca4bf2c86f649261ebf59565dc8c622`;
- all files under the tagged directories: `Lean/Parser` 17, `Lean/Elab` 300,
  `Lean/Meta` 417, `Lean/Server` 45, `Lean/Compiler` 117, and `src/lake` 160.

The Server total comprises 44 `.lean` files plus its README. The Lake total
comprises 158 `.lean` files plus its README and JSON schema. This confirms that
the roadmap's figures are intentionally file-count scale indicators, not Lean
LOC or complexity estimates.

### Mathlib

- tag: `v4.30.0`;
- commit: `c5ea00351c28e24afc9f0f84379aa41082b1188f`;
- 8,606 `.lean` files in the tagged repository, of which 8,094 are under
  `Mathlib/`;
- selected `Mathlib/` directory counts: Algebra 1,319, CategoryTheory 1,084,
  Analysis 795, RingTheory 689, Topology 665, LinearAlgebra 351, Tactic 336.

The reproducible counting primitive is:

```sh
git ls-tree -r --name-only v4.30.0
```

filtered by `.lean` suffix and directory prefix. The exact upstream sources and
reference-manual pages are linked in sections 2.3-4 of the main roadmap.

## 5. Prototype and assurance evidence

The roadmap is backed by implementation rather than only a feature list:

1. the Python format probe inventories official format-3.1 records and has
   eight fixture/hash tests;
2. the separate pure-Rust `axeyum-lean-import` crate keeps JSON/version/resource
   handling outside the zero-dependency kernel;
3. a pinned official flat fixture becomes eight independently checked
   declarations;
4. a pinned direct-recursive `MiniNat`/`MiniList` fixture becomes eleven
   declarations with zero axioms;
5. Axeyum independently regenerates recursors and definitionally compares their
   types and iota rules after universe-binder alpha-renaming;
6. theorem-body and recursor-rule mutations reject;
7. exact projection, Nat, String, and quotient closures established projection
   as the first measured kernel slice; TL2.2-TL2.4 close its exact K1 root and
   TL2.6-TL2.7 close the committed Nat root with checked arbitrary-precision
   constructor/literal semantics, while the unretained String root awaits a
   refreshed first-blocker measurement;
8. focused current validation passes 179 kernel unit tests, 35 kernel
   integration cases across twelve binaries, and twenty-eight importer tests under
   the repository's 4 GiB cap, including a required pinned-Lean Nat-literal
   differential;
9. the separate official-source lane has a committed fail-closed 71/71 Lean
   4.30 representative-family result, without converting it into broad import,
   mathlib, or ecosystem credit.

The exact format contract, fixtures, hashes, negative matrix, and commands are
in the
[`lean4export` Rust prototype report](lean4export-rust-import-prototype-2026-07-21.md).
The four-root dependency evidence and next implementation order are in the
[official blocker census](lean4export-official-blocker-census-2026-07-21.md).

## 6. Remaining implementation program

The following remain deliberately open and must not be erased by this audit:

- L0 pin/resource/gate/scoreboard/status contracts; ADR-0345 is accepted, the
  selected capability matrix and 65-row axiom inventory are landed, and the
  first corrected remote Lean job still fails before its representative sweep
  on working-directory-dependent elan executable resolution;
- L1 property fuzzing and checkpointed large-stream durable publication;
  whole-environment in-memory publication is atomic, the deterministic 226-case
  mutation corpus is complete with the upstream no-footer prefix boundary
  explicit, and canonical declaration/direct-dependency identity has landed;
- L2 accelerated Nat operations, String literals, quotient semantics, and
  broader generated seam/construct matrices. Strict positivity, recursive-
  indexed/reflexive induction hypotheses, atomic mutual groups, and nested-
  inductive expansion/restoration are now complete for their registered
  populations under ADR-0352 through ADR-0355;
- L3 dependency-closed `Init`/`Std`/mathlib slices and semantic
  discharge/classification of the now runtime/type-digested 65 reconstruction
  assumptions (real 30, integer 34, string 1);
- L4 goals/holes/unification and L5 certificate tactics;
- L6 native parser/macros and L4B elaboration;
- L7 modules/caches/packages/Lake/`.olean` and L8 native editor/LSP;
- L9 evaluator/compiler/runtime/metaprograms outside the proof TCB;
- L10 full pinned-mathlib build, compatibility breadth, and release maintenance.

Those are roadmap phases with explicit exit criteria, not unfinished
requirements of the research/design/prototype/documentation objective itself.
Implementation status remains WIP until their own gates pass.

## 7. Completion verdict

The original objective is satisfied without shrinking its scope:

- every named missing Lean subsystem is researched and separately staged;
- the design preserves the independent checker and gives optional official
  integration a non-TCB adapter role;
- the initial `lean4export` reader and independent declaration admission are
  implemented and mutation-tested, superseding the original "no reader" state;
- real unsupported dependency closures establish the next implementation
  order;
- CAS, rewrite, curriculum, resource, Lean, and mathlib inventories are
  revalidated and interpreted by capability rather than marketing counts;
- the complete L0-L10 program, gates, risks, non-claims, and immediate actions
  live under `docs/plan/`.

The precise status is therefore: **roadmap objective complete; Lean-system
implementation incomplete and continuing from L0 population/remote-gate work,
remaining String/quotient K1 roots, L3 trust/library work, and the unstarted
native K2-K6 stack.** The complete-parity contract supplies the terminal exit;
it does not convert this roadmap audit into implementation completion.
