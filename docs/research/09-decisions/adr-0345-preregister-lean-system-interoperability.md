# ADR-0345: Preregister Lean-system interoperability through a versioned export boundary

Status: proposed

Date: 2026-07-21

## Context

The research register asks whether the proof-assistant bridge should export
obligations to Lean, import checked rewrite rules from Lean, or do both. Axeyum
already implements the first direction for selected proof families: it emits
Lean source and the fail-closed official Lean 4.30 gate currently accepts 71/71
representative generated modules. It also has an independent pure-Rust kernel,
but no declaration import path.

The phrase “Lean parity” had obscured separate targets. Axeyum does not
implement Lean's source parser and macro system, elaborator/unifier, tactic
language, compiler, Lake ecosystem, language server, mathlib, or an `.olean` or
`lean4export` reader. Building those all independently before measuring useful
interchange would be a multi-person-year program and would duplicate official
workflow code before proving demand.

The detailed evidence audit and phased plan is
[`docs/plan/lean-system-compatibility-roadmap-2026-07-21.md`](../../plan/lean-system-compatibility-roadmap-2026-07-21.md).

## Decision

**Axeyum will support both export and import, in that order: keep the existing
official-Lean source cross-check, then add a fail-closed reader for the pinned
official `lean4export` NDJSON interchange and independently admit supported
declarations with `axeyum-lean-kernel`; it will not parse `.olean` directly or
preregister full independent clones of Lean's frontend, compiler, Lake,
language server, or mathlib.**

The implementation has two explicit profiles:

1. **Independent default:** pure Rust, no Lean runtime, independently checks
   native proof artifacts and supported exported declarations. This is the
   checking-credit and WASM-compatible profile.
2. **Optional official integration:** a pinned, sandboxed Lean/exporter process
   or plugin supplies source elaboration, project/module discovery, export,
   editor integration, and official cross-checks. This is an oracle and workflow
   adapter, not independent checking credit.

The interchange rules are:

- pin Lean, exporter, and format versions and record their hashes;
- only the external official process may read `.olean`;
- accept NDJSON only after metadata, topology, resource, safety, axiom, and
  declaration-shape validation;
- keep parsing/translation/independent admission/official admission/workflow
  reproduction as distinct states;
- fail closed on unknown formats or constructs;
- use actual import declines to order kernel work;
- import selected mathlib theorem bases and translate Axeyum certificates; do
  not reimplement mathlib file for file or infer mathlib coverage from CAS and
  curriculum counts;
- build source/Lake/editor adapters before considering native replacements;
- keep compiler output outside the proof TCB.

The Rust reader/admission prototype and its first negative matrix are now
landed in a separate workspace crate. The decision remains proposed until that
crate boundary and the broader projection/literal/quotient/inductive fixture
matrix are reviewed. The exact flat fixture earns independent-admission credit;
the Python inventory by itself still earns none.

## Evidence

### Current Axeyum assets

- `axeyum-lean-kernel` independently implements names, levels, expressions,
  environments, reduction, definitional equality, type checking, and selected
  inductives in pure Rust.
- The checksum-pinned fail-closed official gate accepts the selected 71/71 Lean
  4.30 generated-module family set.
- Track 6 already specifies Goal/Hole/delayed assignment, certificate tactics,
  and the agent/spec surfaces. A new interoperability track should feed it, not
  duplicate it.
- `axeyum-cas` is approximately 14,123 Rust lines with broad exact symbolic
  algorithms and certificates; `axeyum-rewrite` has 56 default stable rules;
  the foundational corpus has 173 validated non-template math packs and 399
  checked rows. These are strong tactic/certificate inputs but not mathlib.

### Official interchange prototype

Official `lean4export` v4.30.0 under Lean 4.30.0 exported a small module
containing an axiom, theorem, flat inductive, generated recursor definition, and
ordinary definition. The committed format-3.1.0 fixture contains 14 names, 2
nonzero universe levels, 43 expressions, and 5 declaration records.

The research reader validates dense indices and backward references, rejects
unknown records, forward references, and unsafe/partial declarations, and
classifies projection, literal, quotient, and harder inductive blockers. The
exact flat fixture has no inventory blockers. That Python result proves only
that the seam is concrete; the separate Rust result below supplies the first
kernel-admission evidence.

The follow-on `axeyum-lean-import` Rust crate now admits that exact official
fixture through `Kernel::add_declaration` and `Kernel::add_inductive`. Five
export records become eight checked environment declarations (`Two`, its two
constructors and generated recursor, `Two.recOn`, `chooseLeft`, axiom `P`, and
theorem `identity`). The importer independently generates `Two.rec` and checks
its universe parameters, type, counts, constructors, field counts, and iota-rule
RHSs against the export. Nine tests reject theorem-body and recursor-rule
mutations, forward references, unknown records, projections, version drift,
partial definitions, and resource-limit violations; repeated import is
deterministic. See the
[measured prototype](../../plan/lean4export-rust-import-prototype-2026-07-21.md).

JSON and format handling live in `axeyum-lean-import`, which depends on the
zero-dependency kernel. The kernel does not depend on `serde_json` or the
importer, and importer code has no access to unchecked environment insertion.
This is an exercised wire-format/checker boundary under ADR-0001 rather than a
convenience module inside the TCB.

### Upstream boundaries

- The Lean reference pipeline separates parser, macro expansion, elaboration,
  kernel admission, and compilation.
- Tactics are integrated with term elaboration; the language server consumes
  elaboration information, so a standalone LSP is not an independent early
  task.
- The official comparator sandboxes `lean4export` instead of directly loading
  untrusted `.olean` files.
- Mathlib v4.30.0 contains 8,606 Lean files across generic mathematical
  libraries, tactic infrastructure, and programming support. Its abstractions
  are qualitatively different from an explicit-domain CAS.

Primary sources:

- [Lean elaboration and compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
- [Lean macros](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Macros/)
- [Lean elaborators](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Elaborators/)
- [Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
- [`lean4export` v4.30.0](https://github.com/leanprover/lean4export/tree/v4.30.0)
- [`lean4export` NDJSON 3.1.0](https://github.com/leanprover/lean4export/blob/v4.30.0/format_ndjson.md)
- [Lean comparator](https://github.com/leanprover/comparator)
- [mathlib v4.30.0](https://github.com/leanprover-community/mathlib4/tree/v4.30.0)

## Alternatives

### Export only

Rejected as the end state. It provides official acceptance but cannot
independently check imported Lean declarations or reuse theorem libraries as a
trusted-second-implementation boundary.

### Import only

Rejected. Existing source emission and official cross-checks are useful and
already operational. The two directions test different failure modes.

### Direct `.olean` reader

Rejected. `.olean` is a version-coupled implementation cache with an unsafe
untrusted-input surface. The official exporter is the supported conversion
boundary and can be sandboxed.

### Full native Lean frontend and ecosystem immediately

Rejected before measurement. Parser extensibility, macros, elaboration,
metaprogramming, compiler/runtime, package management, and editor information
trees form several large coupled systems. The official adapter yields earlier
workflow value while preserving independent kernel checking.

### Reimplement mathlib

Rejected. Axeyum should import and check selected theorem dependencies and use
its CAS/solvers to generate proof terms. Duplicating a vast generic theorem
library is lower leverage than interoperability and theorem discharge.

### Add an external Rust Lean checker as a dependency

Deferred as a reference/benchmark option. Projects such as `oxilean-export`
show format-3.x reading is feasible, but adopting one does not remove the need
to define Axeyum's own admission, safety, axiom, and TCB contracts.

## Consequences

- The independent kernel remains a genuine second implementation, while users
  may use official Lean as a convenient frontend and project tool.
- Kernel breadth is prioritized by dependency-closed import gains rather than a
  feature checklist invented in isolation.
- Parsing never earns checking credit; official acceptance never earns
  independent-admission credit.
- The first implementation work is a Rust NDJSON wire reader and a tiny
  end-to-end environment import. That initial flat slice is now landed;
  projections/literals/quotients and harder inductives follow as real exports
  require.
- The importer is a separate workspace crate so parser dependencies and
  malformed-input logic do not enter `axeyum-lean-kernel`.
- The 64 prelude axioms become a named discharge queue and new axioms fail
  closed.
- Track 6 remains the native proof-assistant plan. Interoperability adds inputs,
  source/workflow adapters, and cross-checks.
- A full native Lean frontend, Lake clone, LSP, compiler, or mathlib equivalent
  requires a later ADR with measured demand and independent exit criteria.
- Changes to exporter format or supported Lean releases require an explicit
  version-profile update; unknown versions do not receive compatibility credit.
