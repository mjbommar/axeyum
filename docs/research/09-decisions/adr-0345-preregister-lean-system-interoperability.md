# ADR-0345: Preregister adapter-first, full Lean-system compatibility through versioned trust boundaries

Status: accepted

Date: 2026-07-21

## Context

The research register asks whether the proof-assistant bridge should export
obligations to Lean, import checked rewrite rules from Lean, or do both. Axeyum
already implements the first direction for selected proof families: it emits
Lean source and the fail-closed official Lean 4.30 gate currently accepts 71/71
representative generated modules. It also has an independent pure-Rust kernel,
and now an initial declaration import path, but no broad dependency-closed
library import result.

The phrase “Lean parity” had obscured separate targets. Axeyum does not
implement Lean's source parser and macro system, elaborator/unifier, tactic
language, compiler, Lake ecosystem, language server, mathlib, or an `.olean` or
general `lean4export` reader. Its new reader admits only a measured format-3.1
profile. Building the other systems all independently before measuring useful
interchange would be a multi-person-year program and would duplicate official
workflow code before proving demand.

The detailed evidence audit and phased plan is
[`docs/plan/lean-system-compatibility-roadmap-2026-07-21.md`](../../plan/lean-system-compatibility-roadmap-2026-07-21.md).
The implementation-grade task graph is
[`docs/plan/lean-system-implementation-plan-2026-07-21.md`](../../plan/lean-system-implementation-plan-2026-07-21.md).

## Decision

**Axeyum will support both export and import, in that order: keep the existing
official-Lean source cross-check, then complete the fail-closed reader for the
pinned official `lean4export` NDJSON interchange and independently admit
supported declarations with `axeyum-lean-kernel`. This export boundary remains
the first critical path. A complete native Lean-compatible frontend, proof
environment, workflow, runtime, and pinned-mathlib build are preregistered as
later profiles with separate gates; they do not enter the kernel TCB or block
useful earlier profiles.**

The implementation has three explicit profiles:

1. **Independent default:** pure Rust, no Lean runtime, independently checks
   native proof artifacts and supported exported declarations. This is the
   checking-credit and WASM-compatible profile.
2. **Native system:** independently implemented parser/macros, elaboration,
   goals/tactics, modules/packages, editor services, compiler/runtime, and
   pinned-mathlib compatibility are enabled incrementally as K2-K6 gates pass.
   They may construct artifacts but do not gain kernel admission authority.
3. **Optional official integration:** a pinned, sandboxed Lean/exporter process
   or plugin supplies source elaboration, project/module discovery, export,
   editor integration, and official cross-checks. This is an oracle and workflow
   adapter, not independent checking credit.

The interchange rules are:

- pin Lean, exporter, and format versions and record their hashes;
- the official process reads `.olean` first; a native version-specific reader
  is allowed only later in the untrusted cache/adapter layer and must reproduce
  declaration digests from the checked export path;
- accept NDJSON only after metadata, topology, resource, safety, axiom, and
  declaration-shape validation;
- keep parsing/translation/independent admission/official admission/workflow
  reproduction as distinct states;
- fail closed on unknown formats or constructs;
- use actual import declines to order kernel work;
- import selected mathlib theorem bases and translate Axeyum certificates first;
  then grow measured profiles to a full pinned source build without inferring
  mathlib coverage from CAS and curriculum counts;
- build source/Lake/editor adapters before depending on native replacements,
  while allowing the independent syntax substrate to proceed after L0;
- keep compiler output outside the proof TCB.

The Rust reader/admission prototype and its first negative matrix are now
landed in a separate workspace crate. The crate boundary and ADR-0167 ownership
are accepted here; the broader projection/literal/quotient/inductive fixture
matrix remains an implementation gate, not a reason to leave ownership
undefined. The exact flat and direct-recursive fixtures earn
independent-admission credit; the Python inventory by itself still earns none.

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
- `axeyum-cas` is 13,929 Rust source lines in the current inventory, with broad
  exact symbolic algorithms and certificates; `axeyum-rewrite` has 56 default
  stable rules;
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
RHSs against the export. A second official fixture adds direct-recursive
`MiniNat` and parametric-recursive `MiniList`: its 30 names, four nonzero
levels, 130 expressions, and five declaration records become 11 independently
checked declarations with no axioms. The official and generated recursors use
different fresh universe binder names (`u_1` and `u.1`); explicit alpha-renaming
before type/rule comparison admits the semantic match without weakening the
arity or definitional-equality checks. Eleven tests reject theorem-body and
recursor-rule mutations, forward references, unknown records, projections,
version drift, partial definitions, and resource-limit violations; repeated
import is deterministic. See the
[measured prototype](../../plan/lean4export-rust-import-prototype-2026-07-21.md).

The next official census exports structure projection, Nat literal, String
literal, and quotient roots with exact source/tool/stream identities. Projection
is the only blocker in its four-declaration closure and the first Rust decline
in both literal closures. The 290-declaration String closure additionally
contains Nat literals and recursive-indexed inductives; quotient is isolated.
ADR-0345 therefore orders projection before literal work while retaining the
bignum-before-typing rule. See the
[blocker census](../../plan/lean4export-official-blocker-census-2026-07-21.md).

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

### Direct `.olean` reader as the first or trusted boundary

Rejected. `.olean` is a version-coupled implementation cache with an unsafe
untrusted-input surface. The official exporter is the initial supported
conversion boundary and can be sandboxed. TL7.9 permits a late, version-specific
reader only outside the TCB, with malformed-input fuzzing and equality against
the export-derived declaration digests.

### Full native Lean frontend and ecosystem immediately

Rejected before measurement. Parser extensibility, macros, elaboration,
metaprogramming, compiler/runtime, package management, and editor information
trees form several large coupled systems. The official adapter yields earlier
workflow value while preserving independent kernel checking.

### Reimplement mathlib independently file for file

Rejected. Axeyum should import and check upstream theorem dependencies and use
its CAS/solvers to generate proof terms. L10 targets a complete pinned mathlib
build through the native compatibility stack, not authorship of a competing
library with duplicate theorem content.

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
- The 64 arithmetic/integer prelude axioms plus the string axiom become a named
  65-row discharge queue and new axioms fail closed.
- Track 6 remains the native proof-assistant plan. Interoperability adds inputs,
  source/workflow adapters, and cross-checks.
- Native parser/macros, elaboration, modules/Lake/`.olean`, LSP,
  compiler/runtime, and full pinned-mathlib compatibility follow the accepted
  L0-L10 dependency graph and their independent exit criteria; none is implied
  by the import prototype or allowed to expand the kernel TCB.
- Changes to exporter format or supported Lean releases require an explicit
  version-profile update; unknown versions do not receive compatibility credit.
