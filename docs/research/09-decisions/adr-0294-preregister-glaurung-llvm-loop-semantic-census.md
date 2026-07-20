# ADR-0294: Preregister a Glaurung LLVM loop semantic census

Status: proposed
Date: 2026-07-20

Result state: zero-row; no registered Glaurung loop has been passed through the
semantic classifier

## Context

ADR-0293's exact structural census finds 12 loops in 12 functions: 11 match the
ADR-0291 self-loop topology and one is an under-diverse early-exit loop. That is
not an 11/12 semantic-support result. The checked loop reflector can still
decline a structurally matching function because its typed CFG, PHIs,
initializers, body operations, memory, external SSA, or IR construction are
outside the admitted semantics.

The next T5.1.4 question is therefore not which loop shape to implement. It is
where the real functions stop in the existing checked pipeline, with every
decline retained under the precise stable error class that made Axeyum useful as
a Glaurung correctness oracle. Silent extraction loss, collapsed diagnostics,
or treating a parse failure as an unsupported loop would repeat the
methodology error of mistaking dropped work for a favorable result.

No semantic classifier has been run on the registered Glaurung population.
Pre-observation smoke tests use only the already accepted `capsum8` and `capdiv`
compiler fixtures plus a deliberate unsupported-instruction and memory
mutation. Those tests validate the measurement route; they do not reveal the
formal population result.

## Decision

Freeze `glaurung-llvm-loop-semantic-census-v1.json`,
`scripts/census-glaurung-llvm-loop-semantics.py`, and the private
`axeyum-llvm-loop-classify` binary before the formal run. This is measurement
infrastructure, not a new public frontend capability or solver surface.

The manifest pins:

- ADR-0293's structural manifest and exact result by path and SHA-256;
- every classifier/reflector source file, `Cargo.lock`, and the package manifest
  by SHA-256;
- exact nightly Cargo/rustc binaries and versions, LLVM 21.1.8
  `llvm-extract`, and the inherited exact clang/`llvm-as` identities;
- a locked, offline, non-incremental classifier build; and
- a strict-plurality selection rule requiring at least two functions from at
  least two sources.

The formal producer recompiles all 12 sources under ADR-0293's exact flags. It
requires every `.ll` SHA-256 and compiler diagnostic to match the retained
structural result before classification. LLVM's own `llvm-extract` isolates
each of the 12 loop functions; the extracted module must assemble unchanged.
No handwritten module splitter is introduced.

For each extracted function, the classifier:

1. runs the existing non-panicking `parse_function` boundary;
2. runs the existing typed `parse_scalar_cfg` boundary;
3. tries every distinct non-Boolean PHI in source order as an unsigned-bound
   target with bound zero, solely to avoid a caller-chosen property name hiding
   an otherwise admissible loop; and
4. calls `reflect_single_latch_loop_checked`, which already includes the
   ADR-0291 self-loop route.

Any successful PHI candidate yields `accepted:self_loop` or
`accepted:single_latch`, with state-component and iteration-path counts. If all
candidates fail, the first non-`InvalidProperty` error wins; otherwise the first
error wins. This prevents a non-loop PHI from masking a later valid loop PHI
while retaining the actual stable `ParseErrorKind` or `LoopReflectErrorKind` and
located diagnostic. No solver call, proof, finding, timing, or performance claim
is part of this census.

Every formal row retains source/function identity, structural profile,
extracted LLVM hash, stage, stable kind, exact diagnostic, and accepted metadata.
The result must account for all 12 registered sources and all 12 loop rows.
Accepted plus rejected must equal 12; no error/unknown bucket may disappear.

The post-result rule is fixed. Among rejected `stage:kind` buckets, select a
next audit lane only if one bucket is the strict plurality and spans at least
two functions and two sources. A tie or insufficient diversity selects no
implementation. Routing is also fixed:

- `function_syntax` or `scalar_cfg` points to T5.1.2 parser/typed-CFG breadth;
- `loop_reflection:unsupported_memory` points to T5.1.5 memory;
- other ordinary loop-reflection shape/body/PHI/SSA/resource declines point to
  T5.1.4; and
- `loop_reflection:syntax` or `ir_construction` triggers a correctness audit,
  not a capability project.

The selected lane still requires its own zero-row semantic ADR before code. An
accepted classification establishes construction of one recurrence only; it
does not establish a property proof, exact exit trace, finding recall, or source
replay.

## Pre-observation gates

1. Commit and push this ADR, manifest, classifier, producer, and tests while the
   formal semantic-result path is absent.
2. Environment validation checks all registered source/tool/producer hashes and
   revalidates ADR-0293's complete result without compiling the formal corpus.
3. Rust tests classify both accepted fixtures without property-name bias and
   preserve precise typed-parser and memory declines; strict Clippy passes.
4. Python tests fail closed on dropped/inconsistent classifier fields,
   manifest drift, ties, and same-source pseudo-diversity.
5. The exact offline Cargo/rustc build plus real `llvm-extract` and classifier
   binary succeeds on the accepted `capdiv` fixture.
6. After this checkpoint is pushed, run the formal producer twice. The first
   run creates the exact registered result and the second must reproduce it
   byte-for-byte.
7. Report every source and function, including zero-loop sources and retained
   compiler warnings. Do not infer semantic support from ADR-0293's structural
   labels.

The gates may be strengthened before the first registered semantic result is
observed. They may not be weakened afterward.

## Consequences

The next implementation decision will be grounded in precise real rejection
causes rather than topology or a singleton pilot. The measurement reuses the
strict checked frontend and its stable diagnostics, adds no coercion or fallback,
and cannot improve its numbers by dropping work.
