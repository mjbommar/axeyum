# ADR-0294: Preregister a Glaurung LLVM loop semantic census

Status: proposed
Date: 2026-07-20

Result state: first formal artifact rejected at byte-reproduction; corrected
producer is zero-row and no accepted result exists

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

At preregistration, no semantic classifier had been run on the registered
Glaurung population. Pre-observation smoke tests used only the already accepted
`capsum8` and `capdiv` compiler fixtures plus a deliberate
unsupported-instruction and memory mutation. The first post-push formal
observation is recorded below, including its rejected reproduction.

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
ModuleID-agnostic extracted LLVM hash, stage, stable kind, exact diagnostic, and
accepted metadata.
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

## First formal observation and reproduction correction

The first post-preregistration run created
`glaurung-llvm-loop-semantic-census-v1-rejected-first-run.json`, SHA-256
`13c97b6e3a2227464e3beb2c1329d267dc1afd6ed82e8e157608b69cda221649`.
The immediate second run correctly refused to overwrite it because all 12 raw
`extracted_llvm_sha256` fields differed. A field-by-field in-memory comparison
showed every classification, diagnostic, count, and selected bucket was
identical; only those hashes drifted.

The cause is precise: `llvm-extract` copies its temporary input path into the
leading `; ModuleID = '...'` comment. Different temporary directories therefore
produce different whole-file hashes while the complete LLVM module after that
comment is byte-identical. The rejected artifact and machine-readable
reproduction-failure report are retained; they are not accepted evidence.

The corrected producer requires the exact leading ModuleID comment, feeds the
unmodified extracted file to `llvm-as` and the classifier, but hashes all bytes
after that non-semantic path-bearing comment. A unit test proves two different
ModuleID paths hash equally while a changed function body does not. The same
review also found that the selection summary counted bare function names,
collapsing repeated `main` functions across sources from 12 source-qualified
identities to 10. The corrected rule counts `(source path, function name)`.
Neither correction changes the observed rejection bucket or its eligibility.

The rejected observation was 0 accepted / 12 rejected, all at
`scalar_cfg:unsupported_instruction`, spanning all 12 source-qualified functions
in four sources. This is not yet an accepted result. The corrected producer and
this disclosure must be committed and pushed before a fresh two-run
reproduction.

## Consequences

The next implementation decision will be grounded in precise real rejection
causes rather than topology or a singleton pilot. The measurement reuses the
strict checked frontend and its stable diagnostics, adds no coercion or fallback,
and cannot improve its numbers by dropping work.
