# ADR-0279: Gate a Glaurung LLVM frontend on the executable-LLIR contract

Status: accepted
Date: 2026-07-19

## Context

The distilled plan proposed a Linux LLVM-IR frontend that would lower bitcode
into Glaurung LLIR and reuse the existing `Domain`, symbolic explorer, and
Axeyum solver. Its explicit first gate was to confirm that LLIR is
frontend-agnostic. That gate must be evaluated against the current sources and
the already accepted symbolic-CVE frontend evidence rather than against the
architectural intent alone.

At Glaurung `403a5c5`, the reusable center is real:

- `LlirFunction` contains blocks of generic `Op` values;
- `Machine<D: Domain>` interprets those operations once for concrete and
  symbolic values;
- the symbolic explorer accepts `LlirFunction` rather than decoder
  instructions; and
- both x86 and AArch64 machine-code lifters already target this surface.

The boundary is not yet a compiler-IR-neutral contract, however:

- `VReg::Phys` derives widths from ISA register names, `VReg::Temp` carries no
  width, and `Machine::op_width` falls back to 64 bits when neither destination
  nor operands disclose one;
- integer constants are untyped `i64` values and addresses are implicitly
  64-bit;
- conditional fallthrough is represented by `LlirBlock::end_va`, so the
  executor assumes machine-address layout rather than two explicit successor
  labels;
- calling conventions, argument seeding, privileged-operation sinks, stack
  handling, and several memory policies name architectural registers directly;
  and
- there is no stated lowering contract for LLVM data layout, address spaces,
  `phi`, `getelementptr`, globals, `alloca`, calls/intrinsics, `undef`, poison,
  `freeze`, or `nuw`/`nsw` flags.

ADR-0268 supplies workload evidence rather than a hypothetical gap list. The
four admitted kernel sides contain 560--1,013 instructions, 59--129 loads,
15--29 stores, 78--117 GEPs, globals, allocas, pointer casts, 172--230 calls
outside Axeyum's supported min/max intrinsic, and 115--139 inline-assembly or
indirect calls. It therefore selected Glaurung's existing AArch64 ELF-to-LLIR
route for the bounded recall campaign and rejected a general LLVM importer as
the smaller implementation. That route subsequently delivered the accepted
selected-pair result.

Axeyum's `reflect::llvm` module is useful semantic scaffolding, not a production
parser to copy. It line-splits a deliberately bounded fragment, documents
panics for malformed or unsupported constructs, treats cycles and specialized
memory through separate test paths, and does not parse a whole kernel module.
P5.1 already names replacement of that surface with a token-level, diagnostic
parser as T5.1.2.

## Decision

The admission gate is **conditional, not passed for direct implementation**.
Keep Glaurung's current AArch64 ELF route as the accepted Linux recall frontend.
Do not build a bitcode-to-current-LLIR adapter, and do not describe the existing
LLIR as fully frontend-agnostic.

Move the general LLVM idea under Track 5 and sequence it as follows:

1. advance P5.1/T5.1.2 in Axeyum with a token-level textual LLVM parser,
   structured unsupported diagnostics, source spans, and parse/print/parse
   corpus gates; retain the current reflector behavior while migrating;
2. before a Glaurung lowering target is public, give imported temporaries and
   values explicit widths, represent both conditional successors explicitly,
   separate ABI/input/sink policy from physical-register names, and document a
   fail-closed LLVM semantics profile;
3. use the structured parser AST as the candidate shared boundary only after a
   second real consumer exists. A new parser crate remains separately
   ADR-gated under ADR-0001; Glaurung must not depend on the broad
   `axeyum-verify` product surface merely to parse LLVM; and
4. admit a binary-vs-IR differential only on the same source function/object,
   with matched environment and explicit unsupported accounting. It is not a
   recall estimate or a shortcut around source-to-machine identity.

This is not a decision to abandon compiler-IR reflection. It prevents a broad
frontend from duplicating P5.1, weakening LLVM semantics, or destabilizing the
accepted Glaurung evidence baseline.

## Evidence and checks

The audit used current Axeyum `626c5a87` and Glaurung `403a5c5`. The primary
Glaurung worktree has unrelated active edits, including formatting changes in
`src/ir/types.rs` and control-flow work in `src/analysis/cfg.rs`; it is not an
implementation surface for this decision.

The following source facts make the result falsifiable:

- `src/exec/interp.rs` dispatches generic `Op` values through `Machine<D>` but
  defaults unresolved operation widths to `Width::W64`;
- `src/symbolic/explore.rs` accepts `LlirFunction`, but uses `block.end_va` as
  the false/fallthrough target and contains x86 register-specific sink and ABI
  code;
- `src/ir/types.rs` documents ISA-named physical registers and untyped
  temporaries/constants; and
- Axeyum's P5.1 task table already leaves the full `.ll` parser, automatic loop
  bridge, and general memory lowering open.

No frontend code, solver behavior, finding population, or performance result is
changed by this ADR.

## Consequences

- PLAN item 6 becomes a conditional Track-5 horizon, not the immediate
  integration increment.
- T5.1.2 is the next reusable implementation prerequisite, beginning with a
  structured parser slice rather than a second line-oriented parser.
- Glaurung's accepted AArch64 ELF frontend remains the publication route for the
  current Linux recall evidence.
- The future claim is narrower and stronger: one semantic parser can eventually
  feed an Axeyum term reflector and a hardened Glaurung LLIR lowerer, but neither
  lowering is inferred correct from sharing syntax alone.

## Alternatives

- Lower LLVM directly into current LLIR: rejected because i8/i16 temporary
  chains and arbitrary CFG false edges can silently acquire the wrong
  semantics.
- Expand the current line-based Axeyum reflector to cover the kernel surface:
  rejected by ADR-0268's measured memory/call/inline-assembly breadth and by
  P5.1's existing full-parser plan.
- Replace the accepted AArch64 ELF campaign with LLVM execution: rejected
  because the paired recall result already has a smaller, working frontend and
  changing it would invalidate the evidence identity.
- Create a shared LLVM parser crate immediately: deferred until the second
  consumer and API boundary are implemented and reviewed under ADR-0001.
