# ADR-0293: Preregister a Glaurung LLVM loop-shape census

Status: proposed
Date: 2026-07-20

Result state: zero-row; the formal 12-source result does not exist

## Context

ADR-0291 and ADR-0292 admit a checked scalar self-loop and one checked
single-latch natural loop. The next T5.1.4 capability must be selected from real
consumer demand, not from another hand-written shape. Glaurung provides a
bounded set of tracked C fixtures that its own frontend and tests consume.

Before this analyzer and selection rule were frozen, exploratory
`opt-21 -passes=print<loops>` runs were made on `hello.c`, `mathlib.c`, and
`pac.c`. They exposed self-loops and a multi-block early-exit loop in
`mathlib_is_prime`; that pilot therefore influenced the taxonomy below. No
formal 12-source totals, coverage ratio, or next-capability decision has been
observed. The pilot cannot authorize an implementation.

This census measures only LLVM LoopInfo structure. It does not establish that a
loop's instructions, memory, calls, poison behavior, or PHIs fit Axeyum's
semantic profile. It is a demand-selection gate, not a frontend acceptance or
finding-recall result.

## Decision

Freeze `glaurung-llvm-loop-census-v1.json` and
`scripts/census-glaurung-llvm-loops.py` before the formal run. The manifest pins:

- Glaurung revision `403a5c5c1f6c5152fef6cefd0d78c3eb90d3888f` and exactly
  12 clean tracked C sources by path and SHA-256;
- Ubuntu clang/LLVM 21.1.8 commands, real paths, binary SHA-256s, and version
  lines;
- target `x86_64-pc-linux-gnu`, `-O1`, disabled loop/vector unrolling, and the
  exact include directory; and
- LLVM LoopInfo's exact `print<loops>` invocation and a fail-closed parser.

Every LoopInfo row is classified into exactly one frozen profile:

1. the ADR-0291 self-loop shape;
2. the ADR-0292 single-latch shape, where only the latch exits;
3. a single-latch early-exit shape;
4. a single-latch no-exit shape;
5. a multi-latch shape;
6. a nested shape; or
7. another shape.

If any function contains a depth-greater-than-one row, all its loop rows are
conservatively classified as nested. Unknown LoopInfo syntax, dirty or changed
sources, tool drift, manifest drift, compile/assembly failure, or a second
non-identical result fails closed with a precise error. The output omits
timestamps and absolute temporary paths and must reproduce byte-for-byte.

The post-result selection rule is fixed now. Exclude the two already admitted
profiles, count rejected rows and their distinct functions and source files,
then select a new profile only if it is the strict plurality and occurs in at
least two distinct functions from at least two distinct source files. A tie or
failure of either diversity threshold selects no implementation. Multi-latch
and nested shapes never receive automatic authorization from this census; even
if dominant, each requires a separate architectural decision. A selected
profile still needs its own zero-row semantic ADR and compiler fixture before
code changes.

## Pre-observation gates

1. Commit and push this ADR, manifest, analyzer, and unit tests while the formal
   result path is absent.
2. `--validate --glaurung-root /nas4/data/workspace-infosec/glaurung` verifies
   all pinned sources and tools without invoking LoopInfo.
3. Unit tests cover captured real LoopInfo text, every taxonomy cell, malformed
   syntax, manifest drift, and byte-identical retention.
4. The formal command is run twice after the preregistration commit. The first
   run creates the registered path and the second must report `reproduced`.
5. Report every source row and every zero-count profile; do not discard compile
   warnings or unsupported shapes.

## Consequences

T5.1.4 advances through measured consumer structure. A small corpus or a
negative selection remains useful evidence: it prevents a single pilot loop
from silently becoming the roadmap. No loop capability, performance claim, or
Glaurung finding claim is added by this zero-row decision.
