# ADR-0282: Preregister typed LLVM CFG syntax and validation

Status: accepted
Date: 2026-07-19

Result state: accepted; implementation and gates complete

## Observed result

The implementation adds the frozen `BlockId`, `Phi`, `Terminator`, `CfgBlock`,
and `ScalarCfg` types plus `parse_scalar_cfg`. It groups multiline switches
without losing exact source offsets, retains supported terminator metadata,
normalizes signed switch constants, derives deterministic graph edges, and
checks every target, entry, terminator, switch, and PHI predecessor invariant
before returning a graph.

Unmodified clang 21.1.8 and rustc 1.97-nightly division diamonds both assemble
with `llvm-as` and converge to the expected conditional-branch/two-arm/PHI
shape. Seven focused tests cover all admitted terminators, quoted and numeric
labels, negative cases, repeated destinations, metadata, exact multiline error
locations, malformed graph classes, and 4,096 deterministic noise inputs. All
existing LLVM CFG equivalence fixtures now pass `parse_scalar_cfg` before the
legacy proof path runs. The complete `axeyum-verify --all-features` suite,
strict Clippy, strict rustdoc, formatting, and the link checker pass.

No checked CFG executor was added. `unreachable` is represented explicitly but
is not yet interpreted by a new proof API; ADR-0283 must freeze that semantics.

## Context

ADR-0280 establishes a non-panicking textual function/block boundary and
ADR-0281 types the straight-line scalar fragment with explicit LLVM
definedness. Control flow remains a separate panic-oriented string parser in
the compatibility reflector: `br`, `switch`, `phi`, and `unreachable` are split
with ad hoc delimiters; missing labels and malformed predecessor sets panic;
and an `unreachable` arm is dropped as a don't-care during joins.

That is not a checked LLVM boundary. It also preserves the exact Glaurung LLIR
contract gap identified by ADR-0279: successor identity and direction are not
explicit enough to share safely, and execution policy is entangled with graph
recovery. Before checked CFG execution or a second lowerer is considered,
Axeyum needs a typed, validated graph that neither consumer can reinterpret.

## Decision

Add a `reflect::llvm::syntax` CFG layer over the accepted `Function` syntax:

- `BlockId` distinguishes the unlabeled entry block from a named LLVM label;
- `Phi` records destination, integer width, ordered `(value, predecessor)`
  pairs, and source span;
- `Terminator` records one of scalar `ret`, unconditional `br`, conditional
  `br` with explicit true and false targets, integer `switch` with a default
  and ordered normalized constant cases, or `unreachable`;
- `CfgBlock` retains ordered typed scalar body instructions, leading PHIs,
  one terminator, deterministic predecessor/successor sets, and source span;
  and
- `ScalarCfg` retains the function identity, parameters, entry ID, and ordered
  blocks.

Expose one fail-closed `parse_scalar_cfg(&Function) -> Result<ScalarCfg,
ParseError>` entry point. It may reuse the ADR-0281 scalar parser, but it must
not invent a second lexer or infer execution policy.

The parser validates the graph before returning it:

1. every block is nonempty and ends in exactly one supported terminator, with
   no instruction after a terminator;
2. PHIs are contiguous at the start of a block and each incoming predecessor
   appears exactly once;
3. every branch/switch/PHI label resolves within the same function;
4. the entry block has no predecessor;
5. each PHI predecessor set equals the block's unique CFG predecessor set;
6. conditional branches have an `i1` scalar operand;
7. switch scrutinee/case widths agree, case constants fit the width after
   signed spelling is normalized, and normalized constants are unique; and
8. `poison`/`undef`, unsupported terminators, unsupported scalar body
   instructions, and malformed or ambiguous constructs return stable located
   errors rather than being ignored.

Repeated destinations are legal (for example both conditional arms or several
switch cases may target one block), but the derived predecessor/successor lists
are stable first-occurrence sets. Metadata attachments are either retained
verbatim in a dedicated field or rejected explicitly; they are never consumed
as operands or silently discarded.

This slice does **not** execute the graph. In particular it does not bless the
legacy executor's unreachable-arm dropping. A following ADR must define checked
acyclic execution with path-conditioned value and definedness joins, branch and
switch condition UB, selected PHI incoming definedness, and explicit cycle
decline/`TransitionSystem` routing.

## Acceptance gates

Tests begin red and then require:

1. committed, unmodified clang 21 and rustc 1.97 CFG fixtures parse into the
   same typed conditional-diamond shape where the compilers converge;
2. exact typed cases cover unconditional/conditional `br`, multiline and
   single-line `switch`, scalar `ret`, `unreachable`, PHIs, quoted labels,
   numeric labels, negative case constants, repeated destinations, and retained
   metadata if metadata is admitted;
3. predecessor and successor sets are deterministic and preserve explicit
   true/false/default/case roles in the terminators;
4. missing targets, entry backedges, duplicate normalized switch constants,
   misplaced/duplicate/missing PHI incomings, terminator fallthrough, trailing
   instructions, non-`i1` branch conditions, width mismatches, poison/undef, and
   unsupported terminators return stable located errors without panicking;
5. each existing hand-written CFG fixture in `cross_ir_equivalence.rs` passes
   the new validator before its legacy equivalence proof runs;
6. 4,096 deterministic graph-shaped noise inputs cannot panic and repeated
   parses are byte-for-byte/debug-representation deterministic; and
7. the complete `axeyum-verify --all-features` suite, strict Clippy, strict
   rustdoc, formatting, and the repository link checker remain green.

The gates may become stricter before implementation observes the new compiler
fixtures; they may not be weakened in response to a failure.

## Consequences

Control structure becomes a reusable correctness boundary without prematurely
sharing Axeyum or Glaurung execution policy. Glaurung still cannot consume it:
ADR-0279's explicit-width LLIR hardening and a checked LLVM semantics profile
remain prerequisites, and ADR-0001 still defers a shared parser crate until a
second implemented consumer exists.

The next T5.1.2 increment is checked acyclic CFG reflection. Cycles remain the
`TransitionSystem` route; memory, pointers, general calls, exceptions,
`indirectbr`, `callbr`, `invoke`, `freeze`, and `undef` remain separate slices.

## References

- [LLVM Language Reference](https://llvm.org/docs/LangRef.html), `phi`, `ret`,
  `br`, `switch`, and `unreachable`.
- ADR-0279, ADR-0280, and ADR-0281.

## Alternatives

- Keep parsing control flow inside the executor: rejected because malformed
  graph structure remains indistinguishable from execution failure.
- Add checked execution in the same preregistered result: rejected because the
  graph invariants and path-definedness rules need independently reviewable
  gates; accepting syntax must not accidentally accept legacy semantics.
- Lower directly to Glaurung LLIR: rejected by ADR-0279 until LLIR carries the
  required width and successor contracts.
