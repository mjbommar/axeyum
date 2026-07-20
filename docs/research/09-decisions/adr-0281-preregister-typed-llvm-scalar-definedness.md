# ADR-0281: Preregister typed LLVM scalar instructions and definedness

Status: accepted
Date: 2026-07-19

Result state: interface and tests frozen before implementation

## Context

ADR-0280 establishes a non-panicking function, parameter, block, and source-line
boundary, but each instruction is still an untyped string. The compatibility
reflector tokenizes those strings repeatedly and silently discards LLVM flags
such as `nuw`, `nsw`, `exact`, `disjoint`, and `nneg`. That behavior is an
explicit prototype limitation, not an acceptable checked front end: these flags
produce poison when their promises are violated, shifts also produce poison for
an out-of-range amount, and `select` propagates poison only from its condition
and selected arm.

The publication strategy leads with strict translation and fail-closed
diagnostics. The next parser slice must therefore make the existing scalar
fragment typed and expose its definedness, rather than merely replacing one
string split with another.

## Decision

Extend `reflect::llvm::syntax` with a typed, span-carrying representation for
the straight-line scalar integer fragment already lowered by Axeyum:

- assigned integer binary operations (`add`, `sub`, `mul`, `and`, `or`, `xor`,
  `shl`, `lshr`, `ashr`, `udiv`, `sdiv`, `urem`, and `srem`);
- `icmp`, `select`, `zext`, `sext`, and `trunc`;
- direct `llvm.umin` and `llvm.umax` scalar intrinsic calls; and
- scalar `ret`.

The typed form records destination and operand identities, integer widths,
opcodes/predicates, semantic flags, and the original instruction span. Add an
explicit unsupported/malformed instruction error class. Unknown opcodes,
non-scalar types, `undef`, `poison`, malformed arity, invalid flag/opcode
combinations, and width-inconsistent syntax fail closed with a located error.
Do not reinterpret them as an existing operation.

Add a checked straight-line reflection API returning a value term together with
a Boolean `defined` term. Every SSA binding carries both. The definedness rules
for this slice are:

- ordinary operations require defined operands;
- `nuw`/`nsw` on add/sub/mul require the matching no-overflow predicate;
- every shift requires an amount smaller than the operand width;
- `shl nuw`/`shl nsw` and right-shift `exact` require lossless reverse-shift
  identities;
- `or disjoint` requires the operands' bitwise intersection to be zero;
- `zext nneg` requires a non-negative source; `trunc nuw`/`trunc nsw` require
  lossless zero/sign extension of the result;
- division/remainder require a nonzero divisor, and signed division/remainder
  exclude `MIN / -1`; `exact` division additionally requires zero remainder;
  and
- `select` requires a defined condition and only the chosen value's
  definedness, not both arms'.

Legacy panic-oriented APIs remain compatibility surfaces in this slice. Migrate
at least one existing scalar reflection proof to the checked API and prove its
definedness rather than silently dropping flags.

## Acceptance gates

Tests begin red and then require:

1. committed, unmodified clang 21 and rustc 1.97 textual LLVM fixtures parse
   into identical typed scalar instruction shapes where the compilers converge;
2. every supported opcode, predicate, cast, and flag has an exact typed-parser
   case, including quoted/numeric SSA names and negative constants;
3. malformed arity/type/width/flag combinations and an unsupported opcode return
   stable, located errors without panicking;
4. checked reflection reproduces the existing modular value terms on the
   flag-free fragment;
5. safe compiler-emitted `nuw`/`nsw`/`disjoint` chains prove `defined` for every
   input, while one violating witness makes each corresponding predicate false;
6. the existing `day`-shape select proves defined for every input even though
   its unselected `add nsw` arm can be poison;
7. an out-of-range shift, zero divisor, signed `MIN / -1`, and inexact division
   are represented in `defined` and never inherit SMT-LIB's total BV result as
   an LLVM-defined execution;
8. one existing LLVM reflection proof migrates to the checked API with its
   definedness premise/gate explicit;
9. deterministic noise cannot panic either typed parsing or checked reflection;
   and
10. all existing LLVM/cross-IR suites, strict Clippy, rustdoc, and the repository
    link checker remain green.

The gates may become stricter before implementation observes external corpus
results; they may not be weakened in response to a failure.

## Consequences

This slice turns LLVM's current scalar compatibility path into a usable
correctness boundary and makes poison obligations visible to callers. It does
not yet type or migrate `br`/`phi`/`switch`, memory, pointers, calls other than
the two named intrinsics, vectors/aggregates, `freeze`, `undef`, or module-wide
symbol resolution. Those remain explicit later T5.1.2/T5.1.5 increments rather
than being guessed from strings.

The typed representation remains in `axeyum-verify`; ADR-0001 still forbids a
new parser crate until a second implemented consumer proves the boundary.

## References

- [LLVM Language Reference](https://llvm.org/docs/LangRef.html), integer,
  conversion, comparison, `select`, and poison semantics.
- [LLVM IR Undefined Behavior Manual](https://llvm.org/docs/UndefinedBehavior.html).
- ADR-0279 and ADR-0280.

## Alternatives

- Parse opcodes but continue discarding flags: rejected because it preserves the
  exact silent semantic gap this track is meant to close.
- Reject every flagged compiler instruction: rejected because the existing
  QF_BV term language already expresses the bounded definedness obligations.
- Model all LLVM poison, `undef`, memory, and control flow at once: deferred;
  those semantics need separate typed syntax and acceptance gates.
