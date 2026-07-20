# ADR-0295: Preregister checked LLVM direct-body call reflection

Status: accepted
Date: 2026-07-20

## Context

[ADR-0294](adr-0294-preregister-glaurung-llvm-loop-semantic-census.md)
retains three ordinary-call declines in the exact Glaurung loop population.
The two `tests/fixtures/android/pac.c` rows call the same defined scalar
function, `leaf(i32) -> i32`, from inside otherwise admitted self loops. The
`samples/source/c/hello.c` row first calls external `puts`, but the same
function also contains pointer memory plus `strlen` and `printf`; accepting
that one call would neither make the function executable nor establish a sound
effect model.

The observed `stage:kind` plurality selected an audit lane, not an
implementation. Ordinary-call grouping was post-observation and therefore
cannot retroactively authorize code. A new gate is required before extending
the typed syntax or loop transition relation.

[P5.2](../../plan/track-5-verified-systems/P5.2-contracts-modular.md)
ultimately requires calls to compose through explicit callee contracts, plus a
modular-versus-inlined differential. The smallest sound predecessor is not an
opaque return value or a syntax-only `Call` node: it is a checked direct-body
resolver that supplies exact inlined semantics as that later differential's
baseline.

## Decision

Preregister one opt-in checked direct-body call experiment over the two exact
Glaurung PAC loop callers before adding ordinary calls to the typed LLVM
profile.

The experiment may add a typed assigned direct scalar-call form and an explicit
resolver-backed loop entry point only under all of these boundaries:

1. The existing `reflect_single_latch_loop_checked` API continues to reject
   every ordinary call. There is no default resolver, uninterpreted return,
   zero value, nondeterministic witness, or effect-erasing fallback.
2. A call is eligible only when the caller supplies one exact defined LLVM
   function body for the named direct callee. The resolver validates a
   non-variadic scalar signature (`i1` through `i128` arguments and result),
   argument count and widths, and a unique callee name before lowering.
3. Callee execution reuses the checked value-plus-definedness reflector in the
   caller's arena. Parameter definedness, callee poison, immediate undefined
   behavior, and returned-value definedness all constrain the transition.
   Dropping `nuw`/`nsw`, `noundef`, or any other admitted semantic promise is a
   test failure, not a compatibility path.
4. Version one accepts only a straight-line, memory-free callee containing no
   further ordinary call. Missing bodies, recursion, nested calls, indirect
   calls, variadics, void calls, pointer arguments/results, signature drift,
   and external declarations fail with stable located errors.
5. The stored resolver inventory is deterministic and source-visible. Duplicate
   callee definitions fail closed; hash-map iteration order cannot affect
   rendered syntax, state layout, terms, or diagnostics.
6. Canonical rendering must preserve the complete admitted direct-call form and
   render/reparse to an equal typed CFG. Unsupported call attributes remain
   precise errors rather than being discarded.
7. `puts` remains rejected. This experiment models neither external effects nor
   the rest of `hello.c`'s pointer/call surface and makes no cross-source
   acceptance claim.

This is a T5.1.2/T5.1.4 inlining baseline and a prerequisite for T5.2.4. It is
not `#[requires]`/`#[ensures]`, modular verification, a general LLVM module
executor, or evidence that two settings are distinct algorithms.

## Frozen evidence gates

Implementation is admitted only if one committed test/evidence bundle passes
all of the following without weakening after result observation:

1. The exact clang-21 `-O1 -fno-unroll-loops -fno-vectorize
   -fno-slp-vectorize -fno-strict-aliasing` `pac.c` source, compiler identity,
   compile arguments, source hash, full-module hash, both caller-function
   hashes, and `leaf` hash are registered and revalidated before every exact
   fixture test.
2. `compute` and `main` both fail through the unchanged default API at their
   located `@leaf` calls and both reach checked canonical loop reflection only
   when the registered `leaf` body is explicitly supplied.
3. The reflected `leaf` result and definedness equal an independently built
   `x*x+1` specification including multiplication signed overflow plus
   addition unsigned and signed overflow. The
   automatic caller transition relation equals an independently built
   recurrence formula; do not validate the reflector with a second call to the
   reflector.
4. Deterministic exhaustive/fuzz comparison covers at least 100,000
   `(caller, pre-state, parameter)` tuples with `DISAGREE = 0`, including
   defined executions, multiplication overflow, addition overflow, and branch
   boundaries. Source replay is required for every claimed reachable state;
   undefined C executions are classified, not run and counted as agreement.
5. Unbounded and bounded safety exercise the resulting transition systems.
   Any reachable abstract recurrence witness used in evidence is replayed
   against the exact source, preserving ADR-0291's exit-over-approximation
   boundary.
6. Negative tests cover a missing body, duplicate body, wrong callee name,
   argument-count and width mismatch, result-width mismatch, pointer/variadic/
   void/indirect calls, nested call or recursion, unsupported call attributes,
   and a semantic mutation of `leaf`. Every decline retains a stable class and
   a precise location.
7. The standing reflection semantics gate, complete `axeyum-verify` tests and
   doctests, strict all-target/all-feature Clippy, warning-denied rustdoc,
   formatting, and documentation links pass.

The two PAC rows are one-source evidence. They may prove that the mechanism is
real and unblock a later modular differential, but they do not satisfy a
cross-source demand threshold or alter ADR-0294's 0/12 accepted census. Any
formal census update requires a separately preregistered producer and complete
12/12 accounting.

## Evidence before implementation

The registered Glaurung revision `403a5c5c1f6c5152fef6cefd0d78c3eb90d3888f`
compiles `leaf` to a straight-line `mul nsw` followed by `add nuw nsw`, and
both loop callers contain one assigned `tail call i32 @leaf(i32 noundef ...)`.
They have no other instruction-class rejection before loop reflection.

By contrast, `hello.c::main` calls external `puts` before its loop and later
uses pointer GEP/load, `strlen`, global i32 load/store, and variadic `printf`.
An ignored-return or effect-free `puts` rule would therefore be both
semantically ungrounded and incapable of admitting that function. The exact
evidence selects the internal direct-body experiment and rejects an external
call shim.

The existing checked scalar reflector already owns the required callee
value/definedness semantics. The new work is bounded to typed direct-call
syntax, explicit resolution, transition composition, and independent gates;
it must not fork arithmetic or poison semantics.

## Accepted result

The frozen experiment passes without widening its scope:

- `DirectCallResolver` accepts only explicitly supplied, unique, non-variadic,
  scalar, straight-line, memory-free, call-free bodies. The new
  `reflect_single_latch_loop_with_direct_calls_checked` entry point is opt-in;
  the pre-existing checked loop APIs still reject ordinary calls as
  `UnsupportedCall`.
- The exact Glaurung revision, PAC source, clang-21 command, complete LLVM
  module, and `leaf`/`compute`/`main` function hashes are registered in
  `glaurung-llvm-direct-call-v1.json`. Offline validation and live reproduction
  against the registered Glaurung tree both pass.
- Both PAC callers reflect with the supplied `leaf` body. Their automatic
  `init`, `trans`, and `bad` terms equal independently constructed formulas.
  The deterministic comparison covers 50,000 tuples per caller, 100,000 total,
  with zero disagreements and explicit multiplication, caller-addition, and
  counter-overflow coverage.
- Immediate UB in a callee constrains the caller even when its result is
  unused. An unused poison return remains lazy until observed, preserving the
  checked reflector's LLVM value/definedness distinction.
- The complete missing/duplicate/signature/type/attribute/indirect/nested/
  memory/semantic-mutation boundary fails closed or disproves equivalence as
  preregistered. Canonical direct-call syntax render/reparses exactly.
- The standing gate now owns 63 checked semantic variants in 15 evidence
  groups and runs nine binaries / 88 tests. The focused suite, checker mutation
  tests, complete Verify tests and doctests, strict Clippy, warning-denied
  rustdoc, formatting, provenance reproduction, and documentation links pass.

This accepts one-source inlined baseline evidence. It does not revise
ADR-0294's historical 0/12 census, admit `puts` or external effects, or close
P5.2. The next trajectory is contract composition measured against this exact
inlined baseline, not another syntax-only call widening.

## Alternatives

- **Parse ordinary calls and reject them later:** rejected as the syntax-only
  shim ADR-0294 explicitly forbids.
- **Treat calls as fresh unconstrained results:** rejected because this drops
  callee preconditions, poison, immediate UB, and effects; it could prove false
  invariants or manufacture transitions.
- **Assume external calls with unused results are harmless:** rejected because
  LLVM calls may have memory, control, termination, and undefined-behavior
  effects. `puts` also does not unlock the measured function.
- **Inline every function from a whole module automatically:** deferred; it
  expands selection, recursion, linkage, globals, memory, and resource policy
  before the explicit boundary is tested.
- **Start full P5.2 contracts now:** deferred until this exact inlined baseline
  exists. T5.2.4 requires both sides of the modular-versus-inlined comparison,
  and annotations must not be designed around one post-hoc Glaurung function.

## Consequences

If the gates pass, Axeyum gains a sound, opt-in direct-call execution baseline
and the two exact PAC loop declines become executable without weakening the
default frontend. P5.2 then has a concrete inlined oracle against which a
contract-composed call can be compared.

If any semantic or reproduction gate fails, remove the candidate typed-call
and resolver implementation and retain the failure. `puts`, external effects,
general memory, recursion, and modular contracts remain separate work in all
cases.
