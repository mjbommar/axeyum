# ADR-0286: Accept checked bounded LLVM byte memory

Status: accepted
Date: 2026-07-20

Result state: accepted; all frozen gates pass

## Context

ADR-0279 defers a general Glaurung LLVM importer until Axeyum has one structured,
fail-closed LLVM syntax and semantics boundary and Glaurung's executable LLIR
has explicit widths and successors. ADR-0280 through ADR-0284 now provide that
boundary for scalar acyclic control flow: located parsing, typed instructions,
explicit value definedness, validated PHIs and terminators, checked path
execution, and canonical rendering. Memory is the next named prerequisite.

The existing Axeyum test prototypes already establish the useful reduction for
small packet/header code. They map one pointer parameter to a fixed vector of
symbolic bytes, track byte offsets through `getelementptr`, and lower a symbolic
byte load to an ITE table. Those prototypes are line parsers, panic on rejected
input, do not model stores, and report bounds as a separate test value rather
than LLVM definedness. They cannot be reused as a checked consumer boundary.

The live Glaurung audit at `403a5c5` independently confirms that byte-addressed
memory is the compatible seam: `Memory<D>` stores domain-generic bytes and
assembles wider loads/stores explicitly. It also confirms why this ADR must not
claim an importer. Current LLIR still infers some temporary widths, encodes a
false successor through machine-address fallthrough, and has its own unmapped-
memory policy. LLVM object bounds, poison, alignment, lifetime, and provenance
cannot be inherited from that policy.

LLVM distinguishes deferred poison from immediate undefined behavior. A GEP
whose `inbounds` or wrap promise fails yields a poison pointer; dereferencing a
poison pointer is immediate UB. An inbounds pointer may designate one byte past
an object, but a load or store there is still out of bounds. Storing a poison
value is permitted and writes poison; loading that byte later yields poison.
The checked reflector must preserve each distinction instead of mapping an
unmodeled or invalid byte to zero.

## Decision

Add one explicit **bounded initialized byte-region** profile to the checked
acyclic LLVM CFG path. It is a semantic profile with a visible precondition, not
general pointer or address-space semantics.

The initial API accepts exactly one `ptr` function parameter and binds it to one
live, non-null, non-aliasing allocation of 1 through 256 initialized bytes. Each
input byte is a fresh defined BV8 symbol. All remaining parameters and the
return remain the existing scalar `i1` through `i128` profile. The result owns:

- the term arena and scalar parameter symbols;
- the pointer parameter identity and input-byte symbols;
- the final byte values and their per-byte definedness after path-conditioned
  stores; and
- the returned [`DefinedValue`](../../../crates/axeyum-verify/src/reflect/llvm/checked.rs).

The structured instruction layer gains located typed forms for only:

- `getelementptr inbounds [nuw] i8, ptr %base, i64 <index>` with exactly one
  scalar index;
- non-atomic, non-volatile `load i8, ptr %p, align 1`; and
- non-atomic, non-volatile `store i8 <value>, ptr %p, align 1`.

Direct loads/stores from the bound base pointer are allowed. A derived pointer
retains a region identity, a BV64 byte offset, and a Boolean pointer-definedness
term. GEP offset arithmetic is LLVM's signed index interpretation. `inbounds`
requires every resulting offset to be in the closed range `0..=len`; explicit
`nuw` additionally requires unsigned addition not to wrap. One-past is therefore
a defined pointer but not a valid byte access.

A load or store adds immediate-execution obligations that its pointer is
defined and its byte offset is strictly below the region length. A load's
ordinary result definedness is the selected byte's definedness. A store does not
require the stored value to be defined: it writes both the modular byte value
and its definedness predicate. Symbolic loads and stores use deterministic ITE
tables over the bounded byte vector. Branches clone memory state and join every
final byte value and definedness predicate under the same selected path used for
the scalar return.

Extend canonical rendering to the admitted typed memory forms, so the accepted
profile retains the parse-print-parse and semantic-replay boundary established
by ADR-0284. Existing scalar entry points remain source-compatible. They decline
pointer parameters or memory operations rather than fabricating a region.

Fail closed on zero/oversized regions, zero or multiple pointer parameters,
non-`i8` element/access types, non-`i64` GEP indices, multiple GEP indices,
non-`inbounds` GEP, `nusw` without this profile's explicit proof, alignment
greater than one, atomic/volatile accesses, semantic load metadata, pointer
PHIs/selects/comparisons, `alloca`, globals, null, pointer casts, lifetime
intrinsics, calls, aliasing, wide/endian-sensitive accesses, loops, and any
address space other than the default. No rejected form is approximated as a
byte access.

This ADR does not modify Glaurung, create a shared parser crate, add LLVM module
resolution, or complete T5.1.5. MIR array writes, wide memory, multiple/aliasing
objects, loops, and the executable-LLIR contract remain separately gated.

## Pre-implementation acceptance gates

Tests begin red only after this zero-row ADR is committed. The implementation
must then satisfy all of the following:

1. committed unmodified compiler-emitted fixtures for a fixed-offset read, a
   symbolic-index read, and a store/load round trip parse into exact typed memory
   forms; when `llvm-as` is available, both source and canonical output assemble;
2. parse-render-parse preserves the typed CFG projection byte-for-byte on a
   second render, including GEP flags, pointer identities, access alignment,
   and store source operands;
3. the existing big-endian two-byte read and IPv4-IHL value proofs migrate from
   the panic-oriented line parser to the checked memory API and prove returned
   definedness under the registered region size;
4. a symbolic masked read over four bytes proves unconditionally defined and
   value-correct, while the unmasked form's definedness is exactly `index < 4`
   and has a replay-checked `index = 4` undefined witness;
5. a symbolic store followed by a load at the same offset proves the returned
   byte equals the stored byte exactly when the access is in bounds, and the
   exposed final memory has last-writer-wins behavior at that offset while all
   other bytes are preserved;
6. storing an undefined/poison byte does not by itself make a later constant
   return undefined, but loading the stored byte propagates poison; using a
   poison or one-past pointer for either access makes execution undefined;
7. unused GEP poison remains deferred, selected versus unselected out-of-bounds
   accesses are path-sensitive, and final memory from a branch joins only the
   selected arm's writes;
8. direct base loads, constant positive offsets, negative/out-of-range offsets,
   explicit `nuw`, quoted/numeric SSA names, duplicate SSA definitions, and
   undefined pointer uses have exact focused tests;
9. every excluded construct above returns a stable located syntax/reflection
   error without panicking; region configuration errors have distinct stable
   classes and do not allocate a partial reflection;
10. deterministic memory-shaped noise cannot panic parsing, rendering, or
    checked execution, and repeated reflections have identical typed projections
    and term structure;
11. the new proofs replay their SAT witnesses against the original bounded byte
    model, and no `sat` claim is accepted from an output byte or scalar value
    without its definedness condition; and
12. all existing LLVM and cross-IR suites, the complete
    `axeyum-verify --all-features` suite, workspace formatting, strict Clippy,
    strict rustdoc, and the repository link checker remain green.

The gates may be strengthened before any new compiler fixture is generated or
any implementation test is run. They may not be weakened after observing a
failure.

## Result

The accepted implementation adds `BoundedMemoryConfig` and
`reflect_bounded_memory_cfg_checked` without broadening the existing scalar
entry points. The owned result exposes collision-safe initialized BV8 input
symbols, path-joined final bytes with per-byte definedness, and the scalar
return with whole-execution definedness. Final memory is explicitly meaningful
only under that whole-execution predicate.

The typed syntax and canonical writer now own the admitted GEP, load, and store
forms. Checked execution keeps pointer poison separate from immediate access
UB, admits a defined one-past pointer but not a one-past access, preserves
poison through stores and later loads, and joins writes only from the selected
acyclic path. Unsupported region shapes, address spaces, widths, alignments,
flags, memory operations, pointer uses, and SSA graphs fail closed with stable
located errors.

Three committed clang 21.1.8 fixtures cover a fixed read, masked symbolic read,
and mem2reg-resistant store/load round trip. The 11-test memory suite covers
their typed/canonical/optional-`llvm-as` boundary, exact fixed and symbolic
proofs, replay of the `index = 4` undefined witness, final-memory behavior,
poison versus UB, one-past and wrapping promises, selected-arm writes, naming
collisions, rejection classes, and deterministic noise. The 20 historical LLVM
reflection tests now route their byte-load proofs and fuzz checks through the
checked memory API instead of private line parsers.

The dedicated memory suite (11/11), migrated LLVM reflection suite (20/20),
complete `axeyum-verify --all-features` suite and doctests, all ordinary
workspace tests, workspace formatting, strict workspace Clippy/rustdoc, and the
repository link checker pass. The two EVM doctests that initially hit an
environmental linker `SIGBUS` under `/tmp` pass unchanged with `TMPDIR` on the
workspace filesystem.

## Consequences

Axeyum now has one small but honest compiler-memory boundary that matches the
byte-addressed center already present in Glaurung and keeps strict
sort/definedness diagnostics as the publication-strength contribution. The
profile retires duplicate test-only memory parsers and exposes store effects
for later MIR and LLIR differentials.

It intentionally trades breadth for a checkable object contract. A future
general memory profile must make allocation identity, aliases, alignment,
endianness, initialization, lifetime, and provenance explicit rather than
silently broadening this bounded region.

## References

- [LLVM Language Reference](https://llvm.org/docs/LangRef.html),
  `getelementptr`, `load`, `store`, and poison values.
- [LLVM IR Undefined Behavior Manual](https://llvm.org/docs/UndefinedBehavior.html).
- T5.1.5 in the Track 5 reflection plan.
- ADR-0010 and ADR-0279 through ADR-0284.

## Alternatives

- Reuse the line-oriented test reflectors: rejected because they panic, omit
  stores, and keep bounds outside LLVM definedness.
- Start with an unbounded SMT array: rejected for this first slice because it
  loses the allocation bound needed to distinguish one-past GEP from a valid
  access and would not preserve the existing QF_BV/WASM profile.
- Treat absent/unmapped bytes as zero: rejected because it fabricates a defined
  LLVM value and conflicts with both the publication correctness thesis and
  Glaurung's separate environment policy.
- Add general provenance, wide accesses, stack allocation, globals, and aliases
  together: deferred; each changes the semantic contract and needs independent
  fixtures and gates.
