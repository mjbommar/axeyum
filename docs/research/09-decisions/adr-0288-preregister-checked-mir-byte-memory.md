# ADR-0288: Preregister checked MIR byte-memory CFG reflection

Status: accepted
Date: 2026-07-20

Result state: accepted; all frozen gates pass

## Context

ADR-0287 authenticates one exact `rustc -Zunpretty=mir` artifact and captures a
real array store followed by a checked read. It deliberately adds no semantics.
The only current MIR reflector remains a panic-oriented line executor. It
assumes a preceding MIR `assert` guards every array read, chooses an arbitrary
element value out of range, cannot parse array destinations, and does not return
final memory. Extending that executor with one store arm would preserve an
unsound artifact boundary and make branch-local writes impossible to join.

ADR-0286 already supplies the comparison contract on LLVM: one initialized
bounded byte region, typed accesses, explicit definedness, final memory, and a
checked store/load proof. T5.1.5 requires the analogous MIR proof before its
both-IR exit can close. Rust MIR models bounds failure as a panic edge rather
than LLVM poison/undefined behavior, so the result must retain a first-class
panic predicate instead of copying the LLVM definedness API.

The registered compiler target is `x86_64-unknown-linux-gnu`; therefore MIR's
target-dependent `usize` is 64 bits for this artifact. That target width must be
an explicit checked input, not inferred from the machine running the reflector.

## Decision

Add a new structured checked path under `reflect::mir`, alongside but separate
from the legacy compatibility APIs. It consumes the complete authenticated MIR
module plus one function name and returns `Result`; no public checked call may
panic on source text.

The initial located syntax owns exactly:

- one selected `fn` item from a multi-item `-Zunpretty=mir` module;
- typed parameters, return local, local declarations, ordered `bbN` blocks,
  source spans, and unique block labels;
- scalar `bool`, `u8..u128`, `i8..i128`, `usize`, and `isize` types plus one
  `[u8; N]` parameter with `1 <= N <= 256`;
- `copy`/`move` locals, typed integer/Boolean constants, `Lt`, `Eq`, `BitAnd`,
  and scalar `Use` assignments;
- byte-array reads `copy _A[_I]` and stores `_A[_I] = copy _V`;
- `assert(...)->[success: bbN, unwind continue]`, `goto`, Boolean/integer
  `switchInt`, and `return`; and
- ignorable debug declarations and `StorageLive`/`StorageDead` statements only
  where their syntax is recognized.

Everything else is rejected with a stable located syntax or reflection class.
In particular, do not reinterpret unsupported projections, references,
aggregates, calls, drops, unwinds, subslices, non-byte arrays, indirect indices,
raw pointers, loops, or target-width ambiguity.

The checked memory API requires exactly one `[u8; N]` parameter. It declares N
fresh, initialized BV8 input symbols; scalar parameters are fresh defined
symbols at their parsed widths. A configuration names the selected function and
the target `usize` width. The registered fixture must use 64, and a configuration
that conflicts with the authenticated target fails before reflection.

Every array read or store independently contributes an immediate panic
condition `index >= N`, whether or not a preceding MIR `assert` exists or has
the expected formula. This removes the legacy guard-trust assumption. Reads use
a deterministic bounded ITE table. Stores update every byte with an index-
selected ITE and use last-writer-wins semantics. Returned values and final memory
are meaningful only when the result's whole-execution panic predicate is false.

Checked execution validates an acyclic CFG, follows `assert` success edges,
and executes every `switchInt` successor from a cloned state. It joins returned
values, panic predicates, and every final byte under the exact typed switch
guard. Cycles and a fixed execution-expansion limit return errors rather than
panicking or hanging.

Extend the authenticated Rust source with one conditional-store function and
regenerate it only through ADR-0287's exact-toolchain path after this ADR is
committed. Preserve the existing legacy APIs and their callers until tests are
migrated deliberately; do not silently change their panic contract in this
slice.

## Pre-implementation acceptance gates

Tests, source changes, and regenerated MIR begin only after this zero-row ADR is
committed. The implementation must then satisfy all of the following:

1. the authenticated source gains one `conditional_store` function whose true
   arm writes and whose false arm preserves the array; two regeneration captures
   and a required third replay are byte-identical, with reviewed hash/provenance
   changes and no normalization;
2. the structured parser selects each named function from the full raw module,
   owns exact parameter/local/block/statement/terminator types and nonempty
   spans, and rejects missing/duplicate function names or block labels;
3. malformed or unsupported source, deterministic structured noise, truncated
   blocks, invalid locals/types/constants, undefined targets, cycles, and the
   execution bound return stable errors and never unwind;
4. a read or store without a preceding bounds assertion still has panic exactly
   when `index >= N`; a wrong or unrelated assertion cannot suppress the access
   predicate;
5. the authenticated `store_then_load` reflection proves `!panic` exactly when
   `index < 4`, returns the stored byte under that condition, updates exactly
   the selected final byte, and preserves all others;
6. the authenticated conditional store proves path-sensitive memory: on the
   true arm the selected byte becomes the input value, on the false arm every
   byte is preserved, and out-of-bounds panic occurs only on paths that execute
   an access;
7. the existing checked/clamped bounds proofs migrate from embedded MIR strings
   to named functions in the authenticated module, preserve exact panic/value
   results, and replay both in-bounds values and one solver-produced OOB panic
   against the real Rust functions;
8. the MIR and accepted LLVM roundtrip reflections separately prove the same
   bounded store/load specification with the same 64-bit index and four-byte
   region, and sampled concrete executions agree with the real Rust function;
9. all result-value and final-memory claims are explicitly guarded by
   `!panic`; no SAT witness is accepted without replay against source behavior;
10. zero/more-than-256-byte regions, multiple arrays, non-`u8` elements,
    mismatched target widths, invalid scalar widths/signedness, duplicate or
    undefined locals, and unsupported memory/control forms fail with distinct
    stable classes before a partial result is returned;
11. repeated parsing/reflection has identical typed projections and rendered
    Axeyum terms, memory symbol names cannot collide with scalar/source locals,
    and the default/native/MSRV/WASM dependency surfaces remain unchanged; and
12. focused syntax/semantic/replay tests, migrated bounds tests, the complete
    `axeyum-verify --all-features` suite, workspace formatting, strict
    Clippy/rustdoc, ADR-0287 fixture checks, and repository links pass.

The gates may be strengthened before the source is changed or the first red
semantic test is run. They may not be weakened after any regenerated artifact
or test outcome is observed.

## Result

The authenticated source now contains `conditional_store`, and exact
regeneration expands the raw compiler artifact from 2,304 to 3,262 bytes and
from four to five named functions. Two regeneration captures plus required
replay are byte-identical under the registered rustc/LLVM identity. The source
and MIR hashes are respectively
`2f637e370ba1d673c6d4bbfd545e8ce151ebd989199a2bf903b9c2a382f1bd61`
and
`b8eccaf7ab795c0bfb01f20704cac3c67d7b4fc6e86dd5c8845aa21e81ad3d14`;
provenance remains unchanged.

`reflect::mir::syntax` selects one named function from the complete artifact
and owns located parameters, locals, blocks, scalar/array types, operands,
assignments, byte reads/stores, and admitted terminators. `reflect::mir::checked`
is a separate `Result` API with explicit 64-bit target configuration, stable
syntax/reflection error classes, initialized byte symbols, acyclic bounded
execution, and path joins over result, panic, and every final byte. The legacy
panic-oriented compatibility API remains unchanged.

Every read and write constructs its own unsigned `index < N` predicate and
adds its negation to `panic`; removing the compiler assertion or replacing it
with an unrelated true assertion does not change that access obligation. The
authenticated straight-line function proves `panic <-> index >= 4`, returns
the stored byte under `!panic`, and updates exactly the selected byte. The
conditional function proves `panic <-> take && index >= 4`, preserves all
bytes when `take` is false, and joins the selected write only on the true path.
Return and final-memory claims in the tests are guarded by `!panic` and sampled
against the real Rust functions.

Seven dedicated tests cover typed full-module selection, missing/duplicate
names, exact straight-line and conditional memory semantics, absent/wrong
assertions, source replay, deterministic symbols/terms, malformed/noisy input,
region/type/local/control rejection classes, cycles, and execution expansion.
The three existing bounds tests now consume authenticated named functions
instead of embedded MIR strings while preserving the solver-produced OOB
witness replay. The MIR and accepted LLVM fixtures separately prove the same
four-byte, 64-bit-index store/load contract.

The dedicated and migrated tests, exact fixture verification/replay, eight
fixture-checker adversarial tests, complete `axeyum-verify --all-features`
suite, formatting, strict Clippy, rustdoc, and repository links pass. No Cargo
dependency, default feature, native, MSRV, or WASM surface changes.

## Consequences

This slice will close the first honest MIR half of T5.1.5: real compiler text,
strict types, explicit access safety, stores, branch joins, final memory, source
replay, and an LLVM-aligned specification. It will also remove the existing
bounds tests' dependence on embedded hand-copied MIR.

It does not complete T5.1.3's arbitrary target-crate selection, replace all
legacy MIR reflection, model general Rust places/references/borrows, support
loops/unwinds/drops/calls, add wide/endian-sensitive memory, or adopt
`stable_mir`. Those remain separately evidence-gated.

## Alternatives

- Add store syntax to `exec_stmt`: rejected because the legacy executor panics,
  trusts external assertions for safety, and cannot return or join memory.
- Reuse the checked LLVM AST: rejected because Rust MIR panic/unwind semantics,
  local places, and target-dependent integer types are not LLVM poison/pointers.
- Parse only the extracted `store_then_load` substring: rejected because the
  point of ADR-0287 is to consume the authenticated multi-item compiler output
  and detect selection/drift errors.
- Defer branch joins: rejected because a straight-line-only store model would
  not establish the memory-state behavior needed by real control flow and could
  not validate that final bytes follow the selected path.

## References

- ADR-0286 and ADR-0287.
- T5.1.3 and T5.1.5 in the Track 5 reflection plan.
- `docs/consumer-track/verify/reflect-common-abstraction.md`.
- `docs/consumer-track/verify/real-rust-frontend.md`.
