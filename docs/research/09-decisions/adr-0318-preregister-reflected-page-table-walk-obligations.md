# ADR-0318: Preregister reflected page-table walk obligations

Status: proposed
Date: 2026-07-21

## Context

P5.2 v1 is closed. The next recommended Track 5 phase is P5.3, whose remaining
first obligation family is bounded memory and page-table-style index math.
ADR-0288 already accepts the required checked MIR substrate: one initialized
byte-array region, typed scalar parameters, casts, shifts, masks, checked
dynamic reads, explicit panic predicates, and bounded acyclic control. A new
memory model or solver feature is not justified unless a real compiler shape
proves that substrate insufficient.

A zero-row probe was therefore compiled with the registered
`nightly-2026-05-01` rustc before this decision. Two good functions and three
deliberately broken controls use only:

- one `[u8; 4]` table and one `u8` virtual address;
- `Shr`, `BitAnd`, `Lt`, `IntToInt`, `assert`, array reads, and `return`;
- a level-one index `(virtual_address >> 6) & 3`;
- a level-two index `table[level1] & 3`;
- an aligned frame result `table[level2] & 0xfc`; and
- effective permissions `(parent & table[level2]) & 3`.

The exact compiler MIR stays inside ADR-0288's accepted syntax and semantics.
The shift and both reads carry compiler assertions, but the checked reflector
must continue deriving each access predicate itself. No new IR operator,
reflection syntax, memory representation, solver route, or public API is
needed.

## Proposed decision

Preregister one bounded two-level byte-table experiment as T5.3.2's v1 cell.
Extend the existing excluded `mir-target-crate` Cargo fixture with the five
probe functions above. Capture the complete raw MIR through the existing
typed `axeyum-mir-build` checked-memory profile, registered Cargo/rustc pair,
explicit package/target/function selection, 64-bit target width, fresh target
directory, and locked build. Commit raw bytes and source/compiler/argument
provenance; do not normalize compiler output or infer trust from hashes.

Reflect `walk_frame` and `walk_permissions` independently from that artifact.
The good obligations are:

1. both complete without panic for every table and virtual address;
2. every derived level index is in `[0, 4)`;
3. `walk_frame & 3 == 0` for every input;
4. the permission result is an exact subset of both the parent and selected
   leaf permission bits; and
5. reflected results equal the real Rust functions on every sampled row.

The table is an intentionally tiny finite model, not an MMU claim. Its two
low entry bits encode the next index/permissions; its upper six bits encode a
four-byte-aligned frame token. The experiment establishes obligation shape and
replay discipline only.

## Frozen evidence gates

Implementation is admitted only when all gates pass.

1. Commit this zero-row ADR and the exact compiler-shape audit before changing
   fixture source, capture bytes, or tests.
2. Two fresh owning-Cargo captures are byte-identical; the committed raw MIR is
   a third exact copy. Provenance binds manifest, lockfile, source, raw bytes,
   compiler/Cargo identities, ordered arguments, selected package/target/
   function, profile, and target width.
3. A stable-CI validator checks all committed hashes and typed provenance.
   When the registered nightly is available, one command reproduces the raw
   artifact byte-for-byte. Wrong compiler/selection, tamper, malformed MIR,
   failed output, or existing output leaves no credited artifact.
4. Both good functions parse through the existing checked-memory surface with
   exactly one four-byte input region. Their parameter, result, panic, and
   input-memory terms are deterministic across repeated reflection.
5. Solver proofs establish universal panic freedom, exact aligned-frame
   masking, exact permission intersection, and permission subset of both the
   selected parent and leaf. Every proved goal uses reflected terms from the
   committed compiler artifact, not a hand-built implementation formula.
6. `broken_walk_index` yields a replay-checked out-of-bounds panic witness.
   `broken_frame_unaligned` yields a replay-checked low-bit alignment witness.
   `broken_permissions_escalate` yields a replay-checked parent-permission
   escalation witness. Each neighbor/good control remains clean.
7. A deterministic fixed sampler covers all 256 virtual addresses across a
   preregistered table corpus including zero, all-ones, identity-index, mixed
   frame/permission, and witness-neighbor tables. It records zero reflection/
   Rust disagreement, evaluation error, or dropped row.
8. Mutation tests remove an index mask, frame mask, and parent intersection;
   swap parent/leaf selection; alter the region size/target width; and corrupt
   a compiler assertion. Each is either semantically refuted with replay or
   rejected with a stable class. Compiler assertions cannot suppress the
   reflector-owned access predicate.
9. Record proof and sampled-replay wall times separately. Make no performance,
   scalability, real-address-translation, cache, TLB, aliasing, concurrency,
   or external-target claim.
10. Existing ADR-0287/0288/0289 fixtures, checked-memory default behavior,
    source-contract/MIR bridge, dependency/features, unsafe policy, MSRV, and
    WASM surface remain unchanged. Focused tests, the complete package and
    doctests, strict Clippy/rustdoc, reflection semantics gate, formatting,
    links, and the one-job 4 GiB/OOM audit pass.

No gate may be weakened after observing the first fixture change, committed
capture, solver result, or replay population.

## Rejected alternatives

- **Add a general page-table memory model first.** Rejected: the compiler probe
  fits the existing checked finite byte-region model.
- **Prove hand-built table terms.** Rejected: T5.3 requires reflected code and
  source-replayed counterexamples.
- **Use only sampled tests.** Rejected: sampling corroborates execution, while
  the universal invariants are solver proofs over every table/address input.
- **Call the four-entry encoding an MMU model.** Rejected: no physical memory,
  aliasing, privilege mode, TLB, concurrency, or architectural page-table
  semantics is represented.
- **Begin with Asterinas or another external target.** Deferred to P5.5 after
  this obligation shape is independently green and measured.

## Consequences

- A positive result closes T5.3.2 only as a bounded reflected obligation cell.
- A negative result records the exact parser/semantic/proof boundary and may
  select a later ADR; it does not authorize reactive widening.
- T5.3.1's branch-only constant-time residual and T5.3.3 FSM refinement remain
  independent work.

## References

- ADR-0287 through ADR-0289: authenticated MIR capture and checked byte memory.
- ADR-0317: authenticated source-contract to checked-MIR summary binding.
- `docs/plan/track-5-verified-systems/P5.3-kernel-theories.md`.
- `crates/axeyum-verify/src/reflect/mir/checked.rs`.
