# ADR-0320: Preregister bounded reflected page-table evidence

Status: proposed
Date: 2026-07-21

## Context

ADR-0318 rejected the first T5.3.2 page-table-shaped cell before capture when
the registered compiler emitted unowned nested lexical-scope metadata.
ADR-0319 separately accepted that exact metadata grammar, proved it
semantically inert, and demonstrated that the unchanged `walk_permissions`
source now reaches the existing checked-memory profile. That result retained
no raw walk artifact and claimed no invariant.

The five syntax-gate functions now present in the excluded
`mir-target-crate` fixture remain the intended bounded population: two good
walks and three deliberately broken controls over one `[u8; 4]` table and one
`u8` virtual address. The compiler projection uses only the already accepted
checked-MIR byte-memory fragment. The next question is therefore evidence
construction, not another syntax or semantic extension.

## Proposed decision

Run one fresh, bounded T5.3.2 v1 evidence cell without changing production
reflection code, IR operators, solver routes, public APIs, dependencies, or
features. Capture the complete fixture MIR through `axeyum-mir-build`'s
existing `checked-memory` profile under the registered Cargo/rustc pair. One
committed raw module may serve both good-function selections only because the
owning Cargo build emits the same complete module for each; retain separate
typed selection summaries and prove all fresh raw copies byte-identical.

Interpret each byte entry as a deliberately tiny teaching model: bits 0--1
select the next entry and encode permissions, while bits 2--7 are a
four-byte-aligned frame token. Define an independent finite specification in
the test harness using only the reflected input symbols:

```text
level1 = (virtual_address >> 6) & 3
parent = table[level1]
level2 = parent & 3
leaf = table[level2]
frame = leaf & 0xfc
permissions = (parent & leaf) & 3
```

The four-element symbolic table selection must be a deterministic nested
`ite`, separate from the reflected implementation terms. Prove the reflected
good results equal these specifications for every table and address. From the
reflected terms also prove universal panic freedom, aligned frame output, and
effective permissions that are subsets of both selected parent and leaf
permission bits.

This is an obligation-shape experiment, not a real MMU or address-translation
model.

## Frozen evidence gates

1. Commit this zero-result ADR before creating or retaining raw capture bytes,
   provenance, proof tests, sampler output, timing output, or result prose.
   The fixture functions admitted only for ADR-0319 syntax selection are not
   evidence for this ADR.
2. Capture `walk_frame` and `walk_permissions` independently, twice each, with
   fresh target/output directories, locked owning-Cargo builds, the registered
   `nightly-2026-05-01` Cargo/rustc binaries, 64-bit target width, and the exact
   `checked-memory` profile. All four raw modules and the committed raw module
   must be byte-identical; the two selection summaries may differ only in
   function-specific typed projection fields.
3. Commit raw bytes plus canonical provenance, both canonical selection
   summaries, and SHA-256 inventory. Provenance binds schema, manifest,
   lockfile, source, raw module, Cargo/rustc identities and commits, ordered
   Cargo/rustc arguments, package, target kind, both selected functions,
   profile, target width, repetition count, and byte-identity result. Paths in
   committed summaries are root-independent placeholders.
4. A stable-CI validator checks the exact path/hash set and every typed
   provenance field without requiring the pinned nightly. When that nightly is
   available, one opt-in command reproduces both selections and raw bytes.
   Wrong tool, selection, profile, width, tamper, malformed MIR, failed output,
   or an existing output path receives no credit and leaves no partial
   artifact.
5. Both good functions reflect from the committed compiler artifact through
   the unchanged checked-memory API with exactly one four-byte input region,
   parameters `[u8; 4]` and `u8`, four basic blocks, an eight-bit result, and
   deterministic result/panic/input terms across repeated reflection.
6. Solver proofs establish, over every table/address input: each good function
   has `panic == false`; `walk_frame` equals the independent frame
   specification and has zero low two bits; `walk_permissions` equals the
   independent permission specification; and its result has no permission bit
   absent from either the selected parent or selected leaf. Proof goals use
   the reflected compiler terms, not a hand-built implementation substitute.
7. Each broken function is reflected from the same committed raw module and
   yields a replay-checked concrete witness: `broken_walk_index` panics from an
   unmasked address; `broken_frame_unaligned` returns nonzero low frame bits;
   `broken_permissions_escalate` returns a permission bit absent from the
   parent. Evaluate each witness against both reflected terms and the exact
   fixture source imported as Rust; the corresponding good neighbor remains
   clean.
8. Freeze this sampler table corpus before execution, in this order:
   `[00,00,00,00]`, `[ff,ff,ff,ff]`, `[00,01,02,03]`,
   `[40,81,c2,03]`, `[01,01,00,00]`, `[01,02,00,00]`,
   `[03,42,81,c0]`, `[fc,81,42,03]`. For every table, evaluate all 256 virtual
   addresses for both good functions. Record exactly 4,096 function rows and
   zero reflection/spec/Rust disagreement, evaluation error, panic, or dropped
   row. The sampler corroborates but does not replace the universal proofs.
9. Mutation teeth remove each index mask, remove the frame mask, remove the
   parent permission intersection, swap parent/leaf selection, alter region
   size and target width, corrupt a compiler assertion, and tamper with raw
   bytes/provenance/summary/hash inventory. Every mutation is replay-refuted or
   rejected with a stable located class; compiler assertions cannot suppress
   the reflector-owned access predicate.
10. Record capture, proof, and sampled-replay wall times separately. Do not
    claim performance, scalability, real address translation, physical memory,
    privilege semantics, aliasing, page sizes, cache/TLB behavior,
    concurrency, or external-target coverage.
11. Existing authenticated MIR fixtures and projections, checked-memory
    defaults, source-contract bridge, dependency/features, unsafe policy,
    MSRV, and WASM surface remain unchanged. The executable-semantics inventory
    remains 81 variants because this cell adds evidence, not a new semantic
    form. Focused tests, complete `axeyum-verify` and doctests, strict
    Clippy/rustdoc, reflection semantics gate, formatting, links, and the
    one-job 4 GiB/OOM audit pass.

No gate may be weakened after the first capture, proof, sampler, or mutation
result is observed. A failure records a negative result and restores/removes
candidate production, test, and artifact changes as required by the failed
gate.

## Rejected alternatives

- **Resume ADR-0318 after fixing its blocker.** Rejected: its frozen protocol
  already ended negative; post-result reuse would erase the preregistration
  boundary.
- **Treat ADR-0319's successful syntax selection as a capture result.**
  Rejected: it intentionally retained no raw evidence and tested no invariant.
- **Add a general page-table memory model.** Rejected: the current bounded
  byte-region surface is sufficient for this exact cell.
- **Prove only hand-built formulas or sampled executions.** Rejected: T5.3
  requires compiler-reflected terms, universal proofs, and replayed controls.
- **Call the four-entry model an MMU.** Rejected: the cell lacks architectural
  page-table semantics and every system effect listed in gate 10.

## Consequences

- A positive result supplies T5.3.2's first bounded reflected obligation family
  and discriminating broken controls, but does not complete the phase or
  authorize a real kernel target.
- Any newly exposed compiler or semantic form stops this ADR; it requires its
  own audit and preregistration.

## References

- ADR-0287 through ADR-0289: authenticated checked-MIR capture and byte memory.
- ADR-0318: rejected predecessor cell.
- ADR-0319: accepted lexical-scope metadata prerequisite.
- `docs/plan/track-5-verified-systems/P5.3-kernel-theories.md`.
- `crates/axeyum-verify/src/reflect/mir/checked.rs`.
