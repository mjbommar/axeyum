# ADR-0328: Preregister authenticated Tock log2 LLVM capture

Status: accepted
Date: 2026-07-21

## Context

ADR-0327 accepts the strict checked semantics required by the selected Tock
integer-log helpers. P5.5 still has no authenticated Tock artifact: the prior
owning-kernel module was a single-root feasibility observation, its hash and
symbol spellings are not expected results, and the sparse reference checkout
is not an admissible source tree.

The compiler is rustc's LLVM 22.1.2. The installed system `llvm-extract` is
LLVM 21.1.8 and rejects that module's LLVM-22 attributes; using it, rewriting
the text, or extracting by line ranges would weaken the strict frontend claim.
Ubuntu's exact `llvm-22` candidate is `1:22.1.2-1ubuntu1`. Its tools may be
installed after this zero-result decision, but their paths, SHA-256 hashes,
and version output must be committed in the producer registration before the
first official build.

## Decision

Create a v1 local-only producer for the exact Tock kernel revision
`ac5d597d22fbf3b03ef2169a577bac246ef65ffb` (tree
`5243357a7034d3a5fa68487ea839a25e573a25ef`). Materialize the complete Git tree
twice, build both independent copies sequentially at identical virtual source
and target paths in network-isolated mount namespaces, require raw complete
LLVM-module equality, then extract, assemble, and admit exactly the two
selected functions with registered LLVM 22 tools.

## Frozen v1 gates

1. Commit this zero-result ADR before adding a producer, registration, or
   result and before starting either official build. The feasibility module
   size/hash/symbols/timing seed no expected field.
2. Bind the upstream commit/tree plus every critical source, workspace,
   toolchain, lock, and license hash in the Tock selection note. Reject a dirty
   or wrong local Git object database; do not use its sparse worktree contents.
3. Register `/usr/bin/git` by path, SHA-256, and version. Use `git archive` of
   the exact commit to materialize two separate complete source roots through a
   traversal-safe extractor. Require distinct physical source and Cargo-target
   roots and independently recheck every registered file in both trees.
4. Register Bubblewrap 0.11.1 at its existing path/hash and run its no-write
   `--unshare-all` probe. Each build gets a fresh constructed root, read-only
   `/usr`, `/etc`, Cargo home, Rustup home, and source tree, writable private
   target, `/dev`, `/proc`, and `/tmp`. The only run-specific argv bytes are
   host-side bind sources; virtual destinations are exactly
   `/axeyum-vroot/{source,target}`.
5. Register rustc/cargo `nightly-2026-04-21`, rustc commit
   `66da6cae1a6f12e9585493ab8f8f19cf753091fd`, Cargo commit `7ecf0285e`, and
   LLVM 22.1.2. Register LLVM 22 `llvm-as`, `llvm-dis`, and `llvm-extract` by
   absolute path, SHA-256, and version before builds. LLVM 18/21 tools and
   line/text extraction are forbidden.
6. Validate the locked dependency cache before builds with the exact workspace
   lock and an offline metadata probe. The cache is read-only in both
   namespaces. No `--prepare-cache`, network, alternate registry, lock update,
   source edit, feature change, patch section, or vendored dependency is
   permitted during the official run.
7. Reject ambient `RUSTFLAGS`, `CARGO_BUILD_RUSTFLAGS`, and
   `CARGO_ENCODED_RUSTFLAGS`. Use identical ordered environment values,
   `SOURCE_DATE_EPOCH=1784602213`, `CARGO_BUILD_JOBS=1`,
   `CARGO_INCREMENTAL=0`, release debug disabled, and virtual
   `CARGO_TARGET_DIR`. From `/axeyum-vroot/source`, run only:

   ```text
   cargo rustc -p kernel --lib --release --locked --offline --
     -Ccodegen-units=1 -Clink-dead-code --emit=llvm-ir
   ```

8. Run the complete producer sequentially inside the standing one-job 4 GiB
   memory / 512 MiB swap scope. Require exactly one `kernel-*.ll` per build,
   record time/peak RSS and cgroup OOM deltas, reject every physical/temp root
   token, and require matching virtual-path counts.
9. Require raw full-module byte size and SHA-256 equality before symbol
   discovery. Any mismatch stops with no extraction, admission, partial
   output, or credit; no normalization or post-observation remapping is
   allowed.
10. After equality, assemble the full module with LLVM 22. Discover exactly one
    definition following each exact demangled comment
    `kernel::utilities::math::{log_base_two,log_base_two_u64}`; require symbols
    and declared `(i32)->i32` / `(i64)->i32` widths to agree across builds.
    Extract by the discovered symbols with registered `llvm-extract`, assemble
    each extraction, and permit only the known first-line `ModuleID` exclusion
    when comparing otherwise exact extracted bytes.
11. Run a hash-pinned `axeyum-llvm-scalar-admit` containing accepted ADR-0327
    semantics. Require canonical render/reparse identity, exact parameter and
    return widths, the checked straight-line scalar class, and accepted
    `range`/`ctlz` syntax for both functions. Parser decline is a capture
    failure, not permission to rewrite LLVM.
12. The producer writes only beneath ignored
    `target/tock-log2-20260721/capture-v1`, uses a sibling partial directory,
    and renames atomically only after every gate passes. Commit only
    Axeyum-owned producer/tests/registration plus result metadata and prose;
    Tock source, modules, bitcode, extractions, build cache, and canonical text
    remain local.
13. Mutation tests cover Git/tool hashes and versions, archive traversal,
    wrong/aliased roots, cache/lock/offline drift, ambient flags, namespace
    argv/order/destinations, host-path leakage, module count/inequality, wrong
    LLVM version, symbol ambiguity/width, extraction/assembly/admission
    failure, and atomic cleanup. Stages and kinds are stable; no partial credit
    exists.
14. Success closes only authenticated local T5.5.2 capture and parser
    admission. It permits a separate zero-row proof/scoreboard ADR for the
    already preregistered obligations. It authorizes no property query, source
    replay, negative control, proof, performance number, or external claim.

No gate may be weakened after the first official build starts.

## Result

Accepted as a negative v1 result. Producer commit `a2051514` was pushed before
the first official invocation. The producer accepted every frozen source,
producer, tool, namespace, and resource identity, materialized no target output,
then stopped at the pre-build locked-offline metadata probe:

```text
stage=cache
kind=offline_metadata
detail=error: failed to download `ghash v0.4.4`

Caused by:
  attempting to make an HTTP request, but --offline was specified
```

Zero official builds start or complete. No module, extraction, admission, target
byte, property query, proof, or scoreboard row exists; atomic cleanup leaves no
output or partial directory. The exact negative metadata is committed in
`bench-results/verify-tock-log2-20260721/capture-v1-negative.json`. The capped
producer reports the cache failure rather than an OOM-delta failure.

Populating the ambient Cargo cache after observing this miss and rerunning v1
would change an authenticated input after observation. V1 therefore ends here.
Tock remains eligible only through a fresh zero-result decision that freezes a
separate checksum-validated cache-preparation and inventory protocol before any
networked preparation or successor official build.

## Rejected alternatives

- **Use LLVM 21 anyway.** Rejected: it already fails on LLVM-22 syntax and is
  not the compiler's IR version.
- **Use rustup's LLVM tools alone.** Rejected: the component has LLVM 22
  assembler/disassembler tools but no `llvm-extract`.
- **Extract text by comments or line ranges.** Rejected: that authenticates an
  Axeyum text slicer rather than an LLVM symbol extraction.
- **Reuse the feasibility source/target tree.** Rejected: it is single-root,
  post-cache-fill, and not an official independent reproduction.
- **Commit extracted Tock LLVM.** Rejected: third-party generated bytes remain
  local; committed hashes and metadata make the result reviewable.

## Consequences

- Tool-version fidelity becomes part of capture correctness rather than a
  best-effort postprocessing detail.
- V1 demonstrates that the ambient cache is incomplete even before Cargo
  execution; the missing locked crate is an input-reproducibility failure, not
  a frontend or semantic result.
- A successor may prepare a dedicated cache only after separately freezing its
  network/checksum/inventory boundary. V1 itself is never rerun.

## References

- [Tock target selection](../../plan/track-5-verified-systems/P5.5-target-selection-tock-log2.md).
- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
- [ADR-0327](adr-0327-preregister-tock-log2-reflection.md).
