# ADR-0324: Preregister the Maestro LLVM root-drift diagnostic

Status: accepted
Date: 2026-07-21

## Context

ADR-0323's first official T5.5.2 capture is negative at its earliest artifact
gate. Two isolated, offline, memory-capped builds of the exact Maestro revision
completed, but their complete textual LLVM modules differed in both size and
SHA-256:

- root A: 36,037,712 bytes at `89b26e831789f210fe768982d8ae7c69a085ac1c4d7fa38faccd9e61911c5084`;
- root B: 36,038,199 bytes at `56bc0a408d905c4b0aa15723683ed75d4f8f39fb47189ef69ffd720c42627b94`.

The frozen protocol stopped before extraction and atomically removed both
modules. The mismatch could be a semantic code-generation difference, a crate
or symbol identity difference, reordered module content, upstream build-script
output, or path-bearing non-semantic metadata. The current evidence cannot
distinguish those cases. Retroactively ignoring bytes would violate ADR-0323;
moving directly to the three functions would abandon the authenticated owning-
build boundary.

## Decision

Add a non-crediting diagnostic producer,
`scripts/diagnose-maestro-llvm-root-drift.py`, with a registration and metadata-
only result beside ADR-0323's capture files. It reuses the exact registered
source, compiler, Cargo, target, flags, offline cache, memory limits, and two
isolated roots. Unlike the capture gate, it retains both complete modules under
ignored `target/` storage after observing the expected mismatch, then computes
a complete line diff and selected-function comparison.

This diagnostic cannot accept T5.5.2. Its only output is a causal
classification and the evidence needed to preregister one successor. No
normalization rule, parser change, solver query, verification result, or
scoreboard row is authorized.

## Frozen diagnostic gates

1. Commit this zero-row ADR before rerunning either owning build or inspecting
   a new root-drift byte. The discarded ADR-0323 modules and the earlier single-
   root feasibility module provide no diff evidence and do not seed expected
   categories.
2. Reuse ADR-0323's exact repository commit/tree, six critical-file hashes,
   pinned Rust/Cargo/LLVM identities, build argv and environment, two source
   roots, offline credited builds, one-job 4 GiB scopes, and no-vendoring
   boundary. Any identity drift fails before a build.
3. Require exactly one complete `kernel-*.ll` per root and require each to
   assemble under registered `llvm-as-21`. Record raw size/SHA-256, line count,
   wall time, and peak RSS. The expected inequality is diagnostic input, never
   an acceptance condition; accidental equality closes the diagnostic as
   `no_drift_reproduced` and still does not accept ADR-0323.
4. Run GNU `diff --speed-large-files --unified=0` over the complete modules
   under the memory cap and retain the complete diff locally. Record its size,
   SHA-256, hunk count, added-line count, removed-line count, first and last
   changed source lines, and whether either temporary absolute root occurs in
   either module or the diff. No diff line may be silently truncated or
   dropped; a diagnostic cap failure is itself the result.
5. Classify every added and removed line, without changing it, into exactly one
   stable syntactic bucket: module/source identity, target/module assembly,
   global/function/COMDAT identity, function body or terminator, attribute,
   metadata, comment/whitespace, or other. Report counts and representative
   SHA-256 identities, not third-party line text, in the committed result.
   `other > 0` is allowed and must remain visible.
6. Independently discover the selected definitions in each module by the exact
   demangled comments plus the constrained mangled-name shapes for
   `kernel::device::id::{major,minor,makedev}`. Record the full discovered
   symbols. Missing, duplicate, cross-root-renamed, or additional matches are
   explicit outcomes; the diagnostic must not silently substitute ADR-0323's
   earlier symbol hashes.
7. Extract each discovered selected definition separately with registered
   `llvm-extract-21`, assemble it, compute raw and exactly ModuleID-agnostic
   hashes, and run the existing `axeyum-llvm-scalar-admit` probe. Record exact
   widths, block/PHI/instruction counts, frontend-canonical hashes, and cross-
   root equality. This is diagnosis only: selected-function equality cannot
   override a full-module mismatch.
8. Produce a root-insensitive semantic projection of each selected typed graph
   using the existing canonical renderer. Compare complete canonical bytes and
   value+definedness admission metadata, but do not solve equivalence. A later
   ADR may use an equal projection only after independently specifying why the
   excluded full-module differences are non-semantic and how the owning-build
   chain remains authenticated.
9. Mutation tests cover missing/extra diff lines, every classification bucket,
   absolute-root detection, mismatched line counts, symbol rename/duplication,
   ModuleID-only versus non-ModuleID extraction drift, parser decline,
   result/registration hashes, existing output, and partial writes. Each has a
   stable stage/kind.
10. Commit only Axeyum-owned producer/test code plus hashes, aggregate counts,
    tool identities, and outcome prose. Complete modules, diff text, extracted
    LLVM, canonical LLVM, bitcode, source trees, and build products remain
    local under ignored `target/`; staged-path and extension audits enforce
    zero external bytes.
11. Run focused Python tests, the scalar-admission binary tests, existing LLVM
    checked-scalar tests, reflection semantics gate, strict formatting/docs/
    links, result recomputation, and the one-job 4 GiB OOM audit. No production
    semantics, public API, dependency, feature, unsafe, MSRV, WASM, or benchmark
    claim changes.
12. The result selects at most one next decision:
    - if every difference is demonstrably non-semantic and all three selected
      canonical projections are byte-identical, preregister a new canonical
      owning-build identity without rewriting ADR-0323;
    - if selected symbols or typed projections differ, investigate the exact
      build nondeterminism or change targets in a new decision; or
    - if the diagnostic cannot classify every changed line, retain the blocker
      and do not proceed to extraction credit or T5.5.3.

No gate may be weakened after either diagnostic build starts. The result is
valuable whether drift is narrow, semantic, broad, or unreproduced.

## Result

Accepted as a diagnostic result with no capture credit. Both exact owning-
kernel builds reproduced the broad drift while staying below the memory cap:

| Root | LLVM bytes | Lines | SHA-256 | Wall | Peak RSS |
|---|---:|---:|---|---:|---:|
| A | 36,038,043 | 446,429 | `9a7402491b1a5d2674a56f98a4335ce9f7afa2e0e01d272b49fad96f6e88d5f8` | 43,946 ms | 998,648 KiB |
| B | 36,038,537 | 446,429 | `f55a7b75f28cc2b46542a999f7be1ab3304b8e78a1e3fbc55433dcc0343e3ef4` | 43,842 ms | 997,760 KiB |

The complete 40,665,637-byte diff has SHA-256
`9209b68292689510dd3e5da10443ef7bce2878e76820ecbfc901d7a12977434d`,
65,752 hunks, and exactly 159,799 added plus 159,799 removed lines. All
319,598 changed lines are classified: 151,370 metadata, 101,000 function body
or terminator, 39,282 other, 15,274 global/function/COMDAT identity, 12,620
comment/whitespace, 48 attribute, and four module/source-identity lines. The
nonzero `other` bucket and body-scale churn forbid a semantics-free conclusion
from the complete diff.

Both modules contain seven copies of their own absolute source root. Direct
local inspection locates all seven in path constants from the Maestro `utils`
path dependency (collection and pointer modules). The registered remap was a
trailing `cargo rustc -- ...` argument, which Cargo applies to the final
`kernel` crate rather than every dependency. The unremapped dependency paths
therefore enter constant identities and cascade through hashes, symbols, and
metadata. This is an identified build-protocol root leak, not an LLVM-parser
failure.

All three selected functions are discovered once in both modules and pass the
existing checked scalar admission profile at the expected widths, one block,
zero PHIs, and 6/5/13 instructions. However, all three mangled symbols differ
across roots, so their ModuleID-agnostic extracted hashes and current frontend-
canonical hashes also differ. A local line diff shows that each small frontend
canonical pair differs only in the mangled function name, with its instruction
text unchanged. That final observation was not a frozen name-erasure gate and
earns no equality or capture credit; ADR-0324's selected-symbol-drift branch
therefore fires.

The committed result contains only hashes, sizes, aggregate categories,
admission metadata, and the outcome. The two modules, 40 MB diff, extracted
functions, and canonical text remain ignored local artifacts. No solver query
ran, ADR-0323 remains negative, T5.5.2 remains open, and no verification or
scoreboard row exists.

The result selects a new build-reproducibility decision: preregister a fresh
two-root retry in which root remapping reaches every Cargo dependency (not only
the final crate), then require raw full-module equality before extraction. Do
not normalize the observed modules or use name-erased selected bodies as a
substitute.

## Rejected alternatives

- **Treat rustc output as semantically deterministic despite byte drift.**
  Rejected: the owning-build evidence boundary must identify what changed.
- **Ignore all module metadata.** Rejected: metadata, attributes, COMDATs, and
  symbol identities do not share one semantics-free status, and arbitrary
  deletion could hide load-bearing differences.
- **Compare only the three function bodies.** Rejected as an acceptance route:
  it can diagnose stability but does not authenticate the complete owning
  build required by ADR-0323.
- **Switch immediately to Tock.** Rejected until this bounded diagnostic says
  whether the problem belongs to Maestro, rustc, or Axeyum's capture protocol.
- **Run the inverse proofs now.** Rejected: T5.5.3 remains behind authenticated
  T5.5.2 capture and a separate zero-row measurement ADR.

## Consequences

- The next work is bounded evidence gathering rather than a speculative parser
  or solver change.
- A narrow non-semantic cause can support a fresh, auditable canonical-identity
  proposal; broad or semantic drift stops the Maestro route honestly.
- ADR-0323 remains an immutable negative result regardless of the diagnostic.

## References

- ADR-0323.
- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
- [Maestro target selection](../../plan/track-5-verified-systems/P5.5-target-selection-maestro-device-id.md).
- ADR-0294 (the prior extracted-LLVM ModuleID drift lesson).
