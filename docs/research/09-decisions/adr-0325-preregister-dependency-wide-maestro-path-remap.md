# ADR-0325: Preregister dependency-wide Maestro path remapping

Status: proposed
Date: 2026-07-21

## Context

ADR-0323 rejects the first exact Maestro capture because two isolated owning-
kernel builds produce different complete LLVM modules. ADR-0324's complete
diagnostic identifies the build-protocol cause: the registered
`cargo rustc -- --remap-path-prefix=...` argument reaches only the final
`kernel` crate. Seven absolute source paths from Maestro's `utils` path
dependency remain in each module and cascade through allocation names,
dependency metadata, crate disambiguation, mangled symbols, and the complete
textual module.

The selected `major`, `minor`, and `makedev` bodies all pass the checked scalar
profile, but every symbol and current canonical function hash differs. Their
body-text similarity earns no credit because the authenticated whole-build
boundary remains open. The next experiment must fix source-path input before
code generation, not normalize the already-observed modules afterward.

## Decision

Create a fresh v2 capture producer and registration. Apply root remapping to
every target crate through `CARGO_ENCODED_RUSTFLAGS`, preserving the upstream
configuration's `-Zexport-executable-symbols` flag explicitly:

```text
-Zexport-executable-symbols<US>--remap-path-prefix=<isolated-root>=/axeyum-external/maestro
```

where `<US>` is Cargo's unit-separator encoding (`0x1f`). Remove the trailing
final-crate remap from `cargo rustc` itself; retain only the registered final-
crate codegen-unit, linked-dead-code, and LLVM-emission arguments. All other
ADR-0323 source, toolchain, target, offline-build, resource, atomic-output, and
local-only artifact boundaries remain.

This is a fresh capture attempt, not a reinterpretation of ADR-0323 or a
normalization of ADR-0324's modules.

## Frozen v2 gates

1. Commit this zero-result ADR before adding the v2 producer/registration or
   running any dependency-wide-remapped build. ADR-0324's modules may motivate
   the flag placement but do not supply an expected v2 hash or symbol.
2. Reuse exact Maestro commit/tree and all six source/config/lock/target hashes,
   nightly/Cargo/LLVM tool identities, custom target, release library target,
   one codegen unit, linked-dead-code retention, offline credited builds,
   `SOURCE_DATE_EPOCH`, two isolated roots, one job, 4 GiB scopes, and local-
   only external artifacts from ADR-0323.
3. Set `CARGO_ENCODED_RUSTFLAGS` to exactly two ordered flags for both credited
   builds: `-Zexport-executable-symbols`, then the root-specific remap to the
   common `/axeyum-external/maestro` prefix. Reject an inherited `RUSTFLAGS`,
   `CARGO_BUILD_RUSTFLAGS`, or preexisting `CARGO_ENCODED_RUSTFLAGS` rather than
   merge ambient options. Record the encoded bytes and their printable
   template in provenance.
4. The final `cargo rustc` tail is exactly
   `-Ccodegen-units=1 -Clink-dead-code --emit=llvm-ir`; it contains no path
   remap. This preserves the distinction between dependency-wide Cargo flags
   and final-crate-only rustc flags.
5. Require exactly one complete `kernel-*.ll` per root and require each to
   assemble. Before comparing hashes, require zero occurrences of either real
   source root and zero occurrences of the system temporary parent in each
   module. The shared canonical prefix may occur and is recorded, not erased.
6. Require the two raw complete modules to be byte-identical in size and
   SHA-256, with no normalization. Any inequality is a negative v2 result and
   stops before extraction. Do not add another diff rule or fall back to
   selected-function equality.
7. After full equality only, discover exactly one definition for each selected
   function from its exact demangled comment and constrained mangled-name
   shape. Record the newly observed full symbols; do not require ADR-0323's
   old feasibility symbols or ADR-0324's root-specific symbols.
8. Extract each selected definition independently, assemble it, require the
   same-symbol raw and ModuleID-agnostic bytes to reproduce across roots, and
   pass the existing scalar-admission binary at exact widths, one block, zero
   PHIs, scalar return, and no memory/call/loop. Require frontend canonical
   render/reparse and reassembly equality across roots.
9. Write a deterministic metadata-only result with source/tool/flag identities,
   full-module size/hash/root-token counts, discovered symbols, extracted and
   canonical hashes, parser metadata, stage timings, peak RSS, stable
   stage/kind, and zero dropped targets. Recompute its identity from retained
   local artifacts without rebuilding.
10. Mutations cover ambient flag injection, encoded-flag order/separator,
    missing upstream export flag, final-tail remap reintroduction, source/target
    hashes, root-token detection, full-module byte drift, symbol discovery,
    extraction, ModuleID grammar, parser profile, existing output, and partial
    write. Each fails closed with no capture credit.
11. Commit no Maestro source, full/extracted/canonical LLVM, diff, bitcode,
    generated harness, or Cargo product. Only Axeyum-owned producer/tests,
    registration, hashes, aggregate metadata, and result prose may enter Git.
    The distribution/attribution gate remains unresolved and unchanged.
12. Run focused producer tests, scalar-admission tests, existing LLVM checked-
    scalar tests, reflection semantics gate, strict formatting/docs/links,
    result/hash recomputation, and the one-job 4 GiB OOM audit. No production
    IR/solver/reflection semantics, public API, dependency, feature, unsafe,
    MSRV, WASM, or benchmark claim changes.
13. A positive result closes only reproducible T5.5.2 local capture and parser
    admission. It authorizes a separate zero-row T5.5.3 ADR; it does not
    authorize construction or solving of inverse properties, source replay,
    negative controls, verification claims, or a scoreboard row.

No gate may be weakened after the first v2 build starts. A second raw-module
mismatch closes this correction negatively and forces a new target/build-route
decision rather than another post-hoc canonicalization.

## Result

Proposed. No dependency-wide-remapped build, module identity, discovered
symbol, parser result, capture credit, proof, or scoreboard row exists.

## Rejected alternatives

- **Strip the seven path constants from ADR-0324's modules.** Rejected: their
  identities have already cascaded through symbols and metadata.
- **Erase mangled names only.** Rejected: that authenticates selected body text
  rather than the owning build and ignores 319,598 changed lines.
- **Set ordinary `RUSTFLAGS` without preserving upstream config.** Rejected:
  environment flags may override configured rustflags, silently dropping
  `-Zexport-executable-symbols`.
- **Use one physical source root twice.** Rejected: it would avoid rather than
  test root independence.
- **Proceed directly to proofs because all bodies parse.** Rejected: parser
  admission is downstream of authenticated reproducible capture.

## Consequences

- The retry tests the diagnosed cause at input time with a stricter zero-root-
  token gate and raw full-module identity.
- Success yields stable newly discovered symbols and permits T5.5.3
  preregistration; failure ends this correction without moving the goalposts.
- ADR-0323 and ADR-0324 remain immutable negative/diagnostic evidence.

## References

- ADR-0323.
- ADR-0324.
- [P5.5 external target](../../plan/track-5-verified-systems/P5.5-external-target.md).
- [Maestro target selection](../../plan/track-5-verified-systems/P5.5-target-selection-maestro-device-id.md).
