# Bounded memory and page-table-shaped math

## Claim

For one authenticated compiler-reflected four-byte table walk, Axeyum proves
panic freedom, equality to an independent finite specification, aligned frame
output, and permission monotonicity for every table and `u8` address. This is a
bounded memory-obligation shape, not an MMU or real address-translation claim.

## Goal shape

For `table : BV8[4]` and `virtual_address : BV8`, the independent specification
is

```text
level1     = (virtual_address >> 6) & 3
parent     = table[level1]
level2     = parent & 3
leaf       = table[level2]
frame      = leaf & 0xfc
permissions = (parent & leaf) & 3
```

Seven universal proof groups cover all `2^32 * 2^8` table/address assignments:

1. both reflected good functions cannot panic;
2. `walk_frame` equals `frame`;
3. `walk_permissions` equals `permissions`;
4. the returned frame has zero low two bits; and
5. each returned permission bit occurs in both the selected parent and leaf.

## Supported fragment

The source fixture is dependency-free Rust over `[u8; 4]` and `u8`. The checked
MIR route admits one fixed four-byte non-aliasing input region, typed byte
indexing, scalar BV operations, compiler assertions, and acyclic control in the
accepted checked-memory profile. The complete 8,218-byte compiler MIR module is
captured from the registered owning Cargo build, not copied from a hand-written
IR example.

## Evidence route

The fixture's
[`provenance.json`](../../../../crates/axeyum-verify/tests/fixtures/mir-target-crate/artifacts/provenance.json)
binds source, lockfile, registered Cargo/rustc identities, ordered arguments,
profile, target width, selected functions, and four byte-identical fresh
captures. [`SHA256SUMS`](../../../../crates/axeyum-verify/tests/fixtures/mir-target-crate/artifacts/SHA256SUMS)
authenticates the exact source/artifact set; the raw MIR hash is
`6a1e7c82ad14de2355d5e7039422933b99c410e3ca4bff89b1704ee53f5b5c43`.

[`mir_page_table.rs`](../../../../crates/axeyum-verify/tests/mir_page_table.rs)
reflects the committed compiler artifact, builds the specification independently
from reflected inputs, and universally proves the seven claims. Three faulty
source functions yield concrete countermodels that replay through reflected
terms and exact Rust source. An eight-table sampler evaluates all 256 addresses
for both good functions as a separate reflection/spec/source cross-check.

## Worked example

[ADR-0320](../../../research/09-decisions/adr-0320-preregister-bounded-reflected-page-table-evidence.md)
accepts:

- four byte-identical fresh compiler captures of one 8,218-byte module;
- seven universal claims;
- replayed controls for an unmasked index panic, unaligned frame output, and
  parent-permission escalation;
- exactly 4,096 sampler rows with zero disagreement, evaluation error, panic,
  or dropped row; and
- twelve semantic or authentication mutations with no unexpected survivor.

Recorded wall observations are 369 ms for pinned two-selection capture
reproduction, 100 ms for the universal proof group, and 234 ms for the sampler.

## Reproduce

The stable artifact/proof/replay route is:

```sh
MEM_LIMIT_GB=4 CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 \
RUST_TEST_THREADS=1 scripts/mem-run.sh \
  cargo test -p axeyum-verify --test mir_page_table --all-features --jobs 1 \
  -- --test-threads=1
```

Authenticate the committed inventory separately:

```sh
(cd crates/axeyum-verify/tests/fixtures/mir-target-crate && \
  sha256sum -c artifacts/SHA256SUMS)
```

The exact fresh-capture test is
`compiler_page_table_selections_reproduce_the_authenticated_raw_module` in
`cargo_mir_build.rs`. Set `AXEYUM_VERIFY_MIR_CARGO` and
`AXEYUM_VERIFY_MIR_RUSTC` to the registered binaries and
`AXEYUM_VERIFY_MIR_REQUIRE_CARGO_BUILD=1` to make unavailable or wrong tools a
hard failure.

## Boundaries and residuals

- The table has four byte entries and the address is `u8`; this is a teaching
  model, not a page-table architecture.
- Physical memory, page sizes, privilege levels, accessed/dirty bits,
  invalidation, aliasing, provenance, concurrency, and cache/TLB behavior are
  absent.
- The result is not a real MMU, address-translation implementation, external
  kernel target, or scalability claim.
- The sampler corroborates the universal proof; it does not expand its domain.
- Wider arrays, realistic entries, general pointer/memory semantics, and a real
  external target require separately preregistered evidence.

See the [catalog index](README.md) for the evidence-level comparison.
