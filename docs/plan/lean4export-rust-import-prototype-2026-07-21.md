# Rust `lean4export` 3.1 import and kernel-admission prototype

Status: implemented initial profile; broader admission remains open

Date: 2026-07-21

Parent roadmap:
[`lean-system-compatibility-roadmap-2026-07-21.md`](lean-system-compatibility-roadmap-2026-07-21.md)

Decision gate:
[ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md)

## Result

Axeyum now has a Rust `lean4export` reader that sends supported declarations
through the independent kernel's real admission gates. The official Lean 4.30
fixture used by the earlier Python inventory admits as:

```text
LEAN4EXPORT_IMPORT|format=3.1.0|lean=4.30.0|names=14|levels=2|exprs=43|decl_records=5|admitted=8|axioms=P
```

Five export declaration records become eight kernel declarations because the
one inductive-group record admits the family, two constructors, and the
kernel-generated recursor:

```text
Two
Two.left
Two.right
Two.rec
Two.recOn
chooseLeft
P
identity
```

This closes the **flat initial import slice**, not the general import gap. The
reader rejects projections, literals, quotient declarations, unsafe/partial
declarations, and recursive-indexed/mutual/nested/reflexive inductive groups. It
has not imported `Init`, `Std`, or mathlib. `P` is reported as an axiom, not
silently counted as a proved theorem.

The second official fixture closes the direct-recursive positive control:

```text
LEAN4EXPORT_IMPORT|format=3.1.0|lean=4.30.0|names=30|levels=4|exprs=130|decl_records=5|admitted=11|axioms=none
```

It independently admits `MiniNat`, `MiniList`, their constructors and generated
recursors/`recOn` definitions, plus `miniOne`. This is exact direct-recursive and
parametric-recursive fixture credit; recursive indexed, mutual, nested, and
reflexive families remain outside the profile.

## Why a separate crate

The implementation is
[`axeyum-lean-import`](../../crates/axeyum-lean-import/src/lib.rs), separate from
[`axeyum-lean-kernel`](../../crates/axeyum-lean-kernel/src/lib.rs).

The dependency direction is one way:

```text
untrusted NDJSON bytes
  -> serde_json + format/topology/resource validation  axeyum-lean-import
  -> translated Name/Level/Expr handles                axeyum-lean-import
  -> add_declaration / add_inductive                    axeyum-lean-kernel
  -> admitted Environment                              independently checked
```

`axeyum-lean-kernel` still has zero dependencies. JSON parsing and format
dispatch do not gain access to kernel-private unchecked insertion. The new
crate depends on the kernel; the kernel does not depend on the importer. This
is the same exercised-boundary rationale used for the separate SMT-LIB parser:
wire-format complexity should not become checker complexity.

The new crate is pure Rust, denies `unsafe` through workspace lints and its own
crate attribute, and does not depend on official Lean. Official Lean is needed
to produce or cross-check a fixture, not to import an already exported stream.

## Exact input provenance

The committed flat fixture is
[`lean4export-v4.30-axeyum-probe.ndjson`](fixtures/lean4export-v4.30-axeyum-probe.ndjson).
Its metadata binds:

- exporter: `lean4export` format/exporter version 3.1.0;
- Lean version: 4.30.0;
- Lean source hash: `d024af099ca4bf2c86f649261ebf59565dc8c622`;
- source shape: one axiom, one identity theorem, one flat two-constructor
  inductive, its generated recursor/`recOn`, and one ordinary definition.

Its committed source is
[`lean4export-v4.30-axeyum-probe.lean`](fixtures/lean4export-v4.30-axeyum-probe.lean),
and its NDJSON SHA-256 is
`c582b5d5ab19cba61183d592d70c17eb7d101b8a1ad61e8c4c6022dfe95a8280`.

The direct-recursive source and export are
[`lean4export-v4.30-recursive-shapes.lean`](fixtures/lean4export-v4.30-recursive-shapes.lean)
and
[`lean4export-v4.30-recursive-shapes.ndjson`](fixtures/lean4export-v4.30-recursive-shapes.ndjson).
They contain `MiniNat`, `miniOne`, and parametric `MiniList`; the NDJSON
SHA-256 is
`91df1e44219483b213000b94b06016f9569dc648d0680d9ae91ff3198817db08`.

The exporter tag used to produce them was v4.30.0 at
`a3e35a584f59b390667db7269cd37fca8575e4bf`. The format is specified by the
[official 3.1.0 document](https://github.com/leanprover/lean4export/blob/v4.30.0/format_ndjson.md).

Both fixtures reproduce byte-for-byte with the pinned checkout and toolchain.
The repository filenames are copied to valid Lean module names before compiling:

```sh
cp docs/plan/fixtures/lean4export-v4.30-axeyum-probe.lean AxeyumProbe.lean
lean -j1 -o AxeyumProbe.olean AxeyumProbe.lean
LEAN_PATH=. .lake/build/bin/lean4export AxeyumProbe | sha256sum

cp docs/plan/fixtures/lean4export-v4.30-recursive-shapes.lean AxeyumImportShapes.lean
lean -j1 -o AxeyumImportShapes.olean AxeyumImportShapes.lean
LEAN_PATH=. .lake/build/bin/lean4export AxeyumImportShapes | sha256sum
```

The expected hashes are the two SHA-256 values above. The `.olean` files are
transient official-toolchain inputs and are not committed or parsed by Axeyum.

## Wire contract

The reader currently recognizes all format-3.1 record discriminants while
admitting only the independently supported profile.

### Metadata

- line 1 must be the sole `meta` record;
- exporter name must be exactly `lean4export`;
- format version must be exactly 3.1.0;
- exporter version, Lean version, and Lean git hash are retained in the report;
- unknown fields reject rather than being ignored.

### Topology

- exported name IDs start at 1; ID 0 is the anonymous root;
- exported level IDs start at 1; ID 0 is `Level.zero`;
- exported expression IDs start at 0;
- all three index spaces must be dense;
- names, levels, and expressions may refer only to earlier records;
- every declaration reference must resolve through those maps;
- declaration records are processed in stream order, matching their dependency
  order.

The exported IDs are wire IDs only. They map to kernel-interned IDs and are not
assumed numerically equal.

### Resource and safety policy

The default profile limits a record to 16 MiB and a stream to two million
records. Limits are explicit caller data. Blank lines, malformed JSON, unknown
record kinds, duplicate metadata, unknown fields, non-dense indices, forward
references, integer narrowing, unsafe declarations, and partial definitions
reject with typed errors.

The reader now owns a private staging `Kernel` and returns a field-private
`CompletedImport` only after the full stream succeeds. On malformed,
unsupported, resource, I/O, or kernel rejection, the staging state is dropped
and no environment or arena handle reaches the caller. This closes TL1.3
without cloning or attempting partial rollback of kernel interners and caches.

## Translation profile

| Export construct | Translation/admission state | Current boundary |
|---|---|---|
| `Name.str`, `Name.num` | translated | dense/backward parent reference required |
| `succ`, `max`, `imax`, `param` levels | translated | dense/backward references required |
| `bvar`, `sort`, `const`, `app`, `lam`, `forallE`, `letE` | translated | binder mode and every child reference validated |
| `mdata` | semantically erased to its referenced expression | metadata object still shape-checked |
| `proj` | translated and kernel checked | TL2.2-TL2.4 representation/inference/reduction admit and compute the official root; TL2.5 structure eta is now separately live and does not change this import population |
| `natVal` | translated and kernel checked | TL2.6 provides arbitrary-precision storage; TL2.7 types only against the checked canonical `Nat` bootstrap and implements constructor/literal conversion |
| `strVal` | typed decline `literal-string-typing` | kernel currently rejects literal inference |
| safe `axiom` | kernel admitted and axiom name reported | type must check; proposition remains an assumption |
| safe `def` | kernel admitted | hint translated; value must check against type |
| safe `opaque` | kernel admitted | value checks but does not unfold |
| `thm` | kernel admitted | proof term must check against theorem type |
| `quot` | typed decline `quotient-package` | quotient package/check/reduction absent |
| one supported inductive family | kernel admitted and generated recursor cross-checked | flat, parametric-recursive, and direct-recursive fixtures accepted; harder shapes need fixtures |
| mutual inductive group | typed decline `inductive-mutual` | kernel gate is single-family |
| nested/reflexive group | typed declines | kernel deliberately rejects these shapes |
| unsafe/partial declarations | typed decline | never admitted by default |

## Inductive and recursor validation

An importer must not accept an inductive merely because its constructors pass a
local shape check. The official export also carries informational recursor data,
and a mismatch there can expose a semantic difference between kernels.

For the admitted profile, the importer:

1. validates one family, constructor order, parent identities, universe
   parameters, declared parameter count, and safety flags;
2. calls `Kernel::add_inductive`, which checks the family and constructor types
   and independently generates a recursor;
3. checks the generated recursor name, universe parameters, type by
   definitional equality, parameter/index/motive/minor counts, constructor rule
   identities, field counts, and each iota-rule RHS by definitional equality
   against the official export;
4. admits later declarations such as `Two.recOn` only after that comparison.

Universe parameter names are binders. The direct-recursive fixture made
official Lean choose `u_1` where Axeyum generated `u.1`; exact name equality
would therefore reject an alpha-equivalent recursor. The importer now requires
equal universe-parameter arity, substitutes every exported binder into the
generated namespace, and then applies the same definitional-equality checks to
the recursor type and every iota-rule RHS. This fixes naming without treating
different arity or computation as equivalent.

This is stronger evidence than translating the exported recursor directly and
inserting it. Axeyum and official Lean independently derive the computational
object and compare results.

## Negative matrix

The 23 Rust integration tests across two binaries in
[`lean4export_v31.rs`](../../crates/axeyum-lean-import/tests/lean4export_v31.rs)
cover:

| Test | Expected result | Boundary proved |
|---|---|---|
| official flat fixture | 5 records / 8 declarations admitted | first end-to-end import slice |
| official direct-recursive fixture | 5 records / 11 declarations, zero axioms | direct and parametric recursion cross the official seam |
| official projection fixture | 61 expressions / 9 declarations admitted; imported selector computes | exact K1 projection root closes |
| official Nat fixture | 90 expressions / 10 declarations admitted, zero axioms; imported definition computes to `37` | exact K1 Nat-literal root closes under bootstrap and above-`u128` mutation controls |
| remaining official blocker fixtures | quotient declines on its package; the large String closure needs a refreshed current blocker | no broader closure credit |
| repeated import | identical report and declaration debug projection | deterministic construction |
| unknown record | malformed rejection at line 2 | no open-world guessing |
| forward expression reference | malformed rejection at line 2 | topological stream contract |
| projection wire mutations | oversized index and forward structure reject | wire width/topology stay bounded |
| official projection mutations | wrong structure name and field index reject at the kernel gate | translation cannot grant semantic credit |
| format 4.0.0 mutation | stable unsupported decline | version changes fail closed |
| theorem-body mutation | kernel rejects `identity` | parsing cannot grant theorem credit |
| exported recursor-rule mutation | importer rejects the group | generated computation is compared |
| partial definition | stable unsupported decline | unsafe/partial code cannot enter default profile |
| line/record limits (two cells in one test) | resource rejection | bounded input contract |
| completed publication | borrowed and consumed kernel length equals the matching report | success publishes one owned checked pair |
| late failure matrix | appended JSON, final kernel rejection, quotient, late record limit, and post-stream I/O error return no completed environment | whole-environment transactionality |
| generated TL1.4 corpus | 226 cases: every record body/prefix/top-level field plus ID/reference/depth/Unicode/integer/cycle/version families | deterministic stable-class mutation coverage; 64 valid prefixes are explicitly unsealed |

Several tests contain multiple mutation cells: the blocker fixture, projection
mutations, resource limits, arbitrary-precision values, and late-publication
failure classes remain separated by assertions even when they share one test
function. The mutation binary separately freezes exact population/class counts
and byte-identical repeated summaries.

The earlier Python probe remains useful as an implementation-independent
inventory oracle. Six reader tests plus two exact census/hash tests and the Rust
tests consume the same official fixtures but exercise separate code paths.

## Commands and result

```sh
cargo test -p axeyum-lean-import
cargo clippy -p axeyum-lean-import --all-targets -- -D warnings
cargo run -q -p axeyum-lean-import --example lean4export_import -- \
  docs/plan/fixtures/lean4export-v4.30-axeyum-probe.ndjson
cargo run -q -p axeyum-lean-import --example lean4export_import -- \
  docs/plan/fixtures/lean4export-v4.30-recursive-shapes.ndjson
```

Measured local result under the repository's 4 GiB process cap:

- eleven integration tests pass;
- warning-denied all-target Clippy passes;
- the example prints the exact result at the top of this page;
- the existing 181 kernel unit/integration tests and kernel doctest remain
  green from the immediately preceding roadmap landing.

No timing or throughput claim is attached to this tiny fixture.

## What this changes in the roadmap

The initial parts of L1 and L2 are now implemented together:

- Rust format/version/topology/resource reader: **initial profile landed**;
- translation of the kernel's existing expression surface: **landed**;
- safe axiom/definition/opaque/theorem admission: **landed on the fixture**;
- flat, parametric-recursive, and direct-recursive non-indexed inductive
  admission with recursor comparison: **landed on the two fixtures**.

L1 is not complete because there is no property fuzz target, declaration
dependency digest, completed wire-model separation for every unsupported
variant, or large-stream checkpoint/durable publication protocol. The
deterministic truncation/ID/reference/field/depth/Unicode/integer/cycle/version
matrix is complete. L2 is not
complete because String literals, quotients, recursive-indexed, mutual, nested,
and reflexive groups remain explicit declines.

## Next evidence-bearing increments

1. Preserve the landed projection/Nat/quotient streams and source/command/hash-
   bound String closure; generate recursive-indexed Vector, mutual, nested, and
   reflexive families.
2. Add a generated parsed/translated/admitted/dual-admitted matrix from those
   fixtures.
3. **DONE (TL1.4):** retain the 226-case duplicate-ID, truncation-at-every-
   record, integer, deep-JSON, Unicode, cycle, version, unknown-field, and
   publication corpus. Sixty-four record-boundary prefixes remain explicitly
   unsealed until authenticated artifact identity lands.
4. **DONE:** hash axiom names **and canonical types**, then bind the 65 actual
   Axeyum prelude assumptions (real 30, integer 34, string 1) to that stable
   [runtime-derived identity](lean-axiom-ledger-v1.json).
5. Export the smallest dependency-closed `Init` root and rank the actual decline
   population.
6. **Projection/eta/Nat/TL1.3 slices DONE:** representation, dependent
   inference, constructor reduction, wire translation, exact projection-root
   admission/computation, separately gated structure eta, arbitrary-precision
   Nat storage, checked literal semantics, and exact Nat-root admission/
   computation are complete; private staging now publishes only an owned
   completed environment. Execute TL1.7 declaration content/dependency digests
   next; TL1.5 later adds property fuzzing over the frozen paths.

The four-root
[`official blocker census`](lean4export-official-blocker-census-2026-07-21.md)
resolves the first implementation choice for the measured roots: projection is
the first slice. It does not replace the broader `Init` dependency-closure
census.

Do not begin a native Lean parser, Lake clone, standalone LSP, compiler, or
mathlib breadth campaign before this import matrix shows which core constructs
actually block dependency-closed declarations.
