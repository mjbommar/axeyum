# Rust `lean4export` 3.1 import and kernel-admission prototype

Status: implemented initial profile; broader admission remains open

Date: 2026-07-21

Parent roadmap:
[`lean-system-compatibility-roadmap-2026-07-21.md`](lean-system-compatibility-roadmap-2026-07-21.md)

Decision gate:
[proposed ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md)

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

The reader is declaration-granularity transactional, not whole-stream
transactional. A caller must import an untrusted stream into a fresh `Kernel`;
that rule is stated in the public crate documentation. A later production
project cache may publish a completed environment only after the full stream
returns successfully.

## Translation profile

| Export construct | Translation/admission state | Current boundary |
|---|---|---|
| `Name.str`, `Name.num` | translated | dense/backward parent reference required |
| `succ`, `max`, `imax`, `param` levels | translated | dense/backward references required |
| `bvar`, `sort`, `const`, `app`, `lam`, `forallE`, `letE` | translated | binder mode and every child reference validated |
| `mdata` | semantically erased to its referenced expression | metadata object still shape-checked |
| `proj` | typed decline `expr-projection` | kernel has no projection node/check/reduction yet |
| `natVal` | typed decline `literal-nat-bignum-and-typing` | bignum must precede literal typing |
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

The eleven Rust integration tests in
[`lean4export_v31.rs`](../../crates/axeyum-lean-import/tests/lean4export_v31.rs)
cover:

| Test | Expected result | Boundary proved |
|---|---|---|
| official flat fixture | 5 records / 8 declarations admitted | first end-to-end import slice |
| official direct-recursive fixture | 5 records / 11 declarations, zero axioms | direct and parametric recursion cross the official seam |
| three official blocker fixtures | projection/Nat closures decline first on projection; quotient declines on its package | real dependency closures preserve stable first blockers |
| repeated import | identical report and declaration debug projection | deterministic construction |
| unknown record | malformed rejection at line 2 | no open-world guessing |
| forward expression reference | malformed rejection at line 2 | topological stream contract |
| projection | stable unsupported decline | missing kernel feature is not erased |
| format 4.0.0 mutation | stable unsupported decline | version changes fail closed |
| theorem-body mutation | kernel rejects `identity` | parsing cannot grant theorem credit |
| exported recursor-rule mutation | importer rejects the group | generated computation is compared |
| partial definition | stable unsupported decline | unsafe/partial code cannot enter default profile |
| line/record limits (two cells in one test) | resource rejection | bounded input contract |

The Rust test count is eleven because the official blocker-fixture test contains
three cells and the final resource test contains both line
and record cells.

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

L1 is not complete because there is no fuzz target, axiom type digest, completed
wire-model separation for every unsupported variant, truncation/duplicate-ID/
deep-nesting matrix, or large-stream checkpoint/publication protocol. L2 is not
complete because projections, literal typing, quotients, recursive-indexed,
mutual, nested, and reflexive groups remain explicit declines.

## Next evidence-bearing increments

1. Preserve the landed projection/Nat/quotient streams and source/command/hash-
   bound String closure; generate recursive-indexed Vector, mutual, nested, and
   reflexive families.
2. Add a generated parsed/translated/admitted/dual-admitted matrix from those
   fixtures.
3. Add duplicate-ID, truncation-at-every-record, oversized integer, deep JSON,
   unknown-field, and whole-stream publication mutations.
4. Hash axiom names **and types**, then inventory the 64 Axeyum prelude axioms
   against that stable identity.
5. Export the smallest dependency-closed `Init` root and rank the actual decline
   population.
6. Implement projection representation/inference/constructor reduction, then
   rerun the literal closures before choosing the next slice.

The four-root
[`official blocker census`](lean4export-official-blocker-census-2026-07-21.md)
resolves the first implementation choice for the measured roots: projection is
the first slice. It does not replace the broader `Init` dependency-closure
census.

Do not begin a native Lean parser, Lake clone, standalone LSP, compiler, or
mathlib breadth campaign before this import matrix shows which core constructs
actually block dependency-closed declarations.
