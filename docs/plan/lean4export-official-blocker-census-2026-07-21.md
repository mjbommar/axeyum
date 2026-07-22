# Official `lean4export` blocker census: projections, literals, and quotient

Status: measured implementation-order gate

Date: 2026-07-21

Parent roadmap:
[`lean-system-compatibility-roadmap-2026-07-21.md`](lean-system-compatibility-roadmap-2026-07-21.md)

Decision gate:
[ADR-0345](../research/09-decisions/adr-0345-preregister-lean-system-interoperability.md)

## Result

Four declaration roots were exported from one official Lean 4.30 environment
with `lean4export` format 3.1. The result changes the implementation order from
a guessed feature list to an observed dependency order:

1. **Projection was first and is now cleared.** TL2.2-TL2.4 represent, infer,
   reduce, and translate it; the four-record official structure closure now
   admits nine declarations and computes its selector.
2. **Bignum Nat plus literal typing is now the exact next blocker.** Re-running
   the committed Nat root advances its first decline to line 125
   `literal-nat-bignum-and-typing`. Literal typing must not land while the kernel
   still stores only `u128`.
3. **String remains a mixed, unrefreshed closure.** Its 290 declaration records
   contain recursive-indexed inductives plus Nat/String literals, but the exact
   post-projection first blocker is unmeasured until the bound large stream is
   retrieved or regenerated.
4. **Quotient is isolated.** `Quot.mk` produces the fixed four-record quotient
   package plus `Eq`, with no projection or literal blocker.

This is a four-root implementation-order result, not an `Init` population
frequency claim. A complete minimal-`Init` census remains open.

## Exact tool and source identity

- Lean: 4.30.0 at
  `d024af099ca4bf2c86f649261ebf59565dc8c622`;
- `lean4export`: v4.30.0 at
  `a3e35a584f59b390667db7269cd37fca8575e4bf`;
- export format: 3.1.0;
- source:
  [`lean4export-v4.30-blocker-census.lean`](fixtures/lean4export-v4.30-blocker-census.lean),
  SHA-256
  `df164017b06f5d4a136b0895b633a061686f5c1aad65e74f9819fb044629bb67`.

The source deliberately imports `Init.Prelude`, then defines one two-field
structure, one projection-using definition, one Nat literal, and one String
literal. `Quot.mk` is selected directly from the same environment.

## Closure census

`N/L/E/D` means exported names / nonzero levels / expressions / declaration
records. “Current Rust result” is the exact result from `axeyum-lean-import`,
not merely the research probe's blocker inventory. The String result cannot be
refreshed locally because its exact large stream was intentionally not retained.

| Root | Bytes / records | N/L/E/D | Occurring blockers | Current Rust result | Exact stream SHA-256 |
|---|---:|---:|---|---|---|
| `importPairLeft` | 5,491 / 89 | 21/2/61/4 | projection x1 | **pass:** 61/61 translated, 9 declarations admitted, selector computes | `731d9a50659adadf11b2faac18f7c299211f20f85a48371a25a8c79cd4cec5fa` |
| `importNatLiteral` | 7,381 / 130 | 30/4/90/5 | projection x1; Nat literal x1 | line 125 `literal-nat-bignum-and-typing` | `8cdb40da9441b77d140f1c794ac04e6dc941fee7466004bf3595ae43c6782603` |
| `importStringLiteral` | 570,807 / 10,339 | 1,781/24/8,243/290 | projection x27; Nat literal x20; String literal x1; recursive-indexed inductive | **not rerun:** old line-184 projection decline retired; new first blocker unmeasured until exact bytes are retained | `2404a6ca64999088ee9e4aa76f3426e77fda8eed5c63f5d8ad593c6b08ae0ab4` |
| `Quot.mk` | 6,301 / 121 | 25/3/87/5 | quotient package x4 | line 65 `quotient-package` | `060bb9d132fa6b7917170cd549ded5fb5703935c74ca1f7f32a3b77b6d9903c8` |

The exact small streams are committed as:

- [`lean4export-v4.30-projection.ndjson`](fixtures/lean4export-v4.30-projection.ndjson);
- [`lean4export-v4.30-nat-literal.ndjson`](fixtures/lean4export-v4.30-nat-literal.ndjson);
- [`lean4export-v4.30-quotient.ndjson`](fixtures/lean4export-v4.30-quotient.ndjson).

The 570,807-byte String closure is intentionally not duplicated in the source
tree at this gate. Its producing source, exact target, byte/record counts, and
stream hash are committed; the command below regenerates it byte-identically.
It should enter an artifact store with the later dependency-closure matrix,
rather than making a four-root research probe look like a supported library.

Two consecutive exporter runs produced all four hashes identically.

## Assurance-separated matrix

| Profile | Syntax inventoried | Translated | Independently admitted | Official source accepted | Credit |
|---|---|---|---|---|---|
| flat `Two`/identity fixture | yes | yes | 8 declarations | yes | exact dual-admitted flat slice |
| `MiniNat`/`MiniList` fixture | yes | yes | 11 declarations, zero axioms | yes | exact dual-admitted direct-recursive slice |
| projection closure | yes | yes | 9 declarations; computes | yes | exact K1 projection-root pass |
| Nat-literal closure | yes | no; Nat literal is first | no | yes | refreshed blocker/order evidence |
| String-literal closure | yes | not rerun after projection | no | yes | inventory plus historical blocker evidence only |
| quotient closure | yes | no; stable decline | no | yes | blocker/order evidence only |

Official compilation proves that the source is accepted by the pinned official
toolchain. The projection row now also has independent Axeyum admission and
computation evidence. It does not grant those results to the still-declined
rows; conversely, the inventory probe seeing every record never grants
translation or admission credit by itself.

## Reproduction

From the pinned `lean4export` checkout, with the Lean 4.30 toolchain selected:

```sh
AXEYUM_ROOT=/path/to/axeyum
cp "$AXEYUM_ROOT/docs/plan/fixtures/lean4export-v4.30-blocker-census.lean" \
  AxeyumImportUnsupported.lean
lean -j1 -o AxeyumImportUnsupported.olean AxeyumImportUnsupported.lean

for target in importPairLeft importNatLiteral importStringLiteral Quot.mk; do
  LEAN_PATH=. .lake/build/bin/lean4export \
    AxeyumImportUnsupported -- "$target" |
    python3 "$AXEYUM_ROOT/scripts/prototype_lean4export_census.py" --label "$target"
done
```

The census helper hashes the exact bytes and invokes the independent Python
format/topology/blocker probe. It deliberately reports syntax and blockers, not
`checked=true`. Its own fixture/hash tests and the existing probe tests are in
`scripts/tests/`.

The Rust example accepts `-` for stdin, so the first product decline can be
checked without retaining a raw stream:

```sh
LEAN_PATH=. .lake/build/bin/lean4export \
  AxeyumImportUnsupported -- importPairLeft |
  cargo run -q -p axeyum-lean-import --example lean4export_import -- -
```

## Why projection is an L-sized trusted-kernel slice

**Implementation checkpoint (2026-07-21):** items 1--4 and 6--7 below are
complete under TL2.2-TL2.4, including structural/de Bruijn operations, both
renderers, checked parameter/index metadata, dependent telescope inference,
constructor reduction, validated wire translation, and malformed-shape
mutations. The exact projection root now independently admits and computes.
Item 5 remains TL2.5 and deliberately receives no credit from this slice.

The census establishes priority, not implementation simplicity. Projection is
a first-class Lean core expression, so it changes more than the importer:

1. **DONE (TL2.2):** add `Proj(structure_name, field_index, structure)` to the kernel expression
   language and every structural traversal, hash-consing, de Bruijn operation,
   metadata computation, and renderer;
2. **DONE (TL2.3):** preserve enough single-constructor structure metadata to validate the
   structure name, field index, parameters, and constructor telescope;
3. **DONE (TL2.3):** infer a dependent field type by substituting parameters and earlier field
   projections into the selected field's type;
4. **DONE (TL2.4):** reduce a projection of a constructor application to the selected field;
5. add structure eta only as a separately tested definitional-equality slice;
6. **DONE (TL2.4):** translate the wire `proj` only after the kernel can reject malformed names,
   indices, constructor shapes, and dependent-field substitutions;
7. **DONE for TL2.4:** mutation-test wrong structure names, out-of-range fields, under/over-applied
   constructors, dependent second fields, universe-polymorphic structures, and
   non-constructor neutrals.

The existing
[`kernel gap audit`](../prover-track/research/06-kernel-gap-analysis.md)
independently sized projection plus structure eta at roughly 800--1,300 lines
and identified the same official-kernel algorithm. The new contribution here is
that official dependency closures now prove it is the first blocker, not merely
the most invasive missing enum variant.

Projection and structure eta should be separate commits and gates. Constructor
projection reduction and type inference can unlock the measured closure without
immediately expanding definitional equality with eta; eta earns credit only
after positive and false-equality controls pass both kernels.

## Updated next order

1. **DONE:** accept ADR-0345's separate wire/checker boundary.
2. **Projection slice DONE:** TL2.2-TL2.4 implement and adversarially test
   structure, dependent typing, constructor reduction, wire translation, and
   the committed projection closure.
3. **Nat rerun DONE:** its first decline is now line 125 literal typing. The
   unretained String stream must be retrieved/regenerated before its new first
   blocker can be measured; do not infer it from syntax counts.
4. **NEXT:** add TL2.5 structure eta as its own definitional-equality gate, then
   replace `Lit::Nat(u128)` with an arbitrary-precision representation before
   admitting any `natVal`; then add typing and bounded accelerated reductions.
5. Land positivity before recursive-indexed/reflexive admission, then re-run the
   String closure.
6. Treat quotient as an independent fixed-package slice; do not let it reorder
   the projection/literal dependency chain merely because its fixture is small.
7. Expand from four selected roots to a dependency-closed minimal-`Init` census
   and generate the parsed/translated/admitted/dual-admitted matrix.

No parser, macro, elaborator, tactic, compiler, Lake, LSP, or mathlib-cloning
work is justified by this result. It strengthens the bridge-first roadmap: the
next useful work is one measured core construct.
