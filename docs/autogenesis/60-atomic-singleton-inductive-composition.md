# Atomic singleton-inductive composition

Date: 2026-08-20

## Result

The public theorem-rooted composition boundary can now reconstruct a demanded
non-recursive singleton inductive in the real imported target. It does not copy
three declaration records. It rebuilds the family and ordered constructor
types in the target arena and submits them together to `Kernel::add_inductive`;
the target kernel checks the package and generates its own recursor.

The exact r082 control uses a freshly checked native theorem,
`Composition.existsTrue`, whose proof requires `Exists`. The imported target
contains no existential package. V3 reconstructs:

- `Exists`;
- `Exists.intro`; and
- target-generated `Exists.rec`.

All three exact target declaration identities equal their source identities.
The independently admitted control theorem has an empty kernel-derived axiom
footprint. The target environment changes from
`82ac7b0143bdd9891b666a37220fb91b86afc4af4b920d68773d80b5c9348855`
to
`52e5b2e9dcc275fe83e77b9b0ca7c5b4f00b8a3b2cca3b471d0c7d29ad947847`.
The package-and-theorem receipt is
`71a9824ff9c091dbaa4825dac197ecd906881f2f0bbb7c3879a793eb8b04afdc`.

## Boundary

The source closure must contain the complete missing family, every constructor
in checked order, and the canonical generated recursor. The family must be
non-recursive and its recursor must have one motive with matching
parameter/index counts and reduction rules. Any partial collision or absent
member declines before publication.

Recursive `Nat`, a synthetic two-family mutual group, standalone unsupported
kinds, axioms, and opaques remain negative controls. Nested, mutual, recursive,
partial, and quotient packages receive no authority from the singleton result.
Every later theorem still passes the ordinary target admission gate, and any
failure discards the private clone.

Receipt schema V3 records the family, ordered constructors, recursor, and exact
source and reconstructed-target identities. Reverification recomposes the
package rather than accepting those fields as assertions.

## Measured downstream delta

The unchanged `Nat.eq_one_of_dvd_one` control now passes translated
definitional compatibility for the order surface and recognizes its singleton
logical packages. Its first unsupported closure member becomes:

```text
UnsupportedMissingDeclaration { name: "Nat.mul", kind: "definition" }
```

The failed attempt leaves the caller environment identity unchanged. The next
bottom-up increment is therefore exact checked definition composition, not
broader inductive transport.

A definition extension must preserve the rebuilt type, value, universe
parameters, and reducibility hint; admit through `Kernel::add_declaration`;
record both source and target identities; and retain fail-closed conflicts,
opaques, free variables, and late-stage rollback. After `Nat.mul` enters,
retry the same theorem root to let the next real closure member choose the
following task.

That measured follow-up is now complete: [checked definition
composition](61-checked-definition-composition.md) admits exact `Nat.mul` and
`Nat.dvd` plus eight axiom-free theorems. The unchanged larger control advances
to the imported/native `Bool.rec` branch-order mismatch.

## Evidence

The immutable exact-commit observation is:

`/nas3/data/axeyum/autogenesis/probes/fced2b166-singleton-inductive-composition-v9/observation.json`

It is mode `0444` inside a mode `0555` directory and binds the exact V3 API,
probe, environment transitions, package identities, theorem footprint,
receipts, negative decline, and no-write authority. Verify with:

```sh
python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
CARGO_TARGET_DIR=/data0/axeyum/codex-singleton-target \
  cargo test -p axeyum-lean-import --lib
```
