# Proof-isolated Euclidean construction capsule

Date: 2026-08-20

## Result

The next clean construction context no longer needs to browse a Mathlib or Lean
source tree. A generated capsule contains exactly 13 theorem statements needed
to attempt the joint quotient/remainder fuel invariant, together with the three
audited computation-root identities and their empty footprints.

The capsule is
[`euclidean-joint-div-mod-proof-capsule-v1.json`](../../artifacts/autogenesis/euclidean-joint-div-mod-proof-capsule-v1.json).
It is regenerated directly from the immutable 39 MB statement inventory and
the retained equation-root audit. The generator rejects a changed or mutable
external input, a missing or duplicate statement, a changed root identity, or
a nonempty audited footprint.

## Isolation boundary

The capsule separates two kinds of input:

- theorem statements, modules, and type hashes are readable construction
  material;
- the root-selected lean4export stream is identified by path and SHA-256 but is
  permitted only as input to Axeyum's kernel importer.

The stream must not be printed, searched, opened, or supplied as model context.
Mathlib/Lean theorem source, olean theorem values, upstream proof terms, and the
contaminated predecessor transcript are likewise forbidden. Compiler
diagnostics from independently authored source remain allowed because they
describe that new source, not the upstream proof.

If the boundary is crossed, the capsule requires discarding the authored proof,
claiming zero proof credit, and restarting from the capsule in another fresh
context. This converts clean-room discipline from a prose reminder into a
reproducible, mutation-tested input contract.

## Construction contract

The only authorized theorem is:

```text
Axeyum.Autogenesis.divModGoReconstruct :
  forall y (hy : 0 < y) fuel x (hfuel : x < fuel),
    y * Nat.div.go y hy fuel x hfuel +
      Nat.modCore.go y hy fuel x hfuel = x
```

It must be independently authored by induction on shared fuel, reconstruct
twice, enumerate its direct dependencies, and have an empty kernel-derived
footprint. The capsule authorizes zero exact-target submissions, executor
invocations, semantic receipts, evaluation credit, or ledger writes.

## Why this is reusable

This is more than a handoff for one Fibonacci theorem. The same capsule pattern
can isolate future theorem construction from large reference libraries while
still letting their checked definitions and generated equations enter the
kernel by hash. It is a concrete mechanism for replacing Mathlib bottom-up:
read propositions, independently rebuild proofs, and let only a small checker
see proof-bearing imports.

## Verification

```sh
python3 scripts/gen-autogenesis-euclidean-proof-capsule.py --check
python3 -m unittest \
  scripts.tests.test_gen_autogenesis_euclidean_proof_capsule
```
