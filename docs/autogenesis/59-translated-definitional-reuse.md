# Translated definitional reuse

Date: 2026-08-20

## Result

The first apparent representation bridge was not a mathematical or kernel
capability gap. `Nat.zero_le` and `Nat.le_trans` differ structurally across the
native and imported environments because the import retains reducible
typeclass and numeric-literal wrappers. After rebuilding each source type in a
private clone of the actual target, the target kernel judges it definitionally
equal to the existing target type.

ADR-0524 therefore adds a second explicit receipt class,
`translated-definitional-equality`. It is intentionally weaker than exact
declaration identity and grants only permission to submit fresh translated
proofs to the target gate. The receipt schema advances to
`axeyum.checked-theorem-composition.v2` so the policy change cannot be confused
with V1 evidence.

## Measured downstream delta

Under V1, the negative `Nat.eq_one_of_dvd_one` root declined at
`Nat.zero_le`. Under V2, the same source, target, roots, and no-write authority
advance past both order declarations and decline at:

```text
UnsupportedMissingDeclaration { name: "Exists", kind: "inductive" }
```

The caller target environment identity is unchanged. The positive
`Nat.add_comm` control remains exactly the same three axiom-free theorem
admissions. Its eight reused dependencies all use the cheaper
`kernel-type-shape` class, demonstrating that the fallback is demand-triggered
rather than applied indiscriminately.

The in-tree semantic control uses a reducible proposition wrapper whose source
and target type-shape digests differ. Translation, target inference to a sort,
and target definitional equality succeed; the new theorem still must pass the
ordinary admission gate. Mutating the recorded compatibility class invalidates
receipt replay.

## Historical next boundary

At this checkpoint the measured blocker was atomic inductive-package
composition. `Exists`
cannot be copied as three unrelated declarations: its family, constructor, and
generated recursor share positivity, parameter, elimination, and reduction
contracts. The smallest responsible extension is singleton-package-only,
reconstructed into the target arena and submitted through
`Kernel::add_inductive` in the private clone. Mutual, nested, partial, and
quotient packages must continue to decline until separately demanded and
specified.

The subsequent
[atomic singleton-inductive composition](60-atomic-singleton-inductive-composition.md)
admits that exact package in r082 and moves the next failure to `Nat.mul`.
This page retains the V2 receipt identity.

## Evidence

The immutable exact-commit observation is:

`/nas3/data/axeyum/autogenesis/probes/c17b7e65b-nat-defeq-reuse-v8/observation.json`

It is mode `0444` inside a mode `0555` directory and is bound by the tracked
manifest to the exact probe and API hashes. Verify with:

```sh
python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
cargo test -p axeyum-lean-import --lib
```
