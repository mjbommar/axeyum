# Kernel-type-shape prelude compatibility

Date: 2026-08-20

## Result

The conservative `r082` prelude census now distinguishes kernel-relevant type
structure from elaborator and pretty-printer metadata. Of 43 names shared by
the imported Mathlib environment and Axeyum's native Nat prelude:

- 7 declarations have exact canonical identity;
- 18 more have alpha-stable type identity;
- 10 more have the same kernel type shape after binder information is ignored;
- 8 remain structurally different.

The new identity ignores binder names, binder information, and the spelling of
universe parameters. It retains sorts, constant identities, application and
recursor order, projections, literals, bound-variable structure, and universe
incidence. Positive controls cover Pi and lambda binder metadata and universe
renaming. Negative controls cover sorts, constants, application order,
bound-variable structure, universe sharing, projection indices, lambda versus
Pi, and recursor branch order.

The ten newly classified names are `And.intro`, `Eq`, `Eq.rec`, `Eq.refl`,
`Nat.eq_of_beq_eq_true`, `Nat.le.rec`, `Nat.le.refl`, `Nat.le.step`, `Or.inl`,
and `Or.inr`. Their earlier mismatch was binder metadata, not expression
structure.

## Remaining boundary

The eight unresolved names are `Bool.rec`, `Nat.le_of_succ_le_succ`,
`Nat.le_trans`, `Nat.lt_irrefl`, `Nat.lt_of_lt_of_le`, `Nat.mod_lt`,
`Nat.not_succ_le_zero`, and `Nat.zero_le`. `Bool.rec` differs in constructor
branch order. The Nat rows expose a deeper representation boundary: imported
types use typeclass-expanded `LE.le`, `LT.lt`, `OfNat.ofNat`, and `HMod.hMod`,
whereas the native library uses direct `Nat.le`, `Nat.lt`, `Nat.zero`, and
`Nat.mod` constants. These are not cosmetic differences and remain fail-closed.

Kernel-type-shape equality is a diagnostic, not transport authority. Even the
28 compatible declarations with different content receipts have not been
grafted, replaced, or treated as the native declaration. The next step is to
trace the seven required coprimality lemmas through their declaration closures
and determine which of the eight representation mismatches actually block
replay. Any bridge must be explicit, transactional, and independently checked
in the combined environment.

## Evidence and authority

The immutable observation is
`/nas3/data/axeyum/autogenesis/probes/24b16642e-fib-coprime-kernel-type-shape-v3/observation.json`.
It is read-only inside a read-only directory and binds the exact stream and
probe hashes. The run inspected only the train partition, displayed no proof
bodies, invoked no proof search, made no target kernel submission, and
performed no ledger write.

Verify it with:

```sh
python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
```

The subsequent
[required-theorem closure census](56-required-nat-theorem-closure-census.md)
shows that `Nat.add_comm` reaches none of the eight structural mismatches and is
the first bounded transactional composition slice.
