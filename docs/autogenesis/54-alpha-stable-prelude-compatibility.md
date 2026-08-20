# Alpha-stable prelude compatibility

Date: 2026-08-19

## Result

The imported/native Nat prelude seam is narrower, but it is not yet safe to
compose. Axeyum now has a separate cross-kernel expression identity that ignores
cosmetic binder names and normalizes universe-parameter spelling. The existing
canonical identity used by receipts is unchanged.

Against the proof-isolated Mathlib 4.30.0 `r082` train stream, the native Nat
prelude has 43 named overlaps:

- 7 declarations have exact canonical identity;
- 18 more have alpha-stable type identity but different declaration content;
- 18 still have different type identities under this conservative comparison.

The remaining group is not evidence of 18 genuine incompatibilities. Rendered
types show that binder information and imported notation or instance expansion
explain at least part of it. The probe therefore records these rows as
unresolved and does not authorize reuse.

## Architectural boundary

Receipt identity and compatibility answer different questions. A receipt must
continue to bind the exact admitted declaration. A compatibility check may
ignore presentation-only differences, but only when the kernel-relevant type
shape and reused declaration behavior are independently checked.

The next bounded increment is therefore a dedicated kernel-type compatibility
identity that ignores binder names, binder information, and universe-parameter
spelling while retaining term structure and constant identities. It must be
validated against positive alpha-equivalent controls and negative sort,
constant, application, recursor-order, and universe-incidence controls. Only
then should the r082 overlap be reclassified and selected declarations be
transported into one fresh kernel.

## Evidence and authority

The immutable observation is
`/nas3/data/axeyum/autogenesis/probes/d1eb38a13-fib-coprime-prelude-compatibility-v2/observation.json`.
It binds the exact stream and probe hashes. The run inspected the train
partition, displayed no proof bodies, invoked no proof search, made no target
kernel submission, and performed no ledger write. It establishes a
compatibility census, not the Fibonacci coprimality theorem and not permission
to graft the native prelude.

Verify it with:

```sh
python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
```

The subsequent
[kernel-type-shape census](55-kernel-type-shape-prelude-compatibility.md)
resolved ten of the eighteen conservative mismatches as binder-metadata-only
and retained eight as structurally different.
