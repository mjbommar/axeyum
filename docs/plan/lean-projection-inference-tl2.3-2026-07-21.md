# Lean dependent projection inference — TL2.3 result

Date: 2026-07-21
Status: **complete for native kernel inference; no import or reduction credit**

## Result

The independent Rust kernel now infers the type of a Lean projection

```text
Proj(structure_type_name, zero_based_field_index, structure)
```

for checked, single-constructor inductive structures. The implementation follows
the pinned Lean 4.30 kernel algorithm: infer and weak-head-normalize the projected
value's type, require the declared structure head and complete parameter/index
spine, instantiate the sole constructor telescope, and substitute projections of
earlier fields into dependent later-field types.

This closes **TL2.3 only**. It does not reduce a projection applied to a
constructor (TL2.4), add structure eta (TL2.5), translate `expr-projection` in
`axeyum-lean-import`, or admit the official projection dependency closure.

## Trusted metadata and checks

Checked inductive declarations now retain `num_params` and `num_indices`. The
projection path consumes only metadata produced by the existing transactional
inductive-admission gate and validates all of the following before returning a
field type:

- the projected value's type has the projection node's structure name as its
  constant head;
- that name denotes an inductive with exactly one constructor;
- the type application supplies exactly `num_params + num_indices` arguments;
- the constructor belongs to that inductive and the field index is in range;
- the constructor telescope remains well formed while parameters and earlier
  fields are instantiated; and
- a proof-valued structure is not eliminated into data, matching Lean's
  proof-irrelevance restriction.

Failures are typed and fail closed: `ProjectionTypeMismatch`,
`ProjectionNotInductive`, `ProjectionConstructorCount`,
`ProjectionArityMismatch`, `ProjectionFieldOutOfBounds`,
`MalformedProjectionConstructor`, and `ProjectionFromPropToType`.

## Evidence

`projection_inference.rs` adds four integration families:

1. parameterized dependent fields, including a second-field type that contains
   the first projection;
2. universe-polymorphic parameter metadata and indexed-family metadata;
3. wrong structure names, non-inductive heads, wrong arity, wrong constructor
   count, and out-of-range fields; and
4. Prop-to-Type rejection with a proof-field positive control.

An internal unit test injects inconsistent unchecked metadata and confirms that
the kernel returns `MalformedProjectionConstructor` rather than panicking or
manufacturing a type. The existing representation suite now checks the real
unbound-free-variable failure at the admission boundary.

Under the repository's hard 4 GiB wrapper:

- `axeyum-lean-kernel`: **179 unit tests and 13 integration cases across six
  integration binaries pass**;
- `axeyum-lean-import`: **11 integration tests pass** while projections remain
  intentionally declined; and
- the kernel doctest, warning-denied rustdoc, all-target checking, and
  warning-denied all-target kernel Clippy pass.

The algorithm is cross-checked against the pinned upstream
[Lean 4.30 type checker](https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/type_checker.cpp).
This is design provenance, not an official-Lean differential runtime result.

## Credit boundary and next step

TL2.3 earns native K0 checker credit for projection inference. K1 import remains
declined because the wire translator still rejects `expr-projection`, and the
official projection root cannot compute until TL2.4 implements constructor
projection reduction. TL2.15 also remains partial: the new semantic seam has
deterministic positive and mutation coverage, but the generated seam-fuzz family
must be extended alongside TL2.4/TL2.5 before projection/eta fuzz credit closes.

The next critical-path task is **TL2.4**: reduce projections of constructor
applications, test parameterized and universe-polymorphic cases, then enable the
wire translation only when the pinned official projection closure independently
admits and computes. TL2.5 structure eta remains a separate semantic change and
gate.
