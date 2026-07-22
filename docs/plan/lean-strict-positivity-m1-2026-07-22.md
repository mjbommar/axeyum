# Lean strict positivity: M1 trusted-preflight result

Status: complete; M2 public-family matrix and generated grammar next

Date: 2026-07-22

Parents:

- [TL2.11 execution plan](lean-strict-positivity-tl2.11-plan-2026-07-22.md);
- [proposed ADR-0352](../research/09-decisions/adr-0352-preregister-lean-strict-positivity.md);
- [M0 source freeze](lean-strict-positivity-m0-2026-07-22.md).

## Result

M1 adds a separate strict-positivity preflight to `Kernel::add_inductive` for
the currently representable single-family declaration profile. The preflight
runs after the family parameter/index telescope has been opened and before the
temporary family declaration is inserted into the environment.

For each non-parameter constructor field it now:

1. weak-head normalizes the field;
2. accepts a field with no occurrence of the family;
3. rejects a family occurrence in a `Pi` domain as
   `NonPositiveInductiveOccurrence`;
4. recursively checks the instantiated `Pi` codomain;
5. otherwise accepts only the exact family constant and universe instance,
   fixed parameter expressions, complete index arity, and family-free indices;
6. classifies every other containing form as `InvalidInductiveOccurrence`.

Both errors carry the family, constructor, and zero-based non-parameter field
index. Malformed parameter telescopes remain owned by the later typed
constructor checks rather than being reclassified by the preflight.

## Ordering and regression evidence

The ordering regression combines a negative field with a dangling constant in
its codomain. It receives the registered non-positive error instead of the
later `UnknownConst` and compares the complete ordered environment snapshot
before and after the failed call. No family or constructor declaration is
published.

Additional exact public-path tests reject:

- the family nested beneath a foreign head;
- the family inside its own recursive index;
- a mixed positive/negative `Pi` field.

The pre-existing positive controls remain unchanged:

- direct-recursive `Nat`, `List`, and tree families admit and compute;
- a canonical recursive-indexed field still returns
  `RecursiveIndexedNotSupported`;
- a positive parametric reflexive field still returns
  `ReflexiveOrNestedNotSupported`.

This is the intended two-stage boundary: M1 establishes the soundness guard but
does not widen the admitted inductive fragment.

## Bounded gates

All commands used at most two Rust build jobs and the repository's 4 GiB
memory wrapper:

```text
CARGO_BUILD_JOBS=2 MEM_LIMIT_GB=4 ./scripts/mem-run.sh \
  cargo test -p axeyum-lean-kernel --lib
  -> 182 passed; 0 failed

CARGO_BUILD_JOBS=2 MEM_LIMIT_GB=4 ./scripts/mem-run.sh \
  cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings
  -> pass

CARGO_BUILD_JOBS=2 MEM_LIMIT_GB=4 RUSTDOCFLAGS='-D warnings' \
  ./scripts/mem-run.sh cargo doc -p axeyum-lean-kernel --no-deps
  -> pass
```

Focused `rustfmt --edition 2024` and `git diff --check` also pass for the three
modified Rust files.

## Remaining gates

M1 is not ADR acceptance and does not complete TL2.11/T6.0.2. M2 must still:

- exercise all twelve preregistered rows through the public admission path;
- cover parameters, indices, sorts, multiple constructors, and first/later
  failing fields with exact transactional outcomes;
- run at least 256 independently classified generated cases twice and compare
  the serialized summaries byte-for-byte.

M3 must then execute the immutable official sources with pinned Lean twice,
add the mandatory official differential/import boundary, and rerun the frozen
construct matrix. Only M4 may accept ADR-0352 and mark TL2.11/T6.0.2 complete.
