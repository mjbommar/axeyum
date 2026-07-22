# Lean recursive induction hypotheses: M1 shared-representation result

Status: complete; M2 generalized native semantics is next

Date: 2026-07-22

Parent:
[TL2.12 execution plan](lean-recursive-induction-hypotheses-tl2.12-plan-2026-07-22.md)

Decision gate:
[ADR-0353](../research/09-decisions/adr-0353-preregister-lean-recursive-induction-hypotheses.md)

Baseline: `f819db227b4e8a21a77905fcf87df36127b181f7`

## Result

M1 establishes the shared trusted representation required before TL2.12 may
widen recursive admission. Constructor checking, minor-premise construction,
and computation-rule construction now use one WHNF telescope-tail operation
for a field of the form:

```text
u : Pi xs, I params indices
```

The operation:

- WHNFs the field type and every opened telescope body;
- preserves nested binder names, types, dependencies, and binder information;
- validates the exact family constant/universe instantiation, fixed parameter
  values, complete index arity, and occurrence-free indices;
- optionally applies the recursive field value to the opened telescope in
  lockstep;
- pops every temporary local before returning expressions for abstraction.

`CheckedCtor` stores only a stable field position and telescope depth. The
minor and rule paths independently reopen the field in their current local
context and use the resulting indices and applied value. A disagreement is the
typed `RecursiveFieldShapeMismatch` error; it cannot silently turn a recursive
field into a non-recursive one and does not panic.

M1 deliberately records only the already-supported zero-telescope,
zero-index direct field. `RecursiveIndexedNotSupported` and
`ReflexiveOrNestedNotSupported` retain their exact existing public behavior.
The importer policy is unchanged, and neither M0 computation stream has been
run through Axeyum.

## Direct-recursive identity

The official direct-recursive importer control now asserts the complete
canonical recursor declaration identities:

| Declaration | Canonical content SHA-256 |
|---|---|
| `MiniNat.rec` | `dee04a36959066e63f15d5711a5a03de2ac91d71333c48135ef0fdc89cb0f5ef` |
| `MiniList.rec` | `1087558f366706316eefaca0abc48a4b592da2a8496e5d6bbdaa7eea5b677660` |

These digests cover the independently regenerated declaration type and
recursor rules. Existing exact computations remain green:

- `nat_rec_computes_identity`;
- `list_rec_computes_length`;
- all direct-recursive iota-backbone and importer comparison tests in the
  bounded kernel/importer suites.

## Bounded evidence

All Rust build/test commands ran with at most two build jobs through the
repository's 4 GiB memory wrapper; final crate-wide tests, clippy, and rustdoc
used one job.

| Gate | Result |
|---|---|
| `cargo test -p axeyum-lean-kernel --lib` | 182 passed |
| `cargo test -p axeyum-lean-kernel --test strict_positivity` | 2 passed; frozen 840-case summary repeated byte-identically |
| direct `MiniNat.rec` / `MiniList.rec` importer identity control | 1 passed; 19 filtered |
| complete `axeyum-lean-import` suite | 30 tests plus one compile-fail doctest passed |
| focused Nat/List computation controls | 2 passed |
| focused recursive-indexed/reflexive decline controls | 2 passed with the original typed variants |
| M0 recursive-IH, strict-positivity, and construct-matrix contract tests | 31 passed |
| three corresponding contract validators | valid |
| focused all-target/all-feature clippy | warnings denied; passed |
| focused rustdoc | warnings denied; passed |
| parity-doc underlying recipe | 62 Python tests plus all freeze/generator/checker steps passed |
| foundational resources / relative links | 137 concepts, 174 packs, all links valid |

The 840-case summary remains exactly:

```text
cases=840
outcomes=admit:174,recursive-indexed:42,reflexive:144,non-positive:270,invalid:210
descriptor-fnv1a64=02985687422aa0ff
```

## Negative observations retained

The first shared-helper draft exposed two defects before this checkpoint was
accepted:

1. eager construction through `bool::then_some` sliced an invalid application
   spine even when the tail predicate was false, panicking on ordinary
   parametric families; explicit conditional construction fixed the issue and
   the complete 182-test kernel suite then passed;
2. WHNF classification initially changed a reducible `let`-wrapped indexed
   profile from the frozen reflexive decline to recursive-indexed. The
   mandatory 840-case grammar caught the error-precedence drift. M1 now retains
   the historical surface-form decline boundary while recording the shared
   semantic shape for the later, explicit M2 widening.

These were implementation failures, not accepted changes to the plan or the
baseline.

The first kernel doctest link also failed twice because the shared `/tmp` tmpfs
was already 80% full and the link exhausted its remaining space: `lld` surfaced
signal 7, while a diagnostic GNU `bfd` run reported `No space left on device`.
The unchanged doctest passed from a fresh repository-local temporary directory.
No broad `/tmp` cleanup or memory-limit increase was performed.

## Claim boundary

M1 proves that the existing direct-recursive path has been moved onto a
context-safe representation capable of carrying telescopes and indices without
identity drift. It does **not** claim native admission of recursive-indexed or
higher-order fields, official `MiniVector`/`MiniAcc` import, new recursor
computation, importer-policy widening, or ADR acceptance.

## Next gate

M2 may now enable the preregistered native positive rows using the representation
already exercised by direct recursion. It must add telescope/index-aware native
tests and mutations, preserve the exact direct identities above, distinguish
positivity outcomes from intentional feature-admission changes, and run the new
fixed-seed recursive-profile grammar before any importer policy change.
