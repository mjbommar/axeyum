# Lean mutual inductive groups: M1 representation and singleton delegation

Status: complete; M2 native mutual semantics is next

Date: 2026-07-22

Parent:
[TL2.13 execution plan](lean-mutual-inductive-groups-tl2.13-plan-2026-07-22.md)

Decision gate:
[proposed ADR-0354](../research/09-decisions/adr-0354-preregister-lean-mutual-inductive-groups.md)

Baseline: `b23a514a7c7f5b35b880514863c28a3e994d6574`

## Result

M1 establishes the ordered public group representation and one scalable atomic
transaction before any multi-family semantic admission. The new
`InductiveFamilySpec` owns one family name, closed type, and constructor list;
`Kernel::add_mutual_inductive` receives the universe-parameter list and shared
parameter count exactly once plus the ordered family slice.

`Kernel::add_inductive` is now a source-compatible one-family wrapper over that
path. The complete established single-family checker, positivity rule,
constructor classification, recursor generation, self-check, publication, and
iota rules remain one private worker; no second singleton algorithm exists.

For more than one family, M1 checks only the preregistered facts that must be
stable before M2:

1. the group is nonempty;
2. every family, constructor, and generated recursor name is fresh and unique;
3. every family type is well typed;
4. every family exposes the declared shared parameter count;
5. later parameter domains are definitionally equal to the first family's
   domains after instantiation with the exact same shared locals;
6. each family opens its own remaining index telescope;
7. every resulting universe is equivalent to the first family's universe.

A valid group with two or more families then returns the typed
`MutualInductiveNotSupported { family_count }`. M2, not M1, owns complete-group
positivity, constructor checking, multiple motives/minors, target-family
recursive calls, mutual-`Prop` elimination, and multi-family publication.

## Atomic transaction

The environment now keeps a private insertion log. An inductive transaction
records its current log length, and an error removes only declarations first
inserted after that checkpoint in reverse order. Environment-sensitive infer
and WHNF caches are cleared on rollback. Name, level, and expression interning
remain monotone and deterministic.

This is intentionally not a clone of the complete environment. A clone per
inductive would make a large official import quadratic in the number of already
admitted declarations and increase peak memory. Checkpoint cost is constant;
rollback cost is proportional to the failed group. The log is private, is not
iterated, serialized, or hashed, and does not change declaration-identity v1.

The existing single-family worker's local cleanup remains defensive, while the
outer transaction is authoritative. A failed constructor/recursor attempt can
be retried with the same names and correct types; no declaration or stale
environment-sensitive cache escapes.

## Typed M1 boundary

M1 adds these exact errors:

- `EmptyInductiveGroup`;
- `DuplicateInductiveGroupName { name }`;
- `MutualInductiveParameterMismatch { family, parameter_index }`;
- `MutualInductiveResultUniverseMismatch { family }`;
- `MutualInductiveNotSupported { family_count }`.

An already-admitted name retains `DeclarationExists { name }`. Singleton
malformed-constructor errors retain their existing payloads; the focused retry
control still returns
`ConstructorResultMismatch { expected: family, ctor: constructor }`, restores
the exact prior environment, and then admits the corrected family under the
same names.

## Singleton identity and retained controls

One of nine new public-path tests compares the legacy `add_inductive` surface
with a direct one-family `add_mutual_inductive` call constructed in an
independent kernel. Their complete ordered `Declaration` values are equal,
including the generated recursor type and every rule, and the `zero`
constructor's iota case computes to the same minor.

The official importer control retains the exact canonical recursor identities:

| Declaration | Canonical content SHA-256 |
|---|---|
| `MiniNat.rec` | `dee04a36959066e63f15d5711a5a03de2ac91d71333c48135ef0fdc89cb0f5ef` |
| `MiniList.rec` | `1087558f366706316eefaca0abc48a4b592da2a8496e5d6bbdaa7eea5b677660` |

The retained 768-case recursive grammar remains byte-identical at descriptor
`0d245921566be735`. The retained 840-case positivity grammar remains
byte-identical at TL2.11 descriptor `02985687422aa0ff`, with its current
partition unchanged:

```text
admit:360,recursive-indexed:0,reflexive:0,non-positive:270,invalid:210
```

The historical TL2.11 baseline partition embedded in that summary also remains
unchanged. No M0 mutual computation stream was passed to Axeyum, and the
importer's `inductive-mutual` policy decline is untouched.

## New focused cases

The M1 integration binary covers:

- exactly equal singleton wrapper versus direct singleton-group declarations;
- identical direct-recursive zero iota computation;
- typed empty-group rollback over a nonempty prior environment;
- definitionally equal dependent shared parameters with intentionally different
  binder annotations;
- distinct per-family index counts reaching the policy decline;
- parameter-count and parameter-type mismatches identifying the exact later
  family and parameter position;
- inequivalent result universes identifying the exact later family;
- duplicate family, cross-family constructor, and generated-recursor names;
- collision with an existing declaration retaining `DeclarationExists`;
- exact singleton error payload, full rollback, cache-safe same-name retry, and
  successful corrected publication.

## Bounded evidence

Every Rust command used one build job under the repository's 4 GiB wrapper.

| Gate | Result |
|---|---|
| complete `axeyum-lean-kernel` all-target/all-feature suite | 182 unit + 51 integration tests passed |
| new M1 group representation binary | 9 passed |
| recursive/positivity generated controls | 768 + 840 cases repeated byte-identically |
| exact direct-recursive importer identity control | passed with both frozen digests |
| complete `axeyum-lean-import` all-target/all-feature suite | 34 integration tests passed |
| kernel/importer clippy | all targets/features, warnings denied; passed |
| kernel/importer rustdoc | warnings denied; passed |
| kernel doctest | 1 passed from repository-local temporary storage |

The first doctest link attempt used the shared `/tmp`, which was 80% full, and
`lld` terminated with signal 7. The unchanged doctest passed immediately with
`TMPDIR=target/tl213-m1-doctest`; no memory cap was raised and no shared files
were deleted.

The first transaction draft cloned the full environment. It passed focused
tests but was rejected before this checkpoint because repeated official imports
would scale quadratically. The insertion-log checkpoint replaced it before the
complete gates above.

## Claim boundary

M1 proves that Axeyum has one explicit ordered group input, exact common-
parameter/result-universe preflight, efficient environment rollback, and a
single-family wrapper with retained declarations, computations, identities,
generated summaries, and error payloads.

It does **not** claim multi-family positivity, constructor admission, mutual
recursor generation, mutual iota computation, importer support, official
mutual-stream admission, mutual `Prop` elimination, nested/well-founded
lowering, ADR acceptance, or Lean parity.

## Next gate

M2 generalizes positivity to the complete family occurrence set, checks all
constructors against provisionally staged family headers, derives all motives
and globally ordered minors, selects the recursive target family's motive and
recursor, self-checks every per-family recursor, and commits the complete group
atomically. It closes the preregistered native positive/negative rows and
semantic mutations without passing the M0 official streams to the importer.
