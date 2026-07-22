# Lean nested-inductive elimination M2: native expansion and restoration

Date: 2026-07-22

Status: complete

Semantic commit: `96b6fbd4da7e20277b338f59983fbe7316b31d22`

Decision gate:
[proposed ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)

Execution contract:
[TL2.14 P0--M6 plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md)

## Result

M2 implements native nested-inductive expansion and restoration inside
`Kernel::add_mutual_inductive`. A structurally recognized application of an
already checked inductive container is expanded into private auxiliary
families, the complete expanded group is checked once by the unchanged
TL2.11--TL2.13 atomic group algorithm, and the temporary group is replaced by
the source families/constructors, their main recursors, and deterministic
`First.rec_1`, `First.rec_2`, ... auxiliary recursors.

The public declaration-identity schema is unchanged. The only added persistent
kernel state is a private, rollback-aware ordered-group index used to recover
the complete checked mutual container group. It is not iterated, serialized,
or included in declaration identity.

This is native kernel admission credit. The importer still returns
`Unsupported("inductive-nested")`, and none of M0's three official computation
streams has been passed to it. M4 owns the first official-stream admission and
exact wire comparison.

## Expansion contract implemented

The implementation follows the exact pinned Lean 4.30 algorithm at commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`:

1. reopen each constructor's shared parameter prefix with canonical free
   variables while preserving its own binder names and binder information;
2. discover only applications headed by an already admitted inductive family;
3. require the complete container parameter prefix, at least one active family
   occurrence in that prefix, exact universe arity, and no loose bound variable;
4. canonicalize and structurally deduplicate the specialized container
   application;
5. copy every family and constructor in the container's checked ordered mutual
   group under collision-free private names;
6. substitute the container's universe parameters, instantiate away its
   parameters, prepend the outer parameter telescope, and retain its indices;
7. process copied constructors through the same queue until the expansion
   reaches a fixed point; and
8. reject more than 256 auxiliary families with a typed deterministic bound.

Freshness covers the complete expanded surface: family, constructor, and
generated recursor names. An adversarial source constructor occupying the first
private candidate makes generation advance deterministically rather than turn a
valid declaration into a later collision.

## Atomic checking and restoration

The expanded group enters the existing `add_inductive_group` worker once. No
second positivity, constructor, recursive-field, motive/minor, recursor, rule,
or inference algorithm was added.

After that worker succeeds:

- every required temporary declaration is cloned;
- the temporary insertion checkpoint is rolled back;
- both closed-inference and WHNF caches are cleared before final staging;
- source inductives are staged first;
- original constructor types are restored, checked for temporary-name leakage,
  inferred, and required to be definitionally equal to the source contracts;
- auxiliary family/constructor applications are recursively restored with the
  original container levels, parameters, indices, and constructor names;
- auxiliary recursor constants are renamed using Lean's string
  `append_after` shape, so the public name is `rec_1`, not `rec.1`;
- every restored recursor type is inferred before publication;
- all main and auxiliary recursor constants are staged together before any
  closed rule right-hand side is inferred, preserving cross-recursive calls;
- every expression and projection type name is scanned for exact private-name
  leakage; and
- only the ordered source family group is registered in the final private
  group index.

Any error remains inside the outer insertion-log transaction. Late public-name
collision, restored-type/rule inference failure, or leakage therefore exposes
no partial family, constructor, recursor, private group entry, or stale cache.

## Native matrix

`crates/axeyum-lean-kernel/tests/nested_inductive_elimination.rs` contains 23
focused public-path tests.

Positive coverage includes:

- one-family `Box Rose` expansion and exact source-only surface;
- exact `Rose.rec_1` name structure and auxiliary rule-constructor restoration;
- the computation chain `Rose.rec -> Rose.rec_1 -> Rose.rec` reducing to the
  registered two-successor control;
- repeated structural applications reusing one auxiliary family;
- two parameterizations of one container in an outer mutual self/cross group;
- zero, one, and two outer parameters;
- zero, one, and two container indices;
- differing outer/container parameter counts;
- container-universe substitution into a differently named outer universe;
- complete copying of an existing mutual container group;
- an empty owner in a copied container group and its zero-rule public recursor;
- positive higher-order tails;
- one- and two-level fixed-point expansion;
- allowed `Type` and `Prop` results;
- exact final-type and closed-rule inference;
- source-name collision avoidance; and
- reuse of a restored parameterized family as a later container, proving that
  the final source-only group index replaced the temporary expanded mapping.

Typed negative and rollback coverage includes:

- incomplete container parameter prefixes;
- loose nested parameters;
- a negative family occurrence inside the specialized container parameter;
- a non-inductive foreign head;
- a noncanonical inductive lacking checked group metadata;
- the 256-family expansion bound;
- a pre-existing `First.rec_1` collision after temporary checking;
- full environment equality after rejection; and
- successful retry through the same pre-existing container after early and
  late failures.

The private environment unit test separately freezes ordered group lookup,
suffix rollback, and preservation of pre-checkpoint group metadata.

## Validation

All commands used one Cargo job and one test thread under the registered
`MemoryHigh=3G`, `MemoryMax=4G`, `MemorySwapMax=512M` user scope with a
repository-local temporary directory.

- focused nested matrix: 23 passed;
- complete `axeyum-lean-kernel --all-targets --all-features`: 185 unit tests and
  every integration binary passed;
- retained deterministic populations: 720 mutual, 768 recursive, and 840
  positivity profiles passed byte-identically;
- complete `axeyum-lean-import --all-targets --all-features`: 41 integration
  tests passed, including the unchanged typed nested decline;
- warning-denied kernel Clippy passed;
- warning-denied kernel rustdoc passed;
- M0 freeze checker passed for three roots / 114,596 bytes with no Axeyum
  product observations;
- all 13 M0 checker unit tests passed;
- focused Rust formatting and `git diff --check` passed; and
- local, tracking, and remote semantic refs all resolved to
  `96b6fbd4da7e20277b338f59983fbe7316b31d22` after push.

An independent read-only agent reviewed the completed implementation twice
against the pinned C++ source and ADR-0355. Its first pass identified full-
surface freshness, binder-aware recursive restoration, `.rec_N` shape,
cache-ABA clearing, recursor staging order, and private-group rollback as the
critical risks. The implementation and tests close each. Its final pass found
no restoration/publication correctness blocker; the remaining direct mutation
teeth belong to M3.

## What remains

M2 does not claim the at-least-640-case generated grammar, direct internal
restoration mutations, official nested import, `numNested`/wire comparison,
pinned computation-stream replay, assurance overlay, or ADR acceptance.

M3 is next. It must preregister and repeat at least 640 unique public-path
profiles byte-identically, add independent expansion/reuse/restoration oracles
and forced mutation seams, and retain the exact 720/768/840 populations without
changing importer policy or observing an M0 computation stream.
