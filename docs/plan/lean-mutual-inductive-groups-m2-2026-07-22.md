# Lean mutual inductive groups: M2 native-semantics result

Status: complete; M3 deterministic group grammar is next

Date: 2026-07-22

Parent:
[TL2.13 execution plan](lean-mutual-inductive-groups-tl2.13-plan-2026-07-22.md)

Decision gate:
[proposed ADR-0354](../research/09-decisions/adr-0354-preregister-lean-mutual-inductive-groups.md)

Baseline: `8e49a7f161efd8aa55dfb9b00c9af4d749177b15`

## Result

M2 replaces M1's valid-group policy decline with one native trusted algorithm
for singleton and multi-family inductive groups. The publication unit is the
complete ordered group:

1. preflight checks names, shared parameters, per-family indices, and equivalent
   result universes;
2. positivity ranges over every family before any header is visible;
3. all family headers are staged so every constructor can resolve cross-family
   references;
4. constructor checking classifies each recursive field by stable field
   position, terminal family, and telescope depth;
5. all constructors are staged;
6. motives are generated in family order and minors in family-then-constructor
   order;
7. each owner recursor binds the complete motive/minor vectors, its own indices,
   and its own major;
8. each recursive induction hypothesis selects the terminal family's motive,
   and each computation-rule call selects the terminal family's recursor;
9. every recursor type and every closed rule value is inferred after all group
   recursors are staged;
10. any failure rolls the complete attempted group back through the insertion
    checkpoint.

`Kernel::add_inductive` remains a one-family wrapper over this path. There is
no second single-family positivity, constructor, or recursor implementation.

This is deliberately a native-kernel milestone. The importer still returns its
registered `inductive-mutual` decline, neither M0 computation stream has been
passed to the Rust product, and the frozen official construct observations are
unchanged. M4 owns that first product widening.

## Native case matrix

The focused public integration binary has 18 tests covering every registered
M2 shape. Several tests combine related positive dimensions but check each
dimension explicitly.

| Registered row | Native evidence |
|---|---|
| `singleton-wrapper-control` | wrapper and direct singleton-group paths publish equal declarations and compute the same iota result |
| `two-family-cross` | two motives, three global minors, owner-only rules, and nested cross-family iota computation |
| `mixed-self-cross` | one constructor carries self, earlier/later-family fields and preserves recursive-field order |
| `three-family-cycle` | `A -> B -> C -> A` with three motives and four global minors |
| `shared-dependent-params` | later dependent parameter domains are definitionally equal against shared locals |
| `different-index-counts` | one group contains zero-, one-, and two-index families |
| `indexed-cross` | target indices feed the target motive/recursor; owner result indices feed the owner motive |
| `higher-order-cross` | a strict-implicit field telescope is preserved in the IH and recursive lambda |
| `multiple-targets` | self plus both neighboring target families each select the correct recursor exactly once |
| `empty-constructor-family` | a family with no constructors still receives a recursor and the global minor count |
| `type-mutual-prop` | mutual predicates receive no elimination-level parameter and no K-like target |
| `empty-group` | typed rejection with exact environment preservation |
| `parameter-mismatch` | both count and dependent-domain mismatches identify the family/position and roll back |
| `result-universe-mismatch` | typed family-specific rejection and rollback |
| `cross-negative-domain` | a family occurrence in a `Pi` domain is non-positive before publication |
| `cross-invalid-application` | incomplete target application is invalid before publication |
| `duplicate-group-name` | family, constructor, recursor, and existing-environment collisions retain typed boundaries |
| `late-recursor-failure` | a mutated final rule fails after recursor staging and the complete group disappears |

Every positive multi-family call runs a common contract assertion over every
published family, constructor, and recursor. It checks parameter/index counts,
the group-global recursive bit, constructor ownership/index/field count,
motive/minor counts, owner-rule order and field counts, and inference of every
recursor type to a sort. Selected non-indexed, indexed, and higher-order rows
also compute through a cross-family recursor call.

## Positivity, recursion, and elimination details

The positivity walker uses the complete family constant table. After WHNF, a
`Pi` domain may mention no group family; its codomain is checked recursively.
Any remaining group occurrence must be a complete application of one family to
the exact shared parameters and its declared index arity, and no index may
itself mention a group family. Constructor checking repeats the terminal-family
classification after all headers are visible and rejects any mismatch.

The generated group `is_recursive` value is global, matching pinned Lean: if
any constructor has a recursive field, every family header records the group as
recursive. A group whose common result universe may be `Prop` eliminates only
to `Prop` when it has more than one family. The historical singleton syntactic-
subsingleton rule remains unchanged; mutual groups never receive singleton K
behavior.

## Mutation teeth and rollback

Two kernel-private mutation tests exercise independently checkable products of
the generator rather than adding trusted production flags:

- the recursor metadata validator rejects a missing recursor and mutations of
  recursor name, motive/minor/parameter/index counts, owner-rule order/count,
  rule constructor, and rule field count;
- ordinary kernel inference rejects a mutated recursor type and a closed rule
  RHS containing an unknown constant;
- the final-rule failure is injected only after every family, constructor, and
  recursor has been staged, then the public transaction proves exact rollback;
- an exact 16-entry registry freezes the preregistered semantic mutation
  classes, including motive/minor order, target motive/recursor, target indices,
  family lists, IH/field order, constructor ownership, mutual-`Prop` policy, and
  late publication.

The integration tests separately make target-family use observable: the
three-target rule contains each expected target recursor exactly once, indexed
cross recursion computes only with the recursive occurrence's index, and the
higher-order rule retains its field telescope.

## Retained singleton and generated controls

The direct singleton wrapper and direct singleton-group call still publish
equal complete declaration vectors. The frozen official importer identities
remain:

| Declaration | Canonical content SHA-256 |
|---|---|
| `MiniNat.rec` | `dee04a36959066e63f15d5711a5a03de2ac91d71333c48135ef0fdc89cb0f5ef` |
| `MiniList.rec` | `1087558f366706316eefaca0abc48a4b592da2a8496e5d6bbdaa7eea5b677660` |

The retained 768-case recursive grammar repeats at descriptor
`0d245921566be735`. The retained 840-case positivity grammar repeats at
TL2.11 descriptor `02985687422aa0ff`, with the established current partition:

```text
admit:360,recursive-indexed:0,reflexive:0,non-positive:270,invalid:210
```

M2 does not claim the future mutual grammar. M3 must add and repeat at least 640
unique public-path group cases while retaining both controls above.

## Bounded evidence

Every Rust command used one Cargo build job inside the registered 4 GiB cgroup.

| Gate | Result |
|---|---:|
| focused native mutual-group integration binary | 18 passed |
| kernel-private late-rollback and mutation-contract tests | 2 passed |
| complete `axeyum-lean-kernel` all-target/all-feature suite | 184 unit tests plus all integration/doctest targets passed |
| complete `axeyum-lean-import` all-target/all-feature suite | 34 integration tests passed |
| recursive/positivity generated controls | 768 + 840 cases repeated byte-identically |
| direct-recursive declaration identity control | both frozen digests retained |
| kernel/importer clippy | all targets/features, warnings denied; passed |
| kernel/importer rustdoc | warnings denied; passed |
| parity, foundational-resource, link, owned-file formatting, and diff gates | passed |

The workspace-wide `cargo fmt --all --check` remains red on unrelated existing
CAS/bench files. M2 does not rewrite or claim those files. All five owned Rust
files pass direct edition-2024 `rustfmt --check`, and the complete owned diff
passes `git diff --check`.

## Claim boundary

M2 establishes native atomic mutual-family admission for the registered
non-indexed, differently indexed, higher-order, mixed self/cross, empty-family,
and mutual-`Prop` shapes. It establishes complete-group positivity, globally
ordered motives/minors, target-family IHs/recursive calls, per-owner recursors,
selected cross-family computation, and whole-group rollback.

It does **not** establish the >=640 mutual grammar, importer support, comparison
with official mutual recursors, official cross-family computation in Axeyum,
assurance-matrix promotion, nested/well-founded frontend lowering, ADR-0354
acceptance, broad `Init`/`Std`/mathlib admission, or Lean parity.

## Next gate

M3 adds an independent fixed-seed group grammar with at least 640 unique public-
path cases, derives expected admission/metadata/iota/rollback from each
production record, repeats its canonical summary byte-for-byte, and retains the
768 recursive and 840 positivity controls. It does not widen importer policy or
observe the M0 official computation streams.
