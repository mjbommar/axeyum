# Lean mutual inductive groups: M3 deterministic grammar result

Status: complete; M4 importer and exact official groups are next

Date: 2026-07-22

Parent:
[TL2.13 execution plan](lean-mutual-inductive-groups-tl2.13-plan-2026-07-22.md)

Decision gate:
[proposed ADR-0354](../research/09-decisions/adr-0354-preregister-lean-mutual-inductive-groups.md)

Baseline: `3829f487f29891a2ef66d18150eab604519219ab`

## Result

M3 adds an independent fixed-seed grammar that executes 720 unique cases
through public `Kernel::add_mutual_inductive`. It repeats the entire population
twice and requires the canonical summaries to be byte-identical before matching
the committed constant.

The generator builds inputs and expected contracts from one production record;
it never calls a private positivity, constructor, or recursor helper. For every
positive case it independently checks:

- every family name, parameter/index count, constructor list, and group-global
  recursive bit;
- every constructor's owner, index, and source-derived field count;
- every recursor's motive/minor/parameter/index counts and inference to a sort;
- motive order and minor order read directly from each generated recursor's
  `Pi` telescope;
- target-recursion counts read structurally from each generated computation
  rule;
- one exact base-constructor iota result selecting the correct global minor.

For every negative case it predicts the exact `KernelError`, snapshots the
complete environment, and proves exact rollback. No generated case invokes the
importer, and neither M0 official computation stream has entered the product.

## Population

The cross-product has 720 unique case IDs:

```text
3 group sizes
  x 4 shared-parameter profiles
  x 2 common result sorts
  x 10 productions
  x 3 primary telescope depths
= 720 cases
```

The four parameter profiles are zero parameters, one parameter, two independent
parameters, and the dependent pair `(α : Type) (a : α)`. Per-family index and
constructor counts are selected independently by the fixed-seed stream, while
the ten production classes remain exactly balanced.

| Dimension | Frozen population |
|---|---|
| outcomes | 432 admit; 288 reject |
| group sizes | 240 each at one, two, and three families |
| parameter profiles | 180 each at `0p`, `1p`, `2p-independent`, `2p-dependent` |
| common sorts | 360 `Prop`; 360 `Type` |
| productions | 72 each across no recursion, self, earlier, later, mixed, multiple targets, negative domain, invalid arity, invalid parameter/index, result mismatch |
| per-family indices | 485 zero; 481 one; 474 two |
| per-family constructors | 235 zero; 132 one; 689 two; 384 three |
| selected total fields | all values zero through five |
| selected recursive fields | 360 zero; 216 one; 72 two; 72 three |
| recursive target occurrences | 336 self; 124 earlier; 116 later |
| recursive telescope depths | 192 each at zero, one, and two |
| recursive binder information | 193 explicit; 193 implicit; 190 strict-implicit |
| selected recursive indices | 426 constant; 175 field/telescope-dependent |
| selected result indices | 363 constant; 50 field-dependent |

The population includes self-only, cross-only, mixed self/cross, multiple-
target, empty-constructor-family, differently indexed, restricted mutual-
`Prop`, dependent-parameter, and higher-order shapes. Zero-constructor families
occur inside nonempty positive groups; a separate owner base constructor keeps
exact iota observable for every positive case.

## Frozen summary

```text
schema=axeyum-lean-mutual-group-grammar-v1
seed=41584d55545f4d33
cases=720
outcomes=admit:432,reject:288
group-sizes=1:240,2:240,3:240
parameter-profiles=0p:180,1p:180,2p-dependent:180,2p-independent:180
sorts=prop:360,type:360
productions=cross-earlier:72,cross-later:72,invalid-arity:72,invalid-parameter-or-index:72,mixed-self-cross:72,multiple-targets:72,negative-domain:72,no-recursion:72,result-mismatch:72,self-recursive:72
primary-and-recursive-depths=0:240,1:240,2:240,recursive-0:192,recursive-1:192,recursive-2:192
per-family-index-counts=0:485,1:481,2:474
per-family-constructor-counts=0:235,1:132,2:689,3:384
selected-total-fields=0:57,1:114,2:117,3:142,4:145,5:145
selected-recursive-fields=0:360,1:216,2:72,3:72
recursive-targets=earlier:124,later:116,self:336
recursive-binder-info=Default:193,Implicit:193,StrictImplicit:190
selected-index-productions=recursive-constant:426,recursive-field-dependent:175,result-constant:363,result-field-dependent:50
mutation-checks=group-order:288,negative-rollback:288,target-family:240
descriptor-fnv1a64=2ea6769fa45ea159
```

The descriptor hashes each complete production record, including owner, every
family's index/constructor counts, total/recursive field positions, target
families, telescope depths, binder information, and the field-dependent-index
selection bit. It is not computed from kernel declarations.

## Generated mutation teeth

M3 closes the three registered generated mutation boundaries:

1. **Group order:** all 288 positive two/three-family cases read the motive and
   minor prefix from generated recursor types, compare it with source family/
   constructor order, then reject a swapped independent expectation.
2. **Target family:** all 240 applicable positive multi-family recursive cases
   count each target recursor constant in the selected rule, compare the vector
   with the production record, then reject a moved target count.
3. **Rollback:** all 288 negative cases compare exact typed errors and exact
   pre/post environment snapshots.

The negative population is balanced across cross-family `Pi`-domain
non-positivity, invalid target arity, invalid shared parameter or recursive
index, and constructor result-owner mismatch. These checks exercise the normal
public transaction; there is no test-only admission switch.

## Retained controls and bounded evidence

Every Rust command uses one Cargo build job inside the registered 4 GiB cgroup.

| Gate | Result |
|---|---:|
| M3 generated grammar | 720 cases x 2; byte-identical; descriptor `2ea6769fa45ea159` |
| generated positive/negative split | 432 admission/inference/iota; 288 typed rollback |
| generated mutations | 288 group-order; 240 target-family; 288 rollback |
| retained recursive grammar | 768 cases; descriptor `0d245921566be735` |
| retained positivity grammar | 840 cases; descriptor `02985687422aa0ff` |
| complete kernel all-target/all-feature suite | 184 unit tests plus all integration targets passed |
| complete importer all-target/all-feature suite | 34 integration tests passed; mutual decline unchanged |
| kernel/importer clippy and rustdoc | warnings denied; passed |
| kernel/importer doctests | two passed from repository-local temporary storage |
| parity, foundational-resource, link, owned formatting, and diff gates | passed |

Workspace-wide `cargo fmt --all --check` remains red on unrelated existing CAS/
bench files. M3 adds one owned Rust test file, which passes direct edition-2024
`rustfmt --check`; the complete owned diff passes `git diff --check`.

## Claim boundary

M3 establishes deterministic generated native coverage of the registered
mutual-group dimensions and mutations. Together with M2, it supports native
atomic admission and selected iota for these generated shapes.

It does **not** establish importer support, official recursor comparison,
official M0 cross-family computation in Axeyum, assurance-matrix promotion,
nested/well-founded frontend lowering, broad `Init`/`Std`/mathlib admission,
ADR-0354 acceptance, or Lean parity.

## Next gate

M4 removes only the blanket importer `inductive-mutual` policy decline. It must
validate ordered `all` arrays without trusting wire recursor position, invoke
the atomic native group gate once, compare every family/constructor/recursor
type and rule, import both frozen official computation streams twice, check the
registered normal forms, and prove completion-only publication under metadata,
type, count, rule, field, and late-failure mutations.
