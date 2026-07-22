# Lean nested-inductive elimination M3: generated-grammar plan

Date: 2026-07-22

Status: complete

Parent:
[TL2.14 P0--M6 plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md)

Native prerequisite:
[M2 result](lean-nested-inductive-elimination-m2-2026-07-22.md)

Decision gate:
[proposed ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)

Baseline documentation checkpoint: `70c1c7e786e038d1b39bcaf7a90f47cbb1c231bb`

Semantic implementation: `6a2afdd57c969bc1a847d77a85cc99552fa935b1`

Result:
[M3 deterministic grammar and restoration integrity](lean-nested-inductive-elimination-m3-2026-07-22.md)

## Boundary

M3 adds deterministic native-kernel evidence only. It owns one public-path
generated grammar and private forced mutations of the M2 expansion/restoration
artifacts. It does not change `axeyum-lean-import`, pass an M0 stream to the
product, trust `numNested` or wire recursor order, change declaration identity,
or claim official nested import/computation.

The intended implementation touches exactly:

- new `crates/axeyum-lean-kernel/tests/nested_inductive_grammar.rs` for the
  public population and independent observer; and
- `crates/axeyum-lean-kernel/src/inductive/inductive_tests.rs` for mutations
  that require private temporary expansion/restoration state.

Production code changes are forbidden unless a preregistered mutant survives
both transactional rejection and independent observation. Any such change is
a stop-and-review event, not an invitation to add a second checker.

## Stop-and-review amendment: temporary-artifact integrity

The independent M3 audit reached the preregistered stop condition before the
semantic checkpoint was committed. Malformed temporary constructor
owner/index/type metadata was not consumed by the M2 restoration path and
therefore could survive without either transactional rejection or a public
observer difference. M3 publication remains blocked until those mutations are
rejected.

The survivor evidence is the pre-amendment restoration dataflow itself:
restoration cloned source constructors plus main/auxiliary recursors, but never
re-read temporary auxiliary constructor declarations. Consequently, changing a
temporary copied constructor's `inductive`, `idx`, or `ty` field after the
ordinary group check could affect neither rejection nor the restored public
surface. The M3 private registry names and forces all three mutations; the
amended path must classify each as
`NestedInductiveRestorationMismatch`, prove exact pre/post environment
equality, and admit the unchanged source on retry.

The reviewed scope is amended to permit one bounded production change in
`crates/axeyum-lean-kernel/src/inductive.rs`: preserve the expansion universe
parameter list and validate the already-checked temporary declaration surface
against the expansion artifact immediately before restoration. The validation
is limited to exact family/constructor names and order, unique specialization
keys, restoration-map completeness, temporary family/constructor metadata,
and deterministic freshness state. It does not reimplement positivity,
recursor construction, inference, or declaration admission; the ordinary
inductive worker remains the only semantic checker.

This amendment does not relax any M3 gate. Swapped/dropped/duplicated
auxiliaries, shifted freshness, malformed temporary constructor metadata, and
missing restoration maps must reject with complete environment rollback and a
valid retry. All original public-observer, generated-grammar, resource, M4
boundary, and retained-control requirements remain binding.

## Frozen generator identity

- schema: `axeyum-lean-nested-inductive-grammar-v1`;
- seed: `0x4158_4e45_5354_4d33` (`AXNESTM3`);
- exact cases per run: 640;
- repetitions: two complete fresh-kernel runs;
- identity: byte-identical canonical summaries followed by equality with one
  committed summary constant; and
- descriptor: FNV-1a64 over every complete, independently constructed case
  record plus one newline.

The 640 identities are the exact Cartesian product:

```text
10 productions
  x 4 outer-parameter profiles
  x 2 result sorts
  x 2 nested-depth bands
  x 2 shape variants
  x 2 index variants
= 640 cases
```

The four outer-parameter profiles are zero, one, two independent, and the
dependent pair `(alpha : Type) (a : alpha)`. The result sorts are `Type` and
the already-supported restricted `Prop` profile. Each case name encodes all
six axes and its ordinal; the generator must prove all 640 names and complete
descriptors are unique before invoking the kernel.

Enumeration order is production, outer-parameter profile, result sort, depth,
shape variant, then index variant. For zero-based indices `p`, `o`, `s`, `d`,
`v`, and `x`, the remaining dimensions are fixed as follows:

```text
source group size       = 1 + (p + o + v) mod 3
container group size    = 1 + (p + s + d + x) mod 3
container parameter count = 1 + (o + d + v) mod 3
container index count   = (p + o + x) mod 3
constructors per family = (p + o + 2*v + x) mod 4
fields per constructor  = (p + 2*o + d + v + x) mod 6
nested application count = 1 + (p + o + v + x) mod 3
recursive target class  = (p + s + v) mod 3
```

The fixed seed is mixed with the ordinal to select only orthogonal details:
source/container owner, binder information, the active container-parameter
slot, negative subtype, and shallow filler placement. These choices never
filter a case or control whether a registered range endpoint appears.

## Required range coverage

The two variant axes plus fixed-seed choices derive the remaining registered
dimensions without filtering or retry:

- source group sizes one through three;
- existing container group sizes one through three;
- container parameter counts one through three;
- container index counts zero through two;
- zero through three constructors per container family;
- zero through five fields per copied constructor;
- one through three nested applications, repeated or structurally distinct;
- nested depth one and two;
- recursive targets in the source family itself, an outer sibling, and a
  copied container auxiliary; and
- accepted and typed-reject classifications.

Every listed value must have a nonzero frozen summary count. Fresh kernels keep
each expanded group bounded to three source families and, except for one
dedicated limit sentinel, at most twelve auxiliary families. The 256-family limit
case runs once per repetition and is not multiplied across the full product.

## Productions

Five accepted productions each have 64 cases:

1. `nested-self` selects one structurally specialized container application;
2. `repeated-identical` places the same application more than once and expects
   one copied auxiliary group;
3. `distinct-specializations` places structurally different positive
   parameterizations and expects distinct copied groups;
4. `higher-order-tail` places the nested application in a positive `Pi` tail;
5. `outer-sibling` combines nesting with source-group self/cross recursion.

The depth axis makes each accepted production use either the selected checked
container directly or a checked wrapper whose constructor reaches that
container, forcing one more fixed-point expansion step.

Five rejecting productions each have 64 cases. Their fixed subvariants cover:

1. `candidate-shape`: non-inductive foreign head and incomplete container
   parameter prefix;
2. `parameter-shape`: loose bound variable and negative family occurrence in a
   specialized parameter;
3. `fixed-occurrence`: wrong fixed source parameter and malformed container
   index/arity occurrence;
4. `container-metadata`: a generic inductive without checked group metadata
   and malformed copied owner/index/type metadata; and
5. `capacity-or-publication`: wrong universe arity, the single expansion-limit
   sentinel, and late public `rec_1` collision.

The oracle freezes the exact `KernelError` class and full pre/post environment
equality for every public rejection. It must not infer success from a generic
error or from declaration counts alone.

## Independent public observer

Before `Kernel::add_mutual_inductive`, the grammar derives an expected contract
from semantic production records, not from production `ExprId`s or private
nested helpers. After an accepted case it reads only the public environment,
declaration metadata, expression traversal, ordinary inference/definitional
equality, and selected WHNF computation.

The observer checks:

- exact source family, constructor, and main-rec names and source constructor
  types;
- structurally unique specialized-container keys and the expected auxiliary
  family count/order;
- exact `First.rec_1`, `First.rec_2`, ... names with no skipped or duplicate
  suffix;
- family/constructor ownership, indices, field counts, motives, minors, rule
  counts, original rule constructors, and rule `nfields`;
- main/auxiliary recursor dependency edges by recursively counting public
  recursor constants in closed rule right-hand sides;
- motive/minor order parsed from the public recursor telescope;
- ordinary inference of every public type and closed rule;
- exact/definitionally equal restored source constructor types;
- absence of `_nested` declaration names, constants, and projection type
  names; and
- one selected public main/auxiliary iota chain per applicable accepted
  production.

The canonical summary uses ordered maps/sets and includes every population
dimension, outcome/error class, auxiliary count, dependency-edge class,
mutation tooth, and the independent descriptor digest.

## Mutation registry

Type-correct semantic mutations must be detectably distinct from the
precomputed contract; malformed artifacts must reject transactionally.

Public grammar observation covers:

- container family order;
- specialized parameter identity;
- auxiliary reuse versus duplication;
- public auxiliary name/suffix;
- copied constructor owner, index, type, and field count;
- motive and minor order;
- recursive main/auxiliary target;
- restored recursor reference;
- restored rule constructor and `nfields`; and
- exact final-surface publication and temporary-name absence.

Private unit mutations use one canonical fixture inside the existing outer
inductive transaction. They cover:

- swapped/dropped auxiliary records and a forced duplicate specialization;
- shifted private freshness state;
- malformed temporary constructor owner/index/type;
- missing family, constructor, or recursor restoration mappings;
- temporary `Const` and `Proj` type-name leakage;
- mutated recursor motives, minors, parameters, indices, universes, rules,
  recursive targets, rule constructors, and `nfields`;
- bad restored type after source-family staging;
- dangling closed rule after all public recursors are staged; and
- late public `rec_1` collision.

Each rejecting mutation compares the complete environment before and after the
outer transaction and performs a valid retry through the same checked
container. A type-correct mutation that is intentionally not rejected must
change a named independent observation. A mutation that neither rejects nor
changes the observer is a failed M3 gate.

Wire-only `numNested`, exported recursor count/order/name, unsafe/K flags, and
exact exporter comparison remain M4 work.

## Retained controls and resources

M3 must retain the exact summaries and descriptors for:

- 720 mutual profiles: `2ea6769fa45ea159`;
- 768 recursive-IH profiles: `0d245921566be735`; and
- 840 positivity profiles: `02985687422aa0ff`.

It also retains the M2 23-case native matrix, direct singleton identities,
complete kernel/importer suites, the typed importer decline, the 35-declaration
well-founded control, and the M0 no-product-observation checker.

All Rust work uses one Cargo job and one test thread inside
`MemoryHigh=3G`, `MemoryMax=4G`, `MemorySwapMax=512M`, with a repository-local
temporary directory. No workspace-wide parallel build is permitted.

## Stop conditions

Stop and amend the plan before broadening scope if any case ID is duplicated,
any required range has zero coverage, summaries differ, a negative publishes
state, a temporary name leaks, a restored type/rule fails ordinary inference,
the public recursor chain stops computing, a forced mutation survives without
detection, a retained descriptor drifts, implementation needs a second
positivity/recursor algorithm or declaration-identity change, importer/M0
observation becomes necessary, the 256 bound must increase, the 4 GiB scope is
killed or exceeded, or another lane overlaps either owned Rust file.
