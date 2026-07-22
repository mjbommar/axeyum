# Lean nested-inductive elimination M3: deterministic grammar and restoration integrity

Date: 2026-07-22

Status: complete

Semantic commit: `6a2afdd57c969bc1a847d77a85cc99552fa935b1`

Stop-review amendments: `ab5dbf99` and `d03ba0fc`

Decision gate:
[proposed ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)

Execution contract:
[TL2.14 P0--M6 plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md)

Frozen design:
[M3 generated-grammar plan](lean-nested-inductive-elimination-m3-plan-2026-07-22.md)

## Result

M3 closes the native generated-evidence and restoration-integrity milestone.
The public grammar constructs exactly 640 unique nested-inductive profiles from
the preregistered Cartesian product, runs the complete population twice in
fresh kernels, and requires byte-identical summaries equal to one committed
constant. The final descriptor digest is `a20fe056c9443a37`.

An independent observer derives its expectation from semantic production
records, then reads only the public environment, declaration metadata,
expression traversal, ordinary inference/definitional equality, and selected
WHNF computation. It does not consume the production expansion artifact or its
private restoration maps.

The private mutation registry now forces malformed expansion/restoration
states through the same outer transaction and proves exact environment
equality plus a valid retry. Type-correct public recursor mutations must either
reject under ordinary typing or change a named independent observation. No
temporary `_nested` declaration, constant, or projection type name reaches the
published surface.

This remains native-kernel evidence only. `axeyum-lean-import` retains the M1
typed `Unsupported("inductive-nested")` policy boundary, and none of M0's
three frozen computation streams was passed to Axeyum. M4 owns the first
official nested import and exact wire/publication comparison.

## Stop-review amendment

The first independent M3 audit found that post-check mutations of temporary
copied-constructor owner, index, and type metadata were not consumed during M2
restoration. Those mutants could therefore survive without rejection or a
public observer difference. This met the preregistered stop condition before
the semantic checkpoint was committed.

Commit `ab5dbf99` amended the frozen plan to permit one bounded production
change. Commit `d03ba0fc` recorded the survivor dataflow and required outcome.
The implementation preserves the expansion universe parameters and validates
the already-checked temporary surface against the expansion artifact
immediately before restoration. The validator is limited to:

- exact source and temporary family/constructor names and order;
- unique specialized applications and auxiliary names;
- restoration-map completeness;
- temporary family and constructor type/owner/index/field metadata; and
- deterministic freshness state.

It does not reproduce positivity, recursor construction, inference, or
declaration admission. The existing atomic inductive worker remains the only
semantic checker. All three survivor mutations now return the exact restoration
mismatch class, roll back the complete environment, and admit the unchanged
source on retry.

## Generated population

The generator retains schema `axeyum-lean-nested-inductive-grammar-v1`, seed
`0x4158_4e45_5354_4d33`, exact enumeration order, and all preregistered axes.
Every descriptor includes both scheduled and branch-actual values, including
the selected source/container owner, active parameter slot, binder information,
negative subtype, filler position, and recursive target. All 640 case names and
descriptors are unique before kernel admission begins.

The exact committed summary is:

```text
schema=axeyum-lean-nested-inductive-grammar-v1
seed=41584e4553544d33
cases=640
outcomes=admit:320,reject:320
errors=expansion-limit:1,incomplete-application:32,invalid-occurrence:96,loose-parameter:32,malformed-container:108,non-positive:32,public-collision:19
productions=candidate-shape:64,capacity-or-publication:64,container-metadata:64,distinct-specializations:64,fixed-occurrence:64,higher-order-tail:64,nested-self:64,outer-sibling:64,parameter-shape:64,repeated-identical:64
outer-group-sizes=1:216,2:216,3:208
container-group-sizes=1:208,2:216,3:216
outer-parameter-profiles=0p:160,1p:160,2p-dependent:160,2p-independent:160
container-parameter-counts=1:200,2:240,3:200
container-index-counts=0:216,1:216,2:208
constructors-per-family=0:160,1:160,2:160,3:160
fields-per-selected-constructor=0:78,1:82,2:84,3:82,4:78,5:76,no-constructor:160
nested-applications=1:212,2:216,3:212
nested-depths=1:320,2:320
result-sorts=prop:320,type:320
recursive-target-classes=container-auxiliary:208,outer-sibling:140,outer-sibling-fallback-self:84,self:208
shape-variants=0:320,1:320
index-variants=0:320,1:320
source-owner-indices=0:397,1:181,2:62
container-owner-indices=0:390,1:171,2:79
active-parameter-slots=0:385,1:189,2:66
binder-infos=Default:212,Implicit:213,StrictImplicit:215
negative-subtypes=expansion-limit-sentinel:1,foreign-head:32,incomplete-parameter-prefix:32,late-public-rec-1-collision:19,loose-parameter:32,malformed-container-index-arity:40,negative-specialized-parameter:32,unregistered-constructor-metadata:16,unregistered-generic:16,unregistered-index-metadata:16,unregistered-recursion-metadata:16,wrong-fixed-source-parameter:24,wrong-universe-arity-one:23,wrong-universe-arity-two:21
shallow-filler-positions=0:226,1:234,2:128,3:52
published-auxiliary-counts=1:23,12:15,2:64,3:63,4:54,6:56,8:18,9:27
public-recursor-dependency-edges=aux-to-aux:1044,aux-to-main:866,main-to-aux:644,main-to-main:168
iota-checks=auxiliary:462,main:320
mutation-checks=auxiliary-count-and-order:320,deduplicated-reuse:64,distinct-specialization:64,motive-and-minor-order:320,recursor-dependency-target:320,restored-rule-constructor-and-nfields:320,temporary-name-leakage:320,typed-rejection-rollback:320
descriptor-fnv1a64=a20fe056c9443a37
```

The accepted half covers all five positive productions across outer groups of
one through three families, checked container groups of one through three
families, zero through two indices, zero through three constructors per family,
zero through five selected-constructor fields, one through three nested
applications, direct/depth-two nesting, `Prop`/`Type`, repeated and distinct
specializations, self/source-sibling/container-auxiliary recursion, and empty
owners. The rejecting half freezes the exact typed error class and complete
rollback for every scheduled negative branch, including the single 256-family
limit sentinel and 19 late public `rec_1` collisions.

## Independent observation and computation

For every admitted case the observer checks the exact public source family,
constructor, and recursor surface; original container metadata; auxiliary
`rec_N` count/order; complete specialized keys; motive/minor order; rule owner,
constructor, field count, and target; and the exact
`(source recursor, rule constructor, target recursor) -> count` dependency map.
Aggregate dependency classes are recorded only after that exact map agrees.

All public declaration types and closed rule bodies infer. Restored source
constructor types match their source contracts. The computation observer opens
the real recursor telescope in a typed local context, constructs a typed source
major and public container-constructor majors, infers the complete main redex,
and follows the produced auxiliary call through one or two nested levels. The
frozen run performs 320 main and 462 auxiliary iota checks and selects the
minor corresponding to the actual major constructor.

## Mutation evidence

The malformed private registry contains 16 concrete teeth:

- swapped and dropped auxiliary records;
- duplicate and wrong specialized applications;
- shifted freshness state;
- missing family, constructor, and recursor restoration mappings;
- malformed temporary constructor owner, index, and type metadata;
- temporary `Const` and projection type-name leakage;
- dangling restored rules and wrong restored source types; and
- late public `rec_1` collision.

Each mutation executes inside the outer inductive transaction, compares the
entire environment before and after rejection, and retries the valid fixture
through the same checked container. The temporary `Const` tooth exercises the
actual publication guard from inside that transaction rather than only calling
the scanner directly.

The type-correct observer registry mutates recursor motive/minor counts,
parameter/index counts, universe parameters, rule values, recursive targets,
rule constructors, and rule field counts. Adjacent motive and minor order
mutations rebuild real typed `Pi` telescopes under fresh free variables. A
surviving mutation must infer and change its named public observation.

## Validation

All Rust commands used one Cargo job and one test thread under
`MemoryHigh=3G`, `MemoryMax=4G`, and `MemorySwapMax=512M`, with a
repository-local temporary directory.

- the frozen 640-case grammar passed twice in fresh kernels with the exact
  committed summary and digest;
- the focused nested unit subset passed six tests;
- complete `axeyum-lean-kernel --all-targets --all-features` passed 188 unit
  tests and every integration target;
- retained deterministic populations passed byte-identically at 720 mutual,
  768 recursive-IH, and 840 strict-positivity profiles;
- the 23-case M2 public nested matrix remained green;
- complete `axeyum-lean-import --all-targets --all-features` passed all 41
  integration tests, including the unchanged typed nested decline;
- warning-denied kernel and importer Clippy passed;
- warning-denied kernel/importer rustdoc and both doctests passed;
- the M0 freeze checker passed for three roots and 114,596 bytes with no
  Axeyum product observations;
- all 13 M0 checker unit tests passed;
- direct Rust formatting and `git diff --check` passed; and
- local, tracking, and remote semantic refs all resolved to
  `6a2afdd57c969bc1a847d77a85cc99552fa935b1` after push.

An independent read-only agent audited the implementation before and after the
stop-review amendment. Its final pass found no semantic blocker, confirmed that
the validator stays inside the amended scope, verified the real order and
transactional-leak mutations, and found no importer/M4 boundary breach.

## What remains

M3 does not claim official nested import, trust exporter `numNested` or wire
recursor order, compare official auxiliary declarations/rules, replay an M0
computation stream through Axeyum, append the assurance overlay, remove the live
nested decline, or accept ADR-0355.

M4 is next. It must remove only the structural nested policy decline, derive
rather than trust auxiliary counts and recursor identities, import all frozen
official construct/computation streams twice, compare the exact checked
declaration contracts, and close the preregistered wire and publication
mutations before M5 receives computation credit.
