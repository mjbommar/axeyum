# Lean mutual inductive groups: TL2.13 execution plan

Status: M3 deterministic group grammar complete; M4 importer and exact official
groups are next

Date: 2026-07-22

Decision gate:
[proposed ADR-0354](../research/09-decisions/adr-0354-preregister-lean-mutual-inductive-groups.md)

Parents:

- [Lean implementation plan](lean-system-implementation-plan-2026-07-21.md)
  (TL2.13);
- [Lean compatibility roadmap](lean-system-compatibility-roadmap-2026-07-21.md);
- [P6.0 kernel trustworthiness](../prover-track/plan/P6.0-kernel-trustworthiness.md);
- [completed TL2.12 result](lean-recursive-induction-hypotheses-final-2026-07-22.md);
- [official construct-matrix handoff](lean-official-construct-matrix-final-2026-07-22.md).

## 1. Outcome and honest boundary

Add one atomic ordered mutual-inductive admission path that reproduces pinned
Lean 4.30's group-wide parameter/universe checks, positivity, multiple motives,
shared global minors, target-family induction hypotheses, target-family
recursive calls, per-family recursors, and all-or-nothing publication.

The existing single-family API becomes a one-member wrapper over the same
implementation and must remain byte-for-byte and behaviorally stable. At
completion, the frozen official `EvenTree`/`OddTree` stream must import twice
with exact independently generated recursor comparison. Separate official
computation streams must force non-indexed and indexed cross-family recursive
calls to registered normal forms in both pinned Lean and Axeyum.

This is bounded core-kernel/import compatibility. It is not native source
elaboration, nested/well-founded lowering, termination checking, pattern-match
compilation, `Init`/`Std`/mathlib coverage, or full Lean parity.

## 2. Baseline that may not move silently

Implementation begins from exact revision
`78f4c5631dbca3fce568be72bde2d906d6e3705f`, where:

- TL2.11 group-local prerequisites exist as a complete single-family strict-
  positivity guard;
- TL2.12 admits direct, indexed, higher-order, and combined recursive fields
  for one family through one telescope-tail rule;
- `add_inductive` publishes one family, its constructors, and one recursor
  transactionally;
- recursors currently carry one motive and one family's minors;
- the importer rejects `types.len() != 1` as `inductive-mutual` before kernel
  admission;
- the frozen mutual stream is 23,596 bytes / 395 records at SHA-256
  `06aa05ccc8abc9309fad04b373017e770da25c7b0c2743fc0f097efd72de3174`
  and declines at line 233 without `CompletedImport`;
- declaration identity v1, completion-only import, the official construct
  matrix, 768-case recursive grammar, and 840-case positivity grammar are
  mandatory controls.

M0 binds these facts and exact selectors in a machine-readable registration.
No existing typed decline, identity, or result is deleted merely because its
primary mutual positive becomes supported.

## 3. Pinned authority and official evidence

Use Lean 4.30 commit
`d024af099ca4bf2c86f649261ebf59565dc8c622` and `lean4export` format 3.1 at
commit `a3e35a584f59b390667db7269cd37fca8575e4bf`.

The executable authority in `references/lean4/src/kernel/inductive.cpp` is:

- `check_inductive_types`: common universe parameters/parameter telescope,
  equivalent result universe, and per-family index counts;
- `has_ind_occ`, `is_valid_ind_app`, and `check_positivity`: one complete group
  occurrence set and target-family selection;
- `elim_only_at_universe_zero` and `init_K_target`: mutual-`Prop` restriction
  and no mutual K target;
- `mk_rec_infos`: one motive per family and one minor per constructor;
- `collect_Cs` and `collect_minor_premises`: family order, then constructor
  order;
- `mk_rec_rules`: recursive fields call the recursor of their terminal family;
- `declare_recursors`: one recursor per family, each binding all motives/minors.

Already-frozen product target:

| target | hash / size | current product | required transition |
|---|---|---|---|
| official mutual construct stream | `06aa05cc...de3174`, 23,596 bytes / 395 records | `Unsupported(inductive-mutual)` at line 233 | complete import with two motives, four minors, exact two recursors |

M0 adds one compact official source with two independent groups:

1. parameterized non-indexed `EvenTree`/`OddTree`, with explicit recursor
   consumers whose reduction alternates `EvenTree.rec -> OddTree.rec ->
   EvenTree.rec`;
2. parameterized indexed `EvenVec`/`OddVec`, with explicit recursor consumers
   that preserve and transform the recursive field's own index.

Freeze one selected theorem stream per group twice. Constructor or pattern-
match witnesses remain admission-only; computation credit requires an explicit
recursor application whose WHNF crosses a family boundary.

The completed [M0 result](lean-mutual-inductive-groups-m0-2026-07-22.md)
freezes both groups and exposes a wire-order constraint that later comparison
must respect: group families remain in source order, but both official `recs`
arrays are dependency-ordered with the odd-family recursor first. Semantic
motive/minor ordering remains source-family order. The importer must therefore
match exported recursors by checked name and owned rules, never by array
position.

## 4. Executable group rule

Let the ordered group be `G = [I_0, ..., I_(g-1)]`. All families share universe
parameters and `m` parameter values `P`; family `I_i` has `k_i` indices and

```text
C_i : Pi indices_i, I_i P indices_i -> Sort v.
```

For owner-family constructor `c : Pi P fields, I_i P result_indices`, classify
each field against the complete group. A field

```text
u : Pi xs, I_j P recursive_indices
```

receives

```text
u_ih : Pi xs, C_j recursive_indices (u xs)
```

and its rule supplies

```text
fun xs =>
  I_j.rec P C_0 ... C_(g-1) all_minors recursive_indices (u xs).
```

The minor concludes in

```text
C_i result_indices (c P fields).
```

Ordering is singular and public:

```text
parameters
  -> motives by family order
  -> minors by (family order, constructor order)
  -> owner-family indices
  -> owner-family major
```

Within one minor, all source fields precede all IHs; IHs follow recursive-field
order. Every recursive call receives the complete motive/minor vectors and
selects the recursor of the recursive target family, not the constructor owner.

## 5. Representation and transaction seam

Add an explicit ordered `InductiveFamilySpec` (final name may differ only before
M0 freezes the public API) and:

```text
Kernel::add_mutual_inductive(uparams, num_params, families)
```

The trusted path is staged:

1. reject empty/duplicate names and validate common universe parameters;
2. open the first parameter telescope and check every later family's parameters
   definitionally against the shared locals;
3. record each family's indices and require equivalent result universes;
4. build the complete family-constant table;
5. run group-wide positivity before provisional insertion;
6. provisionally insert all family headers, then check all constructors;
7. classify recursive fields to stable `(field_position, target_family,
   telescope_depth)` descriptors;
8. provisionally insert all constructors;
9. derive all motives and all minors once, then generate and infer-check every
   family recursor and its own rules;
10. commit the complete staged declaration set atomically, or restore the exact
    prior environment on any error.

`add_inductive` delegates to this path with one family. Do not maintain a
separate single-family recursor algorithm. Context-local telescope binders,
indices, applied fields, motives, and recursor terms are rederived rather than
stored across local contexts.

Importer work occurs only after native/group-generated tests pass. It parses all
types/constructors/recursors, validates every ordered `all` array against the
group, calls the atomic kernel gate once, then compares every generated family,
constructor, recursor type, count, rule, and `nfields` before publication.

Declaration identity v1 is a mandatory non-drift control. Persistent public
group metadata or an identity-domain change is out of scope without a new ADR.

## 6. Preregistered native case matrix

| ID | shape | required result |
|---|---|---|
| `singleton-wrapper-control` | one direct-recursive family | existing declaration identities/type/rules/iota/errors unchanged |
| `two-family-cross` | `Even -> Odd`, `Odd -> Even` | two motives, all minors, target motive/recursor selected |
| `mixed-self-cross` | one family has self and cross fields | IHs and recursive calls follow field order |
| `three-family-cycle` | `A -> B -> C -> A` | three motives and globally ordered minors |
| `shared-dependent-params` | later parameter type depends on earlier one | every family reuses definitionally equal shared locals |
| `different-index-counts` | families have zero, one, and two indices | each recursor owns its declared index suffix |
| `indexed-cross` | field ends in another family at field-dependent indices | target motive receives recursive indices; owner motive receives result indices |
| `higher-order-cross` | `Pi xs, I_j P indices` | telescope-preserving target-family IH and recursive lambda |
| `multiple-targets` | fields target self and two neighbors | one IH per recursive field, correct motive/recursor each time |
| `empty-constructor-family` | one group family has no constructors | motive/recursor still generated; minor count is group total |
| `type-mutual-prop` | two mutually recursive predicates | motives restricted to `Prop`; no K-like reduction |
| `empty-group` | no families | typed rejection, no environment change |
| `parameter-mismatch` | parameter count/type differs | typed pre-publication rejection |
| `result-universe-mismatch` | family result levels not equivalent | typed pre-publication rejection |
| `cross-negative-domain` | a group family occurs in `Pi` domain | group-wide non-positive rejection |
| `cross-invalid-application` | bad target params/arity/index occurrence/foreign head | typed invalid-occurrence rejection |
| `duplicate-group-name` | duplicate family/constructor/recursor name | typed rejection before insertion |
| `late-recursor-failure` | final recursor self-check is mutated | complete group rollback |

Every positive row checks public admission, family/constructor metadata,
recursor types/counts/rules, inference, and selected iota normal forms. Every
negative row snapshots and compares the complete ordered environment and exact
typed error payload.

## 7. Mutation teeth

At least one focused mutation must reject for each load-bearing fact:

- omit, duplicate, or reorder a motive;
- route a recursive occurrence to the owner motive instead of target motive;
- use the owner recursor instead of the recursive target's recursor;
- omit, duplicate, or reorder a global minor;
- use a family-local minor index where the global index is required;
- reorder or alter one `all` family list;
- alter one family's parameter count/type or universe parameter list;
- alter one family's result universe or per-family index count;
- miss a cross-family occurrence during positivity;
- move an IH before fields or reorder IHs;
- alter target indices, telescope binders, or field application order;
- change constructor owner, `cidx`, field count, or rule constructor;
- mutate recursor type, `numMotives`, `numMinors`, rule RHS, or `nfields`;
- grant support by flipping `isRec`/`isReflexive`/`all` metadata alone;
- permit large elimination or K-like reduction for a mutual `Prop` group;
- trigger a failure after the last generated recursor and prove no group or
  `CompletedImport` publication.

Official-stream mutations are synthetic checker evidence and never receive
official-wire credit.

## 8. Generated mutual-group grammar

Add a fixed-seed generator independent of the existing recursive/positivity
grammars. Its production record combines:

- group sizes one through three;
- zero through two shared parameters, including dependent pairs;
- zero through two indices independently per family;
- zero through three constructors per family;
- zero through three recursive fields among zero through five total fields;
- recursive targets self, earlier family, and later family;
- field telescope depths zero through two with explicit/implicit/strict-
  implicit binders;
- constant and field-dependent recursive/result indices;
- `Type` groups and valid/restricted `Prop` groups;
- self-only, cross-only, mixed, multiple-target, and empty-constructor shapes;
- one independently selected negative/mutation class where applicable.

The generator derives expectations from its production record, not from kernel
output. It must execute at least 640 unique identities through the public group
path, repeat a canonical summary byte-for-byte, assert recursor inference/iota
for positives, and assert typed rollback for negatives. The existing 768-case
TL2.12 and 840-case TL2.11 populations remain mandatory.

## 9. Milestones and commit rhythm

### P0 — ADR and execution-plan preregistration

- commit ADR-0354 and this plan before retaining any new source/stream or
  changing kernel/importer semantics;
- update PLAN, STATUS, both Lean roadmaps, P6.0, the research-question register,
  and docs index;
- run link/diff checks, commit, push, and verify remote equality.

### M0 — machine registration and official source/wire freeze

Status: **complete**. See the
[M0 result](lean-mutual-inductive-groups-m0-2026-07-22.md) and machine-checked
[`lean-mutual-inductive-groups-v1.json`](lean-mutual-inductive-groups-v1.json).

- add a v1 machine registration binding the baseline, pins, exact group rule,
  ordered cases/mutations, grammar, controls, resources, commands, claims, and
  stop conditions;
- add the explicit non-indexed and indexed mutual-recursor computation source;
- compile it twice with pinned Lean and freeze the OLEAN/source identities;
- export each selected root twice and freeze independent complete inventories;
- do not run Axeyum on the new computation streams;
- mutation-test the registration against premature product credit;
- commit, push, and verify remote equality.

### M1 — group representation and single-family delegation

Status: **complete**. See the
[M1 result](lean-mutual-inductive-groups-m1-2026-07-22.md). The public ordered
family input, shared parameter/result-universe preflight, insertion-log
transaction, exact singleton delegation, and typed policy decline are live;
multi-family positivity/recursors/admission remain M2-only.

- add the ordered group/family specification and one transaction scaffold;
- route `add_inductive` through a singleton group without widening mutual
  admission;
- freeze existing single-family declaration identities, recursor types/rules,
  computations, error payloads, and generated summaries;
- add typed empty/parameter/universe/name group-preflight failures;
- commit, push, and verify remote equality.

### M2 — native group positivity, recursors, and atomic publication

Status: **complete**. See the
[M2 result](lean-mutual-inductive-groups-m2-2026-07-22.md). One native group
algorithm now covers singleton, cross-family, indexed, higher-order, mixed,
empty-constructor, and mutual-`Prop` shapes with complete-group positivity,
global motives/minors, target-family recursion, recursor/rule inference, and
whole-group rollback. The importer and M0 official streams remain untouched.

- generalize positivity to the complete group occurrence set;
- derive all motives/minors and target-family IH/recursive calls once;
- generate/infer-check all per-family recursors before atomic commit;
- close every positive/negative native row and semantic mutation;
- do not pass the new official streams to the importer;
- commit, push, and verify remote equality.

### M3 — deterministic group grammar

Status: **complete**. See the
[M3 result](lean-mutual-inductive-groups-m3-2026-07-22.md). The independent
fixed-seed grammar executes 720 unique public-path cases twice with a byte-
identical summary, 432 positive inference/iota contracts, 288 exact typed
rollbacks, and generated group-order/target-family mutation teeth. The retained
768/840 summaries are unchanged; importer policy and M0 streams remain closed.

- land and repeat the >=640-case independent grammar;
- retain exact 768-case recursive and 840-case positivity summaries;
- close generated group-order/target-family/rollback mutations;
- commit, push, and verify remote equality.

### M4 — importer and exact official groups

- remove only the blanket multi-type policy decline after native support;
- validate ordered `all` arrays and every type/constructor/recursor record;
- import the frozen construct and computation streams twice;
- compare every generated official declaration and selected computation;
- mutate metadata/type/count/rule/field/publication boundaries;
- commit, push, and verify remote equality.

### M5 — assurance update and closure

- update the machine construct assurance matrix without rewriting historical
  observations;
- run all bounded final gates;
- accept, reject, or defer ADR-0354 strictly from its registered exits;
- synchronize PLAN, STATUS, project state, roadmaps, P6.0, research question,
  and docs;
- hand the primary path to TL2.14 only if every gate passes;
- commit, push, and verify local/tracking/remote equality.

Every milestone stages only owned files. Negative results are documented and
pushed before the plan changes. Existing unrelated worktree changes remain
untouched.

## 10. Resource and validation policy

- Lean: exact pinned binary, one worker, `MemoryHigh=3G`, `MemoryMax=4G`,
  `MemorySwapMax=512M`, bounded timeout, repository-local temporary output;
- Rust: one build job and `MEM_LIMIT_GB=4 ./scripts/mem-run.sh` where applicable;
- no workspace-wide unbounded or parallel-heavy command;
- complete kernel unit/integration/doctest and importer integration/doctest
  suites at final gates;
- focused group, recursive, positivity, direct-identity, construct-matrix, and
  transactional-import regressions at every semantic milestone;
- repeated >=640 mutual, 768 recursive, and 840 positivity populations;
- focused rustfmt, clippy, and rustdoc with warnings denied;
- preregistration/observation validators, parity docs, foundational resources,
  links, `git diff --check`, staged audit, push, and remote-ref equality.

An OOM, signal, missing artifact/tool, partial stream, nondeterministic summary,
or required increase above the registered envelope is a failed gate. Preserve
and diagnose it; do not silently raise limits or shrink populations.

## 11. Stop conditions

Stop, preserve evidence, and amend the decision before continuing if:

1. pinned Lean's group motive/minor/rule order disagrees with this plan;
2. singleton delegation changes any registered single-family identity/result;
3. group positivity fails to range over every family or changes a retained
   single-family classification;
4. supporting cross recursion requires separately published families;
5. constructor checking and recursor reconstruction disagree on target family,
   telescope, or indices;
6. any recursor self-checks but differs from the frozen official recursor;
7. the official group imports without every ordered `all`/count/rule comparison;
8. a constructor/pattern witness is promoted to recursive computation credit;
9. any error exposes a partial group or `CompletedImport`;
10. mutual `Prop` eliminates into data or receives K-like reduction;
11. declaration identity v1 changes without a separate versioned decision;
12. nested/frontend lowering enters the kernel slice;
13. any generated population is too small, duplicated, or nondeterministic;
14. a required process exceeds 4 GiB, is killed, or needs wider parallelism;
15. unrelated dirty work overlaps a target file.

## 12. Explicit non-claims

TL2.13 does not establish:

- native Lean mutual syntax, elaboration, pattern compilation, or termination;
- nested or well-founded source lowering;
- every universe/elimination or unsafe-inductive profile;
- `Init`, `Std`, or mathlib admission beyond exact selected closures;
- native parser, macros, tactics, compiler, Lake, LSP, or `.olean` support;
- full Lean-kernel parity, consistency, or replacement of official Lean.
