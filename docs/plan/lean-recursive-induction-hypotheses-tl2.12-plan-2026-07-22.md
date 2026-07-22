# Lean recursive induction hypotheses: TL2.12 execution plan

Status: M2 generalized native semantics complete; M3 importer policy and exact official streams are next

Date: 2026-07-22

Decision gate:
[proposed ADR-0353](../research/09-decisions/adr-0353-preregister-lean-recursive-induction-hypotheses.md)

Current checkpoint:
[M2 native-semantics result](lean-recursive-induction-hypotheses-m2-2026-07-22.md)

Parents:

- [Lean implementation plan](lean-system-implementation-plan-2026-07-21.md)
  (TL2.12);
- [Lean compatibility roadmap](lean-system-compatibility-roadmap-2026-07-21.md);
- [P6.0 kernel trustworthiness](../prover-track/plan/P6.0-kernel-trustworthiness.md);
- [completed TL2.11 positivity result](lean-strict-positivity-final-2026-07-22.md);
- [official construct-matrix handoff](lean-official-construct-matrix-final-2026-07-22.md).

## 1. Outcome and honest boundary

Generalize Axeyum's independently generated Lean-style induction hypotheses and
recursor computation rules so one checked single-family implementation covers:

- existing direct non-indexed recursion;
- direct recursive-indexed fields (`Vector` shape);
- non-indexed higher-order recursive fields;
- indexed higher-order/reflexive fields (`Acc` shape).

At completion, the frozen official `MiniVector` and `MiniAcc` streams must admit
through the independent Rust kernel, compare their recursors exactly enough for
the importer's existing definitional checks, and execute selected recursor
applications to registered normal forms. This is bounded single-family kernel
compatibility. It is not mutual induction, nested-inductive lowering,
well-founded frontend support, source elaboration, `Init`/mathlib coverage, or
full Lean parity.

## 2. Baseline that may not move silently

Implementation begins from exact revision
`5524f1283790e3fbfeae5e208e46c0f40327dee9`, where:

- TL2.11/ADR-0352 strict positivity is complete before provisional insertion;
- direct non-indexed recursive inductives admit and compute;
- recursive-indexed fields return `RecursiveIndexedNotSupported`;
- positive higher-order fields return `ReflexiveOrNestedNotSupported`;
- the importer rejects `isReflexive=true` before kernel admission;
- the importer owns a private staging kernel and publishes only
  `CompletedImport` after the full stream succeeds;
- official recursor types and rules are regenerated and compared
  definitionally;
- the 840-case positivity grammar, official construct matrix, and direct-
  recursive stream are mandatory regression controls.

M0 binds these facts and exact test selectors in a machine-readable
registration. No baseline error is deleted merely because its primary positive
case becomes supported: malformed/misapplied, mutual, nested, and unsafe shapes
must retain typed fail-closed outcomes.

## 3. Pinned authority and frozen fixtures

Use Lean 4.30 commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`, specifically:

- `is_rec_argument`: WHNF and open a recursive field telescope before checking
  the terminal family application;
- `mk_rec_infos`: construct motive applications and induction-hypothesis types;
- `mk_rec_rules`: construct recursive calls and abstract them over the same
  telescope;
- `declare_recursors`: order parameters, motives, minors, indices, and major
  premises in the final recursor.

Already-frozen product targets:

| Target | SHA-256 | Size/records | Required transition |
|---|---|---:|---|
| recursive-indexed stream | `df1e82fa72eac9f2a37cdf3b0eb8044f118489c51f76ab14b9af06c3f4cf11de` | 9,899 bytes / 175 | `MiniVector` typed decline -> complete exact import |
| reflexive/higher-order stream | `a2dc21e61e6938bd5eb5d8c4032c7d6197e312c7a617b8bd33388f2e46db0ec3` | 10,583 bytes / 196 | `MiniAcc` policy decline -> complete exact import |
| common source | `08c6eeaed9d980a631dff14b30de1e3d8da37011b8ad03b84dbdc03c90bff13d` | frozen by ADR-0351 | pinned Lean source acceptance remains |

`MiniVector` has one parameter and one index; `cons` has three fields, one of
which is direct recursive-indexed. `MiniAcc` has two parameters and one index;
`intro` has two fields, the second of which opens two dependent binders before
ending in the recursive family. These exact facts, not their friendly source
names, define the primary target.

M0 now adds and hash-freezes a small supplemental official source whose
definitions explicitly apply `MiniVector.rec` and `MiniAcc.rec`, plus separate
root streams for their `rfl` computation theorems. The existing constructor
witnesses remain admission-only evidence. See the
[M0 result](lean-recursive-induction-hypotheses-m0-2026-07-22.md).

## 4. Executable semantic rule

Let the checked family be `I`, its fixed parameter values be `P`, its declared
index count be `k`, and its motive be:

```text
C : Pi (i_1 : K_1) ... (i_k : K_k), I P i_1 ... i_k -> Sort v
```

For each constructor field, WHNF and open zero or more `Pi` binders. It is a
recursive field exactly when the terminal expression is:

```text
I P j_1 ... j_k
```

with the same family constant/universe instantiation and fixed parameters.
TL2.11 has already established that the opened domains and indices contain no
occurrence of `I`.

For a recursive field:

```text
u : Pi (x_1 : D_1) ... (x_n : D_n), I P j_1 ... j_k
```

generate the minor-premise induction hypothesis:

```text
u_ih : Pi (x_1 : D_1) ... (x_n : D_n),
         C j_1 ... j_k (u x_1 ... x_n)
```

and the computation-rule argument:

```text
fun x_1 ... x_n =>
  I.rec P C minors j_1 ... j_k (u x_1 ... x_n)
```

The direct/non-indexed cases are obtained only by empty vectors:

| Shape | Telescope | Indices |
|---|---|---|
| direct non-indexed | empty | empty |
| direct indexed | empty | nonempty |
| higher-order non-indexed | nonempty | empty |
| higher-order indexed / reflexive | nonempty | nonempty |

There is no fifth semantic path.

## 5. Representation and implementation seam

The trusted change stays inside the existing inductive pipeline:

1. retain TL2.11 positivity before provisional environment insertion;
2. in constructor checking, classify each field through a shared WHNF
   telescope-tail helper and record its stable field position if recursive;
3. in recursor generation, reopen that field in the current local context;
4. use the same helper output to build both the minor IH type and the rule RHS;
5. self-check the complete generated recursor before publication;
6. retain rollback of the provisional family and constructors on any error.

Do not store fresh nested locals across contexts. Checked constructor metadata
may retain stable field indices; context-specific telescope locals, tail
indices, applied recursive values, and abstractions are rederived where used.
The helper must preserve binder names, binder information, dependent domains,
and WHNF behavior. A mismatch between classification and reconstruction is an
internal typed error, not a panic or silent non-recursive classification.

Importer work is deliberately last: after native support passes, accept
`isReflexive=true` only for the kernel-supported single-family,
`numNested=0`, safe profile. `numNested>0`, multiple types/recursors, unsafe
metadata, and malformed group fields retain their current declines.

## 6. Preregistered native case matrix

| ID | Recursive field shape | Required IH / outcome |
|---|---|---|
| `direct-control` | `u : I P` | existing `C u`; registered type/rule structure and iota result unchanged |
| `vector-direct-indexed` | `u : I P n` | `C n u` |
| `higher-order-zero-index` | `u : (a : A) -> I P` | `(a : A) -> C (u a)` |
| `acc-indexed-dependent` | `u : (y : A) -> R y x -> I P y` | `(y : A) -> R y x -> C y (u y proof)` |
| `two-binder-dependent` | `u : (a : A) -> B a -> I P (j a)` | dependent telescope preserved |
| `mixed-fields` | nonrecursive fields around one recursive field | all original fields first, then the IH |
| `multiple-recursive` | direct and higher-order recursive fields together | IHs after all fields, in recursive-field order |
| `implicit-telescope` | implicit/strict-implicit recursive binders | inner IH binder information preserved |
| `reducible-wrapper` | field WHNFs to a supported recursive telescope | same result as its exposed form |
| `prop-acc` | indexed reflexive family in `Prop` | only Lean-permitted elimination; computation in permitted target |
| `wrong-tail-params` | telescope ends in `I Q ...` | existing invalid-occurrence rejection |
| `family-in-domain` | `(x : I P ...) -> ...` | existing non-positive rejection before insertion |
| `family-in-index` | tail index contains `I` | existing invalid-occurrence rejection before insertion |
| `nested-foreign-head` | tail is `F (I P ...)` | existing invalid/nested fail-closed result, never recursive |

Every positive row must assert the generated recursor type, minor-premise
shape, rule RHS, type inference, and a selected iota normal form. Every negative
row snapshots the environment and compares the complete typed error payload.

## 7. Mutation teeth

At least one focused mutation must reject for each load-bearing fact:

- omit, duplicate, or reorder one IH;
- put an IH before the constructor fields;
- drop or reorder a recursive occurrence index;
- substitute the constructor result index for the recursive field index;
- apply the motive to the unapplied higher-order field;
- omit one nested lambda or apply nested arguments in the wrong order;
- alter a nested binder type or binder information;
- recurse on a neighboring field;
- use the wrong motive or wrong recursor universe instantiation;
- mutate the official recursor type, minor type, rule RHS, or `nfields`;
- flip `isReflexive` alone and prove metadata cannot grant or remove kernel
  support, while `numNested>0`, unsafe, and multi-family boundary mutations
  retain their typed declines;
- force a late error after native admission and prove no recursor or completed
  import is published.

Mutations of official NDJSON are synthetic and must stay labeled as such. They
test the independent checker/import boundary but receive no official-wire
credit.

## 8. Generated recursive-profile grammar

Add a fixed-seed generator, separate from and in addition to TL2.11's mandatory
840-case positivity grammar. It combines:

- zero through three recursive fields among zero through five total fields;
- telescope depths zero through three;
- parameter/index profiles `0p0i`, `1p0i`, `1p1i`, and `2p1i`;
- `Prop` and `Type` result sorts where elimination is legal;
- explicit, implicit, and strict-implicit nested binders;
- constant and field-dependent recursive indices;
- direct, higher-order, mixed, and multiple-recursive shapes;
- one independently selected mutation from each applicable class.

The generator assigns expected structure from its production record, not from
the kernel result. It must emit at least 512 unique case identities, execute the
full public admission/recursor path, and repeat a canonical serialized summary
byte-for-byte. Positive cases check inference and iota; negative cases check
typed failure and rollback. If resource measurements select a lower sustainable
count, amend the preregistration before using the observation; do not silently
shrink after seeing results.

## 9. Official differential and computation credit

The official gate has three distinct layers:

1. **Source:** pinned Lean accepts the unchanged construct source and the new
   computation source twice under the registered resource wrapper. M0 has
   completed the new-source half.
2. **Wire:** the two existing streams stay byte-identical to their frozen
   hashes; M0 has exported and frozen separate Vector and Acc computation
   streams twice before Rust product execution.
3. **Product:** Axeyum imports each stream twice to `CompletedImport`; exact
   declaration counts/names remain stable; generated recursor types and rules
   pass the existing definitional comparison; selected recursor applications
   reduce to the preregistered normal forms.

`recursiveIndexedWitness` and `reflexiveWitness` count only for constructor
admission. Computation credit requires a term whose WHNF exercises the
corresponding recursor rule. Official source acceptance and Axeyum computation
are reported separately; neither is inferred from the other.

## 10. Milestones and commit rhythm

### M0 — machine preregistration and computation-source freeze

**Complete.** The machine registration now binds the baseline revision, exact
semantic/case/mutation/resource/stop contracts, one twice-compiled source, and
two root-specific byte-identical official streams. Ten fail-closed tests reject
drift and premature Axeyum product observations. See the
[M0 result](lean-recursive-induction-hypotheses-m0-2026-07-22.md).

- commit ADR-0353 and this plan first;
- add a machine-readable v1 registration binding baseline revision, Lean pin,
  fixture hashes, executable rule, case/mutation IDs, commands, resources, and
  stop conditions;
- add and hash-freeze the supplemental `Vector`/`Acc` computation source;
- run only registration validation and pinned-Lean source/export freezing—no
  Axeyum semantic observation against the new stream;
- commit, push, and verify local/tracking/remote equality.

### M1 — shared recursive-field representation under existing declines

**Complete.** One WHNF telescope-tail operation now classifies and reopens
recursive fields; checked metadata retains only stable field position and
telescope depth; both the minor and rule paths rederive context-local binders,
indices, and applied values. `RecursiveFieldShapeMismatch` is the typed
fail-closed reconstruction boundary. Direct-recursive declaration identities,
Nat/List computation, the 182-test kernel suite, both feature declines, and the
frozen 840-case positivity summary remain unchanged. See the
[M1 result](lean-recursive-induction-hypotheses-m1-2026-07-22.md).

### M2 — generalized native IH and computation rules

**Complete.** One telescope/index-aware rule now admits all ten positive native
rows and preserves all four negative transactional classes. A fixed 768-case
public-path grammar repeats byte-identically and covers every applicable native
semantic mutation; a separate contract rejects recursor type, minor, rule, and
field-count corruption. The retained 840-case population reports both its exact
TL2.11 baseline partition and M2's deliberate 186-case admission widening. The
182-test kernel suite, direct-recursive identities, focused clippy, and rustdoc
pass. No new official stream was passed to the importer. See the
[M2 result](lean-recursive-induction-hypotheses-m2-2026-07-22.md).

### M3 — importer policy and exact official streams

- narrowly remove the supported reflexive metadata decline;
- import both frozen target streams twice with completion-only publication;
- compare generated official recursors and execute selected reductions;
- add importer type/rule/metadata mutations and preserve all other declines;
- commit and push.

### M4 — pinned computation differential and assurance update

- reproduce both M0 computation streams twice and confirm their frozen
  identities;
- run pinned Lean and Axeyum computation observations twice;
- update the construct matrix from tested facts rather than hand-edited claims;
- record timing/RSS and exact admission/computation assurance separately;
- commit and push.

### M5 — closure and TL2.13 handoff

- run all final bounded gates;
- accept, reject, or defer ADR-0353 from its preregistered exits;
- close the research question and mark TL2.12 DONE only if every gate passes;
- synchronize PLAN, STATUS, both Lean roadmaps, P6.0, project state, and docs;
- hand the semantic spine to TL2.13 mutual groups, retaining TL2.14 frontend
  lowering as dependency-gated;
- commit, push, and verify local/tracking/remote equality.

Each milestone is independently reviewable. Stage only milestone-owned files;
preserve unrelated dirty work. A failed observation is documented and pushed
as a negative result before changing the design.

## 11. Resource and validation policy

- Lean: exact pinned binary, one worker, `MemoryHigh=3G`, `MemoryMax=4G`,
  bounded timeout, repository-local temporary/linker directory;
- Rust: at most two build jobs and a 4 GiB cgroup/wrapper where applicable;
- no unbounded workspace-wide command and no parallel Lean jobs;
- kernel unit/integration/doctest suites and importer integration/doctest suite;
- exact direct-recursive, positivity, construct-matrix, and transactional-import
  regressions;
- repeated >=512-case recursive grammar and repeated 840-case positivity
  grammar;
- focused clippy and rustdoc with warnings denied, focused rustfmt;
- registration/observation validators, parity documents, foundational
  resources, and relative-link checks;
- `git diff --check`, staged-file audit, commit, push, and remote-ref equality.

Commands and selectors are frozen by M0 after confirming their current names.
Any OOM, signal termination, missing artifact, missing required Lean binary, or
partial output is a failed gate, not an implicit pass or invitation to increase
parallelism.

## 12. Stop conditions

Stop, preserve the evidence, and amend the decision before continuing if:

1. pinned Lean's generated recursor shape disagrees with the executable rule;
2. direct-recursive type, rule, computation, or serialized identity changes;
3. any TL2.11 positive/negative/invalid classification changes;
4. constructor checking and recursor generation classify a field differently;
5. a generated recursor self-checks but differs from the frozen official one;
6. `MiniVector` or `MiniAcc` imports without an exact recursor comparison;
7. a constructor-only witness is accidentally promoted to computation credit;
8. a negative/mutation path leaves an environment declaration or
   `CompletedImport` behind;
9. supporting the case requires more than one family motive/recursor group;
10. a `numNested>0`, unsafe, or malformed group becomes admitted;
11. either generated summary is nondeterministic, duplicate, or below its
    registered population;
12. any required run exceeds 4 GiB, is killed, or needs unbounded parallelism;
13. unrelated dirty work overlaps a target file.

## 13. Explicit non-claims

TL2.12 does not establish:

- mutual-inductive admission or positivity over a mutual occurrence set;
- nested-inductive or well-founded source lowering;
- native Lean parser, macro, elaborator, tactic, compiler, Lake, LSP, or
  `.olean` compatibility;
- `Init`, `Std`, or mathlib coverage beyond exact imported closures;
- all inductive families or all universe/elimination combinations;
- full Lean-kernel parity, consistency, or replacement of official Lean;
- computation from constructor admission alone.
