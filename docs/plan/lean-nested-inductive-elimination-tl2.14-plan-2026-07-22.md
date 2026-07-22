# Lean nested-inductive elimination: TL2.14 execution plan

Status: preregistered; P0 complete; M0 source/wire freeze next

Date: 2026-07-22

Decision gate:
[proposed ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)

Parents:

- [post-TL2.13 dependency audit](lean-post-tl2.13-dependency-audit-2026-07-22.md);
- [Lean implementation plan](lean-system-implementation-plan-2026-07-21.md)
  (corrected TL2.14);
- [Lean compatibility roadmap](lean-system-compatibility-roadmap-2026-07-21.md);
- [completed TL2.13 result](lean-mutual-inductive-groups-final-2026-07-22.md);
- [official construct-matrix handoff](lean-official-construct-matrix-final-2026-07-22.md).

## 1. Outcome and honest boundary

Implement pinned Lean 4.30's nested-inductive kernel transformation through the
same atomic admission path that now handles single-family, indexed,
higher-order, and mutual inductives. Discover nested applications from checked
types, create and check a temporary expanded mutual group, restore official
surface types/rules, publish deterministic auxiliary recursors, and compare the
result with exact official exports.

This is trusted kernel/import compatibility for already elaborated inductive
declarations. It is not a native Lean parser, inductive command elaborator,
pattern compiler, structural-recursion compiler, well-founded recursion
elaborator, termination checker, tactic engine, or general `Init`/mathlib
profile. Those source-facing responsibilities remain TL4.9/TL4.10.

## 2. Corrected dependency boundary

The former roadmap row combined nested and well-founded frontend lowering and
depended on TL4.12. The completed
[dependency audit](lean-post-tl2.13-dependency-audit-2026-07-22.md) corrects it:

- nested-inductive elimination is part of Lean kernel
  `environment::add_inductive` and is now unblocked by TL2.13;
- well-founded source recursion is an elaborator transformation to
  `WellFounded.fix`/`Acc.rec` and remains TL4.10;
- the frozen well-founded core stream is already a mandatory passing control:
  160 names, 5 levels, 731 expressions, 23 declaration records, 35 admitted
  declarations, and zero axioms, repeated twice;
- the frozen nested stream currently fails before the registered policy decline
  because its one family legitimately exports one main plus one auxiliary
  recursor.

TL2.14 therefore advances the trusted-kernel trajectory without claiming any
native source workflow.

## 3. Baseline that may not move silently

Implementation begins from pushed revision
`340cf7215c9371778fb08a1a2ff81ca68d10400b`, where:

- TL2.11 strict positivity, TL2.12 telescope/index-aware recursive fields, and
  TL2.13 atomic mutual groups are complete;
- the 720 mutual, 768 recursive, and 840 positivity populations pass;
- importer publication is completion-only and declaration identity uses
  `axeyum-lean-declaration-identity-v1`;
- the existing construct source is 2,059 bytes / 75 lines at SHA-256
  `08c6eeaed9d980a631dff14b30de1e3d8da37011b8ad03b84dbdc03c90bff13d`;
- the nested stream is 23,418 bytes / 409 records at SHA-256
  `faabcde4553b0d597a768aedf35117d7fb4310d3dae052e2545e5b239277456e`;
- its source family `Rose` has `numNested = 1`, one constructor, and exported
  recursors `Rose.rec_1` plus `Rose.rec`;
- product measurement repeats `Malformed(line=248, message="single-family
  inductive must export one recursor")` twice and publishes no import;
- the separately frozen well-founded stream is 49,140 bytes / 920 records at
  SHA-256
  `c1fc14097f9be381625846f13277edfd8294afd93c8e9cadd72c54d71e48e3c6`
  and now completes twice under the TL2.12 overlay.

M0 records these facts in a machine-readable registration before semantic
changes. Historical product observations remain immutable; later milestones
append versioned overlays.

## 4. Pinned executable authority

Use Lean 4.30 commit
`d024af099ca4bf2c86f649261ebf59565dc8c622` and `lean4export` 3.1 commit
`a3e35a584f59b390667db7269cd37fca8575e4bf`.

The required kernel behavior in `references/lean4/src/kernel/inductive.cpp` is:

- `is_nested_inductive_app`: existing inductive head, parameter arity,
  occurrence in a parameter, and no loose variables in nested parameters;
- `replace_if_nested`: copy the complete existing container group and map one
  specialized container family to one auxiliary family;
- `replace_all_nested`: transform constructor types recursively;
- `elim_nested_inductive_fn::operator()`: queue original and copied families
  until expansion reaches a fixed point;
- ordinary `add_inductive_fn`: check the expanded mutual declaration;
- `mk_aux_rec_name_map`: deterministic `.rec_N` surface names;
- `restore_nested`: restore types, constructors, recursor references, and rule
  right-hand sides; and
- `environment::add_inductive`: publish only restored surface declarations.

`references/lean4/src/Lean/Declaration.lean` defines `numNested` as the number
of kernel-produced auxiliary data types. `Lean.Elab.MutualInductive.addAuxRecs`
registers those recursors after kernel admission; it does not generate or
authorize them.

## 5. Required source and wire freezes

M0 retains the existing `Rose α` over `NestList (Rose α)` construct root and
adds explicit computation sources before any product change. The source suite
must force the restored auxiliary recursors to compute; a constructor-only or
root-field pattern match is admission evidence only.

At minimum freeze:

1. the existing parametric `Rose` construct stream;
2. a non-indexed explicit recursor term that traverses `NestList (Rose α)` and
   crosses `Rose.rec -> Rose.rec_1 -> Rose.rec` before reaching its normal form;
3. an indexed container profile whose nested application carries indices;
4. a repeated-container profile proving structurally identical applications
   reuse one auxiliary family; and
5. a negative source with a loose outer variable in a container parameter,
   rejected by pinned Lean with a registered diagnostic.

Compile every retained source twice and export each selected root twice under
the resource policy. Freeze exact source/stream hashes, bytes, lines/records,
root names, declaration/group/recursor inventories, recursor order, expected
normal forms, elapsed time, and maximum RSS. The independent census may inspect
wire records; the Axeyum importer may not consume the new computation streams
until M4.

## 6. Trusted expansion algorithm

Represent the prepass with private checked structures:

- original ordered family specs and shared parameters;
- a structurally keyed mapping from specialized container applications to
  fresh auxiliary families;
- the queue of original/copied family specs;
- auxiliary family-to-original nested application mapping;
- auxiliary constructor-to-original constructor mapping; and
- generated auxiliary recursor-to-surface `.rec_N` mapping.

No exporter record, display string, arena allocation order, or hash-map
iteration order may choose these structures. Use explicit ordered vectors and
canonical structural comparison.

For every queued constructor:

1. reopen exactly the declared shared parameters with their binder info;
2. scan its remaining type for nested candidates;
3. reject incomplete existing-inductive applications and loose nested
   parameters with typed errors;
4. on the first structurally new `F Ds`, copy all families/constructors in
   `F`'s checked mutual group under fresh auxiliary names;
5. instantiate away `F`'s parameters, prepend the outer shared parameter
   telescope, and retain its indices;
6. replace the occurrence with the matching auxiliary application; and
7. queue the copied families so recursively nested containers are processed.

Pass the final expanded group to the existing atomic mutual algorithm once.
Do not create a second positivity, motive/minor, recursive-field, or recursor
implementation.

## 7. Restoration and publication contract

From the checked temporary environment:

- restore original family metadata with only the source `all` group;
- restore every original constructor type;
- restore and publish each original-family recursor;
- restore each auxiliary recursor type/rule and publish it under the first
  source family's deterministic `.rec_N` namespace;
- rename auxiliary rule constructors back to the corresponding original
  container constructors; and
- reject any remaining temporary auxiliary name in a published type, value,
  dependency, or rule.

Infer every restored published type and every closed rule right-hand side in
the final staged surface environment. Commit only after all checks succeed.
Rollback must scale with the attempted group and expose no partial declaration
or completed import.

## 8. Test and mutation matrix

### Named native positives

- one outer family over a one-family list-like container;
- repeated identical container applications;
- two different parameterizations of the same container;
- an existing mutual container group;
- an outer mutual group with self, cross, and nested fields;
- zero/one/two outer parameters and zero/one/two container indices;
- higher-order fields returning nested applications;
- one and two levels of recursive nested expansion;
- `Type` and allowed `Prop` results;
- empty-constructor and mixed recursive/nonrecursive owners.

### Typed native negatives

- non-inductive foreign head;
- incomplete container parameter prefix;
- loose bound variable in a nested container parameter;
- negative occurrence inside a container parameter;
- wrong fixed outer parameter or occurrence index;
- duplicate/fresh-name collision;
- unsupported or malformed copied container metadata;
- expansion limit exhaustion;
- restoration leaving an auxiliary reference;
- restored recursor/rule inference failure;
- late failure after every temporary declaration is staged.

### Mutation teeth

Mutate container family order, specialized parameters, auxiliary reuse versus
duplication, fresh-name index, copied constructor owner/index/type, motive/minor
order, recursive target, restored recursor reference, rule constructor,
`nfields`, `numNested`, recursor count/order/name, indices, universes, unsafe/K
flags, and final publication. Each mutation must reject at its registered layer
without a partial environment.

### Generated population

Run at least 640 unique public-path records twice with a byte-identical summary.
Vary original/container group sizes, parameters, indices, constructors, fields,
nested depth, repeated/distinct container applications, recursion target,
`Prop`/`Type`, and valid/negative classification. The independent oracle reads
the expanded/restored public structures rather than repeating production
branch predicates. Retain exact 720/768/840 descriptors.

## 9. Milestones

### P0 — authority, scope, and dependency correction

Status: **complete** in this preregistration commit.

- inspect the exact current worktree, roadmap dependencies, official C++ kernel
  implementation, Lean declaration metadata, and WF elaborator;
- separate TL2.14 trusted nested elimination from TL4.10 source recursion;
- propose ADR-0355 and this P0-M6 plan;
- synchronize live planning surfaces without claiming product progress;
- commit, push, and verify remote equality before M0 retains new evidence.

### M0 — source/wire and no-product freeze

- add the exact explicit computation/negative sources;
- compile/export every retained root twice with pinned tools;
- commit a fail-closed machine registration and independent census;
- bind current nested diagnostic and passing well-founded control;
- reject any Axeyum observation of new streams;
- commit, push, and verify remote equality.

### M1 — correct diagnostic preflight

- parse type metadata before applying recursor-count policy;
- derive the expected main+auxiliary recursor population shape;
- move the exact nested row to `Unsupported(inductive-nested)` only;
- prove no admission, no partial publication, and unchanged controls;
- commit, push, and verify remote equality.

### M2 — native expansion and restoration

- implement private discovery/copy/queue/restore structures;
- reuse the one TL2.13 atomic group checker;
- close the named native positive/negative matrix;
- prove final-surface inference and whole-operation rollback;
- do not pass M0 computation streams to the importer;
- commit, push, and verify remote equality.

### M3 — deterministic nested grammar

- land and repeat the >=640-case public-path population;
- close generated expansion/reuse/restoration mutation teeth;
- retain exact 720/768/840 populations and direct identities;
- leave importer policy and M0 streams untouched;
- commit, push, and verify remote equality.

### M4 — importer and exact official declarations

- remove only the structural nested policy decline after native support;
- derive and compare `numNested`, main/auxiliary recursors, and every contract;
- import the existing construct and new computation streams twice;
- close wire metadata/order/type/rule/publication mutations;
- commit, push, and verify remote equality.

### M5 — computation and assurance

- repeat pinned-Lean source compilation and Axeyum computations;
- require registered cross-nested normal forms, not constructor witnesses;
- append a TL2.14 assurance overlay without rewriting history;
- remove the live nested decline only after all support gates pass;
- commit, push, and verify remote equality.

### M6 — final closure

- run all bounded final gates;
- accept, reject, or defer ADR-0355 strictly from its exits;
- synchronize PLAN, STATUS, project state, roadmaps, P6.0, research question,
  generated documents, and handoff;
- commit, push, and verify local/tracking/remote equality.

Every milestone stages only owned files. Negative results are committed rather
than hidden. Concurrent solver/FP work remains untouched.

## 10. Resource and validation policy

- exact Lean 4.30 binary and pinned `lean4export`, one worker;
- `systemd-run --user --scope`, `MemoryHigh=3G`, `MemoryMax=4G`,
  `MemorySwapMax=512M`;
- repository-local temporary directories because system `/tmp` may be
  saturated;
- one Rust build job and one test thread for final suites;
- no unbounded workspace-wide or parallel-heavy build;
- kernel/importer full tests and doctests at M6;
- focused nested, mutual, recursive, positivity, identity, construct-matrix,
  well-founded, mutation, and completion-only-publication regressions;
- focused rustfmt, warning-denied Clippy/rustdoc, preregistration validators,
  parity docs, foundational resources, links, `git diff --check`, staged audit,
  push, and remote-ref equality.

An OOM, signal, nondeterministic artifact, missing exact pin, incomplete stream,
required limit increase above 4 GiB, or reduced registered population is a
failed gate, not permission to weaken the plan.

## 11. Stop conditions

Stop, preserve evidence, and amend ADR-0355 before continuing if:

1. pinned Lean does not place the target transformation in kernel admission;
2. official auxiliary discovery differs from the registered head/parameter/
   occurrence/no-loose-variable rule;
3. the existing TL2.13 group checker cannot check the expanded group without a
   second semantic implementation;
4. restoration requires trusting exporter `numNested`, recursor order, or
   auxiliary names;
5. a temporary auxiliary family/constructor leaks into the final environment;
6. restored published types or closed rules do not independently infer;
7. declaration identity v1 must change to represent the accepted surface;
8. the exact official stream cannot be reproduced twice;
9. explicit recursion does not exercise an auxiliary recursor;
10. any failure publishes a partial environment or `CompletedImport`;
11. the generated population duplicates cases or is nondeterministic;
12. any retained 720/768/840 or well-founded control drifts;
13. a required process exceeds the resource envelope or is killed;
14. unrelated dirty work overlaps a target file.

## 12. Explicit non-claims

TL2.14 does not establish:

- native Lean source parsing or inductive-command elaboration;
- pattern matching/equation compilation or structural recursion compilation;
- well-founded/partial recursion elaboration or termination proving;
- tactic, metavariable, typeclass, module, Lake, LSP, compiler, or `.olean`
  compatibility;
- every unsafe or universe/elimination profile;
- broad `Init`, `Std`, or mathlib admission;
- full Lean-kernel parity, consistency, or replacement of official Lean.
