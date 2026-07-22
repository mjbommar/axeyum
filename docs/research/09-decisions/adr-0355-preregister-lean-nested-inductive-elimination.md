# ADR-0355: Preregister Lean nested-inductive kernel elimination

Status: proposed

Date: 2026-07-22

Execution plan:
[TL2.14 nested-inductive plan](../../plan/lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md)

M0 evidence:
[source/wire freeze](../../plan/lean-nested-inductive-elimination-m0-2026-07-22.md)
and [machine registration](../../plan/lean-nested-inductive-elimination-v1.json)

Dependency audit:
[post-TL2.13 trust-boundary audit](../../plan/lean-post-tl2.13-dependency-audit-2026-07-22.md)

## Context

Accepted ADR-0354 supplies the atomic mutual-group checker required by nested
inductives. The former TL2.14 description combined nested-inductive admission
with well-founded source recursion and depended on TL4.12. That does not match
pinned Lean 4.30:

- nested-inductive elimination runs inside kernel
  `environment::add_inductive`; and
- well-founded recursive source definitions are elaborated into checked
  `WellFounded.fix`/`Acc.rec` terms by `Lean.Elab.PreDefinition.WF`.

The distinction is observable in the frozen construct matrix. The elaborated
well-founded root already imports as 35 checked declarations with zero axioms.
The nested `Rose` root instead stops before its inductive record is parsed
because one source family legitimately exports two recursors when
`numNested = 1`.

The exact implementation authority is Lean 4.30 commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`, especially
`elim_nested_inductive_result`, `elim_nested_inductive_fn`,
`is_nested_inductive_app`, `replace_if_nested`, `replace_all_nested`,
`mk_aux_rec_name_map`, `restore_nested`, and `environment::add_inductive` in
`src/kernel/inductive.cpp`.

## Decision

**Implement nested-inductive support as a trusted, deterministic prepass inside
the kernel's atomic inductive admission path. Expand nested container
applications into fresh auxiliary mutual families, check that expanded group
with the existing TL2.11-TL2.13 rules, then restore and publish only the
official surface declarations and auxiliary recursors. Keep well-founded source
recursion in TL4.10.**

For an original ordered group `O` with shared parameters `P`, scan each
constructor type after reopening its parameter telescope. A term is a nested
candidate only when it has the form

```text
F D_0 ... D_(p-1) i_0 ... i_(k-1)
```

where:

1. `F` is an already admitted inductive family with `p` parameters;
2. at least one parameter `D_j` contains a family already in the expanding
   original/auxiliary group;
3. no `D_j` contains a loose bound variable at the nested site; and
4. the application supplies at least all `p` parameters.

For each structurally distinct parameterized container application `F Ds`, copy
every family and constructor in `F`'s existing mutual group to fresh auxiliary
names. Replace `F Ds is` with the corresponding auxiliary family applied to
`P` and `is`. Process copied constructors with the same queue until no nested
application remains. Structural equality, not definitional equality, deduplicates
container applications, matching the pinned implementation.

Admit the expanded group once through the existing complete-group positivity,
constructor, motive/minor, recursive-field, recursor, inference, and rollback
path. The temporary auxiliary group is never the public result. Restore:

- auxiliary family applications to the original parameterized container;
- auxiliary constructor applications to the original container constructors;
- references to auxiliary recursors to deterministic surface auxiliary
  recursor names;
- original family `all` metadata to the original source group; and
- all constructor/recursor types and rule right-hand sides before publication.

Publish the original families and constructors, one main recursor per original
family, and the restored auxiliary recursors named from the first source family
as `.rec_1`, `.rec_2`, and so on. Check name freshness before mutation. All
published types and every closed rule right-hand side must infer in the final
surface environment before the insertion-log transaction commits.

Exporter fields remain comparison evidence, never authority. The importer must
derive the auxiliary population structurally, then require:

- `numNested` equals the derived auxiliary-family count for each exported
  family contract;
- the recursor population and names equal the generated main plus auxiliary
  recursors;
- every recursor's type, motives, minors, indices, rules, constructor owners,
  field counts, and K/unsafe flags match; and
- any mismatch returns a typed non-publication result.

The existing declaration-identity v1 remains unchanged. The restored recursor
types/rules and their dependencies already encode the supported surface. If
explicit persistent nested-origin metadata is added to `Declaration`, it needs
a new identity version and separate ADR.

## Exit gates

ADR-0355 may be accepted only when:

1. the exact Lean revision, source functions, baseline revision, source/wire
   fixtures, hashes, case/mutation populations, resources, and stop conditions
   are committed before semantic implementation;
2. the existing nested row first moves from accidental `Malformed` to the
   registered `Unsupported(inductive-nested)` boundary without admission;
3. nested discovery checks an existing inductive head, full parameter prefix,
   family occurrence in container parameters, and the no-loose-bound-variable
   rule rather than trusting `numNested`;
4. copying includes every family/constructor of the existing container's mutual
   group, supports differing outer/container parameter counts, deduplicates
   structural container applications, and processes recursively nested copies;
5. the expanded original+auxiliary group passes the unchanged TL2.11-TL2.13
   positivity, motive/minor, target-family, recursor inference, and atomic
   rollback rules;
6. restoration removes every temporary auxiliary family/constructor reference
   from published surface types and rules while retaining deterministic
   `.rec_N` auxiliary eliminators;
7. invalid nested parameters, polarity, arity, indices, auxiliary order/name,
   restored constructor/recursor, metadata, and late-publication mutations
   reject transactionally;
8. a generated public-path population of at least 640 unique nested profiles
   repeats byte-identically and covers multiple containers, container mutual
   groups, outer mutual groups, indices, higher-order fields, repeated and
   recursively nested applications, `Prop`/`Type`, and all typed negatives;
9. the frozen official `Rose` stream and separately frozen explicit nested-
   computation streams import twice with exact generated/exported declaration
   comparison and registered normal forms in both pinned Lean and Axeyum;
10. the retained 720 mutual, 768 recursive, and 840 positivity populations,
    singleton/direct identities, well-founded 35-declaration import, and
    completion-only publication controls remain exact;
11. the append-only assurance matrix records nested admission and computation
    without rewriting ADR-0351/TL2.12/TL2.13 history;
12. kernel/importer tests and doctests, focused rustfmt, warning-denied Clippy
    and rustdoc, pinned-Lean differentials, contracts, parity docs,
    foundational resources, links, staged audit, push, and local/tracking/remote
    equality pass under the registered 4 GiB/one-worker policy.

## M2 evidence

The [M2 native result](../../plan/lean-nested-inductive-elimination-m2-2026-07-22.md)
implements exit-gate foundations 3--6 without changing importer policy:

- a private rollback-aware index recovers each existing container's complete
  checked ordered mutual group without changing declaration identity;
- discovery checks the exact head/arity/occurrence/no-loose-variable rule and
  structural deduplication;
- complete groups are specialized, queued to a fixed point, and checked once by
  the unchanged TL2.11--TL2.13 atomic worker;
- temporary declarations are cloned, rolled back with both caches cleared,
  recursively restored, leakage-checked, and published as the source surface
  plus exact string `.rec_N` auxiliary recursors; and
- all restored recursor constants are staged before every closed rule body is
  inferred, preserving main/auxiliary cross-recursion.

Twenty-three focused tests cover the named native shape matrix, typed early and
late rollbacks, exact final inference, and `main -> rec_1 -> main` computation.
The semantic implementation is `96b6fbd4da7e20277b338f59983fbe7316b31d22`.

## M3 evidence

The
[M3 result](../../plan/lean-nested-inductive-elimination-m3-2026-07-22.md)
implements the generated and native-mutation exit foundations without changing
importer policy:

- the exact preregistered 640-case grammar runs twice in fresh kernels with
  byte-identical descriptor digest `a20fe056c9443a37`;
- every frozen range endpoint has nonzero realized coverage, with 320 admitted
  and 320 exact typed-reject profiles;
- an independently derived public observer checks complete specialized keys,
  family/constructor/recursor metadata, motive/minor order, exact per-rule
  dependency maps, inference, restoration, and temporary-name absence;
- typed recursor applications perform 320 main and 462 auxiliary iota checks
  across direct and depth-two chains;
- 16 malformed private expansion/restoration mutations prove complete
  transaction rollback and unchanged-source retry; and
- type-correct recursor mutations reject under ordinary typing or change a
  named independent observation.

The first independent audit triggered the preregistered stop condition because
temporary copied-constructor owner/index/type mutations survived the M2
restoration dataflow. Amendments `ab5dbf99` and `d03ba0fc` were committed before
the semantic checkpoint and permit only exact validation of the already-
checked temporary family/constructor/map/freshness surface. The ordinary
inductive worker remains the only semantic admission algorithm. The semantic
implementation is `6a2afdd57c969bc1a847d77a85cc99552fa935b1`, and the final
independent audit found no semantic blockers.

## M4 evidence

The
[M4 result](../../plan/lean-nested-inductive-elimination-m4-2026-07-22.md)
implements the exact official-import exit foundations without claiming
computation or assurance credit:

- the importer derives the auxiliary population from the checked first main
  recursor's motive count rather than trusting `numNested`;
- the construct stream and three frozen computation streams import twice with
  exact full-report equality at 22/34/34/34 admitted declarations and zero
  axioms;
- every source main and `First.rec_N` auxiliary record is selected by generated
  name and compared for exact types, universes, counts, rules, restored
  constructors, fields, and closed rule bodies;
- reversed recursor arrays preserve the complete report and declaration
  identities, proving that wire order is not authority; and
- 20 registered wire/publication mutation classes reject with exact typed
  diagnostics while the well-founded 35/0 and exact 640/720/768/840 controls
  remain green.

The semantic implementation is
`f03dfcdf2b3e49d86a5bb9ad00aeef20c99926ee`. M0 remains the immutable
pre-product no-observation snapshot; M4 is the planned first product import of
those streams.

ADR-0355 remains proposed: M5--M6 still own registered computation
normal forms, assurance, live-decline removal, and the final aggregate gates.

## Alternatives

### Lower nested groups only in the importer

Rejected. Native kernel callers would retain different semantics, and exporter
metadata would become admission authority. Official Lean performs this work in
the kernel entry path.

### Store a magical recursive field for `NestList (Rose a)`

Rejected. A nested field needs the container's complete constructor and
recursor structure. Treating it as direct recursion cannot generate the
container motive/minors or recursive calls and would not generalize beyond one
fixture.

### Trust `numNested` and exported auxiliary recursors

Rejected. Both can be mutated. Axeyum must derive the auxiliary group and
compare the wire result after independent checking.

### Implement well-founded source recursion in the same slice

Rejected. It needs the native parser, metavariables, unification, tactic-driven
decreasing proofs, typeclass resolution, source metadata, and definition
elaboration owned by TL4.10. The pre-elaborated core is already checkable.

### Change declaration-identity v1

Rejected in this slice. The current surface structure is already represented;
any new persistent metadata requires an explicitly versioned decision.

## Consequences

- TL2.14 becomes a dependency-ready trusted-kernel phase after TL2.13.
- The native frontend remains honestly far: TL4.10 still owns recursive source
  elaboration and termination evidence.
- The nested importer row gains a correct typed boundary before it gains
  admission.
- Auxiliary expansion and restoration enlarge the trusted kernel and therefore
  require broader deterministic and mutation coverage than the single frozen
  `Rose` example.
- TL3.1 prelude inventory and TL1.5 importer fuzzing may proceed independently,
  but neither substitutes for these gates.
