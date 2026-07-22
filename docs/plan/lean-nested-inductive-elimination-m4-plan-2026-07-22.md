# Lean nested-inductive elimination M4: exact importer plan

Date: 2026-07-22

Status: preregistered before the first M4 successful nested stream import

Parent:
[TL2.14 P0--M6 plan](lean-nested-inductive-elimination-tl2.14-plan-2026-07-22.md)

Native prerequisite:
[M3 result](lean-nested-inductive-elimination-m3-2026-07-22.md)

Decision gate:
[proposed ADR-0355](../research/09-decisions/adr-0355-preregister-lean-nested-inductive-elimination.md)

Baseline documentation checkpoint: `bed1614a2403757f4c615d58a9a231624f9d2692`

Native semantic checkpoint: `6a2afdd57c969bc1a847d77a85cc99552fa935b1`

## Boundary and ownership

M4 removes only `axeyum-lean-import`'s structural
`Unsupported("inductive-nested")` policy decline after the native M2/M3 gate
has independently admitted and restored the source group. It derives the
kernel-produced auxiliary population, maps wire recursors by exact generated
name rather than array position, and compares every exported family,
constructor, recursor, type, rule, and metadata contract before the private
staging kernel may become a `CompletedImport`.

The Rust implementation lane owns exactly:

- `crates/axeyum-lean-import/src/lib.rs` for the bounded importer comparison;
- `crates/axeyum-lean-import/tests/official_construct_matrix.rs` for the
  historical M1 expectation transition and retained malformed controls; and
- a new
  `crates/axeyum-lean-import/tests/official_nested_inductive_groups.rs` for
  exact official imports, order non-authority, and wire/publication mutations.

The coordinator separately owns this M4 plan, the eventual M4 result, and the
PLAN/STATUS/resume/roadmap reconciliation checkpoint. No kernel, fixture,
machine registration, construct-matrix history, identity
schema, generated assurance artifact, or live decline registry changes in M4.
Any required kernel semantic/public API change, fixture rewrite, declaration-
identity change, or observation unavailable through `CompletedImport` is a
stop-and-review event before implementation continues.

M4 does not normalize a frozen theorem side, award cross-nested computation
credit, append an assurance overlay, remove the live nested decline, or accept
ADR-0355. Those remain M5/M6 work.

## Derivation before wire comparison

`numNested` and wire recursor order are descriptive inputs, never admission
authority. M4 follows this order:

1. parse all source family and constructor records with the existing exact-key,
   ownership, order, universe, parameter, index, field, unsafe, and group
   checks;
2. retain the group-wide exported `numNested` values only for later comparison;
3. call `Kernel::add_mutual_inductive` once with only the translated source
   families and constructors;
4. read the generated main recursor for the first source family and derive
   `auxiliary_count = num_motives - source_family_count`, rejecting underflow;
5. require every source main recursor to exist and participate in the same
   generated motive population through the ordinary metadata comparison;
6. construct the exact expected name set: each source `Family.rec` plus
   `First.rec_1` through `First.rec_N`, where `N` is the kernel-derived count;
7. compare the exported group-wide `numNested` value to `N` before inspecting
   recursor names;
8. only when that count agrees, apply the recursor-count policy and then
   require the wire recursor population to equal the derived name set; and
9. compare records by name, independent of wire array order.

The derivation uses checked generated recursor metadata, not environment-size
deltas, map iteration order, exporter count, or suffix probing. Successful
native publication already guarantees deterministic, collision-checked,
gap-free `.rec_N` names.

Comparison order is frozen so each tooth reaches its intended layer. A
reported count different from the derived count first returns
`generated/exported numNested differs`, regardless of whether the record array
has been adjusted to that false count. Once the counts agree, a nested group
with missing/extra recursors returns the existing
`nested inductive recursor count differs from numNested`; a derived ordinary
group retains the existing singleton/mutual recursor-count diagnostics. Name
membership and duplication are checked only after both count comparisons.

The bounded Rust shape is fixed: retain `num_nested` in
`ExportedInductiveFamily`; restructure only `ImportState::import_inductive` to
remove the M1 policy decline and perform the post-admission derivation;
generalize `validate_generated_recursor` to accept an exact expected generated
name plus an optional source-main index contract; extend
`validate_recursor_group_metadata` with the derived nested non-K check; reuse
the existing family/constructor/rule/universe helpers; and update the crate-
level nested-support prose. `identity.rs` and every kernel file remain
untouched.

## Exact declaration comparison

The existing importer checks source family and constructor declarations after
native admission. M4 generalizes recursor comparison from one `Family.rec` per
source family to the complete kernel-derived main-plus-auxiliary name set.

For every recursor record, including auxiliaries, require:

- exact generated name membership and no duplicate/missing record;
- exact source-group `all` names while ignoring record array position;
- `isUnsafe = false`;
- universe-parameter arity and alpha-renamed type definitional equality;
- exact parameter, index, motive, and minor counts;
- exact rule count/order, restored constructor name, field count, and
  alpha-renamed closed right-hand-side definitional equality; and
- existence as a generated public `Declaration::Recursor`.

Axeyum's `Declaration::Recursor` intentionally has no stored wire `k` flag, so
M4 does not misdescribe `k` as generated metadata. Pinned Lean 4.30's
`init_K_target()` requires the expanded inductive declaration to contain
exactly one type former, be `Prop`, have one constructor, and have zero
nonparameter constructor fields. A kernel-derived `N > 0` means the checked
expanded declaration had `source_family_count + N > 1` type formers, directly
witnessed by the generated main recursor's motive count. Therefore every
restored main and auxiliary recursor in a derived nested group is independently
non-K, including empty or phantom containers. M4 requires wire `k = false` and
returns `nested recursor may not be a K target` on mutation without adding a K
field or kernel API.

For source main recursors, the generated family index count must still equal
the exported family `numIndices`. Auxiliary index counts are derived from and
compared directly with their generated public recursors; they are not copied
from the source family. This is required for the indexed `NestVec` stream.

All comparison happens inside `import_ndjson`'s private staging kernel. A late
wire or later-declaration failure returns no kernel/report pair and therefore
cannot publish a partial import.

## Frozen positive population

The following retained streams import twice. Each pair must return equal full
`ImportReport`s, zero axioms, declaration identities for every admitted
declaration, and the exact inventory below:

| Stream | N/L/E/D | Admitted | Required nested surface |
|---|---:|---:|---|
| construct-matrix nested | 70/6/322/10 | 22 | `Rose`, `Rose.node`, `Rose.rec`, `Rose.rec_1`, `nestedWitness` |
| auxiliary recursion | 122/8/494/17 | 34 | `Rose.rec`, `Rose.rec_1`, selected theorem |
| indexed container | 134/8/554/17 | 34 | `IndexedRose.rec`, indexed `IndexedRose.rec_1`, selected theorem |
| repeated container | 122/8/518/17 | 34 | `RepeatRose.rec`, one reused `RepeatRose.rec_1`, selected theorem |

The exact stream paths, hashes, roots, and family/recursor inventories remain
those frozen by
[`lean-nested-inductive-elimination-v1.json`](lean-nested-inductive-elimination-v1.json).
M4 tests do not recompute theorem normal forms.

The observer checks the exact public recursor metadata registered in M0:

- source main and auxiliary recursors each have two motives and three minors;
- `Rose.rec_1` owns `NestList.nil/cons` rules with field counts `[0, 2]`;
- `IndexedRose.rec_1` has one index and owns `NestVec.nil/cons` rules with
  field counts `[0, 3]`;
- `RepeatRose.rec_1` appears exactly once despite two identical source fields;
  it owns `NestList.nil/cons [0, 2]`; and
- each source main rule owns its source constructor with the registered field
  count.

The three frozen wire orders are retained as positive non-authority evidence:
the first two list auxiliary before main, while the repeated-container stream
lists main before auxiliary. An explicit swapped-array mutation of each shape
must produce the same full report and declaration identities.

## Frozen rejecting mutation registry

Mutations operate on one retained nested record and preserve valid NDJSON
topology unless the named tooth is specifically a topology failure. Every
rejection asserts the exact `ImportError` layer, line, and stable message/code;
none may return `CompletedImport`.

1. exported `numNested = 0` with the two-record wire population rejects after
   native derivation with `generated/exported numNested differs`;
2. exported `numNested = 2` plus a count-matching third record rejects with
   `generated/exported numNested differs`; that third record may be a duplicate
   because count comparison is frozen before name parsing;
3. removing `rec_1` by exact name rejects with
   `nested inductive recursor count differs from numNested`;
4. extra recursor rejects with
   `nested inductive recursor count differs from numNested`;
5. two records with one duplicated recursor name reject with
   `inductive group repeats a recursor record`;
6. a foreign recursor name rejects with
   `exported recursor name does not belong to kernel-derived group`;
7. a wrong recursor `all` list rejects with
   `inductive recursor all list differs from ordered group`;
8. a wrong recursor type rejects with
   `generated/exported recursor types are not definitionally equal`;
9. a wrong `numParams` rejects with
   `generated/exported recursor numParams differs`;
10. wrong source-main and auxiliary `numIndices` variants reject with
    `generated/exported recursor numIndices differs`;
11. a wrong `numMotives` rejects with
    `generated/exported recursor numMotives differs`;
12. a wrong `numMinors` rejects with
    `generated/exported recursor numMinors differs`;
13. a wrong universe-parameter arity rejects with
    `generated/exported recursor universe-parameter arity differs`;
14. missing and extra rule variants reject with
    `generated/exported recursor rule count differs`;
15. a wrong restored rule constructor rejects with
    `generated/exported recursor rule differs`;
16. a wrong rule `nfields` rejects with
    `generated/exported recursor rule differs`;
17. a wrong rule right-hand side rejects with
    `generated/exported recursor rule differs`;
18. `isUnsafe = true` rejects at the exact line with
    `Unsupported("declaration-unsafe")`;
19. `k = true` variants on both a nested main and auxiliary recursor reject with
    `nested recursor may not be a K target`; and
20. changing the final theorem name in the auxiliary-recursion stream to the
    already admitted `Eq` rejects on line 642 as
    `ImportError::Kernel { declaration: "Eq", source:
    KernelError::DeclarationExists { .. } }` and never publishes a completed
    import.

The separate positive order swaps are not counted as rejection teeth. A
mutation that unexpectedly imports, rejects at a weaker unrelated layer, or
changes a supposedly non-authoritative order result is an M4 failure.

## Retained controls and resources

M4 retains:

- the direct-recursive control before every declined/malformed comparison;
- the 35-declaration/zero-axiom well-founded stream twice;
- ordinary singleton and mutual malformed recursor-count identities;
- complete completion-only-publication and declaration-identity-v1 suites;
- M2's 23 public nested cases and M3's exact 640-case digest
  `a20fe056c9443a37`;
- exact 720 mutual, 768 recursive-IH, and 840 positivity descriptors; and
- the M0 source/wire checker without adding an assurance overlay or normal-form
  observation.

All Rust work uses one Cargo job and one test thread under
`MemoryHigh=3G`, `MemoryMax=4G`, and `MemorySwapMax=512M`, with this worktree's
own `target/` and repository-local temporary directory. Use direct
`rustfmt --edition 2024` only on owned Rust files; never run workspace-wide
`cargo fmt`.

## Stop conditions

Stop and amend this plan before broadening scope if:

- the auxiliary count cannot be derived from checked public recursor metadata;
- successful import requires trusting `numNested` or wire recursor order;
- exact official comparison requires a kernel semantic/public API change;
- a frozen stream, source, hash, root, or identity schema must change;
- auxiliary recursors cannot be compared through the same type/metadata/rule
  path as source main recursors;
- pinned Lean behavior contradicts the expanded-group structural non-K
  derivation;
- a wire mutation imports or reaches only an unrelated weaker rejection;
- an invalid/later record exposes a partial `Kernel` or `ImportReport`;
- importing declarations requires evaluating a frozen theorem normal form;
- a retained 640/720/768/840 descriptor or well-founded control drifts;
- the importer changes any generated assurance/live-decline artifact;
- the 4 GiB scope is killed/exceeded; or
- another lane overlaps an owned importer file.

Preserve the evidence and commit a reviewed amendment before continuing after
any stop condition.

## Exit

M4 is complete only after the four official streams import twice with exact
full-report equality, all 20 rejecting mutations and order non-authority
controls pass, the complete retained gates are green, an independent read-only
review finds no semantic blocker, and the bounded semantic/docs checkpoints
are committed, pushed, and verified against the remote branch.
