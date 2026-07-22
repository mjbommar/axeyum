# ADR-0354: Preregister atomic Lean mutual-inductive group admission

Status: proposed

Date: 2026-07-22

Execution plan:
[TL2.13 mutual-inductive plan](../../plan/lean-mutual-inductive-groups-tl2.13-plan-2026-07-22.md)

## Context

Accepted ADR-0353 completes the single-family recursive rule. TL2.13 is the
first change where an inductive declaration cannot be checked or published one
family at a time. In pinned Lean 4.30, a mutual block is one trusted object:

- all family parameter telescopes must agree and their result universes must be
  equivalent;
- strict positivity ranges over occurrences of every family in the group;
- a recursive field may target any group family;
- every generated recursor binds every group motive and every constructor
  minor, even though its major belongs to one family;
- a recursive field's induction hypothesis and recursive call select the
  motive and recursor of the field's terminal family;
- all families, constructors, and recursors become visible together or none do.

Treating mutual support as repeated calls to the existing single-family API
would be wrong. The first call cannot type-check a constructor that names the
second family, single-family positivity does not see cross-family negative
occurrences, and separately published recursors cannot share a stable motive/
minor order or roll back as one unit.

The exact existing official target is the frozen Lean 4.30 `EvenTree`/
`OddTree` stream from ADR-0351, SHA-256
`06aa05ccc8abc9309fad04b373017e770da25c7b0c2743fc0f097efd72de3174`.
It currently stops at importer policy code `inductive-mutual`. Its two
recursors each carry two motives, four globally ordered minors, and only the
rules for that recursor's own constructors. Its existing `mutualWitness`
establishes source-level pattern-match computation, but does not by itself
exercise Axeyum's independently generated cross-family recursive calls.

The implementation authority is pinned Lean 4.30 commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`, especially
`check_inductive_types`, `check_positivity`, `mk_rec_infos`,
`collect_Cs`, `collect_minor_premises`, `mk_rec_rules`,
`declare_recursors`, `elim_only_at_universe_zero`, and `init_K_target` in
`src/kernel/inductive.cpp`.

## Decision

**Add one atomic, ordered mutual-group admission gate. Preserve the existing
single-family API as a one-member wrapper over that gate, and derive every
motive, minor, induction hypothesis, recursive call, reduction rule, and
publication action from the same checked group order.**

Let a checked group be `G = [I_0, ..., I_(g-1)]`, with shared universe
parameters and shared parameter values `P`. Family `I_i` may have its own index
telescope `K_i` and motive

```text
C_i : Pi indices_i, I_i P indices_i -> Sort v.
```

For a constructor of owner family `I_i`, its result must be exactly
`I_i P result_indices`. For each field, WHNF and open its `Pi` telescope. The
field is recursive exactly when its tail is a valid complete application of
some family `I_j` in `G` at the shared parameters:

```text
u : Pi xs, I_j P recursive_indices.
```

Generate the induction hypothesis

```text
u_ih : Pi xs, C_j recursive_indices (u xs)
```

and the computation-rule value

```text
fun xs =>
  I_j.rec P C_0 ... C_(g-1) all_group_minors
    recursive_indices (u xs).
```

The constructor minor concludes in the owner motive
`C_i result_indices (ctor P fields)`. All constructor fields precede all of
that constructor's induction hypotheses. Motives are ordered by family order;
minors are ordered first by family order and then constructor order; induction
hypotheses are ordered by recursive-field order. Every `I_i.rec` binds the
shared parameters, all motives, all minors, `I_i`'s indices, and an `I_i`
major, and returns `C_i indices major`.

The gate must reproduce the remaining Lean group invariants:

- reject an empty group, duplicate family/constructor/recursor names, parameter
  count/type mismatch, universe-parameter mismatch, or nonequivalent family
  result universes;
- check every constructor against the complete group occurrence set before any
  provisional declaration is visible;
- reject a group-family occurrence in a `Pi` domain and any occurrence that is
  not a complete valid family application with fixed shared parameters and
  occurrence-free indices;
- if the common result universe may be `Prop` and the group has more than one
  family, restrict every motive to `Prop`; mutual declarations are never
  K-like reduction targets;
- generate and infer-check every recursor before atomically publishing any
  family, constructor, or recursor;
- on every error, restore the exact prior ordered environment.

The public group input is an explicit ordered family specification, not loose
parallel vectors. The existing `add_inductive` signature remains source-
compatible and delegates to a singleton group. Wire `all` arrays are validated
against the exact ordered family list; `numMotives`, `numMinors`, per-family
`numIndices`, constructor ownership/index, recursor rules, and `nfields` remain
kernel-checked rather than trusted metadata.

M0 establishes that official format-3.1 `recs` arrays may use dependency order
rather than family order: both frozen two-family streams list the odd-family
recursor before the even-family recursor. This wire order is descriptive.
Import comparison matches recursors by checked name and owned constructor rules;
it may not infer family identity from array position. Motive and minor order in
the recursor types remains the semantic family/family-then-constructor order
above.

M1 establishes the representation and transaction boundary without consuming
that semantic budget. `InductiveFamilySpec` and
`Kernel::add_mutual_inductive` carry the ordered families; common parameter
domains are compared definitionally against shared locals, each family opens
its own indices, result universes are compared for equivalence, and all names
are checked group-wide. `add_inductive` delegates through a singleton group
with its established declarations, rules, computation, identities, and error
payloads unchanged. A private environment insertion log provides a constant-
time checkpoint and rollback proportional to the attempted group. At that
checkpoint, every valid multi-family input still ended in
`MutualInductiveNotSupported`; M2 retained sole ownership of positivity,
constructor admission, motives/minors, recursive calls, recursors, and atomic
publication. See the
[M1 result](../../plan/lean-mutual-inductive-groups-m1-2026-07-22.md).

M2 establishes the native semantic algorithm without consuming importer or
official-stream credit. Positivity ranges over the complete family table before
staging; all family headers and constructors are then staged in one insertion-
log transaction; motives follow family order, minors follow family then
constructor order; recursive hypotheses and calls select the terminal family;
and all recursor types plus closed rule values infer before commit. Eighteen
public integration rows cover the registered singleton, cross, indexed,
higher-order, mixed, empty-constructor, mutual-`Prop`, and negative shapes. Two
kernel-private tests reject recursor-contract/rule mutations and inject a final-
rule failure after complete staging to prove whole-group rollback. The importer
still declines mutual groups and neither M0 computation stream has been passed
to it. See the
[M2 result](../../plan/lean-mutual-inductive-groups-m2-2026-07-22.md).

ADR-0350's declaration-identity v1 remains unchanged in this slice. Group
membership is checked input to atomic generation and is structurally reflected
in generated recursor types/rules and direct dependencies. If persistent public
group metadata is later added to `Declaration`, its canonical identity requires
an explicit new version/ADR; TL2.13 may not silently alter the v1 domain.

## Exit gates

This ADR may be accepted only when:

1. the exact Lean revision, executable group rule, baseline, official sources/
   streams, case/mutation populations, resources, and stop conditions are
   committed before group admission changes;
2. `add_inductive` delegates to the group implementation and all registered
   single-family declaration identities, recursor types/rules, computations,
   and error payloads remain unchanged;
3. group parameter types, universe parameters, result universes, family order,
   per-family indices, constructor ownership, and name freshness are checked
   before publication;
4. positivity ranges over the complete group, including cross-family negative,
   nested, bad-parameter, and recursive-index occurrences;
5. one implementation covers self-recursive, cross-recursive, mixed self/cross,
   indexed cross-recursive, and higher-order cross-recursive fields;
6. every recursor binds all motives and all minors in official order, while its
   result and rules select the correct owner/target motive and target recursor;
7. mutual groups that may inhabit `Prop` eliminate only into `Prop`, and no
   mutual recursor receives K-like reduction;
8. all generated recursors infer-check before one atomic environment commit;
   every negative or late failure leaves no family, constructor, recursor, or
   `CompletedImport` visible;
9. the frozen official `EvenTree`/`OddTree` stream completes twice with exact
   constructor/recursor comparison, and separately frozen explicit-recursor
   streams compute through cross-family and indexed cross-family calls in both
   pinned Lean and Axeyum;
10. mutations of motive/minor order, target motive/recursor, group membership,
    indices, parameters, universes, constructor ownership, rules, and metadata
    reject at the registered boundary;
11. a fixed-seed generated group grammar runs at least 640 unique public-path
    cases twice with byte-identical summaries, while the 768-case recursive and
    840-case positivity controls remain mandatory;
12. focused kernel/importer tests, rustfmt, clippy, rustdoc, pinned-Lean
    differentials, parity documents, foundational resources, links, staged-file
    audit, and remote-ref equality pass under the registered 4 GiB policy.

## Alternatives

### Repeatedly call `add_inductive`

Rejected. It cannot type-check forward cross-family references, enforce
group-wide positivity, generate shared motives/minors, or provide atomic
rollback.

### Support only the exact non-indexed `EvenTree`/`OddTree` fixture

Rejected. Pinned Lean's group algorithm is already parameterized by per-family
index counts and recursive target family. Baking the first fixture's empty
indices into the trusted representation would create a second recursor rewrite
for indexed mutual groups and violate the foundational direction.

### Trust exporter `all`, count, and owner metadata

Rejected. The independent kernel must reconstruct the ordered group from
checked types and constructors, generate its own recursors, and compare the
export. Metadata can describe the claim but cannot grant admission.

### Combine nested/well-founded source lowering

Rejected. TL2.14 changes the frontend representation before the kernel sees the
group. TL2.13 checks the already lowered core group and must remain independently
reviewable.

### Change declaration-identity v1 to add group metadata

Rejected in this slice. The accepted identity domain is versioned and its
single-family digests are mandatory controls. Any public structural extension
needs its own versioned decision rather than an incidental semantic change.

## Consequences

- The trusted publication unit grows from one family to one ordered group.
- Single-family and mutual recursors share one implementation and one ordering
  contract rather than drifting algorithms.
- Indexed and higher-order mutual recursion remain representable without a
  later redesign, even though the first official product target is the frozen
  two-family tree group.
- The generated/mutation burden grows because group ordering and target-family
  selection become soundness-critical.
- TL2.14 can consume a real mutual core after this decision, but native nested/
  well-founded elaboration, broad `Init`/mathlib admission, and full Lean
  parity remain unclaimed.
