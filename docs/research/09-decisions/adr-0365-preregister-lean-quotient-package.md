# ADR-0365: Preregister Lean's fixed quotient package

Status: proposed

Date: 2026-07-23

Execution plan:
[TL2.10 quotient-package plan](../../plan/lean-quotient-package-tl2.10-plan-2026-07-23.md)

Implementation status:
[offline M1--M3 complete](../../plan/lean-quotient-package-m1-m3-result-2026-07-23.md);
the authorization-gated M4 differential and final acceptance remain open.

## Context

The pinned Lean 4.30 kernel does not admit quotient declarations as four
ordinary constants. `environment::add_quot` first validates the canonical
`Eq`/`Eq.refl` bootstrap, constructs `Quot`, `Quot.mk`, `Quot.lift`, and
`Quot.ind` itself, installs all four together, and marks quotient support
initialized. The kernel also gives `Quot.lift` and `Quot.ind` dedicated
reduction rules that ordinary opaque constants do not have.

The pinned lean4export revision exposes that trusted package as four `quot`
records in the fixed order `type`, `ctor`, `lift`, `ind`. Its exporter first
dumps `Eq`, then emits the complete package even when traversal reaches any one
quotient declaration. At preregistration, Axeyum declined the first such record
with `Unsupported(quotient-package)`; the offline M1--M3 result now admits the
exact retained closure. That closure is small and isolated: 6,301 bytes, 121
records, 25 names, three nonzero levels, 87 expressions, and five declaration
records including `Eq`.

Treating these records as arbitrary well-typed constants would be unsound and
would also lose Lean-compatible definitional equality. Treating any prefix as
an independently admissible declaration would violate both the official
package boundary and Axeyum's completion-only publication contract.

The implementation authority is Lean 4.30 commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`, especially
`environment::add_quot` and `check_eq_type` in `src/kernel/quot.cpp` and
`quot_reduce_rec` in `src/kernel/quot.h`. The wire authority is lean4export
commit `a3e35a584f59b390667db7269cd37fca8575e4bf`, especially the `.quotInfo`
case in `Export.lean`.

## Decision

**Represent Lean's four quotient declarations explicitly, but admit them only
through one atomic kernel package operation that independently derives and
checks the canonical Lean 4.30 declarations after validating canonical
`Eq`/`Eq.refl`. Enable the two exact quotient reduction rules only after that
complete package is installed. Buffer the ordered wire package in the importer
and publish nothing unless the entire stream succeeds.**

The kernel representation adds a closed `QuotKind` with `Type`, `Ctor`,
`Lift`, and `Ind`, plus a `Declaration::Quotient` variant. The ordinary
single-declaration insertion API must reject this variant with a typed
package-required error. Only `Kernel::add_quotient_package` may install it.

The package operation must:

1. return idempotently only when all four existing declarations have exactly
   the canonical kinds, universe-parameter arities, and types;
2. otherwise reject any pre-existing package name;
3. validate that `Eq` is the expected one-universe inductive with exactly the
   canonical type and sole constructor `Eq.refl` of the canonical type;
4. independently synthesize the four expected declarations, comparing
   universe parameters positionally so display names remain non-semantic;
5. require exact names, kinds, order, binder information, de Bruijn structure,
   and universe-parameter arities;
6. type-check every expected declaration under one insertion-log checkpoint;
7. insert all four or roll back all four on every error; and
8. expose no general-purpose API for marking an arbitrary environment as
   quotient-initialized.

The canonical package is:

```text
Quot      : {α : Sort u} -> (α -> α -> Prop) -> Sort u
Quot.mk   : {α : Sort u} -> (r : α -> α -> Prop) -> α -> Quot α r
Quot.lift : {α : Sort u} -> {r : α -> α -> Prop} -> {β : Sort v} ->
            (f : α -> β) ->
            (forall a b, r a b -> Eq (f a) (f b)) -> Quot α r -> β
Quot.ind  : {α : Sort u} -> {r : α -> α -> Prop} ->
            {β : Quot α r -> Prop} ->
            (forall a, β (Quot.mk r a)) -> forall q, β q
```

The notation above is explanatory; the independently synthesized interned
terms are authoritative.

Weak-head reduction matches pinned Lean exactly:

- `Quot.lift` uses argument 3 as the function and argument 5 as the major;
- `Quot.ind` uses argument 3 as the function and argument 4 as the major;
- the major is reduced to WHNF first;
- reduction fires only when that WHNF has constant head `Quot.mk` and exactly
  three arguments;
- the result applies the function to the representative, the last `Quot.mk`
  argument, and reapplies every trailing eliminator argument; and
- underapplication, a stuck major, a wrong head, or a wrong `Quot.mk` arity
  remains inert rather than becoming an error.

The importer may observe name, level, and expression records between quotient
records, because those records construct later declaration payloads. It must
not permit another declaration record to interleave with an incomplete
quotient package. The first `quot` record starts a private ordered buffer. The
fourth invokes the atomic kernel API. A duplicate, wrong kind/order/name,
incomplete EOF, declaration interleave, malformed type, or kernel rejection
returns a stable typed error and no `CompletedImport`.

The declaration-identity schema remains
`axeyum-lean-declaration-identity-v1`. Add `DeclarationKind::Quotient` using a
new domain tag after the seven existing tags and include `QuotKind` in quotient
content identity. Existing declaration identities must remain byte-identical.
The four framework declarations are not axioms and do not enter the axiom
ledger; an ordinary later `Quot.sound` axiom remains explicit and ledgered.

Official Lean already provides the quotient package to reconstructed modules.
The Lean renderer therefore traverses quotient declaration dependencies but
does not redeclare the four built-ins. It must emit a deterministic explanatory
comment or omit the command through an explicit built-in path; it must never
silently render them as axioms.

## Evidence required for acceptance

1. The retained quotient stream's exact hash, record counts, source command,
   pinned revisions, and baseline decline are frozen before implementation.
2. Native positive tests admit exactly four quotient declarations after the
   canonical `Eq` bootstrap and admit no axiom.
3. Native mutation tests reject wrong/missing/reordered `Eq` and `Eq.refl`,
   every package name/kind/order/universe/type mutation, duplicates, and
   partial pre-existing packages transactionally.
4. Native reduction tests cover `lift`, `ind`, trailing arguments, WHNF majors,
   underapplication, wrong head, wrong arity, and stuck majors.
5. A deterministic generated seam population covers package and reduction
   combinations and repeats byte-identically, satisfying TL2.15 for quotient
   semantics rather than adding only hand-written examples.
6. Importer tests complete the exact official stream twice with identical
   reports and declaration identities, then reject every registered malformed,
   incomplete, interleaved, duplicated, relation/proof, and late-failure
   mutation without publication.
7. All pre-existing v1 declaration identities remain byte-identical; quotient
   identities are deterministic and change under kind/type/dependency
   mutation.
8. The renderer accepts a module depending on the built-in package without
   redeclaring it or laundering it into the axiom ledger.
9. Focused kernel/importer tests, clippy, rustdoc, parity-doc generation,
   foundational-resource checks, and documentation links pass under the lane's
   resource limit.
10. A pinned-Lean differential checks the positive reductions and registered
    false controls before acceptance. If executing Lean is not separately
    authorized, that gate remains explicitly open and this ADR remains
    proposed.
11. The construct matrix and all public status surfaces remove only the
    quotient-package decline and preserve every other open K1/full-parity gap.
12. Every milestone is committed and pushed from the isolated Lean worktree;
    containing-commit local/remote equality is recorded before DONE.

## Alternatives

### Import four ordinary axioms or opaque declarations

Rejected. It would inflate the axiom surface, lose quotient computation, and
accept packages Lean's kernel would not initialize.

### Trust the four exported types because official Lean produced them

Rejected. The exporter is an untrusted adapter at this boundary. Axeyum must
derive and compare the trusted package independently.

### Admit each quotient record as it arrives

Rejected. A prefix is not a valid Lean quotient environment and cannot safely
activate reduction. The importer and kernel package transaction must align.

### Encode `Quot` as an ordinary inductive family

Rejected. Lean intentionally treats quotients as primitive framework
declarations with dedicated reduction. An inductive encoding changes both
elimination and definitional equality.

### Change all declaration identities to a v2 schema

Rejected for this additive case. A new tag after the frozen existing tags can
represent quotient declarations while preserving every existing v1 digest.
A broader incompatible identity change still requires a separate ADR.

## Consequences

TL2.10 can close one independent K1 root and unblock dependency-closed `Init`
selection without claiming String, complete construct, source, tactic,
workflow, runtime, library, mathlib, or complete Lean parity. The kernel gains
one more privileged declaration class and reduction path, so transactional
mutation coverage and generated seam testing become permanent regression
gates. The importer becomes a small package state machine rather than a purely
record-at-a-time declaration translator. The explicit built-in rendering rule
also prevents later proof reconstruction from misreporting Lean framework
constants as Axeyum-created assumptions.
