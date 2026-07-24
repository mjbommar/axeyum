# Lean TL2.10 quotient-package execution plan

Status: **M1--M3 complete offline; M4 differential and acceptance open**

Date: 2026-07-23

Owner: Lean complete-parity lane

Decision:
[ADR-0365](../research/09-decisions/adr-0365-preregister-lean-quotient-package.md)

Offline result:
[M1--M3 result](lean-quotient-package-m1-m3-result-2026-07-23.md)

Parent contracts:
[Lean system implementation plan](lean-system-implementation-plan-2026-07-21.md),
[complete-parity contract](lean4-complete-parity-contract-2026-07-22.md), and
[execution roadmap](lean4-complete-parity-roadmap-2026-07-22.md)

## 1. Objective and bounded claim

Implement Lean 4.30's fixed quotient package in the independent Rust kernel,
reproduce the exact `Quot.lift`/`Quot.ind` reductions, import the retained
official lean4export closure without trusting its declaration payloads, and
close the quotient portion of TL2.15 seam testing.

The strongest result this plan can establish is:

> Axeyum independently admits and computes the pinned Lean 4.30 quotient
> package for the registered native and official-export populations, with
> deterministic identities and fail-closed mutation/publication evidence.

It does not establish String closure, complete K1, `.olean` compatibility,
native source parsing/elaboration, tactics, projects, runtime/compiler,
`Init`/`Std`/mathlib, or complete Lean parity.

## 2. Why quotient precedes String

Both roots are current K1 blockers and both depend on TL1.7. The quotient root
is an independent kernel primitive with a fixed four-declaration package and
dedicated reduction semantics. Its retained closure is 6,301 bytes and 121
records. The String root spans 570,807 bytes, 10,339 records, and 290
declarations and also reaches literal, Nat, recursive-indexed, and wider
dependency surfaces. Closing quotient first follows semantic dependency order:
it removes a compact kernel primitive needed by later `Init` selection without
pretending that the broader String dependency graph is solved.

## 3. Frozen authority and baseline

### 3.1 Official implementation

| Authority | Exact identity | Required behavior |
|---|---|---|
| Lean | `leanprover/lean4@d024af099ca4bf2c86f649261ebf59565dc8c622` (`v4.30.0`) | `src/kernel/quot.cpp`: canonical Eq bootstrap and atomic four-declaration construction |
| Lean | same revision | `src/kernel/quot.h`: exact `lift`/`ind` major positions, `Quot.mk` shape, representative selection, and trailing-argument replay |
| lean4export | `leanprover/lean4export@a3e35a584f59b390667db7269cd37fca8575e4bf` | `Export.lean`: dump `Eq`, then the complete ordered `Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` package with kinds `type`, `ctor`, `lift`, `ind` |

Primary links:

- <https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/quot.cpp>
- <https://github.com/leanprover/lean4/blob/d024af099ca4bf2c86f649261ebf59565dc8c622/src/kernel/quot.h>
- <https://github.com/leanprover/lean4export/blob/a3e35a584f59b390667db7269cd37fca8575e4bf/Export.lean>
- <https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/>

### 3.2 Retained wire authority

Fixture:
`docs/plan/fixtures/lean4export-v4.30-quotient.ndjson`

| Property | Frozen value |
|---|---|
| SHA-256 | `060bb9d132fa6b7917170cd549ded5fb5703935c74ca1f7f32a3b77b6d9903c8` |
| Bytes / records | 6,301 / 121 |
| Names / nonzero levels / expressions | 25 / 3 / 87 |
| Declaration records | five: canonical `Eq` group plus four quotient records |
| Quotient record lines | 65 `type`, 73 `ctor`, 100 `lift`, 121 `ind` |

The fixture is already bound to the source, command, and pinned tools by the
[official blocker census](lean4export-official-blocker-census-2026-07-21.md).
P0 neither regenerates it nor executes Lean.

### 3.3 Current product baseline

The importer translates all preceding records and returns
`Unsupported { code: "quotient-package" }` at line 65. No environment is
published. `Declaration` and declaration identity expose only axiom,
definition, theorem, opaque, inductive, constructor, and recursor variants.
The type checker has no quotient reduction path. This exact decline remains the
required P0 control and receives no product or parity credit.

## 4. Trusted semantic contract

### 4.1 Canonical Eq prerequisite

Package admission requires:

- `Eq` is an inductive declaration with one universe parameter;
- its type is definitionally the exact implicit `α : Sort u` followed by
  `α -> α -> Prop`;
- its constructor list contains exactly one declaration, `Eq.refl`;
- `Eq.refl` has one universe parameter and exact type
  `{α : Sort u} -> (a : α) -> Eq α a a`; and
- no name, binder-info, universe-arity, constructor-owner, or declaration-kind
  mismatch is normalized away.

Universe parameter *names* are alpha-renamable. Comparison substitutes each
candidate parameter position into an independently synthesized expected type;
it does not compare display strings.

### 4.2 Canonical package

The kernel constructs expected declarations in the order:

1. `Quot`, kind `Type`, one universe parameter;
2. `Quot.mk`, kind `Ctor`, one universe parameter;
3. `Quot.lift`, kind `Lift`, two universe parameters; and
4. `Quot.ind`, kind `Ind`, one universe parameter.

The exact interned types are independently synthesized from the canonical Eq
reference. Exporter terms are compared against those types but cannot define
them. Ordinary `add_declaration` rejects `Declaration::Quotient`; the package
API owns one checkpoint and rolls back on every failure.

### 4.3 Reduction

For an application with head `Quot.lift`, require at least six arguments, WHNF
argument 5, and reduce only when it is exactly `Quot.mk` with three arguments.
Return argument 3 applied to the representative, the last `Quot.mk` argument,
then reapply any arguments after position 5.

For `Quot.ind`, use the same rule with major position 4 and at least five
arguments. Underapplication and a major with wrong/stuck head or wrong arity
remain inert. Reduction must not activate merely because a constant with the
right name exists; the complete checked package must be present.

### 4.4 Import and publication

The importer holds at most one private quotient package:

```text
none -> type -> ctor -> lift -> ind -> atomically admitted
```

Name/level/expression records may occur while the buffer is open. Another
declaration record, duplicate/repeated kind, wrong name/order, malformed
payload, kernel failure, or EOF before `ind` rejects. The private kernel remains
unpublished until the ordinary full-stream completion boundary. A valid
package followed by late bad JSON, limit exhaustion, unsupported input, or I/O
failure also publishes nothing.

### 4.5 Identity, axioms, and rendering

- Preserve `axeyum-lean-declaration-identity-v1` and tags 0 through 6 exactly.
- Add `DeclarationKind::Quotient` at tag 7.
- Domain-separate and hash `QuotKind` in quotient content identity.
- Keep all four package declarations out of `axiom_identities`.
- Keep a later ordinary `Quot.sound` declaration visible as an axiom.
- Traverse dependencies through quotient types.
- Do not redeclare the four built-ins in generated official-Lean modules and do
  not emit them as assumptions.

## 5. Registered mutations

Each class needs at least one direct negative, stable typed classification, and
an assertion that environment state/identity is unchanged after failure.

| ID | Boundary | Mutation |
|---|---|---|
| Q01 | Eq | missing `Eq` |
| Q02 | Eq | wrong declaration kind or universe arity |
| Q03 | Eq | wrong binder info, domain, codomain, or constructor population |
| Q04 | Eq.refl | missing/wrong name, owner, universe arity, or type |
| Q05 | package | direct single `Declaration::Quotient` insertion |
| Q06 | package | wrong first name or kind |
| Q07 | package | wrong later name, kind, or order |
| Q08 | package | wrong universe-parameter arity |
| Q09 | package | relation-domain/codomain type mutation |
| Q10 | package | `lift` function/result/soundness-proof mutation |
| Q11 | package | `ind` motive/minor/result mutation |
| Q12 | package | duplicate or partial pre-existing package name |
| Q13 | transaction | failure after each insertion point |
| Q14 | reduction | underapplied `lift`/`ind` |
| Q15 | reduction | major WHNFs to wrong head |
| Q16 | reduction | `Quot.mk` wrong arity |
| Q17 | reduction | stuck major |
| Q18 | reduction | same-named constants without installed package |
| Q19 | wire | first kind is not `type` |
| Q20 | wire | duplicate, skipped, or reordered kind |
| Q21 | wire | declaration record interleaves package |
| Q22 | wire | EOF after `type`, `ctor`, or `lift` |
| Q23 | wire | late JSON/kernel/unsupported/limit/I/O failure after package |
| Q24 | identity | old seven-kind identity drift |
| Q25 | identity | quotient kind/type/dependency mutation lacks sensitivity |
| Q26 | renderer | built-in redeclared or counted as an axiom |

The generated grammar crosses package completeness, kind/order, Eq shape,
eliminator, major form, arity, trailing-argument count, and expected inert/fire
outcome. It must contain at least 512 unique descriptors, repeat twice to one
summary digest, and exercise public kernel paths rather than a duplicate model.

## 6. Milestones and stop conditions

### P0 — authority and design preregistration

Deliver this plan, proposed ADR-0365, live-plan/status links, and the frozen
baseline. Run documentation and parity-document gates. Commit and push before
semantic code.

Stop if the fixture hash/counts drift, ADR number is occupied, ownership
conflicts, or primary-source behavior differs from this contract.

### M1 — native representation and atomic admission

Add the closed quotient representation, typed errors, canonical Eq validator,
independently synthesized package, checkpoint/rollback, exact positive and
mutation tests, exhaustive match updates, and old-identity preservation tests.
Do not widen the importer in M1.

Stop if any direct single declaration is admitted, a failure leaves a package
name behind, the package types are copied from the wire, or old identities
change.

### M2 — native reduction and generated seam closure

Implement exact `lift`/`ind` reduction and stuck/inert behavior. Add direct
tests plus the repeated generated population and deterministic summary. Keep
the importer decline unchanged.

Stop if reduction fires without the complete package, accepts a non-three-arg
`Quot.mk`, drops trailing arguments, or any generated descriptor disagrees
with the independent expected classifier.

### M3 — importer, identity, and renderer integration

Implement ordered private buffering and atomic translation. Import the exact
fixture twice, preserve completion-only publication, add quotient identities,
and close the built-in renderer boundary. Run all Q19-Q26 mutations. Retire
`quotient-package` only for the exact supported package; retain stable declines
for every unsupported construct.

Stop if a prefix publishes, a declaration interleave passes, an exporter field
becomes kernel authority, quotient declarations enter the axiom ledger, or an
old v1 digest changes.

### M4 — differential, matrix, and closure

With separate execution authorization, run the pinned-Lean positive and false
controls under the registered resource envelope. Regenerate the construct
matrix and parity documents from evidence, update TL2.10/TL2.15 and public
status, accept ADR-0365 only when all exits pass, and record containing-commit
push/ref equality.

Without execution authorization, complete every offline gate but leave M4,
ADR-0365, and TL2.10 open. Do not infer official agreement from source reading
or the retained fixture.

## 7. Commands and resources

No milestone may run an unbounded or shared solver campaign. Use the isolated
worktree target and the standard 4 GiB lane. Formatting is file-scoped:

```sh
rustfmt --edition 2024 <owned Rust files>
cargo test -p axeyum-lean-kernel
cargo test -p axeyum-lean-import
cargo clippy -p axeyum-lean-kernel -p axeyum-lean-import --all-targets --all-features -- -D warnings
RUSTDOCFLAGS="-D warnings" cargo doc -p axeyum-lean-kernel -p axeyum-lean-import --all-features --no-deps
python3 scripts/check-parity-docs.py
just foundational-resources
./scripts/check-links.sh
git diff --check
```

Before merge request, run `just check` in this isolated worktree. Any fresh Lean
execution, exporter invocation, or official differential requires explicit
authorization under the repository execution-evidence policy.

## 8. Commit and publication discipline

Use pathspec-only commits with the required co-author trailer. Expected
checkpoints are P0 documentation, M1 kernel admission, M2 reduction/seams, M3
import/identity/renderer, and M4 result/status. Push after every green
checkpoint, verify `git show --stat`, and compare local and remote commit IDs.
The Lean topic branch never merges itself to `main`; the integration owner
performs the green-before-merge gate.

## 9. Exit checklist

- [x] P0 authority/design committed and pushed.
- [x] Canonical Eq prerequisite independently validated.
- [x] Exactly four quotient declarations admitted atomically.
- [x] Direct/single/partial/mutated packages reject transactionally.
- [x] Exact `lift` and `ind` reductions plus inert boundaries pass.
- [x] Generated quotient seam population repeats byte-identically.
- [x] Exact official fixture imports twice with zero axioms.
- [x] All wire and late-failure mutations publish nothing.
- [x] Old declaration identities remain byte-identical.
- [x] Quotient identities are deterministic and mutation-sensitive.
- [x] Renderer uses official built-ins without redeclaration/axiom laundering.
- [ ] Authorized pinned-Lean differential passes.
- [x] Construct/parity authorities and live status regenerate cleanly.
- [ ] Focused and full repository gates pass.
- [ ] ADR-0365 accepted and TL2.10/TL2.15 status updated honestly.
- [ ] Containing commit is pushed and local/remote equality is recorded.
