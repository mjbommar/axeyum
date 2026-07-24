# Lean TL2.10 quotient-package offline result

Status: **M1--M3 complete; M4 differential and final acceptance remain open**

Date: 2026-07-23

Decision:
[proposed ADR-0365](../research/09-decisions/adr-0365-preregister-lean-quotient-package.md)

Execution plan:
[TL2.10 quotient-package plan](lean-quotient-package-tl2.10-plan-2026-07-23.md)

## 1. Bounded result

Axeyum now independently constructs and atomically admits Lean 4.30's fixed
four-member quotient package, performs the registered `Quot.lift` and
`Quot.ind` reductions, and imports the retained official lean4export closure
without treating exporter types as kernel authority.

This is an offline M1--M3 result. No fresh Lean, lean4export, SMT solver, or
official differential process ran in this lane. The separately authorized M4
pinned-Lean positive/false-control differential therefore remains open;
ADR-0365 remains proposed and TL2.10 remains WIP. This result is not complete
K1, `Init`/`Std`, source, tactic, workflow, runtime, mathlib, or complete Lean
parity credit.

## 2. Published checkpoints

| Milestone | Commit | Result |
|---|---|---|
| P0 | `d7b841c5` | Frozen pinned Lean/lean4export authority, exact fixture identity, semantics, mutations, and stop conditions. |
| M1 | `c28acd75` | Added the closed quotient declaration class, typed failures, canonical `Eq`/`Eq.refl` validation, independently synthesized types, transactional four-member admission, additive identity tag, and built-in renderer path. |
| M2 | `8e383efb` | Added exact WHNF-major `lift`/`ind` reduction, inert boundaries, trailing-argument replay, and the generated quotient seam population. |
| M3 | `0f82291e` | Added ordered private wire buffering, completion-only publication, exact official import/computation, frozen identities, axiom-ledger separation, and malformed/late-failure coverage. |
| evidence closure | `5594cb43` | Froze the 576-row transcript digest, explicit renderer non-laundering, and structural identity sensitivity to kind, type, and dependency changes. |

Each checkpoint was pushed to
`origin/agent/lean/quotient-package-tl2-10` before the next milestone.

## 3. Kernel boundary

`Declaration::Quotient` is not accepted by ordinary
`Kernel::add_declaration`. `Kernel::add_quotient_package` is the sole public
admission route. It:

1. validates the canonical one-universe `Eq` and `Eq.refl` bootstrap;
2. synthesizes the expected `Quot`, `Quot.mk`, `Quot.lift`, and `Quot.ind`
   types independently of the wire payload;
3. checks exact names, order, kinds, universe arities, binder information,
   de Bruijn structure, and types;
4. admits all four under one rollback checkpoint; and
5. treats only an already complete canonical package as idempotent.

Wrong or missing `Eq`, direct insertion, package length/name/kind/universe/type
mutations, partial reserved-name populations, and injected transactional
failure all return typed errors without retaining a package suffix.

Reduction matches the pinned source contract: `lift` uses function position 3
and major position 5; `ind` uses function position 3 and major position 4. The
major is reduced to WHNF, must have the canonical `Quot.mk` head with exactly
three arguments, and supplies its final representative argument. Trailing
eliminator arguments are reapplied. Underapplication, wrong heads, wrong
constructor arities, stuck majors, and same-named ordinary constants remain
inert.

## 4. Generated seam and renderer evidence

The quotient grammar contains exactly 576 unique descriptors:

```text
2 eliminators x 4 major shapes x 3 eliminator arities x
4 trailing axes x 2 function shapes x 3 wrapper depths
```

Two complete runs produce the identical transcript. Its frozen FNV-1a-64
digest is `649c98095f6e8d45`; every descriptor is classified as either an exact
fire or inert outcome, and both partitions are nonempty.

Every installed quotient declaration renders only as a deterministic comment
that Lean supplies the built-in package. Focused tests reject both `axiom` and
`opaque` laundering in that path.

## 5. Import, publication, and identity evidence

The retained 6,301-byte, 121-record fixture imports as 25 names, three nonzero
levels, 87 expressions, five declaration records, and seven admitted
declarations. The four quotient members are `DeclarationKind::Quotient`; the
axiom ledger is empty; and an imported `Quot.lift` application computes to its
representative.

The importer permits name/level/expression records needed to build later
package payloads, but no other declaration may interleave after the first
`quot` record. Incomplete EOF, wrong order, unknown kind, extra wire fields,
wrong names or universe arities, mutated relation/proof types, duplicate
packages, late JSON failure, and declaration interleaving return no
`CompletedImport`. A later ordinary `Quot.sound` axiom remains an ordinary
ledgered axiom.

The additive v1 quotient tag leaves every previously frozen declaration
digest byte-identical. The seven exact closure identities are frozen and
repeat identically; direct dependencies distinguish `Quot.mk -> Quot`,
`Quot.ind -> Quot, Quot.mk`, and `Quot.lift -> Eq, Quot`. A separate structural
test proves quotient content identity changes with kind, type, or dependency.

## 6. Assurance update and exact residual

The bounded compatibility authority can now mark the exact official quotient
row parsed, translated, and independently admitted, removing only the obsolete
`quotient-package` decline. This raises the five selected K1 fixture rows from
4/5 to 5/5. It does not define or complete the full K1 population: String
literal semantics and the dependency-closed declaration/core-term authority
remain open, as do every terminal U0--U9, A0--A11, and G1--G10 requirement.

M4 remains exactly:

1. obtain separate authorization for the preregistered pinned-Lean positive
   and false-control differential;
2. retain its command, resource, process, and output identities;
3. repeat all final aggregate gates;
4. accept ADR-0365 and mark TL2.10 DONE only if every exit passes; and
5. record the containing commit and local/tracking/remote equality.

## 7. Offline validation

The complete bounded crate suites pass:

- `cargo test -p axeyum-lean-kernel`: 199 unit tests, every integration binary,
  the 65.81-second nested grammar, and the doctest pass;
- `cargo test -p axeyum-lean-import`: one library identity test, 52 integration
  tests across seven binaries, and the compile-fail doctest pass;
- warning-denied clippy and strict rustdoc pass for both crates;
- compatibility and complete-parity generation/checks pass;
- the parity-document validator reports 992 SMT-LIB files, 753 decisions, 680
  comparisons, and zero recorded disagreements;
- all 137 foundational concepts and 174 example packs validate; and
- repository links and `git diff --check` pass.

The final workspace-wide `just check` is not green: its first `cargo fmt
--all --check` step reports pre-existing committed formatting drift in CAS and
benchmark files outside this lane. Those paths are clean in this worktree and
identical at current `origin/main` (`50d55a7e`), so this lane does not rewrite
them. The focused Lean formatting, test, clippy, rustdoc, generated-authority,
foundational-resource, and link gates above remain green; the full-repository
exit stays explicitly open.
