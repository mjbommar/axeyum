# Lean post-TL2.13 dependency and trust-boundary audit

Status: complete; roadmap correction required

Date: 2026-07-22

Baseline revision: `340cf7215c9371778fb08a1a2ff81ca68d10400b`

## Question

After TL2.13, should Axeyum immediately implement the roadmap's former
"nested/well-founded frontend lowering" task, and is that one coherent trusted
slice?

## Evidence

The answer is no. The old TL2.14 row combined two mechanisms that official Lean
places on opposite sides of the kernel/elaborator boundary.

### Nested inductives are a kernel admission transformation

Pinned Lean 4.30 commit
`d024af099ca4bf2c86f649261ebf59565dc8c622` implements nested-inductive
elimination in `references/lean4/src/kernel/inductive.cpp`, inside
`environment::add_inductive`:

1. `elim_nested_inductive_fn` scans constructor types for an application of an
   already admitted inductive whose parameter tuple contains a new family.
2. It copies the complete existing container group into fresh auxiliary
   families, substitutes nested occurrences with those auxiliaries, and queues
   copied constructors recursively.
3. It admits the original and auxiliary families as one mutual declaration
   through the ordinary trusted inductive checker.
4. `restore_nested` replaces auxiliary types and constructors with the original
   nested applications in published types and rules.
5. `mk_aux_rec_name_map` publishes auxiliary eliminators as
   `<first-family>.rec_1`, `.rec_2`, and so on.
6. Only the original families/constructors, their recursors, and the restored
   auxiliary recursors enter the final environment; temporary auxiliary family
   declarations do not.

Lean's `InductiveVal.numNested` documents this kernel-produced auxiliary count.
`Lean.Elab.MutualInductive.addAuxRecs` merely registers the variable number of
recursors that the kernel already created. Treating `numNested` as a frontend
authorization bit or lowering the group only in the importer would put trusted
semantics in the wrong layer.

### Well-founded source recursion is elaborator work

Pinned Lean implements source `termination_by`/`decreasing_by` processing in
`Lean.Elab.PreDefinition.WF`. That pipeline packs mutual arguments, creates and
solves decreasing obligations, chooses or checks a well-founded relation,
builds a `WellFounded.fix` term, and emits unfolding equations. These are
metavariable, tactic, typeclass, source-range, and declaration-elaboration
operations, not a new kernel reduction rule.

Axeyum's frozen well-founded root has already crossed the current kernel/import
boundary in its elaborated form. Under the TL2.12 overlay it imports twice as
35 declarations, zero axioms, and completes through the checked `Acc.rec` path.
That is exact pre-elaborated core credit. It does not imply that Axeyum can parse
or elaborate a recursive source definition.

### Current product boundary

| row | frozen evidence | current Axeyum result | interpretation |
|---|---|---|---|
| nested | `faabcde4553b0d597a768aedf35117d7fb4310d3dae052e2545e5b239277456e`, 23,418 bytes / 409 records | repeatable `Malformed` at line 248: `single-family inductive must export one recursor` | diagnostic misclassification before the registered `inductive-nested` policy boundary |
| well-founded | `c1fc14097f9be381625846f13277edfd8294afd93c8e9cadd72c54d71e48e3c6`, 49,140 bytes / 920 records | repeatable completed import, 160 names / 5 levels / 731 expressions / 23 records / 35 declarations / 0 axioms | pre-elaborated core already supported; native source elaboration remains absent |

The nested stream's `Rose` group has one source family, `numNested = 1`, and
two recursors: `Rose.rec_1` owns restored `NestList` rules and `Rose.rec` owns
the `Rose.node` rule. Therefore the importer's generic one-recursor-per-family
preflight is wrong for nested groups even before semantic support is attempted.

## Correction

The roadmap is split along the real trust boundary:

- **TL2.14** becomes trusted nested-inductive kernel elimination and exact
  restored auxiliary-recursor import. It depends on TL2.13, not TL4.12.
- **TL4.10** remains the native source-elaboration task for structural, mutual,
  nested, well-founded, and partial recursion with termination evidence. It
  depends on the native parser/elaborator tasks and may not borrow TL2.14's
  kernel credit.
- The current well-founded stream remains a mandatory positive core control,
  not a TL2.14 implementation target.
- The nested `Malformed` result is repaired first as a TL1.8 diagnostic boundary
  under the TL2.14 plan, without admitting the stream or trusting `numNested`.

This correction makes TL2.14 dependency-ready now while leaving the genuinely
large native frontend program where its parser, metavariable, unification,
tactic, and termination dependencies already live.

## Next action

Proceed under proposed ADR-0355 and the preregistered TL2.14 execution plan.
Freeze an explicit nested-recursion computation source and wire stream before
changing admission. Then implement the pinned kernel transformation, not a
fixture-specific importer rewrite. TL3.1 prelude inventory and TL1.5 importer
property fuzzing remain valid independent lanes, but neither changes the
TL2.14 trust boundary.
