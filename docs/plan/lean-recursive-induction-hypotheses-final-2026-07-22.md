# Lean recursive induction hypotheses: M5 final result and handoff

Status: complete; ADR-0353 accepted; TL2.12 DONE

Date: 2026-07-22

Decision: [accepted ADR-0353](../research/09-decisions/adr-0353-preregister-lean-recursive-induction-hypotheses.md)

Prior checkpoints:

- [M0 source/wire freeze](lean-recursive-induction-hypotheses-m0-2026-07-22.md);
- [M1 shared representation](lean-recursive-induction-hypotheses-m1-2026-07-22.md);
- [M2 native semantics](lean-recursive-induction-hypotheses-m2-2026-07-22.md);
- [M3 importer and official constructs](lean-recursive-induction-hypotheses-m3-2026-07-22.md);
- [M4 computation and assurance](lean-recursive-induction-hypotheses-m4-2026-07-22.md).

## Final result

Axeyum now independently admits and computes the currently representable
single-family direct, recursive-indexed, higher-order/reflexive, and combined
indexed+higher-order inductive profiles through one Lean-compatible rule. For
a checked recursive field

```text
u : Pi xs, I params indices
```

the constructor minor receives

```text
u_ih : Pi xs, motive indices (u xs)
```

and the iota rule supplies the matching recursively computed function. Direct
recursion is the empty-telescope, empty-index case of the same implementation.
One WHNF classifier/reopener is shared by minor-type and rule-right-hand-side
construction; checked metadata stores only stable field position and telescope
depth. TL2.11 strict positivity remains an independent pre-insertion guard.

The importer now treats official `isReflexive` as descriptive metadata rather
than admission authority. Both frozen `MiniVector` and `MiniAcc` construct
streams complete twice, and Axeyum's independently generated constructor and
recursor declarations compare definitionally with the official exports. The
pre-elaborated well-founded stream also completes through `Acc.rec`; this is
kernel/import credit for the lowered form, not native frontend support.

## Accepted evidence

All ADR-0353 exit gates are met:

1. M0 froze the exact Lean 4.30 rule, sources, wire streams, cases, mutations,
   resources, and stop conditions before semantic widening.
2. One implementation covers empty and nonempty field telescopes and index
   vectors; no indexed/reflexive semantic fork was introduced.
3. Fourteen native named rows cover ten positive and four transactional
   negative families. Ten native mutation classes reject type, index,
   telescope, ordering, rule, and field-contract corruption.
4. A fixed 768-case public-path recursive grammar repeats byte-identically at
   digest `0d245921566be735`; it spans zero through three recursive fields,
   `Prop`/`Type`, four shape profiles, two depths, and no/constant/field-
   dependent index production.
5. The retained 840-case TL2.11 population preserves its descriptor digest
   `02985687422aa0ff` and historical partition while recording the intended
   TL2.12 admission widening separately.
6. Exact `MiniNat.rec` and `MiniList.rec` declaration identities and their
   computations remain unchanged.
7. Both official construct targets complete twice with exact generated/exported
   recursor comparison. Mutual and nested retain typed declines; metadata
   flips and late recursor/count/rule/field mutations publish no partial import.
8. Pinned Lean compiles the explicit computation source twice to OLEAN digest
   `8b5136f7e66b18c9ad00b7f67b732ebb0fd9ff437128a80bdce831f011c7f573`.
   Axeyum imports both frozen computation streams twice and normalizes the
   registered theorem sides to `MiniNat.succ MiniNat.zero` and `True`.
9. The machine-derived construct matrix now reports four admitted rows, two
   separately computation-checked rows, and two typed declines. It preserves
   the historical ADR-0351 product observation and validates the current
   TL2.12 overlay separately.
10. Every final bounded code, contract, generated-document, foundational-
    resource, and link gate passes.

## Final bounded gates

The final pass used one Rust build job under the 4 GiB wrapper. Required Lean
runs used one worker under `MemoryHigh=3G`, `MemoryMax=4G`, and
`MemorySwapMax=512M`; repository-local temporary output avoided the constrained
system `/tmp` path.

| gate | result |
|---|---|
| kernel tests | 182 unit + 42 integration + 1 doctest passed |
| importer tests | 34 integration + 1 compile-fail doctest passed |
| recursive grammar | 768 unique cases, byte-identical repeat |
| retained positivity grammar | 840 cases with historical and current partitions checked |
| official construct imports | Vector, Acc, and pre-elaborated well-founded complete; mutual/nested typed declines retained |
| computation differential | two Lean source runs and two Axeyum runs per stream agree at the registered normal forms |
| focused clippy | all kernel/importer targets and features, warnings denied, passed |
| focused rustdoc | kernel/importer all features, warnings denied, passed |
| focused rustfmt | every milestone-owned Rust file passed |
| parity/document contracts | 56 tests plus every registered generator/checker passed; `DISAGREE=0` |
| foundational resources | 137 concept rows and 174 packs validated |
| documentation links | passed |
| `git diff --check` | passed |

The compatibility contract was synchronized with the semantic widening: the
obsolete `inductive-reflexive` decline was removed. The strict-positivity M3
record now freezes its historical construct-matrix hash separately from the
current TL2.12 registration, so later accepted widening cannot rewrite the
earlier observation.

## Scope and non-claims

TL2.12 establishes a bounded single-family kernel/import profile. It does not
claim:

- mutual-inductive admission, multiple motives, or group-wide positivity;
- native frontend lowering for nested or well-founded definitions;
- every inductive universe/elimination combination;
- native Lean parser, macro, elaborator, tactic, compiler, Lake, LSP, or
  `.olean` compatibility;
- broad `Init`, `Std`, or mathlib admission;
- full Lean-kernel parity, consistency, or replacement of official Lean.

## Handoff

The primary semantic path is TL2.13: preregister mutual inductive groups as one
atomic widening of the positivity occurrence set, motives, minor premises,
recursors, and computation rules. Preserve every TL2.11/TL2.12 direct,
negative, generated, official-differential, and completion-only-publication
control. Do not fold TL2.14 nested/well-founded source lowering into that
kernel change; it remains a subsequent frontend phase.
