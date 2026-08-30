# Carrier replay overclaim — correcting the whole-carrier Lean replay claim

<!-- plan-section: lane-status -->

Lane: `carrier-replay-overclaim`. Decision:
[ADR-0775](../../research/09-decisions/adr-0775-the-non-prop-residue-is-a-recorded-boundary-not-a-silent-exclusion.md).
Follows L0/S4's census ([386](386-l0-s4-independent-replay.md), ADR-0760),
which found this.

## Status

Landed. `F:lean-kernel-accepts-the-whole-constructed-real-carrier` claimed
pinned Lean's kernel accepts EVERY declaration of the constructed-real carrier.
It does not. The statement is narrowed to what is measured, the superseded one
is preserved three ways including as a test that fails if it ever becomes true
again, and the 73 declarations it no longer covers are a typed, named, counted
boundary plus their own OPEN ledger row.

## The measurement

One run, pinned Lean 4.30.0 (`d024af09`), whole `creal` carrier, all four tests
green in 146 s:

    AXEYUM-CREAL-CARRIER counts_agree population=2058 representable=1985
      lean_kernel_constants=1985 non_representable=73
    AXEYUM-CREAL-CARRIER superseded-claim-refuted
      rejected_by_lean=CReal.weierstrassMTest reason=theorem-type-not-prop
      theorem_type_not_prop=48
    AXEYUM-CREAL-CARRIER tampered-proof-rejected subject=CReal.Equiv.not_zero_one
    AXEYUM-CREAL-CARRIER residue-typed population=2058 representable=1985
      theorem_type_not_prop=48 blocked_by_dependency=25 untyped=0

S4 measured the same residue (48 + 25) at population 2,045 / representable
1,972; the carrier grew between the runs, the residue did not.

**Nothing was proved wrong.** `Lean.Environment.addDeclCore` refuses a
`theorem` whose type is not a `Prop`; this kernel has no such rule and uses the
freedom deliberately (`CReal.UniformConvergesOn` is `Type`-valued so a
convergence rate is data). Lean refused a KIND, never a proof. What it was is
73 declarations of the flagship carrier holding no independent-replay grade
with nothing in the ledger saying so.

## What changed, and how the old statement survives

Detail moved to [`../notes/389-carrier-replay-overclaim.md`](../notes/389-carrier-replay-overclaim.md).

