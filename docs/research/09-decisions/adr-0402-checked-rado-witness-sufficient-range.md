# ADR-0402: Checked sufficient upper range for the Rado witness

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R7.1.

## Context

ADR-0401 leaves `Z <= N` open because the paper states the exact signed
criterion `Z <= N` iff `N(a-b) <= a^2*b`. The sharpness application itself
uses only the sufficient branch `b>a`. That branch has a direct Nat proof
which should be checked before introducing signed arithmetic for the stronger
biconditional.

## Decision

For the ADR-0400 construction `q=a+u`, `N=b*q`, and `Z=a*(q-a)`, prove

```text
a <= b -> Z <= N.
```

Recover `q-a=u` with conditional subtraction restoration and additive
cancellation. Then use checked order monotonicity to derive
`u<=q`, `a*u<=a*q`, and `a*q<=b*q=N`. Keep the paper's exact signed
biconditional outside this theorem.

## Evidence

The theorem is instantiated at `a=2,b=3,n=0`, where the kernel reduces the
closed form to `Z=12` and `N=24`. A mutation assigns the valid proof to the
false target `12<=11`; the trusted gate rejects it without insertion. The
development remains zero-axiom.

## Consequences

All three witness values have checked membership in `[N]` for the `b>a`
sharpness branch. The exact signed biconditional and the three colour
computations remain before `thm:sharp` can receive theorem credit.
