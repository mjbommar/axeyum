# ADR-0400: Closed-form Rado sharpness witness

Status: accepted

Date: 2026-08-13

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.6 / R7.1.

## Context

ADR-0399 proves the witness equation from abstract facts `N=b*q` and `a<=q`.
The paper's witness is closed form: with `n=k-3`, its geometric calculation
factors `u=a*u'`, then takes `q=a+u` and `N=b*q`. The abstract theorem needed
to be connected to those exact expressions rather than left as an assumption.

## Decision

In the dedicated Rado development, define

```text
u' = 1 + 2*sumRange (fun i => a^(i+1)) n + a^(n+1)
u  = a*u'
q  = a+u
N  = b*q.
```

Admit the resulting universal witness equation by applying ADR-0399 with
reflexive factor evidence and `le_add_right a u`. Compose it with ADR-0396,
which identifies `a*u'` with the paper's expanded finite-sum expression,
including the empty `n=0` corner. Keep range and colour claims out of this
theorem.

## Evidence

At `a=2,b=3,n=0` (`k=3`), the development computes
`u=6,q=8,N=24,X=19,Y=1,Z=12` and checks both equation sides at 36. It also
applies the matching ADR-0396 factorization proof. A mutation keeps `q=8` but
changes `N` from 24 to 21, producing `30=36`; the trusted gate rejects the
valid closed-form proof without insertion. The environment contains zero
axioms.

## Consequences

The factorized closed-form witness equation is checked end to end without
division. Bounds for `X`, `Y`, and `Z`, the range equivalence, valuation and
divisibility facts, and all colour computations remain. No `thm:sharp` credit
is claimed.
