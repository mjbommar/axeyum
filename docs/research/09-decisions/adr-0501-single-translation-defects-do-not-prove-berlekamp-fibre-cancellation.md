# ADR-0501: Single-translation defects do not prove Berlekamp fibre cancellation

Status: accepted
Date: 2026-08-19
Index-summary: Measure exact sign-reversing defects in every simultaneous coset and reject a one-translation proof of the local square-root bound

## Context

ADR-0500 turns every inverse-shift support condition into an explicit affine
Artin--Schreier equation.  The remaining local target is the signed estimate

```text
b_(C,D)^2 <= 2d #_(C,D).
```

One possible elementary proof would pair the low-coefficient cube by a
translation that reverses the Möbius signs, up to a small boundary.

## Decision

Measure that mechanism exactly before attempting to generalize it.  For the
weight `w_(C,D)(m)` in `{-1,0,1}` and every nonzero translation `t`, use

```text
abs(sum_m w_(C,D)(m))
  <= D_t(C,D)
  = (1/2) sum_m abs(w_(C,D)(m)+w_(C,D)(m+t)).
```

The bounded operation `binary_berlekamp_involution_defect_report` computes the
minimum defect over all nonzero translations in each occupied bucket, checks
the displayed triangle inequality, and reports exact sign-reversing and exact
triangle cases.

Reject the proposed sufficient lemma

```text
min_(t!=0) D_t(C,D)^2 <= 2d #_(C,D).
```

At `(ell,k,d)=(9,11,8)`, the worst defect witness has population `88`, signed
magnitude `6`, and minimum defect `54`, so `54^2>16*88`.  None of the eight
occupied buckets has an exact sign-reversing translation.  The original local
signed target nevertheless survives this row.

## Evidence

The pinned test independently reconstructs all bucket weights from Axeyum's
binary factorization and inverse-coset maps.  It checks the finite witness and
also pins a positive control at `(ell,k,d)=(8,12,5)`, where 62 of 471 buckets
have exact sign-reversing translations and the defect candidate holds.

Finite enumeration is not evidence for or against the universal signed target.
It is decisive against the displayed one-translation implication because one
explicit finite bucket violates it.

## Consequences

- Do not replace a bucket's signed magnitude by its best single-translation
  defect in the endpoint ledger.
- A future pairing argument must combine translations or prove cancellation
  within the defect terms.
- The local Berlekamp square-root fact remains conjectured, and the
  complementary cross-order block remains open.
