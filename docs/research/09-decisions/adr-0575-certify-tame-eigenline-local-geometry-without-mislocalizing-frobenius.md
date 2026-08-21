# ADR-0575: Certify tame eigenline local geometry without mislocalizing Frobenius

Status: accepted
Date: 2026-08-20
Index-summary: Prove smooth transverse odd-endpoint cycle eigenlines while retaining the distinct Frobenius-cycle correspondence as REL

## Context

The one-sided relative trace `(REL)` is the sole open statement in the
paper-facing Lemire proof.  The surviving geometric proposal was to localize a
Frobenius--long-cycle trace at the projective fixed points of the long cycle and
compute twisted local terms.  ADR-0553 classifies those points but does not
compute their scheme-theoretic local geometry.

Two issues had to be separated.  First, the fixed points might themselves be
singular or nontransverse.  Second, even perfect local geometry for the cycle
does not automatically localize the different correspondence `Frob*c` at
`Fix(c)`.

## Decision

Extend `sawin_projective_eigenline_report` with the exact tame local model.  At
odd endpoint degree `n=2ell+1`, every surviving eigenline has coordinates

```text
a_i=A lambda^i,  0<=i<n,
```

for a primitive `n`th root `lambda`.  Since

```text
product_i (1-u a_i)=1-u^n A^n,
```

the derivative of the equation `e_j=0` with respect to `a_i` is
`a_i^(j-1)` for `1<=j<=ell`.  The Jacobian is therefore the first `ell`
rows of a Vandermonde matrix and has rank `ell`.  The affine tangent space has
dimension `n-ell`; after removing its radial mode, the projective tangent
weights relative to the fixed eigenline are exactly

```text
lambda, lambda^2, ..., lambda^(n-ell-1).
```

The complementary normal weights are
`lambda^(n-ell),...,lambda^(n-1)`.  No tangent weight is one, so every
surviving odd-degree eigenline is smooth, isolated, and transverse for the
long-cycle correspondence.

Do not convert this into a Frobenius bound.  Grothendieck--Lefschetz applied to
`Frob*c` localizes on `Fix(Frob*c)`, not on `Fix(c)`; the former is the original
short-interval point-count problem.  A formula supported on `Fix(c)` would
need additional Frobenius-dependent local terms and a new estimate for their
sum.  The report therefore retains
`frobenius_weighted_trace_bound_certified=false`.  At even degree the cycle is
wild, and no smoothness, reducedness, or transversality claim is made.

## Evidence

- The native report checks that the tangent and normal weights partition every
  nontrivial `n`th-root character exactly once.
- A separate test constructs primitive roots of orders `5`, `7`, and `9` in
  explicit binary extension fields, builds the literal Jacobian, and performs
  independent finite-field Gaussian elimination.  Its ranks are `ell`.
- Pinned degree `401` has projective tangent weights `1..200` and normal
  weights `201..400`; even pinned degrees retain empty optional local data.
- The actual relative Lefschetz--Verdier source is Lu--Zheng,
  *Categorical traces and a relative Lefschetz--Verdier formula*, Theorem 2.21,
  <https://arxiv.org/abs/2005.08522>.  It proves functoriality of relative trace
  classes; it does not state the required numerical `Frob*c` estimate, and
  Remark 2.24 explicitly excludes a separate twisted formula.  The previously
  suggested arXiv identifier `2309.02587` is Barrett's *The singular support of
  an ell-adic sheaf*, not a relative Lefschetz--Verdier paper.

## Consequences

- At the odd endpoint, singularity of the surviving cycle eigenlines is no
  longer the missing local input.  Any proposed twisted-Milnor obstruction
  must identify a different singular support or wild sheaf contribution.
- Ordinary tame fixed-point localization remains useful for the unweighted
  cycle trace but gives no `(REL)` credit.
- The next geometric theorem must control the complete `Frob*c`
  correspondence, or rigorously construct and bound Frobenius-dependent local
  terms on `Fix(c)`.  Merely counting or smoothing those points is finished.
- The even endpoint retains its separate wild/nonreduced local problem.
