# ADR-0578: Localize REL to one identity-cylinder variance

Status: accepted
Date: 2026-08-20
Index-summary: Reduce REL to a localized identity-cylinder Haar energy without claiming the open variance theorem

## Context

ADR-0572 leaves one paper-facing obligation. For
`a=ell-ceil(log2 ell)-1`, it asks for the lower bound

```text
C = 2^ell N_ell(1)-2^(a-1)N_(a-1)(1) > -B_(ell,n).       (REL)
```

Separate conductor bounds lose the cancellation in `C`. The global second
moment also loses the location of the identity class. The failed `(SUP-L)`
and positivity routes show that another pointwise reformulation is unlikely
to preserve the needed information.

## Decision

Retain `(REL)` as the minimal paper statement, but register the following
strictly sufficient positive-square bridge. Put `c_0=a-1`,
`K=ker(E_ell -> E_(c_0))`, `R=#K`, `x_e=N_ell(e)` for `e in K`, and
`S=sum_e x_e`. Then

```text
C = 2^ell(x_1-S/R),
V_id = sum_(e in K)(x_e-S/R)^2.
```

The sharp zero-sum point inequality is

```text
(x_1-S/R)^2 <= (R-1)V_id/R.
```

Consequently the exact sufficient comparison is

```text
2^(2ell)(R-1)V_id/R < B_(ell,n)^2.                       (ICV-exact)
```

For every `ell>=200`, the cleaner premise

```text
V_id <= 2^(2ell-2)                                      (ICV)
```

implies `(REL)`. The implication is deterministic; `(ICV)` remains open.

Decompose the cylinder by its binary quotient filtration. If `H_j(p)` is
the difference of the two child populations of a parent `p` at level `j`,
restricted to parents above the coarse identity, then the exact localized
Haar identity is

```text
R V_id = sum_(j=c_0+1)^ell 2^(j-c_0-1)
           sum_(p above 1 in E_(c_0)) H_j(p)^2.          (ICV-H)
```

This is the selected analytic form of the bridge: a local Carleson-energy
estimate on one ramified identity subtree. It combines coarse-character
twists before squaring and is not replaceable by a global variance theorem.

## Evidence

- `identity_cylinder_conditional_variance` reconstructs `C`, `V_id`, the
  sharp threshold, and every level of `(ICV-H)` from exact class populations.
- `identity_cylinder_quarter_variance_implication` checks `(ICV)=>(REL)` for
  both endpoint parities through `ell=1024` using exact integer arithmetic.
- The clean premise is false in the small prefix. The even `ell=13` row has
  same-denominator numerator `2181638144` against target `1073741824`.
- It holds at both endpoints for every exact row `14<=ell<=23`. At `ell=14`
  the odd and even conditional-variance numerators are `1288331008` and
  `2905795008`, against target `4294967296`.
- On the odd `ell=14` row, the six exact `(ICV-H)` contributions are
  `14868736`, `29014560`, `313096416`, `67174912`, `284407424`, and
  `579768960`; they sum to the pinned variance numerator.
- At `ell=200`, the clean premise asks for savings `313648` and `627296` over
  the individual-Weil global envelope at the two endpoints. These prices are
  polynomial, while equidistribution among the coarse cylinders would be
  exponentially stronger.

Hast--Matei's `m=2` result averages over all intervals and has constants
depending on the growing interval parameters. Baier--Bhandari's fixed-field
hybrid variance averages over centers and residue classes and excludes the
ramified modulus `Q(0)=0`. Neither proves `(ICV-H)`.

## Consequences

- A candidate theorem can now be rejected or credited against one exact
  level-by-level inequality.
- More unrestricted global moments receive no endpoint credit unless they
  imply the localized ramified estimate `(ICV-H)`.
- Finite success remains diagnostic only; the manuscript warning remains.
- `(REL)`, not `(ICV)`, stays the paper's sole minimal unproved statement.
