# ADR-0584: Expand high-conductor shifts before squaring the Mobius phase

Status: accepted
Date: 2026-08-21
Index-summary: Reduce every aggregate identity-path split to one signed two-Mobius Berlekamp correlation and keep the four-shift energy outside the selected route

## Context

ADR-0583 identifies the aggregate identity-path layer

```text
L_i = 2^i A_i-2^(i-1)A_(i-1)
```

with a low-conductor twist of only the high Hayes trace-power spectrum.  The
older Berlekamp route culminated in ADR-0562's restricted four-shift Mobius
parallelogram, but that object arose after squaring a local autocorrelation.
It was not known whether expanding the new conditional-variance layer would
immediately reproduce the same four-Mobius obstruction.

Let the endpoint discrepancy have its exact convolution-order expansion

```text
D(g) = sum_(1<=d<ell) T_d(g),
T_d(g) = d sum_(u in V_d) M_(n-d)(g u^(-1)).            (O)
```

Let `c` be the coarse identity-cylinder level, `K=ker(E_ell->E_c)`, and
`R=|K|`.  For two orders define on `q in E_c`

```text
w_(d,e)(q)
 = R sum_(g in qK) T_d(g)T_e(g)
   -(sum_(g in qK)T_d(g))(sum_(g in qK)T_e(g)).         (OC)
```

## Decision

Expand `(OC)` before applying Cauchy or taking another moment.  Since
`D=sum_d T_d`, exactly

```text
w = sum_d w_(d,d)+2 sum_(d<e) w_(d,e).                 (OP)
```

The same identity survives identity-cylinder selection and the signed layer
difference.  More explicitly, put

```text
K_i(g,h)
 = 1_(g maps to 1 in E_i)
   (R 1_(g=h)-1_(g maps to h in E_c)),
Q_i = 2^i K_i-2^(i-1)K_(i-1).
```

Expanding `(O)` gives the exact polynomial formula

```text
L_i
 = sum_(d,e<ell) d e
   sum_(u in V_d, v in V_e)
   sum_(deg A=n-d, deg C=n-e) mu(A)mu(C) Q_i(Au,Cv).   (BM2)
```

Here `Au` and `Cv` mean their Hayes classes.  On the squarefree support,

```text
mu(A)mu(C)
 = (-1)^(deg A+deg C+Berl(A)+Berl(C)).                 (BP2)
```

Thus `(BM2)` is a quadratic Berlekamp phase on a pair of polynomial
coefficient spaces, with squareful points carrying zero weight.  It has
**two**, not four, Mobius factors.  The restricted four-shift phase from
ADR-0562 reappears only if `(BM2)` is squared or bounded through a local
energy.  That loses the cross-order and exact-layer signs which the aggregate
path was selected to preserve, so it is not the next route.

Add `identity_path_mobius_order_pair_report`.  It constructs every `T_d`
from the native classwise Mobius distribution, checks their classwise sum
against the independently computed endpoint discrepancy, evaluates `(OC)`
on the requested child and parent cylinders, and reconstructs `L_i` from all
symmetric order pairs.  It exposes diagonal, off-diagonal, signed, and
absolute totals without assigning a bound to any finite row.

The exact contraction prices are now

```text
2 A_i <= A_(i-1)       iff L_i <= 0,
4 A_i <= 3 A_(i-1)     iff 2 L_i <= 2^(i-1) A_(i-1).   (PRICE)
```

Consequently a useful theorem may bound the combined signed sum `(BM2)`
directly; it need not prove nonpositivity and must not bound every `(d,e)`
cell separately.

There is one uniform cellwise theorem.  Translation
`tau:f(x) -> f(x+1)` is a degree-preserving ring automorphism.  It preserves
`mu`, maps every interval space `V_d` bijectively to itself, and therefore
preserves each `T_d` separately.  At

```text
t=2^v_2(n),
```

Lucas parity says that `tau` fixes the first `t-1` leading coordinates and
interchanges the two children at coordinate `t`.  Hence both conditional
cross-covariance masses in every `(d,e)` cell are interchanged equally, and

```text
L_t(d,e)=0                                              (TRANS2)
```

for every order pair whenever `t<=c`.  This strengthens ADR-0582's aggregate
translation split: no cancellation between convolution orders is needed at
that layer.  The report exposes `translation_forces_cellwise_zero` and fails
closed if a computed cell contradicts `(TRANS2)`.

The closest geometric object is Hast--Matei's two-polynomial short-interval
complete intersection `X_(2,n,h)`, with

```text
h=n-ell-1,       n-h-2=ell-1.
```

Thus `h=ell` at the odd endpoint and `h=ell+1` at the even endpoint.  Their
complete-intersection and singular-locus theorem has no `p>n` restriction
when `m=2`, so characteristic two is not excluded at this stage.  But their
arithmetic estimate is a `q -> infinity` statement with a constant allowed to
depend on the growing `(n,h)`, and its explicit top-weight piece is the
ordinary untwisted short-interval covariance already priced in ADR-0554.  It
does not encode the exact-conductor character in `Q_i` or the high-only
conditional subtraction in `(BM2)`.

The precise geometric continuation is therefore an equivariant refinement,
not another invocation of the published variance theorem: pull the nontrivial
principal-unit/Witt character defining layer `i` back to the two-polynomial
coefficient-pair space, remove the coarse-character component, and bound the
long-cycle-by-long-cycle Frobenius trace of that rank-one local system with a
degree-uniform constant that satisfies `(PRICE)`.  A lift of principal-unit
multiplication to the ordered-root cover is not presently proved, so this is
stated as a local-system theorem target rather than as an existing group
action.

## Evidence

`high_conductor_shifted_layers_have_exactly_two_mobius_factors` checks every
layer for both `(ell,n)=(8,17),(8,18)`.  All 28 symmetric order pairs
reconstruct the independently retained ADR-0583 integer.  The pinned rows are

```text
             diagonal    off-diagonal       signed       pairwise absolute
n=17, i=1           0               0             0                       0
n=17, i=2   -14664704        10563584      -4101120               130719232
n=17, i=3     1446400        -5357568      -3911168               178778624
n=18, i=1   -16757248        10284032      -6473216               168878080
n=18, i=2           0               0             0                       0
n=18, i=3    -1549312         9531392       7982080               451683328
```

The translation-forced layers vanish in the full decomposition.  Other rows
show cancellations of one to two orders of magnitude relative to pairwise
absolute values, so an orderwise triangle inequality would discard exactly
the feature retained by `(BM2)`.  Invalid layers and a resource-starved pair
table decline before enumeration.

On both pinned translation layers, all 28 symmetric order-pair cells vanish
individually, independently replaying `(TRANS2)`.

## Consequences

- The new high-only shifted moment is genuinely earlier than the old
  four-shift obstruction.  Conditional-variance subtraction has not proved a
  bound, but it leaves a two-Mobius theorem target on which Berlekamp/Chowla
  cancellation can act directly.
- ADR-0498's single-polynomial inverse-additive phase is not itself the needed
  theorem.  The next analytic statement must control `(BP2)` under the
  centered multiplicative Hayes-class kernel `Q_i`, summed across `d,e,u,v`.
- Squaring `(BM2)`, applying pairwise absolute values, or proving separate
  order-cell estimates is a regression unless the resulting ledger is shown
  to retain the required endpoint saving.
- Hast--Matei `m=2` supplies the characteristic-two geometric carrier, but
  its untwisted, degree-dependent global estimate does not supply the required
  Witt-isotypic trace bound.
- This identity moves the representation boundary but does not prove any
  aggregate contraction, `(REL)`, or Lemire's conjecture.
