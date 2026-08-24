# Lemire endpoint proof: review and unblocking bridges

Date: 2026-08-19

Status: research handoff, not a proof and not theorem evidence

This note reviews the current `gf2-lemire` increment and records the most
promising literature and representation bridges for the remaining endpoint
bound.  It is deliberately separate from the canonical
[`lemire-half-degree-irreducibles.md`](lemire-half-degree-irreducibles.md) so
that the active lane can accept, reject, or refine these recommendations
without concurrent edits to its primary research record.

Revalidate the current branch, `PLAN.md`, the lane status, and the canonical
research note before acting on commit identifiers or finite ranges quoted
below.

## Executive recommendation

The current reduction is sound and is a substantially better attack surface
than another global character-by-character estimate.  The newest exact
experiments have also closed several tempting shortcuts: the collapsed signed
Witt function is not bent or plateaued, each primitive modulo-eight phase has
full Fourier support in the pinned row, and the four positive phase energies
are very far from complementary.  The surviving priorities are now:

1. adjoin the four units modulo eight as an **auxiliary quadratic space**.
   This realizes the exact `chi_8` projector, including squareful zeros, as
   one degenerate quadratic Gauss sum.  Search for a joined group law mixing
   affine fibres, valuations, and Witt parameters, then test modulo-four
   additivity, bilinear polarization, and radical size;
2. retain the second-trace quadratic forms before replacing their Gauss sums
   by Möbius signs, and test whether their pairwise rank/type distribution is
   a bounded-class Kerdock or Delsarte--Goethals configuration;
3. in Sawin's short-interval geometry, use the exact identity
   `lambda_(-1)(std)=p_n` to replace the huge even/odd exterior-power bound by
   a cyclic/Foulkes decomposition.  The required new result is a small
   effective trace or Betti bound for those cyclic rank-one local systems;
4. compute extension-field short-interval traces beginning with the first
   four-fixed-coefficient case.  Small cases expose compact zeta recurrences,
   but the first ordinary factors show that supersingularity is a diagnostic,
   not a uniform solution; and
5. retain `sum_v |Delta_v| <= poly(d) 2^d` and the connected fourth-cumulant/
   gcd stratification as ledger-checked fallbacks without separating
   convolution orders.

The earlier Bagshaw/Hölder route below remains a useful independent fallback,
especially for the global inverse-additive energy.  Ordinary complementary
codes, relative difference sets, signed expanders, and scalar random-matrix
heuristics should be deprioritized: the finite spectra either contradict
their exact hypotheses or show that their optimal projector simply returns
the already-open signed energy.

Do not cite Bagshaw's final 2024 Möbius or prime-distribution theorems as
results over `GF(2)`: that paper globally fixes odd `q`.  The proposal is to
reprove the relevant characteristic-free lemmas and replace the genuinely odd
inputs, not to silently extend a published theorem.

## Current proof boundary

Put

```text
E_ell = (1 + T GF(2)[T]) / (T^(ell+1)),
V_d   = {1 + a_1 T + ... + a_d T^d},
```

and let `M_k(e)` be the degree-`k` polynomial-Möbius sum in principal-unit
class `e`.  The current group-ring logarithmic differentiation gives the exact
identity

```text
Delta_(ell,n)
  = sum_(1<=d<ell) d sum_(u in V_d) M_(n-d)(u^(-1)).       (MC)
```

For the two endpoints, `n=2ell+1` and `n=2ell+2`, the remaining ledger
obligation for `ell>=200` is

```text
abs(sum_(1<=d<ell) d sum_(u in V_d) M_(n-d)(u^(-1)))
  <= 2^ell.                                                (EB)
```

The threshold is paired with Arndt's originally reported finite range through
degree 400 and Axeyum's independent certificate/checker reproduction of that
range.  The exact operation reconstructs finite endpoint discrepancies; it
does not prove `(EB)`.

Two constraints must be preserved:

- substantial cancellation occurs across the signed `d`-terms, so summing
  their absolute values is not presently a plausible proof;
- the proved local wild-Kloosterman estimate is unweighted, whereas a Vaughan
  or Heath--Brown decomposition introduces Möbius-derived weights.

## Review of the landed increment

### Mathematical review

The derivation of `(MC)` is correct.  If `A_d` is the degree-`d` class
distribution and `M=A^(-1)`, then

```text
Lambda_n = sum_(1<=d<=n) d A_d M_(n-d).
```

For `d>=ell`, `A_d` is uniform.  The total polynomial-Möbius sum is `-2` in
degree one and zero above degree one.  Thus the `d=n-1,n` terms produce the
uniform mean `2^(n-ell)`, all other uniform terms vanish, and the remaining
nonuniform part is exactly `(MC)`.

The implementation also maintains the correct epistemic boundary:

- two modular transforms plus signed CRT recover exact finite values;
- the endpoint total is reconstructed and checked;
- the ledger fact remains `conjectured`, with no proof route or evidence; and
- no Autogenesis operation can grant credit for the quantified bound.

### Validation gap worth closing

The endpoint reconstruction tests compare two mathematically distinct routes,
but they share principal-unit indexing and transform infrastructure.  The
existing independent Berlekamp-factorization test validates the classwise
values `M_k(e)`; it does not independently validate the new termwise map

```text
(d,k) |-> d sum_(u in V_d) M_k(u^(-1)).
```

Add a small direct oracle, ideally for every admitted pair with `ell<=5`, that
enumerates and factors the relevant binary polynomials and computes every
individual `d`-term.  It should detect at least these mutations:

- replace `u^(-1)` by `u`;
- omit or shift the factor `d`;
- reverse the mixed-radix coordinate order; and
- mishandle the factor `T` under reciprocal reversal.

This is a test-independence improvement, not a known implementation defect.

## Bridge 1: additive Fourier expansion of inverse-interval membership

This is the most important representation to write down exactly.

Let

```text
J_ell = T GF(2)[T] / (T^(ell+1)),
W_d   = {a_1 T + ... + a_d T^d},
V_d   = 1 + W_d.
```

The additive group `J_ell` has dimension `ell`.  Choose a nondegenerate
additive pairing and write `W_d^perp` for the annihilator of `W_d`, of size
`2^(ell-d)`.  Orthogonality gives

```text
1_(z in V_d)
  = 2^(d-ell) sum_(a in W_d^perp) psi_a(z-1).
```

Consequently, with `k=n-d`, each unsigned fibre in `(MC)` has the exact form

```text
S_(d,k) := sum_(u in V_d) M_k(u^(-1))

         = 2^(d-ell) sum_(a in W_d^perp)
             sum_(deg f=k, f monic) mu(f) psi_a(<f>^(-1)-1).   (AF)
```

Here `<f>` is the leading-coefficient/reciprocal principal-unit class used by
the repository.  Before applying an external theorem, prove the exact change
of variables between `(AF)` and the conventional expression

```text
sum mu(g) e_(T^(ell+1))(a g^(-1)).
```

The bookkeeping is not cosmetic:

- the external papers invert an ordinary polynomial residue, while Axeyum
  inverts a reciprocal leading-coefficient class;
- reciprocal reversal preserves factorization away from the ramified factor
  `T`, which must be split off explicitly;
- the target is an exact-degree monic sum, while papers often sum
  `deg g < k`; and
- the phase lives on a prescribed annihilator rather than all frequencies.

Once those points are proved, `(AF)` places the live obligation directly in
the literature on Möbius-weighted inverse-additive characters.

## Bridge 2: Bagshaw's bilinear Kloosterman and inverse-energy machinery

### The directly relevant paper

Christian Bagshaw,
[*Bilinear Kloosterman sums in function fields and the distribution of
irreducible polynomials*](https://arxiv.org/abs/2401.10399).

The paper studies

```text
sum_(deg x<n) mu(x) e_F(a x^(-1))
```

and weighted bilinear sums with inverse-product phase.  It reaches arbitrary
composite `F` and obtains the required Type-I/Type-II decomposition using a
function-field Vaughan identity.

Applicability boundary: the paper globally fixes an odd prime power `q`.
Therefore Theorems 2.1--2.6 are not established for `q=2` as published.

Nevertheless, Lemmas 4.1 and 4.2 reduce weighted bilinear inverse-product sums
to additive energies of modular inversions by Hölder, Cauchy--Schwarz, and
additive orthogonality.  The displayed proofs appear not to divide by two or
use a quadratic character.  This is an inference from the proofs, not a
published characteristic-two theorem.  Audit their complete dependency chain,
especially Lemmas 3.13--3.14 and every use of the complete Kloosterman bound in
Lemmas 3.10--3.12.

### Arbitrary-characteristic companion

Christian Bagshaw,
[*Bilinear forms with Kloosterman and Gauss sums in function
fields*](https://arxiv.org/abs/2304.05014).

This paper explicitly fixes an arbitrary prime power and says that oddness is
required only where stated.  Its interval Kloosterman Theorem 3.4 gives the
characteristic-free estimates (3.8a--b) for arbitrary composite `F`; only the
additional estimate (3.9a) assumes odd `q`.  Remark 3.5 also allows bounded
weights inside the complete Kloosterman sum.

The 2023 theorem is not itself `(AF)`: its Kloosterman phase has a complete
unit variable.  It is useful as a source of characteristic-free completion and
energy lemmas and as a control for the dependency audit.

### Why the Axeyum local result matters

Bagshaw's odd-characteristic applications use square-root-scale complete
Kloosterman estimates.  Axeyum now has a direct binary prime-power estimate for

```text
K_2(c) = sum_(u in (GF(2)[T]/T^r)^x) psi(u^(-1)+cu),

abs(K_2(c)) <= 2^(ell+1-ceil(ell/3)),  r=ell+1.
```

It is weaker than a generic square-root bound but is valid for the exact wild
modulus and characteristic.  Substitute it only after identifying the precise
complete-sum call in the Vaughan proof.  Then recompute every exponent; do not
retain an exponent derived from the unavailable odd-characteristic estimate.

### Additive inverse energy is a new diagnostic

Bagshaw's Type-II bounds depend on quantities of the form

```text
E_inv(r,m)
  = #{x_1^(-1)+x_2^(-1)=x_3^(-1)+x_4^(-1) mod T^r:
       deg x_i < m}.
```

This is not Axeyum's existing multiplicative product energy
`#{AB=CD}`.  Implement a bounded exact `q=2`, `F=T^r` diagnostic before
assuming that either the generic published estimate or the existing product
energy is sharp for this set.  Compare:

- direct enumeration at small `r,m`;
- the generic Bagshaw exponent;
- any exact plateau or piecewise formula suggested by the data; and
- the fourth Walsh moment of the inverse-interval indicator.

An exact special-modulus energy improvement would feed directly into the
characteristic-free Hölder lemma.

## Bridge 3: fixed-field Möbius uniformity and Hayes phases

Pierre-Yves Bienvenu and Thai Hoang Le,
[*Linear and quadratic uniformity of the Möbius function over
`F_q[t]`*](https://arxiv.org/abs/1711.05358).

Their Theorem 1 gives, for every fixed `q` including `q=2`, a uniform bound

```text
sum_(deg f<n) mu(f) chi(linear coefficient phase of f)
  <<_(epsilon,q) q^((3/4+epsilon)n).
```

The proof uses Hayes `L`-functions and is accompanied by a function-field
Vaughan framework.  This is potentially useful for Type-I pieces after
completion turns part of `(AF)` into a linear coefficient phase.

Limits:

- the `3/4` exponent alone is not strong enough after a naive sum over all
  interval variables or all annihilator frequencies;
- their general quadratic-phase theorem assumes `p>2`; and
- in characteristic two, their special `f^2` Hankel phase collapses to a
  linear phase, but the Berlekamp discriminant is not automatically of that
  form.

Sam Porritt's
[*A note on exponential-Möbius sums over
`F_q[t]`*](https://arxiv.org/abs/1711.08729)
provides a closely related Hayes-based linear estimate.  The canonical Lemire
note has already checked that its explicit general bound does not close the
`q=2` endpoint.  Treat these papers as Type-I/proof-architecture inputs, not as
the endpoint theorem.

## Bridge 4: Berlekamp discriminant as a structured Möbius phase

Dan Carmon,
[*The autocorrelation of the Möbius function and Chowla's conjecture for the
rational function field in characteristic
2*](https://arxiv.org/abs/1409.3694).

For a squarefree binary polynomial, the characteristic-two analogue of
Pellet's formula expresses its Möbius sign through an additive character of the
Berlekamp discriminant.  Thus the Möbius weight in `(AF)` can, on the
squarefree locus, be rewritten as a structured additive rational phase rather
than an arbitrary bounded coefficient.

Carmon's asymptotic is fixed degree with the field size tending to infinity,
not fixed `q=2` with moving degree.  It supplies a representation and
stationary-phase vocabulary, not a usable estimate for `(EB)`.

Use this bridge only after the exponent ledger identifies a failing range.
For that range, compute or bound:

- the algebraic degree of `Berl(f) + a <f>^(-1)` in coefficient coordinates;
- ranks of first and second differences on the relevant interval fibres;
- Walsh support and plateau sizes for small `ell`; and
- whether squareful inputs can be removed without losing the required signed
  identity.

The desired outcome is a low-rank or stationary-fibre theorem special to the
combined phase, not an appeal to Carmon's large-field cancellation result.

## Bridge 5: rational/Padé and Hankel-rank description of `V_d^(-1)`

The inverse interval is not an arbitrary subset of the principal-unit group.
If

```text
z(T) = 1/u(T) mod T^(ell+1),  u in V_d,
```

then

```text
u(T) z(T) = 1 mod T^(ell+1).
```

Therefore the coefficients of `z` satisfy a linear recurrence of order at
most `d`.  Equivalently, `z` is a truncated rational/Padé series with
denominator degree at most `d`; the associated finite Hankel matrices have
rank at most `d`, subject to the usual finite-truncation qualifications.

This provides three possible refinements of the inverse-additive-energy
problem:

1. stratify `V_d^(-1)` by exact minimal recurrence order rather than treating
   it as one set;
2. count additive quadruples through intersections of low-Hankel-rank loci;
3. test whether the Möbius phase is uniform on, or transverse to, the
   Berlekamp--Massey strata.

A first finite experiment should report the minimal linear complexity of each
element of `V_d^(-1)` together with its contribution to the Möbius convolution
and inverse additive energy.  If almost all elements have maximal allowed
complexity and the exceptional strata account for the large Fourier
coefficients, the stratification may isolate the obstruction cleanly.

## Bridge 6: the Carlitz curve as an Artin--Schreier--Witt tower

The canonical note already proves that the family norm `D_ell` is the zeta
numerator of the binary Carlitz cyclotomic curve `C_ell` and that

```text
#C_ell(GF(2^n)) = 2^n + 1 + 2^ell Delta_(ell,n).
```

Aristides Kontogeorgis and Jacob Kenneth Ward,
[*Arithmetic actions on cyclotomic function
fields*](https://arxiv.org/abs/1807.02220),
describe prime-power Carlitz cyclotomic fields recursively as composita of
explicit Kummer and Artin--Schreier extensions, with the higher layers
described by Artin--Schreier--Witt data.  At `q=2`, the tame constant-unit
factor `GF(2)^*` is trivial, so the conductor tower is purely wild.

This suggests replacing the sum over all exact-conductor characters by the
relative cohomology of

```text
C_ell -> C_(ell-1).
```

The exact-conductor trace should live on the new/Prym part of this cover.
Concrete tasks are:

1. derive explicit relative Artin--Schreier equations for the first few
   levels;
2. verify that their relative point-count traces reproduce the existing
   conductor increments `T_(j,n)`;
3. compute the dimension, Swan filtration, and obvious automorphisms of the
   new part; and
4. look for an endpoint-specific trace recurrence or pairing, not a generic
   Hasse--Weil estimate.

The literature on Newton slopes of Artin--Schreier--Witt towers concerns
`p`-adic slopes.  Those results do not by themselves give cancellation of the
complex Frobenius trace needed here.

## Literature applicability matrix

| Source | `q=2` | `T^r` / nonsquarefree modulus | Relevant contribution | Why it does not directly close `(EB)` |
|---|---:|---:|---|---|
| Bagshaw 2024, arXiv:2401.10399 | No, paper fixes odd `q` | Yes | Möbius inverse-additive sums, Vaughan, bilinear inverse-product energy | Final theorems are not established in characteristic two |
| Bagshaw 2023, arXiv:2304.05014 | Yes where oddness is not stated | Yes | Characteristic-free interval Kloosterman/energy lemmas | The principal bilinear form is adjacent to, not identical with, `(AF)` |
| Sawin--Shusterman, arXiv:1808.04001 | The inverse-additive theorem allows arbitrary `q` | No, it assumes squarefree modulus | Möbius orthogonality to inverse additive characters | `T^r` is maximally nonsquarefree; their characteristic-two extension is explicitly left open elsewhere in the paper |
| Bienvenu--Le, arXiv:1711.05358 | Linear theorem yes; general quadratic theorem no | Hayes/short-interval setting | Fixed-field linear Möbius uniformity and Vaughan template | Linear exponent alone is too weak after naive aggregation |
| Carmon, arXiv:1409.3694 | Yes | Not the moving prime-power endpoint | Berlekamp-discriminant phase representation | Large-field, fixed-degree asymptotic |
| Kontogeorgis--Ward, arXiv:1807.02220 | Yes | Yes, prime-power Carlitz tower | Explicit wild Artin--Schreier--Witt tower | Structural model, not an archimedean trace bound |

The missing quadrant is therefore real: fixed `q=2`, a maximally
nonsquarefree moving modulus, and the exact half-degree endpoint.  The current
binary local Kloosterman result is valuable precisely because it may replace
one of the inputs that prevents the arbitrary-modulus analytic method from
entering that quadrant.

## Required exponent ledger

Do not begin a long proof port until this table has been filled symbolically.
Set

```text
r = ell + 1,
n in {2ell+1, 2ell+2},
k = n-d,
1 <= d < ell.
```

For every proposed decomposition range, record:

| `d` range | `k=n-d` range | Fourier normalization | Type-I input | Type-II/energy input | resulting base-2 exponent | constants/poly factors | closes below `2^ell`? |
|---|---|---|---|---|---|---|---|
| small `d` | near `2ell` |  |  |  |  |  |  |
| balanced |  |  |  |  |  |  |  |
| large `d` | near `ell` |  |  |  |  |  |  |

As a calibration only, Bagshaw's published odd-characteristic Theorem 2.3
gives an inverse-Möbius bound of the shape

```text
q^(15k/16 + epsilon k) + q^(2k/3 + r/4 + epsilon k).
```

Even if an identical binary estimate were reproved, comparison with `2^ell`
would make it directly useful only when `k` is close to `r` (roughly
`k <= 16ell/15`, ignoring lower-order terms).  It would not cover the
small-`d`, `k` near `2ell` range.  This calculation is another reason to retain
the recurrence and cancellation across `d` rather than seeking one uniform
black-box estimate.

The ledger must distinguish two possible sufficient outcomes:

- a power saving for every `d`, strong enough that triangle inequality loses
  only a polynomial factor; or
- an estimate for a signed block of `d`-values that explicitly preserves
  cancellation across convolution orders.

## Prioritized bounded work packages

### P0: independent finite control

- Add the direct termwise oracle described above.
- Pin at least one odd and one even endpoint.
- Add mutation-sensitive inverse and weight controls.
- Do not increase theorem credit.

Exit: individual convolution terms, not just their total, agree with an
algebraically separate computation.

### P1: prove the exact Fourier bridge

- State the additive pairing and annihilator explicitly.
- Prove `(AF)` with the repository's reciprocal convention.
- Separate the ramified `T` contribution.
- Reconcile exact-degree/monic sums with the external papers' interval sums.

Exit: every normalization and exceptional term is checked at small levels and
the external analytic target is named without an informal change of variables.

### P2: Bagshaw dependency and exponent audit

- Create a lemma dependency table for Bagshaw 2024 Lemmas 3.10--3.14 and
  4.1--4.2 and the Vaughan step.
- Mark every use of odd characteristic.
- Insert the binary complete-sum exponent where available.
- Add an exact inverse-additive-energy diagnostic for `T^r`.
- Fill the exponent ledger for all `d`.

Exit: either a complete inequality below `2^ell`, or a precise uncovered
`d`-range and the exact exponent deficit.

### P3A: Berlekamp phase, only for an analytic gap

- Restrict to the uncovered range from P2.
- Measure the combined phase rank and stationary fibres.
- Formulate one explicit cancellation lemma with a quantified saving.

Exit: a falsifiable characteristic-two exponential-sum obligation, not a
general statement that Möbius is random.

### P3B: Artin--Schreier--Witt relative trace, as the geometric alternative

- Build the first relative covers `C_ell -> C_(ell-1)` explicitly.
- Match relative traces to exact-conductor filtration data.
- Search for endpoint-specific pairing or recurrence on the new part.

Exit: a geometric statement that improves on bounding every character or
every reciprocal root separately.

## Stop conditions and claim discipline

Stop and record a negative result if any of the following occurs:

- the Bagshaw port needs an odd-characteristic lemma for which the binary
  wild-Kloosterman estimate is not a valid substitute;
- the exponent ledger remains at or above `2^ell` on a nonempty linear-sized
  `d`-range;
- the inverse-additive energy is generically as large as its trivial scale in
  the required range;
- the Berlekamp phase has unbounded rank/complexity with no quantified
  stationary-fibre control; or
- the Artin--Schreier--Witt reformulation only reproduces Hasse--Weil on a
  space of exponentially growing dimension.

Finite agreement, a clean representation, or a proof candidate in prose must
remain separate from a replayable universal certificate.  The endpoint fact
should remain conjectured until the quantified inequality itself is checked by
an accepted proof route.

## Web follow-up after the single-translation counterexample

**Added:** 2026-08-19, after commit `26b16e3d0` rejected the proposed
single-translation Berlekamp cancellation inequality at
`(ell, k, d) = (9, 11, 8)`.

The counterexample should change the proof search, not merely the constant in
the failed inequality.  It says that no fixed nonzero translation need expose
the cancellation that is visible in the signed bucket total.  The next
representations should therefore keep either the whole Artin--Schreier fibre or
the whole conductor/correlation family in one connected system.  The following
four directions were found in a fresh literature search and are ordered by the
cost of obtaining a decisive finite diagnostic.

### 1. Replace the rational Berlekamp phase by a dyadic discriminant or Arf phase

There are two exact coordinate systems for the same squarefree sign.  Both may
make the collective cancellation across all translations more visible than the
current rational-function formula.

#### 1A. Stickelberger--Swan modulo 8

[Swan, *Factorization of polynomials over finite fields*
(1962)](https://msp.org/pjm/1962/12-3/pjm-v12-n3-p27-p.pdf) proves a
characteristic-two version of Stickelberger's theorem.  If `f` is a monic,
squarefree binary polynomial of degree `m`, `F` is its monic integral
coefficient lift, and `r` is the number of irreducible factors of `f`, then

```text
Disc(F) = 1 or 5 (mod 8),
r = m (mod 2)  iff  Disc(F) = 1 (mod 8).
```

Consequently the polynomial Möbius sign has the exact form

```text
mu(f) = (-1)^m (-1)^((Disc(F) - 1)/4).
```

This trades the Berlekamp rational phase for an integer
resultant/discriminant computation modulo 8.  On each existing
Artin--Schreier fibre, compute the first, second, and mixed additive
differences of this two-adic phase in every kernel direction.  The useful
outcome would be that the phase has bounded algebraic depth, or a quadratic
polar form of uniformly large rank, on the *full* fibre even though every
chosen one-dimensional translation can have a large defect.

#### 1B. Second trace form and Arf invariant

[Cassou-Noguès, Erez, and Taylor, *Invariants of a quadratic form attached to
a tame covering of schemes*
(2000)](https://jtnb.centre-mersenne.org/item/JTNB_2000__12_2_597_0.pdf),
Section 1.i, records the older characteristic-two bridge: for an étale algebra
`E/F`, the Berlekamp additive discriminant differs from the Arf invariant of
the second trace form only by a constant determined by `[E:F] mod 8`.  The
constant is zero in degrees congruent to `0, 1, 2, 7 mod 8` and one in the
other four classes.  The second trace form is the quadratic form given by the
second coefficient of the characteristic polynomial.

For `E = F_2[x]/(f)`, this offers a route to replace `mu(f)` by the sign of a
quadratic Gauss sum.  After the correct odd/even-degree restriction and
radical convention are fixed, the bucket sum can be rewritten schematically
as one sum over pairs `(f, y)`, with:

- the coefficient-coset condition on `f`;
- the inverse-coset Artin--Schreier condition already derived in the lane; and
- one additive phase given by the second trace quadratic form evaluated at
  `y`.

This is attractive precisely because it is one connected system.  Instead of
selecting a translation `h` and comparing `f` with `f+h`, sum over the entire
auxiliary quadratic space and seek cancellation from the rank of its polar
form after restriction to the fibre.  A uniform lower bound on that rank, or a
classification of its radical, would give collective square-root cancellation
that a single-translation lemma cannot see.

**Immediate Axeyum experiment.**  Extend the existing fibre report with:

- squarefree population and squareful population, separately;
- the Möbius sign, `Disc(F) mod 8` sign, and Arf sign, with equality checks;
- first and second phase differences along a basis of the full
  Artin--Schreier kernel;
- the polar rank and radical dimension of the restricted quadratic form; and
- the exact signed sum grouped by rank and radical type.

Add mutations that flip one discriminant bit, one quadratic coefficient, and
one squarefreeness flag.  The report is useful only if each mutation makes the
check fail.

**Applicability warning.**  These identities describe the sign on the
squarefree, hence étale, locus.  They do not encode the value `mu(f) = 0` for a
squareful polynomial.  Squarefreeness must remain an explicit gate.  The
odd-degree trace-zero restriction and all degenerate quadratic-space
conventions must also be proved before an Arf/Gauss-sum identity is credited.

### 2. Put the principal-unit group into truncated 2-typical Witt coordinates

[Katz, *Witt Vectors and a Question of Keating and Rudnick*
(2013)](https://web.math.princeton.edu/~nmk/wittchar31.pdf) gives an exact
coordinate decomposition for the truncated big Witt group.  For a ring of
characteristic `p`, the principal-unit series modulo `X^(n+1)` decomposes into
`p`-typical Witt blocks indexed by the positive integers `m <= n` prime to
`p`.  At `p = 2`, the blocks are therefore indexed by odd `m`, and the length
of the `m`-block is the number of powers `m, 2m, 4m, ...` not exceeding `n`.

This structural part of Katz's paper is exact and finite.  In these
coordinates, multiplication of principal units is Witt addition, inversion is
additive negation, and the conductor is the highest active Witt slot.  Thus the
current coefficient equation `z^2 + h z = a` may look nonlinear partly
because it is written in ordinary coefficient coordinates rather than in the
coordinates intrinsic to `E_ell`.

**Immediate Axeyum experiment.**  Add a checked conversion between ordinary
coefficient bits and truncated 2-typical Witt blocks, then annotate:

- every annihilator character and its exact conductor;
- the direct and inverse cosets in every current bucket;
- the Artin--Schreier kernel and image; and
- the failing `(9, 11, 8)` single-translation bucket

by block support and highest active slot.  Recompute the signed energy both
globally and blockwise.  If the excess off-diagonal energy is confined to one
or two blocks, isolate those blocks as the exceptional system and apply
orthogonality or Cauchy across the remaining product.  If it is not confined,
the same data can test whether a tensorized rank statement is more plausible
than a translation statement.

**Applicability warning.**  Katz's equidistribution theorem takes the field
size to infinity and is not a theorem for the fixed field `F_2`.  Import only
the exact Witt-coordinate lemmas.  Also do not assume that the low-degree
polynomial set `V_d` becomes a Cartesian box in Witt coordinates: measure and
then prove the resulting triangular constraints.

### 3. Isolate exceptional real short-interval characters before seeking a generic bound

[Klurman, Mangerel, and Teräväinen, *Correlations of multiplicative functions
in function fields*
(2023)](https://arxiv.org/abs/2009.13497) works with fixed `q` and explicitly
finds a low-characteristic obstruction when `q` is a power of two.  Its setup
combines a Dirichlet character with a short-interval character, exactly the two
types of Fourier data that meet in the present ray/principal-unit formulation.
The important lesson here is not an asymptotic estimate but the obstruction
taxonomy: real characters associated with powers of `T` can support persistent
correlations that generic character arguments miss.

This matters at `q = 2` because `E_ell` is a 2-group and has many order-two
characters.  The large defect for one translation may be the visible shadow of
several simultaneous real Fourier modes, while the final signed bucket still
cancels after those modes interact.

**Immediate Axeyum experiment.**  For each bucket/fibre, compute the exact
projection of

```text
w(f) = mu(f) * 1_bucket(f)
```

onto every order-two principal-unit/Hayes character, grouped by Witt block and
exact conductor.  Compare those projections with the translation defect and
with the signed target.  Then test the decomposition

```text
w = exceptional real projection + orthogonal residual.
```

If a small, stable list of real modes explains the defect, evaluate its
contribution exactly in the weighted `B`-combination and prove cancellation
only for the residual.  This would replace a false uniform local claim by an
exceptional-plus-generic theorem whose exceptional part is finite and
auditable.

**Applicability warning.**  The paper's principal results are averaged or
logarithmic correlation theorems, not a uniform theorem for each local bucket.
Use its characteristic-two exceptional-character mechanism to choose the
decomposition; do not cite its asymptotics as the missing endpoint bound.

### 4. Unfold the connected fourth cumulant by gcd/magic-square strata

The lane already has the exact connected quantity

```text
K4 = 2^ell M4 - 3 M2^2
```

and the exact conductor filtration.  That is a stronger starting point than a
collection of unrelated moment bounds: the three Wick pairings have already
been subtracted, so only genuinely connected off-diagonal configurations must
be controlled.

[Keating and Rudnick, *Squarefree polynomials and Möbius values in short
intervals and arithmetic progressions*
(2016)](https://arxiv.org/abs/1504.03444) identifies Möbius-twisted character
sums with traces of symmetric powers of Frobenius.  [Gorodetsky, *Magic
squares, the symmetric group and Möbius randomness*
(2024)](https://arxiv.org/abs/2102.11966) gives a complementary combinatorial
description of the relevant symmetric-power moments using magic squares and
gcd matrices, following the Vaughan--Wooley style of factorization.

The proposed use is algebraic rather than asymptotic.  Expand the connected
off-diagonal part of the current `K4` into common-factor/gcd-matrix strata.
Subtract the three pairing strata first.  For every remaining connected gcd
graph, count the independent low-coefficient equations imposed jointly by the
ray-class and reciprocal-coset constraints.  The desired statement is that a
connected stratum gains roughly one full factor `2^(-ell)` relative to the raw
quadruple count.  Crucially, perform this count either for all convolution
orders `d` together or directly inside the summation-by-parts formula for `B`;
do not take absolute values separately in `d` and discard the cancellation the
cumulant was built to retain.

**Immediate Axeyum experiment.**  For the currently feasible range
`ell <= 9`, canonically classify every off-diagonal quadruple by:

- its gcd incidence matrix or connected gcd graph;
- its conductor and convolution orders;
- the rank of the joint direct/inverse low-bit constraints; and
- its signed contribution after Wick-pairing subtraction.

Generate a table of the maximum rank deficit by connected graph type.  A
stable finite list of graph types with an affine formula in `ell` would turn
the current empirical fourth-cumulant envelope into a finite family of
combinatorial lemmas.

**Applicability warning.**  Keating--Rudnick use a large-field limit, and
Gorodetsky's function-field moment results likewise do not directly supply the
fixed-`F_2` local bound.  Import the exact symmetric-function identity and the
gcd/magic-square parametrization, not the equidistribution conclusion.

## Recommended order and stopping tests for this follow-up

1. Run the discriminant/Arf rank diagnostic on the already enumerated
   Artin--Schreier fibres.  It is the cheapest test of a genuinely connected
   replacement for the failed translation lemma.
2. Add Witt-block labels and order-two-character projections to the same
   report.  These two views should use one underlying enumeration so their
   populations and signs cannot drift.
3. If the local quadratic rank is uniformly large after removing a small
   exceptional real subspace, state that exact rank lemma and try to prove it.
4. Otherwise, move up one level and attack the connected fourth cumulant by
   gcd strata, preserving the joint `d`/conductor sum.

Deprioritize the local route if the Arf polar rank stays small on a positive
fraction of populated fibres, or if removing all order-two projections does
not reduce the measured energy.  Deprioritize the gcd route if the connected
strata exhibit an unbounded rank deficit rather than a finite exceptional
classification.  Neither negative outcome weakens the finite verification;
it only records that the corresponding representation does not yet provide a
uniform proof.

## Follow-up after the dyadic product-parameter aggregation

The live lane has now gone one step beyond the fibre diagnostics discussed
above.  Its exact energy identity can be written

```text
E(k,d) = Q_k + Delta(k,d),
```

where `Q_k=(2^k-(-1)^k)/3` is the diagonal squarefree contribution and
`Delta` is the complete signed nonzero-shift correlation.  Successively
grouping the terms by exact affine fibre, `(h,w)`, normalized
Artin--Schreier product `(v,h_0/w_0)`, and valuation produces very large
intermediate cancellations.  The important new observation is that one must
also retain cancellation **between valuation layers**.

The coefficient-one valuationwise square-root guess is false.  On
`(ell,k,d)=(10,13,9)`, the sum of the absolute valuation-layer correlations is
`2502`, whose square is about `1.49*2^(k+d)`, whereas the complete connected
correlation is only `-314`.  The lane's sharper surviving candidate is

```text
Delta(k,d)^2 <= 2^(k+d+1).                            (connected target)
```

At a Lemire endpoint `k+d` is the endpoint degree.  Consequently the
connected target puts `Delta` below the missing main-term margin and gives
the conjectural random-scale energy `E(k,d)<2^k`.  This is an arithmetic
implication, not a proof of the target and not control of the complementary
signed cross-order convolution block.

### Additional CAS stress test

The native valuation-layer probe was run on the high tail for `ell=10` and
`ell=11`.  All values below are exact finite computations.  `Val-abs` means
`sum_v |Delta_v|`; no row is theorem evidence.

| `ell` | `d` | endpoint offset | `k` | `abs(Delta)` | Val-abs | `d 2^d` | `Delta^2 / 2^(k+d+1)` |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 10 | 7 | 1 | 14 | 206 | 418 | 896 | 0.0101 |
| 10 | 7 | 2 | 15 | 518 | 702 | 896 | 0.0320 |
| 10 | 8 | 1 | 13 | 6 | 638 | 2048 | 0.000009 |
| 10 | 8 | 2 | 14 | 1032 | 1324 | 2048 | 0.1270 |
| 10 | 9 | 1 | 12 | 1170 | 1322 | 4608 | 0.3264 |
| 10 | 9 | 2 | 13 | 314 | 2502 | 4608 | 0.0118 |
| 11 | 8 | 1 | 15 | 206 | 1266 | 2048 | 0.0025 |
| 11 | 8 | 2 | 16 | 394 | 1434 | 2048 | 0.0046 |
| 11 | 9 | 1 | 14 | 466 | 2274 | 4608 | 0.0129 |
| 11 | 9 | 2 | 15 | 1410 | 3242 | 4608 | 0.0593 |
| 11 | 10 | 1 | 13 | 1592 | 3436 | 10240 | 0.1511 |
| 11 | 10 | 2 | 14 | 452 | 4048 | 10240 | 0.0061 |

Two targets survive this selected matrix:

1. the preferred connected target above; and
2. the weaker backup `sum_v |Delta_v| <= d 2^d`.

The second bound is still strong enough to imply the polynomial-loss energy
scale already accepted by the endpoint exponent ledger on its large-`d`
tail.  It should not be promoted to the primary target, however: the CAS has
already exhibited genuine cross-valuation cancellation, and a proof that
takes absolute values at the valuation boundary is structurally throwing
that saving away.

### Highest-priority new bridge: one Heisenberg/Witt system

[Ito, Takeuchi, and Tsushima, *The L-polynomials of van der Geer--van der
Vlugt curves in characteristic 2*](https://arxiv.org/abs/2505.22036) is a
particularly close methodological match.  Their odd-characteristic method
fails in characteristic two because the relevant group has nontrivial
`4`-torsion.  They replace it by a characteristic-two construction using a
Lang torsor for `W_2`, the associated Heisenberg group, and characters of its
maximal abelian subgroups.  This produces an explicit `L`-polynomial formula
from one connected representation rather than independent estimates for
many fibres.

The proposed use here is diagnostic before it is geometric.  Embed every
valuation layer into the same truncated Witt/principal-unit group using the
appropriate Verschiebung shift.  Regard the complete `Delta`, not each
`Delta_v`, as the trace of the resulting phase representation.  Then compute:

- the commutator pairing of translations in the normalized product parameter;
- its radical and rank, globally and at each exact conductor;
- whether the phase representation is two-step nilpotent (Heisenberg) after
  quotienting a small exceptional centre; and
- the character decomposition over maximal abelian subgroups.

If the commutator rank grows uniformly, the connected square-root target may
be a finite Heisenberg-character orthogonality statement.  If the radical has
large dimension, classify its modes and test whether their total cancels in
the endpoint's signed convolution.  The present dyadic phase uses eighth
roots and can therefore require a `W_3` rather than `W_2` lift; the cited
paper is a template, not a theorem that can be applied verbatim.

[Liu and Wei, *The L-functions of Witt
coverings*](https://arxiv.org/abs/math/0404400) supplies a broader geometric
language for Artin--Schreier--Witt exponential sums.  It becomes useful only
after the CAS identifies a bounded-complexity Witt morphism or Newton
polyhedron.  A generic appeal to Weil bounds is insufficient if the degree or
conductor of that morphism grows too quickly with `ell`.

### The useful part of the older Hsu, Gao, and Fomenko literature

The often-repeated statement that Hsu handled a prescribed "half" must not be
used as an endpoint theorem.  [Hsu, *The Distribution of Irreducible
Polynomials in GF(q)[t]*](https://doi.org/10.1006/jnth.1996.0139) has a
square-root error multiplied by the number of prescribed coefficients.
[Gao--Howell--Panario](https://www.math.clemson.edu/~sgao/papers/GHP99.pdf)
summarize this as prescribing the lower or upper half, but the explicit
inequality, also restated by
[Car](https://www.impan.pl/shop/publication/transaction/download/product/110720?download.pdf),
is not positive at Lemire's exact binary half-degree boundary.  Hsu's
character/conductor organization remains relevant; the numerical conclusion
does not close this conjecture.

The more actionable older source is
[Fomenko, *On some L-functions of polynomial ring over finite
field*](https://eudml.org/doc/187783) (1996).  In the three-prescribed-
coefficient binary problem, Fomenko restricts Hayes characters through a
surjective map to two additive coordinates, with a small kernel, and proves
the Riemann hypothesis for the resulting low-degree `L`-functions.  The map
and its use are recalled explicitly in
[Gorodetsky, *Irreducible polynomials over F_(2^r) with three prescribed
coefficients*](https://arxiv.org/abs/1805.07105), Section 3.3.

The direct experiment is to construct an `epsilon`-analogue from the current
principal-unit character group to the first active coordinates of each
2-typical Witt block.  Group the complete connected correlation by its
`epsilon` image and exact conductor, and record the degree of each resulting
finite `L`-polynomial.  A bounded exceptional kernel plus uniformly
low-degree generic factors would give a concrete route to the connected
target.  Growth of either the kernel rank or the factor degrees proportional
to `ell` would reject this generalization early.

[Hsu and Nan, *On polynomial Gauss sums modulo
P^n*](https://eudml.org/doc/279382) gives a clean primitive/imprimitive
prime-power Gauss-sum decomposition, but the paper assumes that the
characteristic is odd.  It should be used only as a design pattern: compute
the full Witt Fourier transform of the normalized-parameter correlation,
test exact vanishing for imprimitive characters, and seek a
characteristic-two Artin--Schreier--Witt replacement for the primitive
formula.

### Ranked experiments from this follow-up

1. **Compute one connected Witt spectrum.**  Expose the signed value
   `S_v(a)` for every normalized parameter, embed all `(v,a)` into one
   truncated Witt group, and Fourier transform their **signed union** before
   taking absolute values.  Report support by exact conductor and the second
   and fourth spectral moments.
2. **Test the Heisenberg criterion.**  Compute first and second translation
   derivatives of the connected phase in Witt coordinates.  Measure the
   commutator/polar rank and radical.  Compare the resulting finite group
   directly with the `W_2`/Heisenberg decomposition of Ito--Takeuchi--
   Tsushima.
3. **Build the Fomenko `epsilon` analogue.**  Restrict characters to the first
   active Witt slots, then group exact `L`-polynomials and connected
   correlations by image, kernel, and conductor.  This is the most concrete
   way to decide whether the 1990s three-coefficient mechanism scales.
4. **Keep the polynomial valuation envelope as a fallback.**  Extend the
   finite sweep and search for the sharp exponent in
   `sum_v |Delta_v| <= poly(d) 2^d`.  Feed every proposed exponent into the
   existing endpoint ledger before attempting a proof.
5. **Cheaply audit recursive constructions.**  The even-characteristic
   degree-raising transforms in
   [Kyuregyan, *Recurrent Methods for Constructing Irreducible Polynomials
   over GF(2^s)*](https://doi.org/10.1006/ffta.2001.0323) provide a separate
   constructive avenue.  Apply each explicit transform to the existing
   certified sparse polynomials and test whether the forbidden upper-middle
   coefficient window is preserved.  Promote this route only if it covers
   more than isolated doubling families.

Stopping tests should be strict.  Abandon the Heisenberg route if the
connected commutator radical grows linearly and its exceptional contribution
does not cancel.  Abandon the Fomenko route if the `epsilon` kernel or generic
`L`-degree grows too fast for a square-root margin.  Abandon the valuation
envelope if `Val-abs/(d 2^d)` grows systematically in the next feasible
matrix.  These tests leave the connected fourth-cumulant/gcd stratification
above as the next representation, without weakening any finite verification.

## Cross-disciplinary representation audit

There are exact graph, random-matrix, coding-theoretic, and martingale
representations of the quantities now exposed by the proof.  The important
distinction is between an exact representation and a theorem strong enough in
the coupled regime

> base field fixed at `F_2`, degree and conductor growing together, and a
> deterministic Möbius sign rather than a random or freely chosen sign.

Most standard results miss one of those conditions.  The closest prospect for
importing an existing theorem is not generic expander or random-matrix theory;
it is a joint **Heisenberg / generalized-bent / relative-difference-set**
identification of the connected phase.  These are three languages for nearly
the same spectral-flatness phenomenon.

| Field | Exact object in this proof | The theorem that would finish the relevant step | Do we have it? |
|---|---|---|---|
| Signed graph theory | The anti-invariant sector of an unsigned double cover of the coefficient/inverse graph | A uniform bound on its centered second spectral moment, compatible across orders | Exact representation, but it is unitarily equivalent to the open signed energy |
| Heisenberg/Weil representation theory | The exact auxiliary-unit quadratic projector joined to the fibre/Witt variables | A group law with quadratic phase and uniformly small commutator radical | Local projector proved; direct-product fibre lift fails; joined law open |
| Generalized Boolean functions and coding theory | The family of second-trace quadratic forms before taking Arf signs | A bounded-class high-rank Kerdock/Delsarte--Goethals inner distribution | Collapsed gbent and positive complementarity are ruled out; joint Arf lift open |
| Random-matrix/monodromy theory | The Frobenius--long-cycle trace, equivalently a subpolynomial cyclic/Foulkes sum | Uniform effective cyclic-eigenspace trace or Betti cancellation in the fixed-`q`, growing family | Compression exact; applicable bound open |
| Dyadic martingales | Exact-conductor differences as Haar increments | A uniform conditional square-function or fourth-cumulant bound | Filtration yes; increment bound is the open arithmetic content |
| Algebraic geometry | Artin--Schreier--Witt curves/sheaves for the phase sums | A cohomological decomposition with bounded effective multiplicity after connected cancellation | Curves yes; generic Weil bounds are too costly |

### 1. The exact signed-graph model

For fixed `(ell,k,d)`, form a signed bipartite multigraph.  Its left vertices
are the input cosets under the low-coefficient shift space and its right
vertices are the inverse cosets modulo `V_d`.  Each squarefree polynomial `f`
is an edge from its input coset to its inverse coset, with sign `mu(f)`;
squareful polynomials have weight zero.  After parallel edges are collapsed,
let

`B[C,D] = sum of mu(f) over edges from C to D`.

Then the fixed-order signed energy already computed in the CAS is exactly the
squared Frobenius norm `||B||_F^2`.  Removing the exact diagonal `Q_k` gives
the connected off-diagonal correlation.  The Möbius-convolution formula is a
weighted combination of these matrices at the different orders `d`.

Equivalently, put two squarefree polynomials in the same bucket when they have
the same pair `(C,D)`.  The resulting graph on polynomials is a disjoint union
of cliques, and the connected target is the quadratic form of the fixed
Möbius sign vector on those cliques.  This makes the limitation sharper than
the general discussion below: the unsigned graph has no hidden expansion to
exploit.  All useful pseudorandomness must come from the arithmetic signing or
from a richer group action on the phase variables.

This explains both the appeal and the limitation of graph theory.  An ordinary
expander or Ramanujan bound controls a largest nontrivial eigenvalue, whereas
the present target is a centered signed second moment together with coherent
cancellation between several `d`-layers.  The
[Marcus--Spielman--Srivastava signing theorem](https://annals.math.princeton.edu/2015/182-1/p07)
shows that a good signing *exists* for broad classes of graphs, but our signing
is the fixed arithmetic Möbius signing and cannot be selected.  Ihara or
Hashimoto nonbacktracking traces could repackage the connected moments, but
would not by themselves improve them.

Graph theory becomes materially stronger if the graph is proved to be a
Heisenberg Cayley graph, a weighted strongly regular graph, or the development
of a relative difference set.  In those cases the spectrum is forced by group
representations rather than bounded by generic expansion.  Spectra of
[Heisenberg graphs over finite rings](https://www.aimsciences.org/article/doi/10.3934/proc.2003.2003.213)
and the correspondence between generalized bent functions and
[weighted Cayley graphs](https://arxiv.org/abs/1806.07601) supply plausible
templates, not yet a theorem about this particular graph.

**CAS test.**  Materialize `B` for every currently feasible `(ell,k,d)` and
record its singular values, centered Gram spectrum, and nonbacktracking trace
moments.  Check whether the nonzero singular values have one or two exact
magnitudes.  Such spectral quantization would be strong evidence for a
Heisenberg/strongly-regular description; an unstructured continuum of
magnitudes would demote the graph route to bookkeeping.

There is a second exact graph after ADR-0508: the connected integer function
`S:E_ell -> Z` defines a weighted Cayley convolution matrix, whose eigenvalues
are exactly the character transform now reported by the CAS.  The endpoint-
tail sweep for `5<=ell<=10` gives fourth-moment/flat-minimum ratios between
`1.70` and `2.99`; eleven of twelve rows have full Fourier support and the
other has at least `254/256`.  Thus this Cayley graph is not a signed
difference set, a two-eigenvalue weighted strongly regular graph, or a
plateaued spectrum.  The useful graph, if one exists, must again live before
the integer pushforward.

### 2. The random-matrix representation

Each nontrivial Hayes character has an `L`-function whose inverse roots define
a unitarized Frobenius matrix.  With the explicit normalization already used
in the main note, `Delta_(ell,n)` is a family sum of the traces of the `n`th
powers of those matrices.  The desired endpoint estimate asks for substantial
cancellation in the *average across the entire character family*, not merely
the individual Weil bound for each matrix.

This is not an attempt to prove a Riemann hypothesis.  Weil's function-field
Riemann hypothesis is exactly what already puts each Frobenius matrix on the
unitary scale and supplies the known pointwise estimate.  The missing saving
is narrower but lies beyond that theorem: remove the conductor factor by
exploiting correlations across this particular deterministic family.  Random-
matrix language predicts that extra cancellation; it does not license an
independence assumption.

More concretely, if `X_j` denotes the exact-conductor character family, a
sufficient new family theorem would have the schematic form

```text
|sum_(chi in X_j) Tr(Theta_chi^n)| <= C j^A 2^((j-1)/2),
```

uniformly over `F_2` as `j` grows with `n=2j+O(log j)`.  This is best read as
a high-power approximate unitary one-design estimate for one deterministic
arithmetic family.  A fourth-moment proof would require a stronger constrained
four-design analogue.  By contrast, applying function-field RH character by
character gives a factor roughly `j` per trace; applying it to one large
cyclotomic curve repackages the same loss in the curve's genus.  Neither
operation addresses the required cross-character cancellation.

Haar-unitary random-matrix theory predicts more cancellation than is needed,
and the exact diagonal and near-Wick shape seen in the second- and fourth-
moment computations are consistent with that prediction.  There are genuine
nearby theorems.  [Rains's high-power theorem](https://authors.library.caltech.edu/records/013c4-3kf87)
shows that sufficiently high powers of a Haar-unitary matrix have eigenvalues
distributed like independent uniform phases; this predicts trace variance of
the required size, but it is a model rather than an arithmetic independence
theorem.  Keating--Rudnick relate function-field Möbius variance to
[unitary matrix integrals](https://arxiv.org/abs/1504.03444), and
Gorodetsky--Kovaleva obtain fixed-field cancellation for special
[high-conductor character sums](https://arxiv.org/abs/2307.01344).  But the
former takes a large-field limit, while the latter exploits a special symmetry
and does not give the simultaneous all-character prime/Möbius estimate here.
Higher-moment point-counting results such as
[Hast--Matei](https://arxiv.org/abs/1604.02067) likewise keep the relevant
degree data fixed while the field grows.

The same mismatch occurs in the closest monodromy literature.
[Katz--Sawin equidistribution for Witt-vector Dirichlet characters](https://arxiv.org/abs/1805.04330)
keeps the conductor fixed while the field size tends to infinity.  Here the
field is fixed at `2`, while both conductor and trace power grow.  Local-
statistics theorems for Artin--Schreier families, such as
[Entin--Pirani](https://arxiv.org/abs/2107.02131), and slope-stability results
for Artin--Schreier--Witt towers, such as
[Davis--Wan--Xiao](https://arxiv.org/abs/1310.5311), control different regimes
or `2`-adic Newton slopes rather than the needed complex-phase cancellation.

Thus random-matrix theory currently gives the correct conjectural size and a
diagnostic, not a proof.  What would be sufficient is a quantitative
equidistribution theorem—or approximate unitary 4-design statement—for this
wildly ramified family, uniform when the matrix dimension, conductor, and
trace power all grow over `F_2`.  Proving that through monodromy may be
possible, but it is essentially a new theorem rather than an invocation of a
standard Katz-style limit.

#### A more credible geometric refinement: short-interval cohomology

The strongest independent geometric route found in this audit is
[Sawin's complete-intersection treatment of primes in short intervals](https://arxiv.org/abs/1809.05137).
It replaces a sum over individual character bounds by one geometric object
carrying a virtual representation of the symmetric group.  That is precisely
the sort of connected packaging the present proof needs.

The published generic Betti estimate is still too large at `q=2`.  However,
specializing Sawin's weight calculation to the two Lemire endpoints suggests
a meaningful remaining margin: the Frobenius-weight contribution is roughly
`2^(3 ell/4)`, leaving on the order of `2^(ell/4)` for the *effective virtual*
Betti multiplicity before the desired `2^ell` scale is lost.  This numerical
budget is an inference from Sawin's framework and the endpoint exponents, not
a theorem stated in the paper.  A polynomial bound—or even a bound below that
exponential budget—for the cancellations in the virtual representation
`lambda_(-1)(std)` could therefore settle all sufficiently large degrees,
with the existing exact certificates covering the finite remainder.  This
would be a new cohomological multiplicity theorem, not a new theorem about
zeta zeros.

#### Exact long-cycle and cyclic/Foulkes compression

The special virtual representation has substantially more structure than the
generic regular-representation estimate uses.  Put

```text
V_n = lambda_(-1)(std) = sum_i (-1)^i wedge^i(std).
```

For a permutation `g`, its character is `det(1-g | std)`: it is `n` when
`g` is one `n`-cycle and zero otherwise.  Equivalently, its Frobenius
characteristic is exactly the primitive power sum

```text
ch(V_n) = p_n = sum_i (-1)^i s_(n-i,1^i).
```

This is the representation-theoretic version of the logarithmic-derivative/
connected recurrence already used by the Axeyum proof.  More importantly,
if `X` is Sawin's ordered-root space and `sigma` is one fixed long cycle, the
group-averaging formula gives the exact trace compression

```text
Tr(Frob^r | (R Gamma_c(X) tensor V_n)^(S_n))
  = Tr(Frob^r sigma | R Gamma_c(X)).
```

Indeed there are `(n-1)!` long cycles and their contribution is
`n (n-1)!/n! = 1`.  Thus the correct geometric object is one
Frobenius--long-cycle correspondence, not two enormous positive complexes
obtained by splitting the exterior powers into even and odd parity.
[Hast--Matei](https://arxiv.org/abs/1604.02067) use the same fixed-cycle model
for von-Mangoldt-type factorization statistics.

There is a complementary rank-one decomposition.  Let `C_n=<sigma>`, let
`theta_r(sigma)=zeta_n^r`, and put
`F_(n,r)=Ind_(C_n)^(S_n) theta_r`.  Fourier inversion of the generator
indicator on `C_n` gives

```text
p_n = sum_(r mod n) c_n(r)/phi(n) F_(n,r),
```

where `c_n(r)` is the Ramanujan sum.  Its total coefficient cost is exactly

```text
(1/phi(n)) sum_(r mod n) |c_n(r)| = 2^omega(n) = n^o(1).
```

By Frobenius reciprocity, every term is a rank-one `C_n` eigenspace or local-
system problem.  This is the useful part of the Foulkes representation; see
[Shareshian--Sundaram](https://arxiv.org/abs/2305.12007) for the modern
Ramanujan-sum formulation.  The subpolynomial coefficient mass is far below
the inferred `2^(ell/4)` endpoint budget.

This compression is not yet a bound.  Each induced Foulkes module has
dimension `(n-1)!`, and the relevant cyclic eigenspace of compactly supported
cohomology may still be large.  Partition-lattice and free-Lie descriptions
do not fix that: their underlying modules can have the same factorial size,
and `p_n` is not a single free-Lie module.  A sufficient new theorem is a
polynomial, or otherwise sub-`2^(ell/4)`, bound for the **effective** sum of
the `C_n`-eigenspace Betti multiplicities, or directly for the long-cycle
Frobenius trace.  This is a precise target for revisiting Sawin's geometry;
it is not licensed by the existing generic Betti estimate.

The equivariant Koszul resolution supplies a concrete algebraic hint.  On the
homogeneous complete-intersection fibre
`Spec R/(e_1,...,e_m)`, a long cycle `sigma` has graded coherent trace

```text
sum_d Tr(sigma | (R/(e_1,...,e_m))_d) t^d
  = product_(i=1)^m (1-t^i) / (1-t^n).
```

The numerator is dramatically smaller than the parity-split exterior
complex; [Galetto--Geramita--Wehlau](https://arxiv.org/abs/1604.01101)
provide the general symmetric-complete-intersection character framework.
This is not yet the required theorem: it is a coherent Hilbert-series
identity, not compactly supported `l`-adic cohomology of the singular cone in
characteristic two.  The actionable bridge is to seek an equivariant
stratification or nearby-cycles argument that transfers this long-cycle
cancellation without replacing it by total Betti numbers.

#### Extension-field zeta diagnostic and its boundary

The long-cycle virtual trace can be measured without guessing its
cohomology.  For the correct non-strict Lemire interval over `F_(2^r)`, let

```text
h = floor(n/2)+1,
A_r(n) = sum_(f=x^n+terms of degree < h) Lambda(f) - (2^r)^h.
```

An isolated exact finite-field probe, using independent polynomial arithmetic,
irreducibility, prime-power recognition, and von Mangoldt weights, gives:

| `n` | `h` | fixed leading coefficients | exact observed `A_r` |
|---:|---:|---:|---|
| 3 | 2 | 1 | `0` for `1<=r<=3` |
| 4 | 3 | 1 | `0` for `1<=r<=3` |
| 5 | 3 | 2 | `(-4)^r-(-2)^r` for `1<=r<=7` |
| 6 | 4 | 2 | `0` for `1<=r<=3` |
| 7 | 4 | 3 | `8^r-2^r` for `1<=r<=4` |
| 8 | 5 | 3 | `8^r-16^r` for `1<=r<=4` |
| 9 | 5 | 4 | `5,129,-1771,-3855,-28675` for `r=1,2,3,4,5` |

The final degree-nine value exhausts all `32^5=33554432` interval
polynomials over the field represented by `x^5+x^2+1`; its raw Mangoldt sum
is `33525757`.  These are scratch-probe results and should be ported into a
bounded native report before they are used as durable theorem evidence.

For `n=5,7,8`, these sequences have only two Frobenius modes; their reduced
virtual error factors are respectively

```text
(1+2t)/(1+4t),   (1-2t)/(1-8t),   (1-16t)/(1-8t).
```

This is strong evidence that the virtual long-cycle cohomology can be much
smaller than raw cohomology.  It also exposes the stopping boundary.  The
first rows fix at most three leading coefficients, exactly the setting where
the characteristic-two trace curves in
[Ahmadi--Gologlu--Granger--McGuire--Yilmaz](https://arxiv.org/abs/1605.07229)
and [Gorodetsky](https://arxiv.org/abs/1805.07105) decompose into supersingular
pieces.  Degree nine is the first row fixing four leading coefficients.  Its
first four values determine the only possible order-two recurrence over the
rationals; it predicts `A_5=905218847/3187`, whereas exact enumeration gives
`A_5=-28675`.  Thus even an unrestricted two-mode recurrence is false, not
merely a two-root monic integral factor.

[Granger](https://arxiv.org/abs/1610.06878) computes the four- and five-
coefficient binary zeta functions and finds ordinary abelian factors, so the
resulting formulas are no longer periodic.  This matches the observed
transition.  His Artin--Schreier batching method remains highly relevant for
computing the next virtual factors, but supersingularity cannot be the
uniform half-degree theorem as the number of fixed coefficients grows.

The next decisive experiment is therefore not merely another value at `r=1`.
Compute enough `A_r(n)` to recover the reduced virtual zeta factor by exact
Padé/Berlekamp--Massey reconstruction, then plot numerator-plus-denominator
degree against `n`.  Bounded or polynomial growth would support the long-cycle
cohomology route; exponential growth near the available endpoint margin would
reject it.  These zeta functions are finite-field bookkeeping devices.  This
route uses the proved Weil--Deligne Riemann hypothesis as an input and does
not ask for the classical Riemann hypothesis.

**CAS tests.**

1. Compute exact-conductor trace means, covariances, and fourth cumulants near
   `n=2j`.  The high-power Haar model predicts variance `j-1` and fourth
   moment `2(j-1)^2-(j-1)`.
2. Fourier-decompose the trace function by determinant or root number,
   character order, top Witt block, and Galois orbit.  Stable low-dimensional
   modes would expose the exceptional monodromy quotient; full Fourier support
   of the collapsed connected function does not rule these out.
3. Continue the exact extension-field trace sequence at `n=9` and the next
   feasible degrees.  Recover the reduced rational zeta factor and record its
   degree, slopes, and reciprocal-root magnitudes rather than fitting a
   recurrence from too few terms.
4. Continue computing mixed moments between different orders `d`.  Agreement
   with Haar moments is evidence for where to seek a theorem, not permission
   to replace the deterministic family by independent matrices.

### 3. Generalized bent functions, codes, and difference sets

Each exact affine fibre carries a generalized Boolean function
`q:F_2^r -> Z/8`, but the connected object on `E_ell` does **not**.  It is the
integer-valued pushforward `S` obtained only after summing the eighth-root
phases over many different affine fibres.  The blockwise Verschiebung aligns
their normalized parameters; it does not supply one common phase domain or a
group law on the phase variables.

ADR-0508 makes this distinction measurable.  At `(ell,k,d)=(9,11,8)`, all
`512` Fourier coefficients of `S` are nonzero.  A flat spectrum would have
fourth moment

```text
512 * 126568^2 = 8201962815488,
```

but the exact fourth moment is `20409844301824`, larger by a factor
`2.4884097576`.  Consequently the computed connected pushforward is neither
bent nor plateaued.  It cannot itself be the generalized-bent object sought
in the earlier version of this note.

The live lane has now also retained the residue histogram modulo eight at
each embedded Witt class and transformed all four primitive phases
`zeta_8^(jr)`, for `j=1,3,5,7`.  In the pinned row every one of the `512`
characters is nonzero modulo both transform primes for **each** primitive
phase, and the checked Gauss combination reconstructs the signed transform
character by character.  This rules out a second simple explanation: neither
the real pushforward nor any individual primitive phase becomes sparse after
Fourier transform.  It does not test complementary cancellation among their
magnitudes or cross-correlations.

This bridge is unusually promising because generalized-bent theory already
relates flat Walsh spectra to component Boolean functions, codes, and relative
difference sets; see the
[complete characterization for `Z/(2^k)`-valued functions](https://arxiv.org/abs/1605.05713).
The terminology needs one qualification: ordinary generalized bentness only
controls the primitive output character.  A relative-difference-set
interpretation requires the stronger `Z_q`-bent condition, which controls all
nonzero output characters.
The remaining opportunity is narrower: retain the affine coordinate, shift,
inverse-difference, and Witt parameter before pushforward, and find a larger
joined group on which the original unit-valued phase is generalized bent or
quadratic.  Individual nonquadratic fibres do not logically rule that out,
but they do rule out obtaining it by applying a quadratic Gauss-sum theorem to
each current fibre separately.

**CAS test.**  First apply the exact `Z/8` component-function criteria to every
affine fibre and aggregate the failures by valuation and normalized parameter.
The four cyclotomic transforms are now retained far enough to prove full
support and check their Gauss recombination.  Extend that report to exact
phase-to-phase inner products, individual spectral moments, and summed
spectral power.  Only if those data suggest a closed joined domain should the
CAS test a proposed group law, flatness, radical, dual phase, and relative-
difference-set identities.  Re-transforming the already collapsed `S_v(a)`
cannot answer this question.

#### A weaker coding target: a complementary family

The failure of single-function bentness suggests a more flexible coding
identity.  The CAS now constructs four connected primitive-phase functions
`T_j`, for `j=1,3,5,7`, before recombining them into `chi_8`, and proves that
each has full modular Fourier support in the pinned row.  Full support does
not decide the weaker condition that matters here.  It would suffice for
their autocorrelations to be complementary:

```text
sum_j T_j * T_j^*  is concentrated at the identity,
```

or, equivalently, for `sum_j |Fourier(T_j)(chi)|^2` to be constant or uniformly
bounded in `chi`.  This is the generalized-Boolean analogue of a Golay
complementary set; [Schmidt](https://arxiv.org/abs/cs/0611160) develops the
phase-function construction.  It fits the observed mathematics better than
demanding that the collapsed sum be bent, because cancellation is already
known to occur only after several phase and valuation sectors are joined.
There are only four cyclotomic sectors, so a final Cauchy step would cost a
constant rather than a growing factor in `ell`.

A related, stronger signal would be a Kerdock family after an auxiliary-
variable lift: pairwise phase differences would be quadratic with uniformly
bounded radicals.  The classical `Z/4` precedent is the
[Hammons--Kumar--Calderbank--Sloane--Sole construction](https://doi.org/10.1109/18.312154).
The current high-degree fibre phases rule this out in the existing coefficient
coordinates, but not after a genuine phase-resolved lift.

#### Exact stopping test: the four phases are not complementary

The four-phase data admit an exact integer-only complementarity test.  Let
`n_r(a)` be the number of points with residue `r mod 8` above the connected
Witt class `a`, and set

```text
u_r(a) = n_r(a)-n_(r+4)(a),    0<=r<4.
```

The Ramanujan sum over the four odd residues modulo eight is `4`, `-4`, or
`0` according as the residue difference is `0`, `4`, or neither.  Therefore

```text
sum_(j=1,3,5,7) T_j*T_j^* = 4 sum_(r=0)^3 u_r*u_r^*.
```

This removes all cyclotomic arithmetic from the test.  If
`C(s)=sum_r sum_a u_r(a)u_r(a+s)`, the four phases are complementary exactly
when `C(s)=0` away from the identity.  Equivalently, the exact flatness ratio

```text
R_comp = sum_s C(s)^2 / C(0)^2
```

must equal `1`.

An isolated Axeyum probe at both endpoint-tail rows `d=ell-1` gives:

| `ell` | `k` | `R_comp` | `max_(s!=0) |C(s)|/C(0)` |
|---:|---:|---:|---:|
| 5 | 7 | 2.624523 | 0.626953 |
| 5 | 8 | 4.408098 | 0.752375 |
| 6 | 8 | 5.612483 | 0.637005 |
| 6 | 9 | 6.047375 | 0.590560 |
| 7 | 9 | 9.860877 | 0.782105 |
| 7 | 10 | 11.275965 | 0.800880 |
| 8 | 10 | 16.564322 | 0.711074 |
| 8 | 11 | 15.907433 | 0.689391 |
| 9 | 11 | 26.891435 | 0.773548 |
| 9 | 12 | 32.320392 | 0.788478 |
| 10 | 12 | 94.119621 | 0.875180 |
| 10 | 13 | 97.662537 | 0.889212 |

Thus the current four connected phases are not a Golay or supplementary
complementary family, and the deficit worsens rather than stabilizes in this
sweep.  At the pinned `(9,11,8)` row, `C(0)=13942624`, while the signed spatial
second moment is only `126568`: an unweighted Cauchy step across the four
phases reintroduces a squareful even-residue channel more than one hundred
times larger than the signed channel which the dyadic Gauss combination
cancels exactly.  The useful next object cannot be the positive sum of four
spectral powers.  It must retain the **indefinite cross-phase cancellation**
in the checked Gauss combination, or find a larger group law on which that
combined phase is quadratic.

There is also a sharp association-scheme stopping theorem behind these
numbers.  Order the primitive phases by `j=1,3,5,7`, put
`c=(1,-1,-1,1)`, and let `K_s(j,j')` be their full phase-to-phase
cross-correlation matrix at shift `s`.  The signed autocorrelation is exactly

```text
A_S(s) = (1/8) c^* K_s c.
```

At the pinned origin, `trace(K_0)=55770496` whereas
`c^*K_0c=1012544`, giving `A_S(0)=126568`.  Almost all useful cancellation is
therefore in the off-diagonal phase terms.  After squaring, the exact selector
is the positive rank-one projector `cc^*`.  Inverse odd Fourier transform
sends its image to precisely the signed line whose energy is `sum_a S(a)^2`.
Any larger positive-semidefinite Delsarte or Krein projector restores an
orthogonal even/squareful channel; the minimal projector simply returns the
original signed-energy problem.  An indefinite surrogate loses the positivity
on which the linear-programming bound depends.  Consequently a matrix-valued
weight enumerator can preserve the data, but does not create a new inequality.

The equivalent graph construction is an unsigned double cover.  Route every
squarefree edge to one of two sheets according to its Möbius sign.  The
deck-invariant sector counts the squarefree population and the anti-invariant
sector is exactly the signed incidence matrix.  This is a faithful positive
Hilbert-space representation, but bounding its arithmetic anti-invariant
sector is the same open problem.  The only coding-theoretic survivor that is
not such a unitary rewrite is to retain the second-trace quadratic form
`q_f` itself.  Put all `q_f` on a canonical binary space and measure the rank
and Arf type of every difference `q_f-q_g` inside a simultaneous coefficient/
inverse bucket.  If the inner distribution has boundedly many rank/type
classes, the quadratic-form association scheme or Kerdock machinery may
control the Arf imbalance.  If the number of classes or coherent-closure rank
grows rapidly, the coding lane should stop.

#### A viable replacement: the auxiliary-unit Gauss projector

The failure of positive complementarity does **not** destroy the exact
cross-phase cancellation.  It can be internalized by one additional group.
Let

```text
A = (Z/8Z)^x = <3,5> ~= F_2^2,
a = 3^u 5^v = 1+2u+4v (mod 8),
chi_8(a) = (-1)^(u+v).
```

For a fixed discriminant residue `D mod 8`, normalize the summand as

```text
Q_D(u,v) = chi_8(a) zeta_8^((a-1)D)
         = zeta_8^(2(D+2)u + 4(D+1)v).
```

Although the exponent looks linear in the Boolean coordinates, the carries
in the `F_2^2` group law give the exact polarization

```text
B_D((u,v),(u',v')) = (-1)^(D u u').
```

If `D` is odd, the radical is `{u=0}={1,5}` and `Q_D` is trivial there, so
the Gauss sum has magnitude `sqrt(4*2)=2 sqrt(2)`.  If `D` is even, the
polarization is trivial but `Q_D` is a nontrivial character, so its sum is
zero.  Hence the dyadic projector is literally the degenerate quadratic Gauss
identity

```text
sum_(a in A) chi_8(a) zeta_8^(aD)
  = 2(zeta_8-zeta_8^3) chi_8(D).
```

This is the important conceptual gain: the squareful zeros and the signs of
the odd residues are produced coherently by one auxiliary Gauss sum, rather
than recovered by a positive estimate across four disjoint phases.

There is an exact criterion for extending it.  Let `M` be a finite abelian
group, let `D:M -> Z/8Z`, put `D_0=D(0)` and `d(x)=D(x)-D_0`, and define

```text
Q(x,a) = chi_8(a) zeta_8^(a D(x)-D_0)   on G=M x A.
```

Summing out `A` recovers the desired signed sum, up to the known scalar.  The
single phase `Q` is quadratic on the direct product exactly when

1. `x |-> zeta_8^d(x)` is quadratic on `M`; and
2. `d mod 4` is a homomorphism from `M` to `Z/4Z`.

If its radical is `R`, Takeuchi's finite quadratic Gauss theorem gives, in
the nonzero case,

```text
abs(sum_x chi_8(D(x))) = sqrt(|M| |R| / 2).
```

Thus a uniformly bounded radical would produce the required square-root
scale.  The direct-product version cannot repair the existing nonquadratic
affine fibres: restriction to the `a=1` slice is still quadratic, while the
pinned row contains thousands of genuinely nonquadratic fibres, including
support degree seven.  One exact witness at `(ell,k,d)=(9,11,8)`, packed
shift `96`, input coset `0`, and inverse difference `192` has dimension seven
and top ANF coefficient `6 mod 8`; the committed fibre test independently
certifies its twice-odd coefficient class.  The viable test is consequently
very specific.  In an independent exact reproduction the fibre is

```text
F_t = x^11+1+sum_(j=0)^6 t_j x^(j+2),
D_t = Disc(F_t) Disc(F_(t xor 48)) mod 8,
```

and the full Boolean subset-Möbius coefficient of `D_t` is `6 mod 8`.
The XOR is essential: adding `x^6+x^7` to the integral lift is not binary
coefficient toggling when a coefficient is already one.  A new group law must
mix the affine-fibre, valuation, and Witt coordinates so
that a bad individual fibre is not a subgroup.  For any proposed law, test
`d(x+y)=d(x)+d(y) mod 4` first, then full polarization and radical size.  If
that fails, the remaining version must be a genuinely nonabelian Heisenberg
matrix coefficient rather than an abelian quadratic Gauss sum.

### 4. Heisenberg and Weil representations

In characteristic two, a quadratic or generalized-quadratic phase defines a
central extension through its translation commutator.  If that alternating
commutator form has a bounded radical, Stone--von Neumann theory makes the
nontrivial Fourier pieces irreducible and forces Gauss-sum-sized matrix
coefficients.  The characteristic-two construction is subtle—the natural
quadratic data lift to length-two Witt vectors—but a complete Weil
representation is available in
[Gurevich--Hadani](https://arxiv.org/abs/0808.1664).  The recent use of
Heisenberg groups to decompose characteristic-two Artin--Schreier curves in
[Ito--Takeuchi--Tsushima](https://arxiv.org/abs/2505.22036) is especially close
to the geometry already visible here.

The unresolved issue is that the current phase uses eighth roots and appears
to require a length-three, rather than length-two, Witt extension.  We have the
raw ingredients—the Witt coordinates, translation derivatives, normalized
parameters, and connected fibre sum—but not the theorem that their commutator
has uniformly bounded radical.  If the radical calculation succeeds, existing
representation theory is likely to do much of the remaining fixed-order work.
The cross-order Möbius sum must still be built into the same representation or
handled by a final orthogonality argument; proving each order separately and
adding absolute values recreates the known loss.

There is a simpler theorem to target before constructing a full Weil
representation.  [Takeuchi, Proposition A.2](https://arxiv.org/html/2305.15164v1#A1)
works for an arbitrary finite abelian group `M`: if a unit-valued function `Q`
has bilinear polarization

```text
B_Q(x,y)=Q(x+y)/(Q(x)Q(y))
```

and `B_Q` is perfect, then the Gauss sum of `Q` has magnitude `sqrt(|M|)`.
With a radical `R`, the same orthogonality calculation gives either zero or a
factor `sqrt(|R|)` beyond square root, depending on the restriction of `Q` to
`R`.  Thus the exact missing statement is not initially a new `W_3` Weil
representation: it is a phase-resolved finite abelian group law, bilinearity,
and a uniformly bounded radical.  A Heisenberg extension becomes useful only
after those properties have been verified.

### 5. Martingales and harmonic analysis

The exact-conductor filtration is already a dyadic filtration: the differences
between successive conductor truncations are Haar/martingale increments, and
the nonnegative energy increments are its square function.  This is a precise
representation, not an analogy.  Generic Burkholder, Rosenthal, or
hypercontractive inequalities do not close the proof, because they require a
uniform conditional-variance, bounded-increment, or low-Fourier-degree input.
The current phase has full algebraic degree, and the required conditional
square-function estimate is essentially the missing arithmetic theorem.

This route remains a good fallback if the CAS reveals a sparse exceptional
set rather than exact spectral flatness.  The useful statement would be a
Carleson-type estimate saying that the connected energy placed below every
Witt cylinder is controlled uniformly by the cylinder's mass.  That local
condition is stronger and more testable than another global fourth-moment
bound, and standard martingale machinery could then sum the conductor layers.

### 6. Other exact translations, with lower current priority

#### Sparse companion matrices and LFSRs

The original conjecture says that the affine family of companion matrices
whose upper feedback taps vanish contains a matrix with irreducible
characteristic polynomial.  Equivalently, a random polynomial in Lemire's
coefficient subspace has positive probability of being irreducible.  This is
an exact random-matrix/LFSR reformulation, but not an independent source of
cancellation: a companion matrix's characteristic polynomial is the sampled
polynomial itself.  Universality results for matrices with many independent
entries, such as
[Luh--Meehan--Nguyen](https://arxiv.org/abs/1907.02575), do not cover a matrix
with only one partially random row.  A theorem for this sparse companion
ensemble would essentially be the desired restricted-coefficient prime
theorem.

#### Configuration spaces and arithmetic topology

Let `m=floor(n/2)` and regard the allowed polynomials as an affine parameter
space of dimension `m+1`.  Removing the discriminant hypersurface gives the
squarefree locus; adjoining the ordered roots gives an `S_n`-cover; and an
irreducible specialization is exactly a rational point whose Frobenius is an
`n`-cycle.  This is a clean Chebotarev/configuration-space formulation.

For the unrestricted squarefree-polynomial space, twisted
Grothendieck--Lefschetz and representation stability do control many
factorization statistics; see
[Church--Ellenberg--Farb](https://arxiv.org/abs/1309.6038).  They do not
currently control this moving half-dimensional linear section or the moving
`n`-cycle indicator at `q=2`.  To make this route effective one would need a
uniform bound on the relevant compactly-supported Betti numbers strong enough
that the Chebotarev error is smaller than `2^(m+1)/n`.  No such bound is now in
hand, and a generic degree-based bound would be far too large.

**Cheap test.**  Compute the generic Galois group of
`x^n+a_m x^m+...+a_0` for small symbolic `n` in characteristic two.  If it
fails to contain an `n`-cycle infinitely often, the route dies.  If it is
consistently `S_n`, compute point counts of the discriminant complement and
the first twisted cohomological errors, looking for a stable recurrence before
investing in topology.

#### Codes for Kloosterman moments

Binary and quaternary codes can turn exponential-sum moments into weight-
enumerator identities through the Pless power-moment relations.  This is a
real precedent for characteristic-two Kloosterman families; for example,
[Kim](https://arxiv.org/abs/0807.3991) obtains recursive power moments from
binary codes attached to finite groups.  For the current problem one would
repeat each phase-state with its signed multiplicity, let Witt characters
index codewords, and ask whether the resulting `Z/8` code has a simple dual
weight distribution.  Without a few-weight or bounded-dual-distance theorem
this only re-encodes the spectral moments, but the weight distribution is a
useful diagnostic for the Kerdock/complementary-family hypothesis.

#### Higher-order Fourier analysis and nilspaces

An eighth-root phase in characteristic two naturally belongs to the theory of
nonclassical polynomial phases.  The low-characteristic inverse theorem of
[Tao--Ziegler](https://arxiv.org/abs/1101.1469) explains why such phases arise
from large Gowers norms.  It does not currently give the required estimate:
the discriminant phase has proven algebraic support degree growing with `k`,
whereas useful inverse and bias-versus-rank bounds are uniform for fixed
degree.  This route becomes interesting only if the phase-resolved lift makes
the relevant *nonclassical* degree bounded even though the coefficient ANF
degree is large.

#### Discriminants and prehomogeneous-vector-space Fourier transforms

There are explicit Fourier-transform theorems for relative invariants of
prehomogeneous vector spaces, including finite-ring versions such as
[Cluckers--Herremans](https://www.numdam.org/item/BSMF_2007__135_4_475_0/).
They assume a sufficiently large residue characteristic, while the present
prime is `2`; moreover the space of general degree-`n` monic polynomials is not
a fixed prehomogeneous representation as `n` grows.  This literature is a
useful model for what an exact discriminant transform would look like, but it
does not presently furnish one for the binary half-coefficient family.

### Recommended order of attack

1. Certify the auxiliary-unit identities in the native CAS.  Then propose a
   joined fibre/valuation/Witt group law and apply the cheapest necessary test
   first: `d mod 4` must be additive.  Only a survivor merits full
   polarization, radical, and Heisenberg calculations.
2. In parallel, preserve each second-trace quadratic form and compute the
   rank/type distribution of pairwise differences inside simultaneous
   coefficient/inverse buckets.  Stop the coding lane if the number of types
   or coherent-closure rank grows rapidly.
3. Replace Sawin's parity-split exterior-power estimate by the exact fixed-
   long-cycle trace or cyclic/Foulkes decomposition.  Compute enough
   extension-field traces to recover reduced virtual zeta factors, beginning
   at the four-fixed-coefficient boundary `n=9`, and measure their degree
   growth against the inferred `2^(ell/4)` margin.
4. Build signed incidence matrices only to search for additional group
   structure.  Generic graph expansion, positive complementary energies, and
   association-scheme projectors are now stopped: they either admit the fatal
   even channel or reduce exactly to the signed energy.
5. Extend `M2/M4/K4` to mixed conductor/order moments and test the martingale
   Carleson condition only if a small exceptional mode or locally regular
   energy emerges.  Random-matrix predictions remain diagnostics, not proof
   inputs.

The bottom line is therefore asymmetric.  We **do** have enough exact
structure to translate the problem faithfully into graphs, codes, and
Frobenius traces, and enough CAS machinery to reject representations that lose
the crucial cross-phase cancellation.  We **do not** currently have an
applicable generic theorem in any of those fields.  The best chance that an
existing body of theory supplies the decisive estimate is now the
**auxiliary-unit quadratic projector joined to a new group law**.  The
projector itself is exact; the joined law and bounded radical are open.  The
collapsed connected function, the individual additive phases, and positive
complementarity have all failed their stopping tests.

The strongest independent route is the exact Frobenius--long-cycle/cyclic-
Foulkes compression inside Sawin's short-interval geometry.  It replaces a
huge generic representation bound by a subpolynomial coefficient cost, but
still needs a new effective cyclic-eigenspace cohomology theorem.  Small
extension-field zeta factors show that this compression can be dramatic;
ordinary factors beginning with four prescribed coefficients warn that it is
not automatically uniform.  Without one of these two structural inputs,
graph, code, random-matrix, and martingale language mostly restates the signed
energy or fourth-cumulant target.
