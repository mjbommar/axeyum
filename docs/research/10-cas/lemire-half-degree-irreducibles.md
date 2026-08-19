# Lemire half-degree irreducibles: theorem and Axeyum research contract

Status: active research
Date: 2026-08-18

## Exact target

For every integer `n >= 1`, prove that there is a monic irreducible
`f in GF(2)[x]` of degree `n` such that

```text
deg(f - x^n) <= floor(n / 2).
```

This is the conjecture stated in section 4.1 of Lemire and Kaser,
[Strongly universal string hashing is fast](https://arxiv.org/abs/1202.4961).
The social-post phrase "less than `floor(n/2)`" cannot be the all-degree
theorem: at `n = 2` it permits only `x^2 + 1`, which is reducible.  All Axeyum
claims and experiments use the paper's non-strict bound.

The application is a sparse high half: reduction by `f` replaces `x^n` with a
polynomial of degree at most `floor(n/2)`, making the correction step in
Barrett-style binary-polynomial reduction cheap.

## Reciprocal reformulation

Put `m = floor(n/2)` and let

```text
f(x) = x^n + q(x),    deg q <= m.
```

Its reciprocal `g(x) = x^n f(1/x)` is irreducible exactly when `f` is and
satisfies

```text
g(x) == 1 (mod x^(n-m)) = 1 (mod x^ceil(n/2)).
```

Conversely, every monic irreducible degree-`n` polynomial in that residue class
reciprocates to a polynomial of the required form.  The conjecture is therefore
equivalent to the existence, in every degree, of a prime polynomial in the
identity ray class modulo `x^ceil(n/2)`.

This lemma is elementary and should be the first lemma in a short paper.  It
also explains the difficulty: the prescribed-coefficient interval is exactly
at the half-degree boundary, where general short-interval estimates over fixed
`GF(2)` do not immediately give positivity.

## Backward proof plan for a paper under five pages

1. State the exact theorem and prove the reciprocal equivalence.
2. Prove a single central counting or construction lemma: for every `n`, a
   degree-`n` irreducible is `1 mod x^ceil(n/2)`.
3. Discharge any finite exceptional range with independently checked Axeyum
   certificates, and state the exact checker and artifact hashes.
4. Apply reciprocity and give the Barrett-reduction corollary.

The missing mathematics is step 2.  Numerical verification, including Arndt's
reported range through 400, is evidence about the conjecture but is not that
lemma.

## Literature boundary

- Lemire's [MathOverflow question](https://mathoverflow.net/questions/81717/)
  records the problem and its relationship to prescribed coefficients and
  short intervals.
- Bank, Bary-Soroker, and Rosenzweig prove a prime-polynomial theorem in short
  intervals in the large-field regime, not the required fixed field
  `q = 2`: [Prime polynomials in short intervals and in arithmetic
  progressions](https://arxiv.org/abs/1302.0625).
- Pollack's prescribed-coefficient results do not reach this fixed-field
  half-degree boundary: his theorem permits fewer than
  `(1-epsilon) sqrt(n)` arbitrary coefficients, not a linear half of them.
  See [Irreducible polynomials with several prescribed
  coefficients](https://www.pollack-math.net/prescribed.pdf).
- A sentence in Gao, Howell, and Panario's 1999 survey says that Hsu's theorem
  permits the lower or higher "half" of the coefficients to be fixed. The
  explicit bound is not an endpoint existence theorem for fixed `q = 2`.
  Car's restatement of Hsu gives, for `k` prescribed leading coefficients and
  no trailing congruence,

  ```text
  n I(n; k) >= q^(n-k) - (1-q^(-k))(k+3)q^(n/2).
  ```

  At `k = ceil(n/2)-1` this lower bound is negative for all sufficiently large
  `n` when `q = 2`. Thus the survey's informal "half" must not be cited as a
  proof of this conjecture.  Garefalakis gives the same classical consequence
  in an especially transparent form: prescribing `m` lower coefficients is
  guaranteed when `q^(n/2) >= (m+1)q^m`, i.e. only roughly
  `m <= n/2-log_q n`, and explicitly distinguishes this from the endpoint.
  See Hsu,
  [The Distribution of Irreducible Polynomials in
  F_q[t]](https://doi.org/10.1006/jnth.1996.0139), and Car's explicit
  [restatement](https://eudml.org/doc/207235), as well as
  [Irreducible polynomials with consecutive zero
  coefficients](https://users.math.uoc.gr/~tgaref/content/static/publications/paper-ffa-final.pdf),
  Corollary 1.
- The 2003 AIM workshop notes contain an even more tempting unsupported
  remark: for `m=n`, Gao's relaxed `x^m+g` problem is said to be proved with
  `deg g <= n/2`.  The note gives no theorem, author, or reference for that
  sentence.  Read literally it is this conjecture.  The same wording can be
  traced to Gao--Howell--Panario's 1999 survey, which says that Hsu permits the
  lower or higher "half" to be fixed.  But a detailed later exposition of
  Hsu's consequence states the actual condition
  `m < n/2 - log_q(n)` and describes it only as "roughly half."  The AIM
  sentence is therefore inherited shorthand, not an endpoint theorem.  See
  [Future directions in algorithmic number
  theory](https://aimath.org/WWN/primesinp/articles/html/38a/), Problem 7,
  Remark 4; Gao--Howell--Panario,
  [Irreducible polynomials of given
  forms](https://www.math.clemson.edu/~sgao/papers/GHP99.pdf), page 2; and
  Tzanakis's detailed [On the existence of irreducible polynomials with
  prescribed coefficients over finite
  fields](http://repository.library.carleton.ca/downloads/rr171x85d),
  Corollaries 3.1.4 and 3.1.6.  A share-ready proof may mention this ambiguity
  in a footnote, but may not take mathematical credit from it.
- Gao, Kuttner, and Wang's exact Hayes-class formulas reach the relevant
  parameter boundary and are the best current attack surface:
  [Counting irreducible polynomials with prescribed coefficients over a finite
  field](https://arxiv.org/abs/2109.02000). Gao's later
  [improved error bounds](https://arxiv.org/abs/2109.14154) still do not prove
  positivity here. With `ell = ceil(n/2) - 1`, `q = 2`, and the identity type-II
  class, the main term and the published absolute error are of the same
  exponential order; the coefficient multiplying the error is too large.
- Gao's 2023 follow-up obtains existence with *roughly* half the coefficients
  prescribed, including positions near the middle, but does not state the exact
  all-degree fixed-`GF(2)` endpoint needed here: [New Estimates and Existence
  Results About Irreducible Polynomials and Self-Reciprocal Irreducible
  Polynomials with Prescribed Coefficients Over a Finite
  Field](https://doi.org/10.1007/s44007-023-00062-1).
- Gorodetsky and Kovaleva obtain unusually strong cancellation for the special
  primitive character `chi_(k,psi)` modulo `x^(k+1)`, but their Theorem 1.5
  sums over all monic polynomials and explicitly leaves the restriction to
  irreducibles open. Their von-Mangoldt Corollary 3.9 handles one special
  power-sum character, whereas the layer `T_(j,n)` below aggregates every
  character of exact conductor `x^(j+1)`. It therefore does not supply the
  missing family cancellation: [Equidistribution of high traces of random
  matrices over finite fields and cancellation in character sums of high
  conductor](https://doi.org/10.1112/blms.13057).
- Sawin's stationary-phase analysis of wild hyper-Kloosterman sums is a direct
  warning against replacing the missing aggregate estimate by generic
  square-root cancellation for each convolution order.  In equal
  characteristic `p`, divisor-like short-interval sums can exceed the
  square-root scale when their order is divisible by `p`.  This does not bound
  the signed logarithm used here, but it confirms that its cross-order
  cancellation cannot be discarded: [The size of wild Kloosterman sums in
  number fields and function fields](https://arxiv.org/abs/2209.02170).

There is also no reduction of the family size to the odd power traces. In
characteristic two, Newton's identities make the even power traces Frobenius
squares of earlier traces, but they do **not** recover the even elementary
coefficients. Those coefficients carry genuine Witt-vector data. Consequently
the `2^(j-1)` exact-conductor family below cannot be replaced by only about
`2^(j/2)` ordinary additive characters without an additional theorem.

### Exact integral specialization

Complex characters are not required to state the exact recurrence. Let

```text
E_ell = (1 + x GF(2)[x]) / (x^(ell+1))
S_ell = sum_{epsilon in E_ell} epsilon
A_d   = sum_{f monic, deg f = d} <f>  in Z[E_ell].
```

The coefficient classes are injective below `ell` and uniform from `ell`
onward, so

```text
A_d = sum of the 2^d represented classes,       d < ell,
A_d = 2^(d-ell) S_ell,                          d >= ell.
```

For `A(z) = sum A_d z^d`, define
`Lambda(z) = z A'(z) / A(z) = sum Lambda_d z^d`. Comparing coefficients in
`Lambda(z) A(z) = z A'(z)` gives the exact group-ring recurrence

```text
Lambda_n = n A_n - sum_{i=1}^{n-1} Lambda_i A_(n-i).
```

Unique factorization gives its coefficient meaning:

```text
[epsilon] Lambda_n
  = sum_{d | n} d *
      #{P monic irreducible : deg P = d, <P>^(n/d) = epsilon}.
```

Consequently the identity-class irreducible count is recovered recursively by
subtracting the proper-divisor terms and dividing by `n`. This is an exact,
integer-only version of the Hayes-class formula and a useful falsifier for any
proposed cancellation lemma. It is not yet a positivity proof.

Here `ell` counts prescribed zero coefficients. The conjecture's boundary is
therefore degree `2 ell + 1` in the odd case and `2 ell + 2` in the even case.
An independent implementation of the recurrence and direct Rabin enumeration
agree on the identity-class counts through degree 20:

```text
n:      3  4  5  6  7  8  9  10 11 12 13 14 15 16 17 18 19  20
count:  1  1  1  2  3  2  4   7  4 12  6 19 20 28 33 59 49 101
```

The signs of the deviation from the equidistributed main term vary, so a proof
cannot assume that every nontrivial-character contribution has a favorable
sign. The first theoretical work item is now sharper: bound the *aggregate*
properly weighted nontrivial contribution in the identity class at degrees
`2 ell + 1` and `2 ell + 2`, or replace it with a construction. Any claimed
bound must be checked for strict positivity, not merely asymptotic main-term
dominance.

There is an exact way to see why the ordinary Weil estimate stops here. For a
nontrivial character `chi` of `E_ell`, put

```text
P_chi(z) = sum_(0 <= d < ell) (sum_(f monic, deg f=d) chi(<f>)) z^d
D_ell(z) = product_(chi != 1) P_chi(z).
```

The group determinant theorem and the preceding Fourier decomposition give

```text
Delta_(ell,n) = 2^(-ell) n [z^n] log D_ell(z).
```

Characters whose exact conductor is `x^(j+2)` contribute `2^j` polynomials of
degree `j`, for `1 <= j < ell`; one further nontrivial character has constant
`P_chi`. Consequently

```text
deg D_ell = sum_(j=1)^(ell-1) j 2^j = (ell-2) 2^ell + 2.
```

Thus bounding every reciprocal root separately, even at its sharp Weil
absolute value `sqrt(2)`, necessarily loses a factor asymptotic to `ell` at the
endpoint. A proof of the candidate lemma must use cancellation in the power
sum of the *family norm* `D_ell`, not a better degree count for the individual
character polynomials. Exact symbolic group determinants for `ell <= 3` agree
with the factors printed in Gao--Kuttner--Wang; this is a reformulation, not a
new estimate.

There is a sharper endpoint-specific form of the same obligation. Work in the
rational group algebra, put

```text
U   = 2^(-ell) S_ell,
B_d = A_d - 2^d U                 (0 <= d < ell),
B(z)= sum_(0 <= d < ell) B_d z^d.
```

Here `U` and `1-U` are orthogonal idempotents, `B_0=1-U`, and `U B_d=0`.
The exact uniformity `A_d=2^d U` for `d>=ell` therefore splits the full
series without approximation:

```text
A(z) = U/(1-2z) + B(z),
z A'(z)/A(z) = 2z U/(1-2z) + z B'(z)/B(z).
```

Writing `C(z)=sum_(1<=d<ell) B_d z^d` in the complementary algebra, whose
identity is `1-U`, gives the exact centered logarithm

```text
Delta_(ell,n)
 = n [1,z^n] log((1-U)+C(z))
 = n sum_(k>=1) (-1)^(k+1)/k [1,z^n] C(z)^k.       (centered log)
```

Since `deg C <= ell-1`, every term with
`k < ceil(n/(ell-1))` is identically zero.  In particular, at both Lemire
endpoints the expansion begins at order at least three: neither a one-row nor
a two-row correlation contributes.  Expanding one centered product also has
an integral counting interpretation.  For a composition
`d_1+...+d_k=n` with every `1<=d_i<ell`,

```text
[1] B_(d_1)...B_(d_k)
 = #{(f_1,...,f_k): f_i monic, deg f_i=d_i,
                     <f_1...f_k>=1} - 2^(n-ell).
```

Thus the missing estimate can equivalently be phrased as cancellation among
connected factor-tuple correlations of order at least three.  This removes
the already-refuted conductor-by-conductor triangle decomposition from the
formula, but it is not by itself a bound: absolute estimates for the displayed
tuple counts can still lose the whole main term.  The independent integer
group-ring checker evaluates the centered logarithm with exact rational
coefficients for both endpoints through `ell=5`, verifies the structural
support cutoff before class arithmetic, and matches the recurrence
discrepancies.

Nor can the logarithm be bounded by taking absolute values one factor order at
a time.  At `(ell,n)=(5,12)`, its nonzero order contributions are exactly

```text
32, -744, 6144, -20736, 37056, -39480, 26624, -11472, 2976, -368.
```

Their absolute values sum to `145632`, while their signed sum, the full
discrepancy, is only `32`.  The checker pins this cancellation vector.  The
centered formula is therefore a new exact attack surface, not universal
credit: a successful estimate must preserve cancellation both across
conductor levels and across the orders of the logarithm.

A tempting shape-preserving induction also fails. If `f=x^n+q`, then `f^2+x`
has degree `2n` and tail degree at most `n`, but it is reducible for every
shaped irreducible in an exhaustive degree-2-through-12 test. The related
transforms `x f^2+1`, `f^2+f+x`, and `f^2+x f+1` fail the same falsification
range. None is used as a construction lemma.

The standard Artin--Schreier composition cannot repair this doubling route.
Let `f` be shaped and irreducible of degree `n>1`, and let `alpha` be a root.
If `n` is even, the missing `x^(n-1)` coefficient gives
`Tr_(GF(2^n)/GF(2))(alpha)=0`; also `Tr(a)=n a=0` for either `a in GF(2)`.
Thus `y^2+y=alpha+a` is soluble in `GF(2^n)`, and Capell's criterion makes
`f(x^2+x+a)` reducible.  If `n` is odd, its leading summand
`(x^2+x+a)^n` has coefficient one at `x^(2n-1)`, while the substituted tail
has degree at most `2 floor(n/2)=n-1`, so the composition violates the shaped
bound.  Hence no choice of the binary shift `a` turns this familiar extension
construction into a universal shaped doubling induction.

### A sufficient endpoint discrepancy lemma

Let `N_n(1)` be `[1] Lambda_n`, equivalently the number of elements of
`GF(2^n)` whose characteristic polynomial has identity type-II class, and put

```text
Delta_(ell,n) = N_n(1) - 2^(n-ell).
```

Exact transform computations expose a substantially sharper possible central
lemma than a character-by-character estimate:

```text
abs(Delta_(ell,2 ell+1)) <= 2^ell,
abs(Delta_(ell,2 ell+2)) <= 2^ell.                 (candidate)
```

This inequality would be sufficient, together with a finite check.  Hayes
Möbius inversion writes `n I_n(1)` as `N_n(1)` minus signed proper-divisor
terms.  Discarding signs and summing over all relevant root classes bounds
those terms by `sum_(k|n,k>=2) 2^(n/k)`.  At the odd endpoint the proposed
lemma leaves at least `2^ell`; at the even endpoint it leaves at least
`3*2^ell`, of which the `k=2` term consumes at most `2^(ell+1)`.  Elementary
geometric bounds make the remaining divisor contribution smaller for all
sufficiently large `n`, and the committed range through 400 can cover the
finite remainder.  Thus proving this one uniform discrepancy inequality would
complete the missing positivity step without needing favorable signs for the
individual characters.

The Axeyum Hayes endpoint tools evaluate the group-ring recurrence after an
exact Fourier transform of the finite principal-unit group.  They use two NTT
primes, CRT reconstruction, and the a priori bound `N_n(1) <= 2^n`; no
floating-point rounding is involved.  The ordinary regression binary
`axeyum-gf2-hayes-endpoints` retains the range through 23, while the explicit
high-memory `axeyum-gf2-hayes-endpoint` runner reaches level 24.  Through
`ell = 24` (endpoint degrees 49 and 50), the candidate bound holds. The
endpoint discrepancies for `ell = 13..24` are

```text
ell:                 13    14    15    16     17    18      19    20      21     22     23     24
Delta odd:         -345  -896   340  2744  -1988   928    4074  3115  -20938  -7582  57574   1651
Delta even:         980   645 -1832   660   6587  9592  -13496 -4509   25007  28402 -88336   4787
```

This is finite evidence and a proof target, not a theorem.  In particular, the
checker deliberately reports the bound as a `candidate` observation and the
fact ledger must not grant universal credit for it.

A separate C++ transform at `ell=23` on s6 completed in 23m11s with 6.96 GB
peak RSS; the refactored Rust transform
completed in 20m23s with 4.96 GB peak RSS and matched every row through 23.
The Rust output SHA-256 is
`5122d3dec0097e648aa683928d040a87a6fd9c6938757d107bf86fe654e6c4b9`.
This raises the dual-implementation finite diagnostic by one level, not the
certified theorem range or universal credit.

The native one-level Axeyum computation at `ell=24` completed on s4 in
25m41.54s including a clean release build (1519.039s inside the runner), with
10,311,424 KiB peak RSS and exit 0.  Its exact output is
`Delta_(24,49)=1651`, `Delta_(24,50)=4787`; output SHA-256 is
`9a86b99bc22cef6398e48eece2a3dd2c965dc4d14622363bac68b19af57495da`
and the build/resource log SHA-256 is
`0d57b0e5960c54f4020b27fec3e37a598ebbc0b1fc0183126c953ff5f7c1cdef`.
The bounded `axeyum-gf2-hayes-endpoint` binary now retains the exact runner:
it computes only the requested level, rejects `ell>24`, and keeps this
high-memory diagnostic outside default gates.  An algebraically separate C++
replay was started independently; its result is recorded only after it exits.

### A weaker conductor-local lemma would also suffice

The constant-one candidate above is stronger than the application needs. Put
`Delta_(0,n)=0` and, for `1 <= j <= ell`, define the exact-conductor layer

```text
T_(j,n) = 2^j Delta_(j,n) - 2^(j-1) Delta_(j-1,n).
```

Fourier character inclusion shows that `T_(j,n)` is precisely the aggregate
over characters of exact conductor `x^(j+1)`. Equivalently, if `C_0` and `C_1`
count field elements whose first `j-1` characteristic coefficients vanish and
whose next coefficient is respectively zero or one, then

```text
T_(j,n) = 2^(j-1) (C_0 - C_1).
```

This gives the telescoping identity

```text
Delta_(ell,n) = 2^(-ell) sum_(j=1)^ell T_(j,n).
```

One conductor layer vanishes for an exact algebraic reason.  Put
`j=2^v_2(n)`, the least nonzero binary place of `n`.  If

```text
F_alpha(X) = X^n + a_1 X^(n-1) + ... + a_n
```

is the characteristic polynomial of `alpha`, then that of `alpha+1` is
`F_alpha(X+1)`.  Provided `a_1=...=a_(j-1)=0`, Lucas' theorem gives

```text
binomial(n,i)=0 mod 2  (1 <= i < j),
binomial(n,j)=1 mod 2.
```

Translation therefore preserves the first `j-1` zero coefficients and toggles
the next one.  It bijects the two fibres in the definition of `T_(j,n)`, so

```text
T_(2^v_2(n),n)=0.                              (translation pairing)
```

`axeyum_cas::gf2_hayes::translation_paired_conductor_level` computes the
forced level, and every exact conductor transform now checks this zero as an
internal invariant whenever the level is present.  This is a genuine removal
from the analytic error, but only one level; it is not enough by itself to
establish endpoint positivity.

There is also an unconditional split that substantially narrows where new
cancellation is needed.  At exact level `j`, there are `2^(j-1)` characters and
their `L`-polynomials have degree at most `j-1`.  The ordinary function-field
Riemann hypothesis therefore gives, at either endpoint,

```text
abs(T_(j,n)) <= (j-1) 2^(j-1) 2^(n/2)
               <= (j-1) 2^(j-1+ell+1).
```

Consequently levels through `J`, after division by the `2^ell` in the
conductor telescope, contribute at most

```text
2 sum_(j=2)^J (j-1)2^(j-1) = 2 ((J-2)2^J + 2).
```

Set `r=ceil(log_2 ell)+2` and `J=ell-r` (leaving every level unresolved when
`r>=ell`).  The last display is at most `2^(ell-1)`.  Thus ordinary Weil bounds
already consume no more than half of the candidate `2^ell` discrepancy budget
while leaving only the highest `O(log ell)` conductor levels unresolved.  For
the finite-certification boundary `ell=199`, the split controls levels
`1..=189` and leaves ten.  The new
`axeyum_cas::gf2_hayes::low_conductor_weil_split` API checks this exact integer
budget, and the separate group-ring script checks every `ell` through 4000.
This does not control the remaining levels or their interaction with the
proper-prime-power margin, but it replaces the earlier request for uniform
cancellation across all `ell` levels by a top-conductor problem of logarithmic
width.

It exposes a weaker sufficient proof target. Any explicit conductor-uniform
square-root estimate of the form

```text
abs(T_(j,n)) <= C j^a 2^((n+j)/2)
```

for fixed constants `C,a` would imply
`abs(Delta_(ell,n)) = O(ell^a 2^(ell/2))` at both endpoint degrees. That is
smaller than `2^ell` for all sufficiently large `ell`; the dual-checked range
through degree 400 can cover an explicit threshold up to `ell=199`. Thus the
paper need not prove the observed constant-one bound. It is enough to prove
square-root cancellation *within each exact-conductor family* with explicit
polynomial dependence on the conductor and a threshold within the checked
range.

A deliberately generous concrete target is

```text
abs(T_(j,n)) <= 8 j^12 2^((n+j)/2).                 (conductor target)
```

At `n <= 2 ell+2`, telescoping and rounding half-powers upward give

```text
abs(Delta_(ell,n))
  <= 16 sum_(j=1)^ell j^12 2^(ceil(j/2)).
```

The right side is at most `2^ell` for every `ell >= 194`. The base inequality
and the two parity induction are checked with exact integer arithmetic by
`scripts/check-gf2-hayes-sufficient-bound.py`; degrees through 400 cover every
smaller endpoint. Therefore a proof of the displayed conductor target would
complete the counting step with ample slack. The same script checks the strict
proper-divisor margins at the first remaining degrees, `389` and `390`, using

```text
n^6 < 2^(n-3)   (odd),       n^6 < 2^(n-6)   (even),
```

which are exact sixth-power forms of the required
`n 2^(n/3)` estimates and strengthen monotonically within each parity. The
script checks only these arithmetic implications, not the conductor target
itself.

The optional `--conductor-layers` mode of `axeyum-gf2-hayes-endpoints` computes
these `T_(j,n)` values exactly and checks that they telescope back to the full
discrepancy. This is a diagnostic for the proposed lemma, not evidence that the
lemma holds universally.

One tempting much weaker, but constant-sensitive, target is:

```text
T_(j,n)^2 <= 2^(2j-2+n).                            (layer target)
```

Equivalently, the absolute aggregate over the `2^(j-1)` exact-conductor
characters is at most `2^(j-1) 2^(n/2)`.  Telescoping at the odd endpoint
`n=2 ell+1` then gives

```text
abs(Delta_(ell,n)) <= (2^ell-1) sqrt(2),
```

leaving more than `(2-sqrt(2))2^ell` before proper prime powers.  At the even
endpoint it gives `abs(Delta) <= 2^(ell+1)-2`, leaving `2^(ell+1)+2`.

The even square term is substantially smaller than the earlier coarse bound.
If `n=2m` and `<P>^2=1 mod x^(ell+1)`, characteristic two doubles every
coefficient index, so the first `floor(ell/2)` coefficients of `P` vanish.
There are at most `2^(m-floor(ell/2))` such monic degree-`m` polynomials and
their weighted contribution is at most

```text
m 2^(m-floor(ell/2)).
```

All exponent-`k>=3` terms together are at most `n 2^ceil(n/3)`.  Using the
strict rational witness `sqrt(2)<99/70`, these margins hold from `ell=22`.
`check_square_root_layer_bound_sufficiency` verifies the implication with
Rust bignums, and `scripts/check-gf2-hayes-layer-bound.py` independently checks
the same seed and monotonicity inequalities.  The degree-1-through-400
certificates cover the finite remainder.  Neither checker proves the displayed
layer target.

The displayed layer target is in fact **false**, already at the first proposed
symbolic endpoint. At `(j,n)=(5,45)`, exact class arithmetic gives

```text
T_(5,45) / 2^4 = 7,080,448 > 2^(45/2),
```

or `T_(5,45)=113,287,168`. The Rust conductor calculation and the separate
integer group-ring recurrence both pin this counterexample. The conditional
checker is retained only to record which constant would have been sufficient
and why the otherwise attractive route fails; it supplies no assumption for a
proof.

A generic second-moment proof of the layer target does **not** work.  If
`S_chi(n)` is the power sum for an exact-conductor character, Cauchy--Schwarz
would suffice if

```text
sum_chi abs(S_chi(n))^2 <= 2^(j-1+n).
```

The new exact Fourier-energy diagnostic reconstructs this integer using two
NTT primes and CRT, while a separate integer group-ring/Parseval calculation
checks the control.  At `(j,n)=(8,17)` the moment is `86,200,320`, whereas the
required bound is `16,777,216`. Thus average character size is already about
`5.14` times too large in squared norm, even though the tested
identity-direction layer at degree 17 satisfies the target. More importantly,
the degree-45 counterexample above shows that the constant-one target itself
cannot be the missing theorem. A successful estimate must aggregate levels
differently, exploit more endpoint structure, or allow a rigorously controlled
larger constant; unweighted Cauchy--Schwarz cannot establish those refinements.

The exact algebra is no longer trapped in that executable. ADR-0482 extracts a
bounded `axeyum_cas::gf2_hayes` API for the principal-unit cyclic structure,
identity-class populations, endpoint discrepancies, conductor layers, and the
conditional sufficient-bound arithmetic. Every transform admits `ell`, degree,
group-order, and retained-table-cell limits before allocation. The Rust bignum
checker and the separate Python checker both verify the implication and its
failure controls; neither claims the conductor estimate itself.

No SMT surface is missing for this step. Adding ray classes or character sums
to SMT-LIB would require term semantics, model lifting, replay, and proof
evidence but would not prove the required analytic family cancellation. The
research operation therefore remains CAS-local until a real solver consumer
and the foundational contracts justify a broader logic.

## Axeyum boundary and evidence ladder

The research becomes a proper Axeyum component in stages:

1. **CAS value layer:** bounded bit-packed `GF(2)[x]` arithmetic.
2. **Certificate layer:** Rabin Frobenius-chain and Bezout certificates; search
   is untrusted and the checker derives the complete degree factorization.
3. **Artifact layer:** canonical serialization, semantics version, producer
   identity, limits, witness, certificate, checker outcome, and content hash.
4. **Independent layer:** a second small checker implementation and exhaustive
   small-degree differential tests; completion-only fleet jobs receive no
   credit.
5. **Formal layer:** encode reciprocity and the central lemma in the Lean
   kernel path, with any finite computation represented by checked evidence and
   an explicit axiom footprint.
6. **Ledger layer:** only then establish a fact for the universal theorem;
   bounded verified ranges remain separate facts with finite statements.

No finite-field SMT sort is added merely to host the experiment.  A solver
surface becomes justified only with explicit term semantics, total operations,
model lifting, replay, and proof evidence under the foundational DAG.
