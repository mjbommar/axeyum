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
- Gorodetsky's fixed-field large-degree theorem reaches intervals described as
  being as small as the square-root scale, but its explicit error is

  ```text
  max|alpha| q^(n/2-h-1) exp(O_q(n log log n / log n)).
  ```

  For `alpha=Lambda`, `q=2`, and the exact Lemire endpoints
  `h=floor(n/2)`, the remaining subexponential factor is not `o(1)` and cannot
  force the normalized mean to be positive.  The paper's usable asymptotic
  hypothesis has `limsup h/n>1/2`, which supplies a linear exponential margin;
  the equality case here does not.  See [Mean values of arithmetic functions
  in short intervals and in arithmetic progressions in the large-degree
  limit](https://arxiv.org/abs/1810.00483), Theorems 1.1 and 1.3.
- Pollack's prescribed-coefficient results do not reach this fixed-field
  half-degree boundary: his theorem permits fewer than
  `(1-epsilon) sqrt(n)` arbitrary coefficients, not a linear half of them.
  See [Irreducible polynomials with several prescribed
  coefficients](https://www.pollack-math.net/prescribed.pdf).
- Andrade and Yiasemides do prove a fixed-`q`, growing-modulus fourth moment
  for primitive Dirichlet `L(1/2,chi)` values, including square-full moduli in
  their companion second-moment formula.  This is not the missing theorem:
  the endpoint discrepancy uses the high power sums
  `-Tr(Theta_chi^n)`, equivalently coefficients of `L'/L`, and a fourth
  moment of `L` itself does not control its logarithmic derivative on the
  critical circle where the zeros lie.  See [The fourth power mean of
  Dirichlet L-functions in F_q[T]](https://arxiv.org/abs/1901.06295), in
  particular its two main moment theorems.
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
  Corollary 1.  The paper's dedicated consecutive-zero result does not evade
  this loss: Corollary 2 requires `q^(n+l-2m) >= q m^4` for a zero block
  `l<=i<m`.  Lemire's block has `m=n` and `l=floor(n/2)`, making the exponent
  `l-n<0`; the sufficient condition therefore fails before constants are
  considered.
- Voloch gives a geometric version of the same boundary.  His
  cyclotomic-function-field twist theorem proves, for the relevant prescribed
  coefficients, an error at most `7 m q^(n/2)`.  In the unrestricted case
  `p^j>m`, this permits all first `m` coefficients to be prescribed, but at
  `q=2` and `m=floor(n/2)` the factor `7m` is fatal.  The paper itself derives
  existence only in a range `m<n/2-c log n` (with `q` sufficiently large).
  This independently confirms the exact obstruction below: ordinary Weil on
  a cyclotomic curve retains a linear genus/conductor loss, so the endpoint
  needs cancellation internal to that family rather than another generic
  point-count estimate.  See [Generators of finite fields with powers of
  trace zero and cyclotomic function
  fields](https://doi.org/10.4171/PM/1976), Theorems 1.1 and 3.2.
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
  The binary degree pattern left as a conjectural observation in the latter
  paper can be settled directly, but it confirms rather than removes this
  loss.  A character of exact Hayes level `j` has conductor `x^(j+1)` and,
  over `GF(2)`, is even; primitivity therefore gives exact `L`-degree `j-1`.
  Restriction from level `j` to `j-1` has a kernel of order two, so there are
  exactly `2^(j-1)` characters of that degree.  Consequently Gao's vector is

  ```text
  d_h = 2^h  (1 <= h < ell),
  D = sum_(h=1)^(ell-1) h 2^h = (ell-2)2^ell+2.       (proved)
  ```

  The public `binary_hayes_l_degree_distribution` report replays this exact
  conductor count and checks the closed form; an independent mixed-radix
  enumeration checks every character through level six.  Thus replacing the
  coarse bound on `D` by its exact value still leaves an asymptotic factor
  `ell-2` multiplying `2^(n/2)`.  It cannot establish positivity at the
  binary half endpoint.  This closes a useful literature ambiguity without
  promoting an aggregate-degree calculation into the missing connected
  trace estimate.
- Gao's 2023 follow-up advertises existence with *roughly* half the
  coefficients prescribed, including positions near the middle.  Its published
  abstract does not claim the exact all-degree fixed-`GF(2)` endpoint needed
  here, so it cannot be used as that theorem without checking the full
  hypotheses and numerical inequalities: [New Estimates and Existence
  Results About Irreducible Polynomials and Self-Reciprocal Irreducible
  Polynomials with Prescribed Coefficients Over a Finite
  Field](https://doi.org/10.1007/s44007-023-00062-1).
- Gorodetsky and Kovaleva obtain unusually strong cancellation for the special
  primitive character `chi_(k,psi)` modulo `x^(k+1)`, but their Theorem 1.5
  sums over all monic polynomials and explicitly leaves the restriction to
  irreducibles open. Their von-Mangoldt Corollary 3.9 handles one special
  power-sum character, whereas the layer `T_(j,n)` below aggregates every
  character of exact conductor `x^(j+1)`. Their Appendix Proposition 6.1 is
  likewise an individual general-character bound; after (HF) below, summing
  it character by character loses exactly the required `2^(j/2)` family
  gain. It therefore does not supply the missing family cancellation:
  [Equidistribution of high traces of random
  matrices over finite fields and cancellation in character sums of high
  conductor](https://doi.org/10.1112/blms.13057).
  The source-level obstruction is sharper in characteristic two.  Their Lemma
  3.8 uses equality of the image and kernel of the two monomial maps
  `x -> x^k` and `x -> x^gcd(k,2^n-1)` on `GF(2^n)^times`; it does not apply to
  a general linear combination of reciprocal power sums.  More decisively,
  the unique nontrivial additive character of `GF(2)` is sign-valued, so every
  special `chi_(k,psi)` and every product of them has order at most two.
  Frobenius also gives `p_(-2m)=p_(-m)`, hence a single special monomial is
  primitive only at an odd level.  The public
  `hayes_power_sum_character_coverage` report enumerates the full mixed-radix
  character group and checks that the number of primitive quadratic
  characters is exactly

  ```text
  2^((j-1)/2)  for odd j, and 0 for even j,
  ```

  versus `2^(j-1)` primitive characters in the complete layer.  Thus even the
  multiplicative span of every binary power-sum character can cover at most
  `32/1024` characters at level 11 and no primitive character at level 12.
  This rules out extending the special high-trace symmetry by products or
  Galois closure; a whole-family connected estimate is still required.
- Sawin's stationary-phase analysis of wild hyper-Kloosterman sums is a direct
  warning against replacing the missing aggregate estimate by generic
  square-root cancellation for each convolution order.  In equal
  characteristic `p`, divisor-like short-interval sums can exceed the
  square-root scale when their order is divisible by `p`.  This does not bound
  the signed logarithm used here, but it confirms that its cross-order
  cancellation cannot be discarded: [The size of wild Kloosterman sums in
  number fields and function fields](https://arxiv.org/abs/2209.02170).
- The local Kloosterman estimate does not itself bound the layer needed here.
  Sawin's Corollary 1.4 controls a fixed moment of local Gauss sums (and hence
  root numbers).  In contrast, `T_(j,n)` is the first moment, over **every**
  primitive character at that conductor, of the `n`th power sum of all roots
  of its `L`-polynomial.  At `n` near `2j` that trace depends on the complete
  coefficient vector, not only the functional-equation root number.  Turning
  it into one of Sawin's Kloosterman sums would therefore drop data and is not
  a valid reduction.
- Functional-equation root numbers do not recover the missing high power
  sums.  The native `hayes_root_number_fibre_report` computes primitive Hayes
  `L`-coefficients in an exact integral power-of-two cyclotomic basis and
  requires the coefficientwise primitive functional equation
  `2^k A_(d-k)=A_d conjugate(A_k)` before using `A_d` as the root-number
  label.  It also cross-checks every resulting power sum through both NTT
  primes.  At
  conductor level five and endpoint degree eleven, the 16 primitive
  characters form six leading-coefficient fibres, and every fibre contains
  distinct power sums.  In particular, characters 26 and 30 have the common
  leading coefficient `-4`, hence the same functional-equation root number,
  but their degree-eleven sums are `-32+32 zeta_8^2` and
  `-32-32 zeta_8^2`.  Thus a characteristic-two replacement for a
  primitive Gauss-sum formula must retain more than root-number data.  This is
  a bounded exact obstruction, not cancellation toward the connected target.
- Cyclotomic Galois orbits provide an exact intermediate Ramanujan
  decomposition, but they still cannot be bounded separately at one Weil
  unit.  The native `hayes_galois_orbit_trace_report` reconstructs every
  signed integral orbit with both NTT primes, groups them by exact character
  order, and independently recovers the conductor layer.  At `(j,n)=(7,15)`,
  18 of 28 orbits exceed `2^ceil(n/2)` and the maximum is `1696` against
  `256`.  Exact-order aggregation is smaller but not constant-scale: the
  `(11,24)` order layer reaches `663552`, requiring coefficient 17 relative
  to `(j-1)2^ceil(n/2)`.  Both endpoint parities are checked through level 12.
  Thus absolute values must remain outside individual Galois orbits, and a
  future order-layer estimate must carry its conductor growth into the
  endpoint ledger before receiving proof credit.
- Exact-order layers now have an independent spatial formula.  If
  `H_(j,s)` is the subgroup of characters killed by `2^s`, orthogonality
  identifies its annihilator with `2^s E_j`; writing `P_(j,s)` for the
  Mangoldt mass on this power subgroup gives

  ```text
  T_(j,s)=h_(j,s)P_(j,s)-h_(j,s-1)P_(j,s-1)
           -h_(j-1,s)P_(j-1,s)+h_(j-1,s-1)P_(j-1,s-1),
  h_(j,s)=2^(j-floor(j/2^s)).
  ```

  The native class-space reconstruction agrees order by order with the
  two-prime cyclotomic calculation at both endpoints through level 12.  When
  `2^s` divides `j`, the cumulative `H_(j,s)` conductor trace is zero; otherwise
  it is exactly
  `h_(j-1,s)(2P_(j,s)-P_(j-1,s))`.  Thus the missing cancellation is a nested
  sparse-coefficient imbalance, not an unexplained cyclotomic phenomenon.
- Endpoint repricing makes the useful target much weaker than the first
  finite experiment.  It is sufficient that every nonempty exact-order layer
  in the top connected window satisfy

  ```text
  4 ell |T_(j,s)(n)|
    <= #X_(j,s) (j-1) 2^ceil(n/2).
  ```

  This asks only a factor-`4ell` saving over the summed individual Weil
  envelope.  The exact integer ledger checks both endpoint parities for every
  `200<=ell<=1024`; at the first odd endpoint it charges 67 order layers.  The
  stronger diagnostic coefficient `j^2` is refuted at the level-23 even
  endpoint (required coefficient 710, allowance 529), confirming that it
  cannot be the theorem statement.  Proving the displayed linear saving,
  or an aggregate substitute no stronger than it, would close `(REL)`.
- Even that premise need not include low exact orders.  Put
  `c=ceil(log2 ell)` and let `Q` be the largest power of two with `3cQ<=ell`.
  The closed character count
  `h_(j,Q)=2^(j-floor(j/Q))`, the individual Weil bound, and the exact endpoint
  ledger prove that every top-window layer of order at most `Q` fits without
  any family cancellation.  It is enough to impose the factor-`4ell` saving
  only for exact orders greater than `Q`.  At `ell=200`, this unconditionally
  removes 20 of the 67 nonempty layers (orders 2, 4, and 8); asymptotically it
  leaves only `O(log log ell)` possible order bands per conductor.  Thus the
  ordinary Artin--Schreier layer is not the analytic bottleneck; the remaining
  theorem is genuinely a high-Witt-order estimate (ADR-0592).
- Ma and Xing improve the Hasse--Weil estimate for an ordinary
  Artin--Schreier curve by relating it to the minimum distance of a code:
  [The Hasse--Weil bound for Artin--Schreier curves](https://arxiv.org/abs/2105.04370).
  The exact conductor family here contains higher binary Witt-character data,
  not just ordinary additive characters, and their paper determines the
  relevant code distance only in its low-order case.  It supplies neither a
  uniform bound for all of these Witt characters nor cancellation after they
  are aggregated in `T_(j,n)`.

### Why the sparse witnesses are not a construction theorem

Every committed Axeyum witness through degree 400 is much sparser than the
conjecture asks: apart from the degree-one polynomial, there are 227
trinomials and 172 pentanomials.  This population is not inferred from prose.
`scripts/check-gf2-lemire-range.py` pins the exact distribution from the five
shard manifests, while the packed and independently implemented dense
checkers verify the underlying irreducibility certificates and half-degree
tail condition.

That pattern cannot be extrapolated to all degrees.  The *Handbook of Finite
Fields*, Conjecture 2.2.5, explicitly conjectures that every binary degree has
an irreducible trinomial or, when none exists, an irreducible pentanomial.  It
also describes constructions as rare and the surrounding work as largely
empirical or conjectural.  A universal shaped trinomial-or-pentanomial theorem
would imply this published conjecture and is therefore not an available
shortcut for the weaker dense-tail problem here.  See Mullen and Panario,
eds., [*Handbook of Finite Fields*](https://archive.ymsc.tsinghua.edu.cn/pacm_download/672/12637-dingjt-p2.pdf),
Remarks 2.2.3--2.2.4 and Conjecture 2.2.5.

Special pentanomial families do not fill the gap.  Banegas, Custodio, and
Panario study

```text
x^(2b+c) + x^(b+c) + x^b + x^c + 1,   b>c>0,
```

but enumerate the irreducible members and leave their irreducibility
conditions open.  Moreover, the tail exponent `b+c` is strictly larger than
half of the degree `2b+c`, so this orientation is not Lemire-shaped; its
reciprocal has a tail term of exponent `2b`, which also exceeds half.  See
[*A new class of irreducible pentanomials for polynomial based multipliers in
binary fields*](https://arxiv.org/abs/1806.00432), especially the contribution
statement and the open problem following its enumeration table.  The sparse
route is therefore closed unless a genuinely new all-degree construction is
proved; the live obligation remains the cancellation-preserving Hayes bound.

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

The bounded native implementation is now
`axeyum_cas::gf2_hayes::identity_class_irreducible_count`.  It computes the
Mangoldt distribution for every divisor of the target, raises classes in the
mixed-radix principal-unit coordinates, subtracts every weighted proper prime
power, checks nonnegativity and divisibility by the target degree, and then
reconstructs the original population exactly.  Its public report keeps all
three quantities separate.  Regressions recover the independent direct-Rabin
counts below and exercise malformed-input and pre-allocation resource declines.
This closes the CAS implementation gap between population and prime count; it
does not supply the analytic inequality needed to make the final count positive
in all degrees.

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

### Geometric compression of the family norm

The family norm is also the zeta numerator of one explicit curve.  Let
`K_ell` be the binary Carlitz cyclotomic function field of conductor
`t^(ell+1)`.  Its Galois group is

```text
(GF(2)[t]/t^(ell+1))^* = E_ell,
```

and all of its characters are even because `GF(2)^*` is trivial.  The standard
Dirichlet polynomial of every nontrivial character therefore contains the
factor `1-z`.  The leading-coefficient Euler series used above has one extra
Euler factor: reciprocity sends the prime `x` to the unit `1`, so that prime
contributes `(1-z)^(-1)`.  Hence the polynomial called `P_chi` above is exactly
the reduced standard factor `L(z,chi)/(1-z)`.

Artin factorization now gives an exact identity, not an estimate.  The place at
infinity splits into `2^ell` rational places in `K_ell`; cancelling those
factors against the `2^ell-1` nontrivial even-character factors gives

```text
Z_(K_ell)(z) = D_ell(z) / ((1-z)(1-2z)).
```

This is the specialization to `q=2` of the cyclotomic zeta factorization in
Rosen, *Number Theory in Function Fields*, Proposition 16.7, together with the
standard Artin factorization in Chapter 9.  In particular, if `C_ell` is the
smooth projective curve of `K_ell`, then

```text
genus(C_ell) = ((ell-2) 2^ell + 2) / 2
             = (ell-2) 2^(ell-1) + 1,

#C_ell(GF(2^n)) = 2^n + 1 + 2^ell Delta_(ell,n).    (curve trace)
```

The sign and every factor follow by taking `n[z^n] log` of the zeta identity.
For example, `ell=2`, `n=5`, and `Delta_(2,5)=-2` give 25 points on the
resulting genus-one curve.  A primitive Carlitz `t^(ell+1)`-torsion generator
`lambda` also supplies the affine equation

```text
C_(t^ell)(lambda) = t,
```

because `C_(t^(ell+1))(X)/C_(t^ell)(X)=C_(t^ell)(X)+t` in characteristic two.

The same identity gives a small unconditional gain that should not be confused
with the conjecture.  Since

```text
N_n(1) = 2^(n-ell) + Delta_(ell,n),
```

the curve trace rewrites exactly as

```text
#C_ell(GF(2^n)) = 2^ell N_n(1) + 1.                 (point-population identity)
```

The `2^ell` places above infinity are already rational over `GF(2)`, hence over
every `GF(2^n)`.  Therefore `2^ell N_n(1)+1 >= 2^ell`, and integrality gives
`N_n(1)>=1` for every positive `ell,n`.  In words: the identity Hayes class
always has positive Mangoldt mass.  This still does **not** prove a degree-`n`
irreducible.  `N_n(1)` counts prime powers, so all of that mass could in
principle come from primes of proper degree dividing `n`.  The remaining
theorem is precisely that the mass exceeds the proper-prime-power contribution
at the two half-degree endpoints.  Any paper using this observation must retain
that subtraction rather than relabel Mangoldt positivity as prime positivity.

This compression does not by itself prove the conjecture.  Applying ordinary
Hasse--Weil to the curve trace gives only

```text
abs(Delta_(ell,n))
 <= (ell - 2 + 2^(1-ell)) 2^(n/2),
```

which is precisely the asymptotic factor `ell` already exposed by the
characterwise calculation.  A useful geometric proof must exploit additional
structure of this one wildly ramified cyclotomic tower, rather than cite the
generic curve bound.

There is, however, an exact simplification at every **odd** endpoint.  Put
`n=2 ell+1`.  Every proper divisor `d` of `n` satisfies `d<=n/3<=ell`, and the
exponent `n/d` is odd.  The Hayes group `E_ell` has order `2^ell`, so raising a
class to the power `n/d` is an automorphism.  Hence a proper prime power can
have identity class only when its underlying prime already has identity
class.  For degree `d<=ell`, identity class forces the polynomial to be
`x^d`; this is irreducible only for `d=1`.  Therefore the entire proper-power
term is the single ramified power `x^n`, with weight one, and

```text
N_(2ell+1)(1) = 1 + (2ell+1) I_(2ell+1)(1).       (odd reduction)
```

Thus the odd half of the conjecture needs only the strict inequality
`N_(2ell+1)(1)>1`, rather than a general proper-power estimate.  The bounded
native operation `odd_endpoint_prime_power_reduction` records every proper
divisor and checks the degree, parity, and principal-unit group-order
invariants without performing a Fourier transform.  Through `ell=8`, its
constant proper population is cross-checked against the full Hayes inversion.
This is a genuine reduction of the missing theorem, not the missing strict
inequality itself: the curve argument above gives only
`N_(2ell+1)(1)>=1`.

Nor can positivity be amplified by a uniform power-of-two divisibility claim.
The exact native counts already give `N_9(1)=2^(9-4)+5=37`, so the endpoint
population can be odd.  Any new-point argument must provide a genuine lower
bound or cancellation estimate, not infer one from `N_n(1)>=1` and divisibility.

### A refuted normalized two-adic target for odd endpoints

The exact reduction suggested a different algebraic possibility.  Every odd
endpoint through degree 51 satisfied

```text
I_(2ell+1)(1) != 0 mod 8,                           (C8)
```

with observed `2`-adic valuation at most two.  But the next expensive stopping
row refutes `(C8)`:

```text
ell=27, n=55: N_n(1)=268616921,
               I_n(1)=4883944 = 0 mod 8, v_2(I_n(1))=3.
```

This does not threaten Lemire existence in that row; it kills only the fixed
congruence shortcut.  The typed `odd_endpoint_two_adic_report`
retains the exact residues modulo 8 and 16, the valuation, and the geometric
precision needed to reproduce the residue.

The first proposed bridge, Deuring--Shafarevich, is exact but insufficient.
The binary Carlitz cover has group order `2^ell`, one totally ramified finite
place, and split infinity, so

```text
gamma(C_ell)-1=-2^ell+(2^ell-1)=-1,
gamma(C_ell)=0.
```

On the other hand, the point-population and odd prime-power identities give

```text
I_n(1)=((#C_ell(GF(2^n))-1)/2^ell-1)/n.
```

Thus `I_n(1) mod 8` requires the raw point count modulo `2^(ell+3)`.
`2`-rank zero controls only the slope-zero part, or the zeta numerator modulo
two; it does not determine the three normalized bits after division by
`2^ell`.  Before the counterexample, the honest target would therefore have
been a congruence for the **higher-slope normalized trace**, not a p-rank
formula by itself.  The degree-55 row now stops that fixed-modulus target
(ADR-0560).  Nor do the earlier rows yield an even induction:
the known half-sized square proper-power stratum supplies bookkeeping but no
strict inequality or congruence recurrence (ADR-0559).

An exact cyclotomic Newton audit further shows that "higher slope" cannot be
replaced by a thin near-half window.  Because two is totally ramified in
`Z[zeta_(2^r)]`, repeated division by the unique uniformizer `1-zeta`
computes every coefficient valuation exactly.  The native lower convex hull
finds minimum primitive-character slopes `1/2` at levels two and three,
`1/4` at levels four through seven, and `1/8` at levels eight through ten.
At level ten the minimum-slope multiplicity is already 256.  These terms lie
far below the endpoint cutoff and the independently computed integral
conductor trace gains its valuation only after they are summed.  The proposed
theorem would have had to preserve cancellation across the complete
Galois/conductor family of low positive slopes; a characterwise Newton cutoff
does not supply `(C8)`.  With `(C8)` refuted, these polygons remain a diagnostic
for any future degree-dependent trace law, not an active existence bridge.

The closest Newton-polygon papers do not presently restore that bridge.
Kramer--Miller's abelian Artin estimate assumes characteristic at least three,
and Kramer--Miller--Upton's local-to-global Part I explicitly fixes an odd
prime; Part II is a `Z_p`-tower theorem.  Davis--Wan--Xiao is also rank one,
and Ren--Wan--Xiao--Yu's higher-rank coefficient ring is not the binary Hayes
product of finite cyclic 2-groups.  Their local Hodge/Newton machinery is
adjacent technology, not a theorem that can be substituted at `q=2`.

### The exact half-level sieve hits the parity barrier

There is an elementary identity which initially looks strong enough to prove
existence, but it pinpoints rather than removes the sieve obstruction.  Put
`m=floor(n/2)` and let

```text
S_n = {x^n + a_m x^m + ... + a_1 x + 1 : a_i in GF(2)}.
```

For every monic constant-one polynomial `D` of degree `d<=m`, triangular
division at the leading coefficients shows that exactly `2^(m-d)` members of
`S_n` are divisible by `D`.  If

```text
w_m(f) = sum_(D|f, deg D<=m) mu(D),
```

then, after omitting the ramified prime `x`, the polynomial Euler product is

```text
sum_(D monic, D(0)=1) mu(D) u^deg(D)
  = product_(P != x) (1-u^deg(P))
  = (1-2u)/(1-u)
  = 1-u-u^2-u^3-....
```

Consequently the divisibility uniformity gives the exact universal identity

```text
sum_(f in S_n) w_m(f)
  = 2^m - sum_(d=1)^m 2^(m-d)
  = 1.                                             (half-level sieve)
```

A prime has weight one.  The tempting final claim that every composite has
nonpositive weight is false, however.  Already at `n=10`, `m=5`,

```text
f=x^10+x^5+x^3+x^2+x+1
  =(x+1)(x^2+x+1)^3(x^3+x+1)
```

has distinct factor degrees `1,2,3` and
`w_5(f)=1-3+3=1`; the omitted three-factor divisor has degree six.  Native
Berlekamp enumeration finds positive composite weights at every degree
`10<=n<=30`, with maximum observed weight six by degree 30.  This is finite
diagnostic evidence, not an asymptotic assertion.

`axeyum_cas::gf2_hayes::half_interval_mobius_sieve_report` checks the aggregate
identity with exact bignums, computes the truncated weight of a supplied
distinct-factor-degree pattern, enforces caller limits, and pins the degree-10
counterexample against Axeyum's own Berlekamp factorization.  Thus a proof via
divisor weights needs a parity-breaking Type-II/bilinear estimate or an
equivalent Hayes-character cancellation; exact Type-I divisibility alone is
insufficient.  Porritt's explicit exponential--Möbius theorem does not supply
that estimate at `q=2`: its bound
`4 q^((3n+1)/4) (3 sqrt(3)/2)^n` exceeds even the full degree-`n` population in
this specialization.  See [A note on exponential-Möbius sums over
`F_q[t]`](https://arxiv.org/abs/1711.08729), Theorem 1.

### Exact classwise Möbius diagnostic

The parity-breaking quantity can now be inspected without factoring the full
interval.  If `A_chi(z)` is the class generating polynomial in a Hayes
character, define

```text
M_chi(z)=A_chi(z)^(-1)=sum_(d>=0) M_d(chi) z^d.
```

Its coefficients satisfy the exact recurrence

```text
M_0(chi)=1,
M_n(chi)=-sum_(1<=d<=n) A_d(chi) M_(n-d)(chi).
```

Inverse Fourier transformation makes `M_n(e)` the signed sum of the
polynomial Möbius function in class `e`.  The new bounded operation
`axeyum_cas::gf2_hayes::class_mobius_distribution` computes this table with
two NTT primes, signed CRT reconstruction, the pointwise bound `|M_n(e)|<=2^n`,
and the global Euler-product controls

```text
sum_e M_1(e)=-2,
sum_e M_n(e)=0  (n>1).
```

An algebraically separate Berlekamp-factorization test checks every class for
`1<=ell<=5` and `1<=n<=8`.  At `(ell,n)=(8,17)` the identity value is `-22`,
the largest class magnitude is `48`, and the squared `L^2` norm is `85072`.
These are finite diagnostics, not a Möbius cancellation theorem.

There is also an exact short decomposition of the prime discrepancy.  In the
class group ring, logarithmic differentiation gives

```text
Lambda_n = sum_(1<=d<=n) d A_d M_(n-d).
```

For `d>=ell`, `A_d` is uniform.  Since the total polynomial Möbius sum is
`-2` in degree one and zero above degree one, the `d=n-1,n` terms combine to
`2^(n-ell)` and all other uniform terms vanish.  Therefore, for `n>=ell+1`,

```text
Delta_(ell,n)
  = sum_(1<=d<ell) d sum_(u in V_d) M_(n-d)(u^(-1)).             (MC)
```

`identity_class_mobius_convolution` computes both sides from one retained
Möbius recurrence table and rejects unless they agree.  Direct endpoint tests
through `ell=9` reconstruct the existing Hayes discrepancies.  For example,
the seven terms at `(ell,n)=(8,17)` are
`[-1,36,-9,8,40,60,-84]`, summing to `50`; at `(8,18)` they are
`[-20,36,39,0,-20,54,-14]`, summing to `75`.  Larger probes show substantial
signed cancellation, so replacing (MC) by the sum of absolute values is not a
plausible route to the desired sharp endpoint bound.

A separate small oracle factors every monic polynomial needed by both
endpoints for `2<=ell<=5`, constructs its Möbius value and leading-coefficient
class directly, and checks every individual weighted inverse-fibre term.  The
test also requires the corpus to detect both replacing `u^(-1)` by `u` and
omitting the factor `d`; it therefore controls the termwise map rather than
only its final sum.

### Exact inverse-additive Fourier bridge

Write `J_ell=x GF(2)[x]/(x^(ell+1))`, identify its additive characters with
packed coefficient vectors `a`, and put

```text
H_k(a)=sum_(e in E_ell) M_k(e)(-1)^<a,e^(-1)-1>.
```

The annihilator of `W_d={a_1x+...+a_dx^d}` consists exactly of the packed
frequencies whose first `d` bits vanish.  Additive orthogonality therefore
gives the normalization required by (MC):

```text
sum_(u in V_d) M_k(u^(-1))
  = 2^(d-ell) sum_(a in W_d^perp) H_k(a).                    (AF)
```

`inverse_additive_mobius_spectrum` constructs `H_k` by putting the exact
classwise Möbius table into additive coordinates after unit inversion and
applying a checked integral Walsh transform.  It requires inversion to be a
permutation and checks Parseval with unbounded integers.  Orthogonality
reconstructs every endpoint convolution fibre through `ell=9`; an independent
factorization-and-direct-character-sum oracle matches every frequency for
`2<=ell<=5` in the endpoint degree window.

The reciprocal and ramified-`x` bookkeeping can also be stated without an
informal change of variables.  For an ordinary monic polynomial `h` with
`h(0)=1`, define

```text
B_m(a)=sum_(deg h=m, h monic, h(0)=1)
         mu(h)(-1)^<a,h^(-1)-1>,
```

where inversion is modulo `x^(ell+1)`.  Split a monic degree-`k` polynomial
`f` according to its `x`-adic valuation.  Terms divisible by `x^2` have
Möbius value zero; if `f=xg` with `g(0)=1`, then `mu(f)=-mu(g)` and the
reciprocal leading-coefficient unit of `f` is the reciprocal of `g`.
Reversal is a factorization-preserving bijection on monic constant-one
polynomials.  Hence, exactly,

```text
H_k(a)=B_k(a)-B_(k-1)(a).                                  (RT)
```

Combining (AF) and (RT) expresses every term of (MC) as a normalized sum of
the conventional Möbius-weighted inverse-additive phase over ordinary unit
polynomials, with the exact-degree difference and the ramified `x` factor
visible.  Direct Berlekamp factorization checks (RT) frequency-by-frequency
for `2<=ell<=5`.  The remaining applicability issue is now analytic rather
than representational: here `k>ell+1`, whereas several external interval
estimates use different degree/modulus ranges.

There is an exact way to retain cancellation across those convolution orders.
For a packed additive frequency `a`, let `v(a)` be the number of its vanishing
low bits, capped at `ell` for `a=0`.  Then `a` belongs to `W_d^perp` exactly
when `d<=v(a)`, so (MC) and (AF) regroup as

```text
2^ell Delta_(ell,n)
  = sum_a sum_(1<=d<=v(a),d<ell) d 2^d H_(n-d)(a).          (RG)
```

This nesting is an **annihilator depth**, not the multiplicative exact-
conductor filtration used elsewhere in this note.  The two notions cross-cut
each other, so a one-parameter "regroup by conductor" would discard the very
membership information needed in (RG).  The native operation
`inverse_mobius_fourier_regroup` combines every eligible `d` frequencywise,
then groups by exact annihilator depth.  It checks each order against the
original convolution term and the final numerator against `2^ell Delta`.
Both endpoints pass through `ell=8`; separate cellwise, orderwise, and
layerwise absolute numerators make the retained cancellation measurable
without turning it into an asymptotic claim.

Substituting `H_k=B_k-B_(k-1)` and summing by parts gives, for fixed depth
`v>=1`,

```text
sum_(d=1)^v d 2^d H_(n-d)
  = 2 B_(n-1)
    + sum_(d=2)^v (d+1)2^(d-1) B_(n-d)
    - v 2^v B_(n-v-1).                                    (SBP)
```

Thus summation by parts is exact, but it does not manufacture a saving: it
requires a new bound for the weighted `B` combination, including its boundary
term, after aggregation over the annihilator-depth layers.  That is now the
precise low/medium-block lemma rather than an ambiguous appeal to conductor
cancellation.

### Source-level characteristic audit and inverse-additive energy

The arXiv source, rather than PDF text extraction, confirms the exact inverse
notation and dependency boundary in Christian Bagshaw,
[*Bilinear Kloosterman sums in function fields and the distribution of
irreducible polynomials*](https://arxiv.org/abs/2401.10399):

- the paper globally fixes odd `q`, so none of its final theorems may simply
  be specialized to `q=2`;
- Lemmas 4.1 and 4.2 use Hölder, Cauchy--Schwarz, inversion, and additive
  orthogonality, with no visible odd-characteristic step;
- Lemma 3.14's energy proof invokes Lemma 5.3 of Bagshaw's
  [2023 paper](https://arxiv.org/abs/2304.05014), whose initial-interval proof
  is stated for arbitrary prime powers, followed by divisor counting and
  orthogonality; Axeyum now has an independent explicit `q=2,F=x^r` reproof;
  but
- the Type-I estimates in the proof of Theorem 2.3 invoke the complete
  Kloosterman bound from the 2023 paper's Lemma A.13, which explicitly assumes
  odd `q`.

This identifies a plausible reproof boundary, not an automatic extension of
the published theorem.  The 2024 source also contains apparent transcription
defects in the proof of Theorem 2.3 (an extra `n` in one exponent, a missing
upper endpoint in Case 3, and an undefined `t_1` there).  They do not by
themselves refute the theorem, but they make independent exponent derivation
mandatory for this project.

The source dependency audit is:

| 2024 result | role | characteristic status | binary action |
|---|---|---|---|
| Lemma 3.9 | additive orthogonality | characteristic-free | reuse directly |
| Lemma 3.10 | complete Kloosterman square-root bound | imports 2023 Lemma A.13, explicitly odd `q` | replace only by the proved binary wild bound |
| Lemmas 3.11--3.12 | incomplete completion and coprimality removal | algebraic steps are characteristic-free, but inherit Lemma 3.10 | recompute with the binary exponent |
| Lemma 3.13 | general inverse energy | external fixed-`k` estimate | unnecessary for the `k=2` balanced range |
| Lemma 3.14 | fourth inverse-additive energy | 2023 Lemma 5.3 is arbitrary-characteristic; the remaining divisor and congruence argument is characteristic-free | closed internally for `q=2,F=x^r` by the explicit valuation/lift/divisor envelope `(WE)` below |
| Lemmas 4.1--4.2 | Hölder/Cauchy--Schwarz bilinear bounds | characteristic-free once inverse energy is supplied | reusable |
| Vaughan reduction | splits into Type I and Type II | formal convolution is characteristic-free | retain, but audit every resulting range |
| Theorem 2.3 proof, Type-I Cases 1, 2, and 5 | completion/incomplete Kloosterman input | inherits the odd-only square-root bound | a full binary port does not survive unchanged; Case 5 is outside the Lemire cutoff domain |
| Theorem 2.3 proof, balanced Cases 3--4 and Type II | inverse energy and Hölder | characteristic-free after the explicit special-modulus energy reproof | audit the full endpoint ranges and retained losses |

Here is the decisive Type-I calculation.  For effective modulus degree `r0`,
Axeyum proves the complete binary exponent

```text
kappa(r0)=r0-ceil((r0-1)/3).
```

In Case 5, `n<=r0`, `2n/3<=u<=2r0/3`, and the completion argument gives the
worst off-diagonal exponent

```text
2n/3+kappa(r0)/2.
```

At `n=r0=300`, this is exactly `300`; at `(n,r0)=(300,320)` it is `306.5`.
Thus the direct binary substitution has no uniform power saving in this
nonempty Vaughan range.  Congruence-class rounding can save a constant
fraction of one bit for some degrees, but never `delta n`.  This is a precise
failure of the proposed port, not evidence against Bagshaw's odd-
characteristic theorem.

That obstruction must not be over-applied.  Case 5 itself assumes `n<=r0`.
For the Lemire bridge, the cumulative cutoff is always strictly larger than
the original modulus degree:

```text
N=k+1=n0-d+1 > ell+1 >= r0       (1<=d<ell).
```

Consequently Case 5 is empty at every Lemire endpoint.  It prevents citing a
verbatim all-range binary version of Bagshaw's theorem, but it is **not** an
additional endpoint obligation.  In the remaining Type-I cases, inserting the
binary exponent still gives a power saving in the restricted `N>r0` domain;
the endpoint calibration below is therefore the relevant bottleneck.

That last statement can be made fully replayable.  In Type-I Case 1 the exact
integer constraints are

```text
0 <= u <= min(floor(2r0/3),N-r0).
```

Replacing the odd-characteristic square-root complete exponent gives

```text
N-r0/2  ->  N-r0+kappa(r0)
          =  N-ceil((r0-1)/3).
```

The bound is independent of `u` and saves exactly `ceil((r0-1)/3)` bits from
the trivial exponent `N`.  For example, `(N,r0)=(601,301)` has the full range
`0<=u<=200`, binary exponent `501`, and deficit `100`.

In Type-I Case 2 the exact integer interval is

```text
max(0,N-r0) <= u
             <= min(floor(r0/3),N-ceil(r0/3)).
```

The two available bounds become

```text
A(u)=(3N+r0-u)/4,       B(u)=u+kappa(r0).
```

Here `A` decreases and `B` increases, so the exact worst bound
`max_u min(A(u),B(u))` occurs at an interval endpoint or one of the two
integers surrounding

```text
u_*=(3N+r0-4kappa(r0))/5.
```

At `(N,r0)=(300,300)` the crossing is `u=80` and the resulting exponent is
`280`, a `20`-bit saving.  At `(350,300)` the crossing lies beyond the
admissible interval `[50,100]`; the optimizer correctly selects `u=100` and
gives exponent `300`, a `50`-bit saving.  The CAS operations
`binary_type_one_case_one_exponent` and
`binary_type_one_case_two_exponent` implement these exact domains with checked
integer arithmetic.  The Case-2 production optimizer checks the clipped
crossing and endpoints in constant time, while an independent test enumerates
every admissible `u` for all small `(N,r0)` pairs.  Empty cases are rejected,
not silently optimized over.

There is a second, endpoint-facing ledger.  Put `r=ell+1`, let the endpoint
degree be `n0`, and set `k=n0-d`.  Since
`H_k=C_(k+1)-2C_k+C_(k-1)`, the largest cumulative cutoff is `N=k+1`.
Even pretending that Bagshaw's published exponent pair were available over
`GF(2)` with zero epsilon and unit constant, pointwise Fourier control would
require

```text
max(15N/16, 2N/3+r/4) < ell.
```

The first term is limiting.  At `ell=300`, strict pointwise closure begins
only at `d=283` for degree 601 and `d=284` for degree 602.  In general this is
only the large-`d` tail near `d>(14/15)ell+O(1)`; the linear-sized range below
it remains uncovered.  Moreover, a fixed positive margin is still needed to
absorb epsilon, constants, and the polynomial convolution weights.  The CAS
operations `binary_type_one_case_one_exponent`,
`binary_type_one_case_two_exponent`, `binary_type_one_case_five_exponent`, and
`endpoint_inverse_mobius_exponent_calibration` replay both ledgers with exact
integer numerators over their stated denominators while deliberately granting
no theorem credit.

The coarse maximum above is now backed by a source-case table rather than
standing in for one.  For each endpoint, `endpoint_vaughan_range_table`
enumerates every convolution order `1<=d<ell`; each order then enumerates
every effective modulus `1<=r0<=ell+1`, every Type-I split
`0<=u<=floor(2r0/3)`, and every symmetry-reduced Type-II split

```text
r0/3 < v <= min(N-r0/3,N/2).
```

The table records the direct small-modulus line, Type-I Cases 1--3, and all
three Type-II cases with exact numerators over denominator sixteen.  An
unassigned split fails construction.  Because `N>ell+1>=r0`, Type-I Cases 4
and 5 are empty throughout the endpoint table rather than silently omitted.

At `ell=300`, all seven relevant rows are nonempty.  The ideal columns for
degrees 601 and 602 recover the same first strict zero-loss transition as the
coarse calibration: `d=283` and `d=284`, respectively.  At odd `d=282`,
`N=320` and the worst exponent is exactly `15N/16=300`, so the deficit is
zero.  At the next order `N=319`, Type-I Case 3 is worst with exponent
`4785/16`, leaving only `15/16` of one bit.  This small margin does **not**
absorb a positive epsilon, constants, or the convolution weight `d`.

The table now also substitutes the proved finite wrapped-energy envelope into
every energy-using Type-I and Type-II row.  This second column is substantially
more honest: at `ell=300` it has no strict pointwise order at all.  Even the
last odd order `d=299` has exponent `4906/16>300`; its worst row is balanced
Type II at effective modulus `152` and split `151`.  Thus the exhaustive table
closes the range-audit gap but remains non-credit-bearing; the proof frontier
is still cancellation across the signed Möbius convolution.

Restoring even the elementary suppressed losses moves the usable tail much
farther.  The operation `odd_endpoint_vaughan_tail_budget` adds a caller-
selected analytic reserve, restores `ceil(log2 d)` for the convolution weight,
rounds each term upward, and charges their sum against the exact odd-endpoint
absolute budget `2^(ell+1)-2`.  At `ell=300` with zero analytic reserve, the
tail beginning at `d=292` already costs exactly `2^301` and therefore exceeds
the budget by two.  Beginning at `d=293` costs `2^300` and leaves the
low/medium block the exact residual budget

```text
2^301-2^300-2.
```

This is the **ideal-energy** column only.  The parallel explicit-energy tail
does not fit the endpoint budget at either start.  Its zero reserve has paid
the exact finite energy divisor envelope, but not the remaining analytic
Vaughan-weight loss or constants.  The reserve is an exposed proof input, not
an erased term.  The ideal result is nevertheless a useful target: any
aggregate argument can now state exactly which complementary block it must
control and how much budget remains.

An older literature phrase needs similar care.  Gao--Howell--Panario (1999)
say that Hsu proved existence with the lower or upper "half" of the
coefficients prescribed, and a 2006 AIM problem list says the `deg g<=n/2`
case is proved.  The exact Hsu inequality, reproduced as Theorem I.4 by Car,
has a square-root error multiplied by the number `k` of prescribed leading
coefficients.  With no congruence modulus, its lower bound has the shape

```text
n pi(n;k,R)
  >= 2^(n-k) - (1-2^(-k))(k+3) 2^(n/2).
```

Car's improved corollary still has error `(k+1)2^(n/2)`.  At the Lemire
boundary, `k=(n-1)/2` for odd `n` and `k=n/2-1` for even `n`; neither lower
bound is positive for the unbounded degrees at issue.  Garefalakis's later
summary correctly describes the effective range as roughly
`n/2-log_2(n)`.  Thus "half" in the survey sentence is asymptotic shorthand,
not a published proof of the exact endpoint.  See Hsu,
[*The Distribution of Irreducible Polynomials in GF(q)[t]*](https://doi.org/10.1006/jnth.1996.0139),
and Car's explicit restatement in
[*Distribution des polynomes irreductibles dans F_q[T]*](https://www.impan.pl/shop/publication/transaction/download/product/110720?download.pdf).

For `F=x^(ell+1)` over `GF(2)`, Bagshaw's set of invertible polynomials with
`deg h<d+1` is exactly `V_d`.  Therefore his fourth-order inverse energy is

```text
E_inv(ell,d)
  = #{(a,b,c,f) in (V_d^(-1))^4 : a+b=c+f mod x^(ell+1)}.
```

This is **not** the multiplicative collision energy `#{ab=cf}` already in the
CAS.  The new bounded operation
`principal_unit_inverse_additive_energy` computes `E_inv` from the fourth
moment of the additive Walsh spectrum and requires exact Parseval division by
`2^ell`.  A separate pair-sum collision table agrees for all `2<=ell<=9` and
all `1<=d<ell`; the level-eight row is

```text
d:       1    2    3    4     5      6       7
E_inv:   8   40  176  928  7424  77824  1114112.
```

Fleet probes on `s1,s4,s5,s6,s7` computed complete rows for `ell=17,...,21`.
They suggested that fixed-`d` values stabilize near `ell>=3d`; this part is now
a theorem rather than an extrapolation.  Clearing denominators gives

```text
A^(-1)+B^(-1) = C^(-1)+D^(-1) mod x^(ell+1)
iff
(A+B)CD = (C+D)AB mod x^(ell+1).
```

Both sides have degree at most `3d`.  When `ell>=3d`, congruence is therefore
ordinary equality in `GF(2)[x]`, and the energy is independent of `ell`.

The equality also has a divisor classification.  Write `A=ga`, `B=gb` with
`(a,b)=1`, and put `h=(g,a+b)`.  The canonically reduced fraction is

```text
(A+B)/(AB) = ((a+b)/h) / ((g/h)ab).
```

For a fixed reduced fraction `p/q`, any preimage selects an ordered
factorization `q=cab`; then `h=(a+b)/p` and `g=hc` are forced.  Also
`deg q<=2d`.  Thus every fibre has size at most the ternary polynomial divisor
function `tau_3(q)`.  If irreducible factors are split at degree
`R=floor(log_2(d)/2)`, the elementary estimates

```text
# {irreducibles of degree <=R} < 2^(R+1),
Omega_(>R)(q) <= floor(2d/(R+1)),
binomial(e+2,2) <= 3^e
```

give the explicit uniform envelope

```text
E_inv(ell,d)
 <= 2^(2d) (2d+1)^(2^(R+2)) 3^floor(2d/(R+1))
 = 2^(2d+o(d)),                         ell>=3d.       (NW)
```

The operation `principal_unit_inverse_additive_energy_no_wrap` computes the
stable value independently by reduced-rational-function buckets.  It gives
the first six exact values `8,40,176,760,3128,12520` and agrees with the
Walsh route at `ell=3d` and `3d+1`; `(ell,d)=(8,4)` remains below the theorem's
range and has the different wrapped value `928`.  The companion operation
`principal_unit_inverse_additive_energy_no_wrap_bound` replays the explicit
divisor envelope.

In modulus-degree notation `r=ell+1`, the exact no-wrap condition is

```text
3d < r,
```

not `3d<=r`.  Thus the modular checks at `ell=3d` use modulus degree
`r=3d+1` and are inside the theorem, while an exponent substitution at
`r=3d` is outside it.

The wrapped range now has a separate internal theorem.  Put

```text
U_m={A in GF(2)[x]: deg A<m, A(0)=1};
```

this is `V_(m-1)`.  For a nonzero inverse sum `a`, let `s=v_x(a)`.  Since
`AB` is a unit, `s=v_x(A+B)`, and the exact number of ordered pairs in the
stratum is `2^(2m-s-2)`.  Set

```text
k=min(r-s-1,ceil((r+m)/2)).
```

A homogeneous top-coefficient system with `k` equations and `k+1` unknowns
produces `u!=0` with `deg u<=k` and
`v=au mod x^r` of degree at most `r-k-1`.  Since `k<r-s`, also `v!=0`.
Clearing denominators and lifting gives

```text
(vA+u)(vB+u)=u^2+t v x^r.
```

There are at most `2^L` choices for `t`, where

```text
L=max(0,k+m-r,2m-k-2).
```

The right side cannot vanish: if `h=v_x(u)`, its summands have valuations
`2h` and at least `r+s+h`, which differ because `h<r-s`.  Each solution thus
injects into an ordered factorization of a nonzero polynomial of degree at
most `D=2 max(k,r-k+m-2)`.

The implementation now computes the **exact maximum** divisor count at every
finite `D`.  If `I_j` is the number of binary irreducibles of degree `j`, then

```text
2^j = sum_(d|j) d I_d,
tau(P)=product_Q(e_Q+1),
sum_Q e_Q deg(Q) <= D.
```

For fixed `j`, total exponent, and number of used irreducibles, the product is
maximal when the positive exponents are balanced.  A deterministic degree
knapsack combines these sharp per-`j` choices and returns
`max_(deg P<=D) tau(P)`.  Direct Berlekamp factorization of every monic binary
polynomial through degree ten agrees with the optimizer.

`binary_prime_power_inverse_additive_energy_bound` sums the exact stratum
populations times these lift and exact divisor bounds, then adds the diagonal
energy `|U_m|^2`.  Since `D=O(r)`, the divisor exponent is `o(r)`.  The strata
with `k=ceil((r+m)/2)` have
`L=max(0,ceil((3m-r)/2))`; the remaining strata contribute at most exponent
`max(2m,4m-r)+o(r)`.  Consequently, uniformly for `m<=r`,

```text
E_inv(x^r,m)
 <= 2^(2m+o(r)) + 2^((7m-r)/2+o(r)).                (WE)
```

This proves the characteristic-two energy input used by Bagshaw's Cases 2--4
and balanced Type II, including the exact boundary `3m=r`.  Independent exact
Walsh tables dominate-check the explicit envelope for every `3<=r<=9` and
`2<=m<r`; the test `(r,m)=(9,3)` prevents the old boundary gap from
returning.  The retrieved 2023 LaTeX source confirms that the underlying
pointwise argument is characteristic-free; it also reveals a source typo
writing the first inverse twice where the algebra immediately uses both
variables.

Feeding a general energy exponent back into Bagshaw's characteristic-free
`k=2` bilinear lemma gives, in base-two exponents,

```text
w = m+n + (e_m+e_n+r-4m-4n)/8.
```

With the asymptotic main term of `(NW)` on both intervals this is
`3(m+n)/4+r/8+o(m+n)`, which is nontrivial precisely beyond the boundary
`m+n=r/2+o(r)`.  The no-wrap hypotheses also require
`3 max(m,n)<r`, so this closes a genuine small/small Type-II region near
balanced thirds but not the whole endpoint decomposition.  The exact
`binary_bilinear_energy_exponent` report accepts arbitrary rational energy
exponents and returns the deficit from a requested target; it prevents a
sharper energy theorem from being pursued without checking its endpoint
effect.  It is a conditional arithmetic tool: inserting the ideal exponent
`2d` does not insert the proved finite divisor envelope.  The new
`binary_bilinear_explicit_prime_power_energy_exponent` operation instead uses
the ceiling exponent of `(WE)`'s explicit `BigUint` envelope and adds a
caller-selected rational analytic-loss reserve.  At the small wrapped boundary
`(r,m)=(9,3)`, that honest finite report does not close the target.  The full
Vaughan table now carries this same explicit ceiling beside every ideal row.
At `ell=300` the exact divisor optimizer improves the prior crude substitution
by more than eighty bits, but balanced Type II still exceeds the pointwise
target.  A non-credit last-order probe becomes strict by `12/16` at
`ell=1000`; this is finite evidence of sublinear loss, not a monotonicity
proof.  The
remaining analytic task is cancellation across the complete signed Möbius
convolution, not the wrapped energy lemma itself.

Berlekamp's characteristic-two analogue of Pellet's formula is the natural
next structural input: for squarefree polynomials it expresses the Möbius
sign through an additive character of the Berlekamp discriminant.  Carmon's
characteristic-two Chowla argument develops this conversion, but its
asymptotic is fixed degree with `q` tending to infinity, not fixed `q=2` with
degree tending to infinity.  It is therefore a technique source rather than a
theorem that closes (MC): [The autocorrelation of the Möbius function and
Chowla's conjecture for the rational function field in characteristic
2](https://arxiv.org/abs/1409.3694), Section 2.

The original LaTeX source makes the exact boundary explicit:

```text
mu(f)=(-1)^deg(f) chi_2(Berl(f))
```

only when `f` is squarefree.  Over `GF(2)`, `chi_2(z)=(-1)^z`; on squareful
inputs the Möbius weight is zero and the rational Berlekamp discriminant is
undefined.  Accordingly, the bounded native operation
`binary_berlekamp_inverse_phase_report` evaluates the actual combined weight

```text
w_a(f)=mu(f)(-1)^<a,f^(-1)-1>
```

by native factorization rather than inventing a phase on the squareful locus.
For the subspace `H` toggling the first `s` free coefficients, it computes

```text
E_H(a;k)
 = sum_coset (sum_(f in coset) w_a(f))^2
 = sum_(h in H) sum_f w_a(f)w_a(f+h)
```

and checks the exact Cauchy ledger

```text
B_k(a)^2 <= 2^(k-1-s) E_H(a;k).
```

At `(ell,k,a,s)=(4,9,12,4)`, the square bound is `3920`, versus the
trivial `29241`; every one of the sixteen frequencies at `(ell,k,s)=(4,9,4)`
improves strictly.  The direct phase also checks
`B_k(a)-B_(k-1)(a)=H_k(a)` against the independently reconstructed spectrum.
These are non-credit finite stationary-fibre diagnostics.  The missing result
is now a uniform bound for `E_H(a;k)` on the annihilator frequencies and
low/medium degree block that survives the explicit Vaughan tail, with an
exponent that closes the aggregate budget.

The frequency average has a sharper exact form.  Let `H=W_s` act on the low
free coefficients, let `A=W_d^perp`, and partition the degree-`k` monic
constant-one polynomials simultaneously by an input coset `C` modulo `H` and
an inverse coset `D` modulo `W_d`.  With

```text
b_(C,D)=sum_(f in C, f^(-1) in D) mu(f),
```

orthogonality before absolute values gives

```text
sum_(a in A) E_H(a;k)=|A| sum_(C,D)b_(C,D)^2.          (AE)
```

Consequently,

```text
(sum_(f: f^(-1) in V_d) mu(f))^2
  <= 2^(k-1-s) sum_(C,D)b_(C,D)^2.                     (CB)
```

`binary_berlekamp_annihilator_energy_report` computes both the signed energy
in `(AE)` and the larger unsigned simultaneous-collision count.  At
`(ell,k,d,s)=(4,9,3,3)` they are respectively `179` and `599`; the independent
frequency sum is exactly `2*179`.  Thus this regroup retains substantial
Berlekamp cancellation.

There is also an exact shift decomposition

```text
sum_(C,D)b_(C,D)^2
 = sum_(h in W_s) sum_f mu(f)mu(f+h)
     1_(f^(-1)+(f+h)^(-1) in W_d).                    (shift energy)
```

Its diagonal is completely elementary.  If `Q_k` counts the monic,
constant-one, squarefree binary polynomials of degree `k`, then

```text
Q_k=2^(k-1)-Q_(k-1)=(2^k-(-1)^k)/3.
```

The recurrence removes from all monic squarefree degree-`k` polynomials the
ones `xg`, where `g` is constant-one squarefree of degree `k-1`.  In the
counterexample below the diagonal is `Q_9=171` and all nonzero shifts sum to
`138`; the obstruction is therefore an off-diagonal correlation problem.

The first clean conjectural scale is not constant-one.  The proposed bound

```text
sum_(C,D)b_(C,D)^2 <= 2^(k-1)
```

already fails at `(ell,k,d,s)=(6,9,5,5)`, where the left side is `309>256`.
The relaxed candidate `2^k` survives both endpoint windows through `ell=9`,
but remains an unproved Autogenesis fact with no evidence.  The conditional
operation `binary_berlekamp_aggregate_exponent_ledger` immediately feeds any
candidate exponent through `(CB)`, `H_k=B_k-B_(k-1)`, and the weight `d`.  At
`ell=300`, the `2^k` candidate would first make the odd and even weighted
terms strict at `d=207` and `d=208`, respectively.  This is a real improvement
over the ideal Vaughan transition near 283, but it still leaves a linear
low-degree block and therefore is not the missing endpoint theorem.

A more structured surviving finite target is the fibrewise estimate

```text
b_(C,D)^2 <= 2d #(C,D).
```

It holds in the same endpoint controls through `ell=9`, but is not proved.
If established, summing over the buckets and using the exact formula for
`Q_k` would give `E<=2d Q_k<d 2^k`.  The aggregate ledger then first becomes
strict at `d=210` for both endpoints when `ell=300`.  This is almost the same
tail as the bare `2^k` conjecture, while isolating a local square-root
character-sum lemma that may be attacked fibre by fibre.  It still cannot
close the linear complementary block on its own.

The **support** of those fibres is now classified exactly.  For a nonzero
coefficient shift `h`, put

```text
w=f^(-1)+(f+h)^(-1)=h/(f(f+h)) mod x^(ell+1).
```

Then `ord_x(w)=ord_x(h)=v`.  After writing `h=x^v h_0` and `w=x^v w_0`
and cancelling the common power of `x`, inverse-coset equality becomes

```text
f^2+h f=h_0 w_0^(-1) mod x^(ell+1-v).                 (AS)
```

This is affine linear over `GF(2)`.  In
`R_r=GF(2)[x]/x^r`, the kernel of `z -> z^2+h z` has dimension

```text
kappa(r,v)=v+1          if 2v<r,
             floor(r/2) if 2v>=r.                     (kernel)
```

Indeed, `z^2+h z=z(z+h)`.  In the first range the solutions are the two
cosets `x^(r-v)R_r` and `h+x^(r-v)R_r`; in the second they are exactly
`x^ceil(r/2)R_r`.  The operation
`binary_artin_schreier_kernel_report` exposes this formula, exhaustively
checks every truncated ring through `r=12`, and supplies every shift row with
the resulting proved unsigned support ceiling.  This removes the nonlinear
collision-classification gap, but deliberately does not infer cancellation
of `mu(f)mu(f+h)` on a nonempty affine fibre.  That Berlekamp-sign estimate is
still the live local theorem.

A direct sign-reversing involution does explain some, but not all, of that
cancellation.  For one simultaneous bucket define `w(m)` on the low
coefficient cube to be its Möbius sign, or zero outside the bucket.  Every
nonzero translation `t` gives the exact triangle bound

```text
abs(sum_m w(m)) <= D_t,
D_t=(1/2) sum_m abs(w(m)+w(m+t)).                  (translation defect)
```

`binary_berlekamp_involution_defect_report` minimizes `D_t` over every
nonzero `t` separately in every enumerated bucket.  At the odd row
`(ell,k,d)=(9,11,8)`, no one of the eight occupied buckets has an exact
sign-reversing translation.  Worse, the bucket maximizing the defect ratio
has population `88`, signed magnitude `6`, and minimum defect `54`, so
`54^2>2d*88`.  The desired signed inequality still holds there---the relevant
worst signed square is only `225<=16*85`---but it cannot be proved by replacing
the signed magnitude with the best **single-translation** defect.  This is a
finite counterexample to that proposed proof mechanism, not to the local
square-root conjecture.  Any involutive argument must combine translations or
use cancellation inside the defect terms.

The squarefree sign now also has two independently checked algebraic
coordinates.  For the monic `0/1` integral lift `F` of a squarefree degree-`k`
binary polynomial, the
[Stickelberger--Swan theorem](https://msp.org/pjm/1962/12-3/pjm-v12-n3-p27-p.pdf)
gives

```text
Disc(F)=1 or 5 mod 8,
mu(f)=(-1)^k (-1)^((Disc(F)-1)/4).                 (Swan sign)
```

For the étale algebra `E=GF(2)[x]/(f)`, let `T_2` be the second trace
quadratic form: the second characteristic coefficient of multiplication by
an element of `E`.  Use `T_2` on all of `E` in even degree and on the
trace-zero subspace in odd degree.  Its polar form is nondegenerate, and the
older second-trace comparison recorded by
[Cassou-Noguès--Erez--Taylor](https://jtnb.centre-mersenne.org/item/JTNB_2000__12_2_597_0.pdf)
gives

```text
(Disc(F)-1)/4 = Arf(T_2)+epsilon_k mod 2,
epsilon_k=1 for k mod 8 in {3,4,5,6}, and 0 otherwise.       (Arf sign)
```

`binary_second_trace_arf_report` constructs the quotient algebra, the second
trace form, its polar matrix, a symplectic basis, and the integral Sylvester
determinant modulo eight.  It rejects unless factorization, `(Swan sign)`, and
`(Arf sign)` agree.  Exhaustive controls cover every monic constant-one
polynomial through degree ten, while squareful inputs remain explicitly
weight zero and receive no Arf sign.

The discriminant coordinate actually extends the sign formula through those
zero weights.  Define the real primitive character modulo eight by

```text
chi_8(D)= 0               if D is even,
          1               if D=1 or 7 mod 8,
         -1               if D=3 or 5 mod 8.
```

Reduction of the integral discriminant is the binary discriminant, so it is
even exactly when `f` is squareful.  Combining this parity fact with Swan on
the odd locus gives the universal identity

```text
mu(f)=(-1)^k chi_8(Disc(F))                             (dyadic Mobius)
```

for every monic binary `f`, with no separate squarefree indicator.  The CAS
computes the integral discriminant residue for **every** input by fraction-free
integer Bareiss elimination, checks its parity by the packed derivative gcd
independently of Berlekamp factorization, and rejects unless `(dyadic Mobius)`
agrees for every input through degree ten.  On odd residues a separate fast
unit-pivot determinant modulo eight must match the fraction-free result.  The
even residues are therefore available to the individual Fourier phases, not
merely collapsed to an inferred zero.

Moreover, if `zeta_8` is a primitive eighth root, the exact Gauss identity

```text
sum_(a=1,3,5,7) chi_8(a) zeta_8^(aD)
  = 2 chi_8(D) (zeta_8-zeta_8^3)                       (dyadic Fourier)
```

rewrites the whole Möbius weight as four additive discriminant phases modulo
eight.  `binary_dyadic_character_fourier_report` checks all eight residues in
the integral basis `1,zeta_8,zeta_8^2,zeta_8^3`.  This is the promised
Artin--Schreier--Witt entry point: a joint fibre sum no longer needs an
external squarefreeness gate.  What remains is a uniform cancellation theorem
for these four modulo-eight discriminant phases after the inverse-coset
constraints are imposed.

The auxiliary phases can be retained as one exact quadratic projector rather
than bounded four times.  Write

```text
A=(Z/8Z)^x=<3,5>,
a=3^u 5^v=1+2u+4v mod 8,
Q_D(u,v)=chi_8(a) zeta_8^((a-1)D).
```

Direct calculation gives the polarization

```text
Q_D(x+y)/(Q_D(x)Q_D(y))=(-1)^(D u u').
```

For odd `D`, its radical is `{u=0}`, of size two, and the phase is trivial
there; the normalized Gauss sum has squared magnitude eight.  For even `D`,
the polarization is trivial but `Q_D` is a nontrivial character, so its sum
is zero.  The native `dyadic_auxiliary_quadratic_projector_report` checks all
eight residues, all polarization pairs, both radical cases, and `(dyadic
Fourier)` in the exact cyclotomic basis.  This proves the small projector,
not the endpoint bound.  A larger joined fibre/valuation/Witt law must first
make the discriminant difference additive modulo four; the already pinned
nonquadratic affine fibre shows that the direct-product law cannot do so.
The stronger projection-preserving variant now fails exactly as well.
`pinned_dyadic_fibre_projection_obstruction_report` independently reconstructs

```text
F_t=x^11+1+sum_(j=0)^6 t_j x^(j+2),
D_t=Disc(F_t)Disc(F_(t xor 48)) mod 8,
d_t=D_t-D_0 mod 4.
```

Its full-support coefficient is `6 mod 8`, and its first additivity witness is
already `d_1=1`: hence `d_(1 xor 1)=0`, whereas `d_1+d_1=2 mod 4`.  If
`pi:G -> F_2^7` were a surjective homomorphism and `d o pi:G -> Z/4` were a
homomorphism, choosing preimages would force `d` itself to be additive.  Thus
no projection-preserving central extension can repair this fibre.  A viable
joined law must make the displayed affine fibre cease to be a homomorphic
quotient by mixing its multiplication with the auxiliary, valuation, or Witt
coordinates.  This is a stopping theorem for a broad construction class, not
cancellation credit for the remaining mixed law.

The raw discriminant phase is not globally low degree in the binary
coefficient bits.  `binary_discriminant_anf_report` evaluates every integral
discriminant residue, applies the exact subset Möbius transform over `Z/8`,
and reconstructs the complete truth table.  More decisively, the coefficient
of the monomial containing all `k-1` free bits is always odd.  Modulo two that
coefficient is the XOR of discriminant parity over the whole cube, hence the
parity of the exact squarefree population

```text
(2^k-(-1)^k)/3,
```

which is odd.  Thus `Disc(F) mod 8` has maximal multilinear support degree
`k-1` for every `k`, not merely in the exhaustive controls through degree
ten.  A generic bounded-degree polynomial-phase estimate on the full
coefficient cube cannot close the problem.  Any dyadic stationary-phase
saving must appear only **after restriction** to the affine
Artin--Schreier/inverse-coset system, or after preserving cancellation across
the convolution orders.

Restriction helps, but does not make every exact fibre quadratic.  For a
nonzero shift `h`, multiplicativity of the Kronecker character gives the exact
autocorrelation phase

```text
mu(f)mu(f+h)=chi_8(Disc(F) Disc(F+h)).                 (product phase)
```

`binary_dyadic_autocorrelation_fibre_report` groups the contributing pairs by
fixed input coset, `h`, and **exact** inverse difference.  It reconstructs
binary affine coordinates on each solution set, computes the `Z/8` ANF of the
product phase, and rejects unless the dyadic character recovers every signed
shift correlation and their off-diagonal total.

At the failed `(ell,k,d)=(9,11,8)` translation row, all `18,884` nonempty
exact sets are affine and contain `130,048` points in total.  Of these,
`16,587` phases are at most quadratic, but the remaining `2,297` fibres contain
`61,264` points and the maximum support degree is seven on a seven-dimensional
fibre.  Thus a uniform fibrewise quadratic-Gauss-sum theorem is false, and the
nonquadratic sector is not sparse.  Nevertheless its signed correlation is
only `-202` while the sum of absolute fibre correlations is `8,622`; the full
off-diagonal total is `-68`.  This is uncredited finite evidence for
**cross-fibre** cancellation.  The next dyadic theorem must aggregate over
the shift/inverse-difference parameters (preferably in Witt blocks) before
taking absolute values, rather than bounding every exact affine fibre
separately.

That aggregation is now exact.  Write

```text
h=x^v h_0,     w=f^(-1)+(f+h)^(-1)=x^v w_0.
```

Every contributing pair has the same valuation on `h` and `w`, and in the
quotient modulo `x^(ell+1-v)` its normalized parameter is

```text
h_0 w_0^(-1)=f(f+h).                                  (product parameter)
```

The extended fibre report checks this identity independently on a
representative of every exact fibre, then combines correlations successively
over input cosets with fixed `(h,w)`, over all `(h,w)` with fixed
`(v,h_0/w_0)`, and finally over the complete valuation layer.  At
`(ell,k,d)=(9,11,8)`, the absolute totals fall from `33,680` fibrewise to
`16,972`, `3,956`, and `388` at those three aggregation levels, before the
complete signed total `-68`.  The selected odd and even endpoint rows through
`ell=9` show the same qualitative collapse.

This does not yet supply a uniform estimate.  In particular, the initially
tempting bound `valuationwise absolute <=2^(d+1)` is already false: the value
is `672>512` at `(ell,k,d)=(9,12,8)`.  The live algebraic target is therefore
a bound for the sum of the complete valuation layers, possibly after Witt or
conductor orthogonality, using the family of equations
`f^2+h f=a mod x^(ell+1-v)`.  The intermediate absolute sums remain
uncredited finite diagnostics.

The larger feasible matrix rules out a coefficient-one square-root estimate
even after taking absolute values only at the valuation level.  At
`(ell,k,d)=(10,13,9)` that absolute sum is `2502`, whose square is about
`1.49*2^(k+d)`, while the fully combined off-diagonal correlation is only
`-314`.  Thus the observed saving genuinely uses cancellation **between**
valuation layers.  The connected candidate

```text
abs(off_diagonal correlation)^2 <= 2^(k+d+1)           (connected candidate)
```

survives every endpoint row through `ell=9` and the selected tail through
`ell=10`.  The factor two is not cosmetic: the bound without it fails at
`(ell,k,d)=(6,9,5)`, where the off-diagonal value is `138`.  The native energy
report exposes and checks this finite candidate without granting it theorem
credit.  If proved, it would imply the conjectural `E<=2^k` energy scale at
both Lemire endpoints, because `k+d` is the endpoint degree and the exact
diagonal is `(2^k-(-1)^k)/3`.  It still would not by itself control the
complementary signed cross-order convolution block.

There is now a sharper algebraic decomposition of the fibrewise `L^2` half.
For an exact fibre `F`, put

```text
c_F=sum_(f in F) mu(f)mu(f+h).
```

The CAS retains `sum_F c_F^2`, `sum_F #F`, and their difference.  At the
pinned `(ell,k,d)=(9,11,8)` row these are respectively `120680`, `130048`,
and `-9368`.  The square sum splits as `62948+57732` over the
at-most-quadratic and nonquadratic sectors, while their populations split as
`68784+61264`; both sectors separately have negative defect.  The proposed
inequality

```text
sum_F c_F^2 <= sum_F #F                              (E2')
```

also survives every endpoint row through `ell=7` and the maximal-interval
fleet rows through `ell=14`, without theorem credit.

Unlike the earlier spectrum patterns, `(E2')` has an exact four-point form.
In `R=GF(2)[x]/(x^(ell+1))`, write

```text
delta_h(f)=f^(-1)+(f+h)^(-1)=h/(f(f+h)).
```

For every allowed translation `t`, clearing the four unit denominators gives

```text
delta_h(f)=delta_h(f+t)  <=>  h t(t+h)=0 in R.        (parallelogram)
```

The right side is independent of `f`.  The factor `h` is essential because
the truncated ring has zero divisors; the native checker includes a modulo
`x^4` witness that rejects cancelling it.  Expanding `sum_F c_F^2` therefore
turns `(E2')` into the assertion that the restricted off-diagonal sum

```text
sum mu(f)mu(f+h)mu(f+t)mu(f+h+t),
```

over fixed high input cosets and nilpotent translations
`h*t*(t+h)=0`, `t!=0`, is nonpositive.  This is the active local theorem
target.  It requires a sign mechanism on nilpotent Mobius parallelograms;
positive moments alone cannot supply that sign.  Even if proved, the separate
cross-order convolution block would remain.

All valuation layers now also live in one checked Witt system.  If a
normalized parameter belongs to `E_(ell-v)`, then on each odd 2-typical block
the CAS embeds its coordinate by the blockwise Verschiebung

```text
c mod 2^L  |->  2^(M-L)c mod 2^M,
```

where `2^L` and `2^M` are the source and target block orders.  Exhaustive
controls through target level six prove that the product map is injective and
additive.  The signed parameter function is combined in `E_ell` **before**
any absolute value or Fourier transform.  Exact spatial and spectral second
moments and the exact spectral fourth moment are then computed; modular NTT
support is grouped by the general (not merely order-two) character conductor.

At `(ell,k,d)=(9,11,8)`, the `214` normalized parameters occupy `184` common
Witt classes.  Their absolute mass drops from `3956` to `3776`, while the
signed total remains `-68`.  The spatial second moment is `126568`, the
spectral second moment is `64802816`, and the spectral fourth moment is
`20409844301824`.  Every one of the `512` characters is nonzero modulo both
native transform primes, in exact-conductor populations `1,1,2,4,...,256`.
Since a zero cyclotomic transform would reduce to zero, this proves full
support for the finite witness.  It rules out sparse support or blanket
imprimitive-character vanishing as the explanation.

The CAS now retains the complete product-discriminant residue histogram
modulo eight at every embedded class rather than collapsing it immediately to
the real sign.  In the pinned row the total histogram is
`[52596,28796,0,0,19792,28864,0,0]`.  It transforms each of the four primitive
phases `zeta_8^(j r)`, `j=1,3,5,7`, separately and verifies their dyadic Gauss
combination against the signed spectrum character by character.  A one-entry
mutation is rejected.  All `512` transforms are nonzero modulo both native
primes for **each** primitive phase.  Thus passing to an individual additive
modulo-eight phase does not reveal sparse or imprimitive support either.

Nor do the four primitive phases form a complementary family in the pinned
witness.  Writing `u_r(a)=n_r(a)-n_(r+4)(a)` and
`C(s)=sum_r sum_a u_r(a)u_r(a+s)`, the odd-residue Ramanujan identity gives

```text
sum_(j=1,3,5,7) T_j*T_j^* = 4 C.
```

The CAS computes this using integer autocorrelations only.  At
`(ell,k,d)=(9,11,8)` it finds

```text
C(0)                = 13942624,
max_(s != 0)|C(s)|  = 10785296,
sum_s C(s)^2        = 5227607974543488.
```

The last value is about `26.89 C(0)^2`, rather than the complementary value
`C(0)^2`.  Moreover `C(0)` is over one hundred times the signed spatial second
moment `126568`.  Taking positive spectral powers across the four phases would
therefore reintroduce a large squareful even-residue channel that their
indefinite Gauss combination cancels.  The exact integers are pinned, and a
two-point mutation turns an exactly complementary delta into a function with
off-identity mass.

The next diagnostic is therefore not another support count.  The primary
characteristic-two Heisenberg template makes a necessary boundary explicit:
its symplectic form
is the antisymmetrization of a checked group-law cocycle, not a formal second
difference of an arbitrary Fourier spectrum.  The integer-valued connected
Witt function and its four phase-resolved lifts have no such cocycle yet.
Before assigning a commutator rank, the CAS must also retain the affine-fibre
variables, propose a central extension, and verify associativity and its
commutator identity.
None of these finite moments proves the connected candidate.

The remaining simple joined-domain precursor also fails in the pinned row.
For each exact affine fibre, the CAS tests generalized bentness directly.  If
`c_r(h)` counts the differences `q(x+h)-q(x)=r mod 8`, then the primitive
autocorrelation vanishes exactly when

```text
c_r(h)=c_(r+4)(h),  r=0,1,2,3,
```

for every nonzero translation `h`; this follows from
`zeta_8^4+1=0` and is equivalent to a flat primitive Walsh spectrum.  At
`(ell,k,d)=(9,11,8)`, **zero** of the `18,884` fibres pass, containing zero of
the `130,048` fibre points.  Even the `16,587` at-most-quadratic phases are
therefore degenerate or non-flat.  A known bent phase `4 x_1 x_2` passes the
same checker, while changing its `(1,1)` value to zero fails.

This does not logically exclude a larger group mixing fibre, shift, and Witt
variables.  It does remove the measured basis for inventing such a group: the
collapsed functions are neither sparse nor complementary, and none of the
original fibres is generalized bent.  Following the stopping rule, the active
route now moves to connected fourth-cumulant/gcd strata, where cancellation
between fibres, valuations, and convolution orders remains intact.

The Arf coordinate is a better representation of the live squarefree sign,
but not yet its estimate.
For each squarefree `f` the adjusted second-trace space is nondegenerate by
construction, so its full polar rank merely evaluates the normalized Gauss
sum back to `mu(f)`.  A saving requires a rank theorem for the **joint**
`(f,y)` phase after imposing the Artin--Schreier fibre, or an explicit
exceptional-plus-generic decomposition; the per-polynomial Arf rank alone
cannot be inserted into the endpoint ledger.

The uncollapsed pairwise rank test now rejects the simplest such theorem.
`binary_second_trace_bucket_difference_report` keeps the full forms
`Q_f(y)=T_2(m_y)` on their common coefficient space and, inside every
simultaneous coefficient/inverse bucket, classifies `Q_f+Q_g` by polar rank
and by its restriction to the radical.  It independently verifies each exact
binary quadratic Gauss sum.  At the pinned `(ell,k,d)=(9,11,8)` row, 683
squarefree forms give 28,830 unordered within-bucket pairs and ten types,
realizing every even rank from zero through ten.  Five nonzero Gauss
correlations have rank only two and radical dimension nine; their polynomial
differences are `x^3`, `x^3+x`, and
`x^8+x^6+x^5+x^3+x^2`.  At degrees eight and nine, distinct pairs already
have phase-trivial rank zero, hence maximal correlation.  Thus the raw forms
are not a bounded-class high-rank Kerdock/Delsarte--Goethals family.  A useful
Arf lift would still have to aggregate and cancel the growing low-rank sectors,
which is the same connected arithmetic problem rather than a rank shortcut.

The proposed Ito--Takeuchi--Tsushima bridge now has an equation-level
admission test as well.  Their characteristic-two Heisenberg group starts
with a linearized polynomial `R` and the quadratic Artin--Schreier phase
`xR(x)`; the cocycle `f_R` is defined by an explicit coboundary identity before
its commutator is proved symplectic.  Its length-two Witt maximal abelian
subgroup does not quadratize an arbitrary modulo-eight phase.  The degree-seven
raw fibres, zero generalized-bent count, rank-zero second-trace differences,
and mod-four projection obstruction therefore rule out a direct application.
A future use must first reduce the **complete connected sum** to linearized
quadratic summands, or construct and verify a genuinely new mixed-domain
associative cocycle.  This source audit prevents importing nondegeneracy as the
very statement still to be proved; it does not reject a later aggregate
cohomological decomposition (ADR-0525).

The principal-unit coordinates are now explicit as well.  For every odd
`m<=ell`, the generator `1+x^m` has order `2^L`, where `L` is the number of
slots `m,2m,4m,...<=ell`, and

```text
(1+x^m)^(2^j)=1+x^(m 2^j).                         (Witt block)
```

Thus the mixed-radix factors already used by the native Hayes transform are
exactly the additive groups of the truncated 2-typical blocks
`W_L(GF(2))=Z/2^L`; this is the finite coordinate decomposition used by
[Katz](https://web.math.princeton.edu/~nmk/wittchar31.pdf), without importing
his large-field equidistribution theorem.  The operation
`binary_principal_unit_witt_report` converts ordinary coefficient bits to
these blocks, records every active slot and the highest active slot, and
checks reconstruction.  Exhaustive controls cover every unit through level
five.

Every order-two principal-unit character is a parity sign on a subset of the
odd block coordinates.  Its exact conductor is the largest selected odd
block index.  `binary_berlekamp_order_two_projection_report` evaluates every
such sign inside every simultaneous input/inverse coset and checks Parseval on
the quotient by squares:

```text
sum_chi sum_(C,D) |sum_f mu(f) chi(f)|^2
 = #chi sum_(C,D,p) |sum_(f: Witt parity p) mu(f)|^2.       (real Parseval)
```

The failed single-translation witness does not collapse to one or two real
modes.  At `(ell,k,d)=(9,11,8)`, the 32 order-two characters have exact-
conductor average energies

```text
conductor       trivial   1    3    5    7    9
average energy      615 475  553  505  691  693.
```

The largest individual mode is mask `16` at conductor nine with energy
`1719`, while the complete identity is `20832=32*651`.  The mass is spread
across the Witt product rather than confined to a stable tiny exceptional
sector in this witness.  This is finite negative evidence against simply
removing a few real characters, not a theorem about all fibres.  A viable
local proof must instead tensor cancellation across several blocks, prove a
joint Arf/Witt rank statement, or preserve cancellation in the weighted
cross-order convolution.

Fresh release probes on isolated fleet checkouts tested the selected tail
orders `ceil(2ell/3)<=d<ell` at both endpoints for `ell=10,11,12`.  All twenty
rows retained the conjectural global `E<=2^k` and local
`b_(C,D)^2<=2d #_(C,D)` inequalities.  The one-translation defect surrogate
failed on most of the same rows.  These are uncredited finite diagnostics,
not an extension of the theorem range.

This also sharpens the boundary on the new Kloosterman result.  The
stationary-phase bound controls the **unweighted** distribution of one product
of intervals.  A Vaughan identity introduces Möbius-derived weights, and an
unweighted pointwise multiplicity estimate does not bound an arbitrary
weighted bilinear form.  A valid completion must either prove a weighted
binary bilinear estimate, bound the complete signed sum (MC) using its special
Möbius/Berlekamp structure, or
retain cancellation across the orders of the centered logarithm.  Merely
inserting the unweighted Kloosterman number into an odd-characteristic Vaughan
proof would be invalid.

### Exact Type-II product energy

The first bilinear quantity beyond the pointwise sieve has a closed form.  In
the principal-unit group

```text
E_ell=(1+x GF(2)[x])/(x^(ell+1))
```

put `V_d={1+a_1x+...+a_dx^d}` for `1<=d<ell`.  For `a<=b`, let `r_(a,b)(e)`
count ordered pairs in `V_a x V_b` with product `e`.  Then

```text
sum_e r_(a,b)(e)^2 = (a+2)2^(a+b-1),                    a+b<=ell,
sum_e r_(a,b)(e)^2 = 2^(2a+2b-ell)+(ell-b)2^(a+b-1),    a+b>ell. (mixed energy)
```

The equal-degree product energy is the specialization `a=b=d`.

Here is an elementary count.  Reduce an ordered pair `(A,C)` by its monic
constant-one gcd and write `(A,C)=(ga,gc)`, with `(a,c)=1` and
`s=max(deg a,deg c)`, where `A,C in V_a`.  There is one reduced ratio of
height zero and exactly
`2^(2s-1)` reduced ordered ratios of each height `s>=1`; this follows at once
by uniquely gcd-reducing the `2^(2s)` pairs of height at most `s`.  A fixed
reduced ratio has `2^(a-s)` possible common factors `g`.

For that ratio the congruence `aB=cD mod x^(ell+1)` has exactly

```text
2^max(b-s,2b-ell)
```

solutions `(B,D) in V_b^2`.  To see this, write
`aB+cD=x^(ell+1)H`.  At `H=0` the solutions are `(B,D)=(ck,ak)`.  If
`deg H<=s+b-ell-1`, division modulo whichever of `a,c` has degree `s`
gives a particular solution of degree at most `b`; a homogeneous solution
then fixes both constant terms.  Every `H` in that range occurs, and two
solutions for the same `H` differ by one of the preceding syzygies.  Summing
over `s` gives the displayed cases.  At `a+b=ell` they agree.

Finite-group Parseval therefore also gives the exact nonprincipal fourth
moment

```text
sum_(chi != 1) |sum_(u in V_a) chi(u)|^2 |sum_(v in V_b) chi(v)|^2
  = 2^ell sum_e r_(a,b)(e)^2 - 2^(2a+2b).
```

`axeyum_cas::gf2_hayes::principal_unit_mixed_product_energy` evaluates the
mixed identities with exact bignums and explicit admission limits;
`principal_unit_product_energy` is its equal-degree wrapper.  Independent
product-table tests check every ordered degree pair for `2<=ell<=8`.  This is
genuine Type-II information, but it is not the selected Mangoldt fourth
moment: expanding the centered logarithm couples different degrees and
requires cancellation among connected character quadruples.  Hölder applied
to the displayed energies only recovers a polynomial multiple of `2^(n/2)`
at the endpoint, so it does not by itself make the main term strictly
positive.

### A proved wild-Kloosterman amplitude bound

The extremal mixed distribution has substantially more structure than its
energy alone records.  For

```text
u=1+a_1x+...+a_ell x^ell
```

write `q_ell(a_1,...,a_ell)=[x^ell]u^(-1)` and let `W_ell` be the ordinary
additive Walsh transform of `(-1)^q_ell` on `GF(2)^ell`.  Exact transforms
through `ell=26` support the three-valued formula

```text
k=floor((ell-1)/3),
W_ell(v) in {0, +2^(ell-k), -2^(ell-k)},
#{v: W_ell(v)!=0}=2^(2k).                         (plateau candidate)
```

The exact three-valued support formula is stronger than the pointwise estimate
needed below.  Beginning at `ell=11`, the algebraic degree of `q_ell` is
already three, and by `ell=12` its Walsh support is not an affine subspace, so
the familiar quadratic/partially bent classification does not prove it.

The amplitude, however, has a short uniform proof.  Reverse the frequency
coefficients and put

```text
R=GF(2)[x]/(x^(ell+1)),
psi(z)=(-1)^[x^ell]z.
```

Then every Walsh coefficient is, up to sign, the binary wild Kloosterman sum

```text
K_2(c)=sum_(u in R^x) psi(u^(-1)+cu).
```

Write `m=ell+1`, `C=ceil(m/3)`, and `S=ceil((m-1)/3)=ceil(ell/3)`.
In characteristic two, the first nonzero mixed terms in the second difference
of `u^(-1)` are `z^2y+zy^2`; they have total degree three.  Since `3C>=m`,
the phase is an affine additive character on each coset modulo `x^C`, so a
coset contributes either zero or all `2^(m-C)` of its elements.

If two contributing cosets first differ in degree `d<S`, choose a variation
of degree `m-1-2d`, which is at least `C`.  The term `z^2y` then has the unique
lowest valuation `m-1` and nonzero top coefficient, contradicting stationarity
of both cosets.  Thus all contributing cosets agree modulo `x^S`; at most
`2^(C-S)` contribute.  Therefore, uniformly in the frequency,

```text
|W_ell(v)|=|K_2(c(v))|
  <=2^(C-S)2^(m-C)
  =2^(ell+1-ceil(ell/3))
  =2^(ell-floor((ell-1)/3)).                       (proved)
```

This is the stationary-phase scale in Sawin's wild-Kloosterman analysis
(*J. Analyse Math.* 151 (2023), 303--341,
doi:10.1007/s11854-023-0325-9), but the argument above is specialized and
independent.  That distinction matters: at modulus `x^4` and frequency
`c=1+x^2`, all eight phases vanish and `K_2(c)=8`, whereas the paper's later
displayed equal-characteristic specialization of Theorem 1.1 would give
`|K_2(c)|<=2^(5/2)`.  Axeyum uses only the directly proved bound above, which
is attained in this control.

The connection to the Type-II interval is exact.  Let `H=V_(ell-1)` and let
`r(e)` count `(A,B) in H^2` with `AB=e`.  Changing variables to `y=A^(-1)`
turns the two membership conditions into `q_ell(y)=0` and one affine linear
equation.  Orthogonality therefore gives, for a frequency `v(e)` and an
explicit sign depending on the top coefficient of `e`,

```text
r(e)-2^(ell-2) = (+/-) W_ell(v(e))/4.
```

The proved amplitude bound consequently gives the uniform pointwise estimate

```text
|r(e)-2^(ell-2)| <= 2^(ell-k-2),
k=floor((ell-1)/3).                                (proved)
```

The stronger finite plateau formula says when equality or zero occurs; its
squared sum is exactly `2^(2ell-3)`, agreeing with the proved mixed-energy
formula.  The uniform bound already supplies the exponential improvement for
factor compositions containing two degree-`ell-1` intervals.  It does not yet
cover the balanced degree pairs, so it is an input to a fixed-order
Vaughan/Heath--Brown decomposition, not by itself a proof of the Lemire
conjecture.

The finite runs remain evidence only for the stronger exact support formula.
A standalone exact Rust transform checks levels `1..=20` locally.  Fleet
checks returned the same formula at levels `21..=26`; levels 21 and 22 ran on
s4, 23 on s5, 24 on s6, and 25--26 on s7.  The largest run (`ell=26`) used
526,616 KiB peak RSS and 40.23 seconds.  s1 was unavailable for this diagnostic
because that host had no Rust compiler.  The amplitude inequality no longer
depends on those finite runs: `principal_unit_kloosterman_bound` evaluates its
proved closed form with exact bignums, and direct tests enumerate every
frequency and the associated product tables through `ell=9`.

The corresponding ledger object is
`F:gf2-principal-unit-wild-kloosterman-bound`.  It deliberately remains open
to Axeyum: the prose argument is a mathematical proof candidate, while the
native report and exhaustive tests do not independently certify its universal
stationary-phase step.  Autogenesis may therefore see the formal obligation
without manufacturing theorem credit from a bounded computation.

Supersingularity does not provide that extra structure beyond the first few
levels.  Gorodetsky identifies the same curve through the completed
short-interval-character factorization and proves that `C_ell` is not
supersingular for every `ell>=4`; in fact, at binary level four he exhibits a
character whose normalized `L`-roots are not roots of unity.  See
[Irreducible polynomials over `F_(2^r)` with three prescribed
coefficients](https://arxiv.org/abs/1805.07105), Theorem 1.3 and Section 6.
Thus the exact periodic formulas available for one, two, or three prescribed
coefficients cannot extend to the moving half-degree level by declaring the
whole cyclotomic Jacobian supersingular.  The fixed level-four factor is small
relative to the full tower, so this negative result does not rule out a
partial isogeny decomposition or an endpoint-only trace estimate; it rules out
only the tempting global supersingularity shortcut.

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

Nor can a binary projective change of variable repair that odd-degree
composition.  Every quadratic Artin--Schreier output is stabilized by
`x -> x+1`; conjugating through `PGL_2(GF(2))` leaves only the three involution
classes represented by

```text
x -> x+1,  x -> 1/x,  x -> x/(x+1).
```

For odd source degree `n>=3`, translation invariance forces the forbidden
coefficient in degree `2n-2`.  Inversion symmetry reduces a constant-one
half-shaped output to `x^(2n)+x^n+1`, the self-reciprocal cyclotomic candidate
already classified below.  For the third involution, reciprocation turns the
polynomial into an element of the invariant ring `GF(2)[x^2+x]`; the middle
coefficient gap then forces the only constant-one candidate to be
`x^(2n)+(x+1)^n`.  It is divisible by `x^2+x+1`, since a nontrivial cube root
`w` satisfies `w+1=w^2`.  The bounded native
`characteristic_two_projective_doubling_obstruction` constructs both remaining
candidates, checks the explicit factor, and requires the inversion candidate
to equal the existing Q-output exactly (ADR-0546).  Thus all six projective
repairs are impossible, reducible, or the already known cyclotomic family;
none supplies a new all-degree induction.

The standard Q-transform admits a complete negative classification, stronger
than checking its familiar recurrence hypotheses.  For

```text
Q(f)(x)=x^n f(x+x^-1),
```

the output is monic, constant-one, and self-reciprocal.  If it is half-shaped,
all coefficients in degrees `n+1,...,2n-1` vanish; reciprocity then also kills
degrees `1,...,n-1`.  An irreducible output must consequently be exactly

```text
x^(2n)+x^n+1,                                       (Q1)
```

because omitting the middle term gives `(x^n+1)^2`.  The unique invariant-ring
preimage of (Q1) is `D_n(x)+1`, where

```text
D_0=0, D_1=x, D_n=xD_(n-1)+D_(n-2),
D_n(x+x^-1)=x^n+x^-n.
```

For even `n`, `D_n+1=(D_(n/2)+1)^2` in characteristic two and is reducible.
For odd `n>=5`, its coefficient at `x^(n-2)` is one and lies above the allowed
half-degree window.  The sole survivor is
`D_3+1=x^3+x+1`, whose Q-image is the already certified
`x^6+x^3+1`.  The native `characteristic_two_q_shape_obstruction` reconstructs
the Dickson source, checks (Q1) exactly, and replays the classification through
degree 64 under explicit work bounds.  Thus there is no alternate sequence of
standard Q-sources hiding behind the failed familiar iteration.  See ADR-0542.

The raw even--odd decomposition is exact but does not restore an induction.
In characteristic two every polynomial has a unique expression

```text
f(x)=E(x)^2+xH(x)^2.
```

For a half-shaped polynomial of odd degree `2m+1`, `H` is monic, degree `m`,
and half-shaped; for even degree `2m`, `E` has those properties.  However,

```text
f'(x)=H(x)^2,
gcd(f,f')=gcd(E,H)^2,
```

so irreducibility of `f` forces only coprimality of the two components.  It
does not force the smaller shaped component to be irreducible.  The certified
counterexamples `x^5+x^2+1` and `x^6+x^3+1` have respective leading parity
components `x^2` and `x^3+1`, both reducible.  Conversely, fixing the odd
complement to `E=1` can never lift an irreducible `H` of degree greater than
one: `H(1)=1`, hence `(xH(x)^2+1)(1)=0`.  The bounded native
`half_degree_parity_split_report` reconstructs both square components, checks
the two gcds independently, obtains all irreducibility verdicts from the exact
Rabin route, and independently checks every positive certificate (ADR-0551).
Searching other complements is
a new prescribed-coefficient problem and receives no induction credit without
a uniform theorem.

Nor can an odd-degree witness be advanced one degree by `f -> x f+1`.  The
map has exactly the desired shape: a degree-`2m-1` tail of degree at most
`m-1` becomes a degree-`2m` tail of degree at most `m`.  But every irreducible
binary `f` of degree greater than one has `f(1)=1`, since otherwise `x+1`
divides it.  Consequently `(x f+1)(1)=0`, so the proposed even-degree output
is always reducible.  The native Rabin checker also rejects this transform on
all 199 odd-degree committed witnesses from degrees 3 through 399; the
elementary root argument is the theorem, while the scan is only its mutation
control.

The characteristic-two `Q`-transform gives genuine degree families but not an
all-degree induction.  For a monic degree-`n` polynomial put

```text
Q(f)(x)=x^n f(x+x^(-1)).
```

The coefficient of `x^(2n-1)` in `Q(f)` is exactly the coefficient of
`x^(n-1)` in `f`: the leading summand contributes only even exponents, the
`x^(n-1)` summand contributes its top odd exponent, and every lower summand
has degree at most `2n-2`.  Over `GF(2)`, the standard sufficient hypotheses
for indefinitely iterated irreducible `Q`-transforms include
`a_(n-1)=a_1/a_0=1`.  They therefore force the forbidden `x^(2n-1)` output
coefficient.  Conversely, a shaped input of degree greater than two has
`a_(n-1)=0`, so it cannot enter that theorem.  See Kyuregyan,
[*Recurrent Methods for Constructing Irreducible Polynomials over
GF(2^s)*](https://doi.org/10.1006/ffta.2001.0323).

The incompatibility is with the universal recurrence, not with every isolated
transform.  Axeyum checks

```text
Q(x^3+x+1)=x^6+x^3+1,
```

and independently certifies both sides irreducible and shaped.  The next
iterate already has nonzero terms in degrees seven, eight, and nine above its
degree-six allowance.  Separately, the cyclotomic identity

```text
Phi_(3^r)(x)=x^(2*3^(r-1))+x^(3^(r-1))+1
```

gives a shaped irreducible for every degree `2*3^(r-1)`: by the lifting-the-
exponent identity,
`v_3(2^(2*3^(r-1))-1)=r`, so `2` has order
`2*3^(r-1)=phi(3^r)` modulo `3^r`.  This is an infinite family, not coverage
of arbitrary degrees.  The bounded native operation
`characteristic_two_q_transform` expands by Lucas submasks, declines before
unbounded work, and keeps irreducibility as a separate certificate obligation.
Its tests pin the special success, the second-iterate shape failure, the
forced upper coefficient under the standard theorem hypotheses, and typed
resource declines.

Odd monomial composition supplies a broader but still non-universal family.
Let `f` be irreducible of degree `d`, let `alpha` be one of its roots, and let
`k` be odd.  The binary binomial criterion and Capell's lemma say that
`f(x^k)` is irreducible exactly when, for every prime `p|k`,

```text
alpha^((2^d-1)/p) != 1.                              (NCp)
```

Condition (NCp) says exactly that `alpha` is not a `p`-th power in
`GF(2^d)`.  Odd substitution scales every exponent and therefore preserves
the half-degree shape.  The construction iterates indefinitely: if
`beta^k=alpha`, then for each `p|k` the `p`-primary parts of `ord(beta)` and
`2^(dk)-1` both gain `v_p(k)` (the latter by LTE), so (NCp) renews.  One
checked seed therefore proves shaped irreducibles in every degree `d*k^j`,
`j>=0`.

The native `monomial_composition_criterion` replays the source Rabin
certificate, factors `k`, computes every displayed residue, and returns the
exact bounded composition.  `monomial_prime_eligibility` checks a large ray
without allocating its output.  The old `cubic_composition_criterion` is now
a compatible specialization.  On the 400 committed witnesses, scanning odd
primes through 20,000,000 finds 371 eligible seeds, including 174 of the 200
odd degrees; 35 bounded outputs receive fresh certificates from both Axeyum
polynomial implementations, and 400 deliberately incompatible primes are
rejected.  A separate integer-bit-polynomial implementation reproduced all
371 positive residues.  ADR-0565 records the theorem and the correction to
the old cubic-only conclusion.  These are infinite certified families, but
the cutoff census leaves 29 witnesses uncovered and supplies no theorem that
the union contains every degree.  It is not an all-degree proof.

Nonmonomial composition has one exact shape window, now classified natively.
For shaped `f` of degree `n` and monic `sigma=x^k+t`, `s=deg t`, the unique
largest proper degree in the binary Frobenius expansion of `sigma^n` is

```text
kn-(k-s)2^v2(n).
```

It lies below the half line exactly when `sigma=x^k`, or `n` is a power of
two and `sigma` is itself shaped.  `composition_shape_criterion` proves and
directly checks this equivalence; `search_shaped_compositions` retains a
Rabin certificate for every irreducible output.  Exhaustion of the complete
degree-eight domain finds two shaped irreducible sources and four certified
degree-64 compositions, but none of those four accepts any of the 31 shaped
nonmonomial degree-eight substitutions.  Thus the separately observed
degree-64 and degree-512 successes do not form an `8 -> 64 -> 512` chain.
ADR-0566 records the corrected boundary.  The power-of-two window contains
isolated constructions, not a proved inductive family, and cannot address
odd prime degrees in any event.

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
replay on s1 independently returned the same two integers and exited 0 in
1h25m20s with 14,423,180 KiB peak RSS.  Its source, binary, stdout, and
resource-log SHA-256 values are, respectively,
`1ef725facfb88ed25cd6aeebae0356f3cc3fe9809a5b43073b817954d1fddf44`,
`a4335500d8a85f7a539989ae149d92ac522af1726745bfd5dc7191d272670ec3`,
`b0cc7fcf433da1c330ed358e446bb45182d040b6f8b0b1549a3e249e95bfa102`, and
`46c4eae671984fba38542ed00d291193483189d04888ba703d215d74f4d5bffa`.
This raises only the dual-implementation finite diagnostic; it does not prove
the candidate inequality at any uncomputed level.

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

Nor does applying Parseval only after combining every conductor level rescue
the unweighted argument.  The reusable CAS operation now computes exactly

```text
V_(ell,n) = sum_e (N_n(e)-2^(n-ell))^2
          = 2^(-ell) sum_(chi != 1) abs(S_chi(n))^2
```

by summing the exact-conductor energies, checking divisibility by `2^ell`, and
returning a fail-closed sufficient test `V_(ell,n)<2^(2(n-ell))`.  At the two
`ell=8` endpoints it gives

```text
(n, uniform mean, V_(8,n)) = (17, 512, 693360),
                              (18, 1024, 1861136).
```

Both values exceed the square of the uniform mean, so the raw full-family
Parseval/Cauchy estimate cannot even force the identity Mangoldt population to
be positive at these controls.  This does not say that the population is zero,
and it does not refute a weighted or cancellation-preserving moment argument;
it records exactly where the unweighted sufficient inequality fails.  The
Rust two-prime/CRT calculation and the independent integer group-ring checker
agree on both integers.

The failure comes from converting a global norm into a single-coordinate
bound, not from an empty class in these controls.  The bounded inverse-Fourier
API reconstructs every class population and checks that they sum to `2^n`.
At `(ell,n)=(8,17)` and `(8,18)`, the largest absolute class errors are only
`155` and `290`, respectively, and every class has positive Mangoldt
population.  This separates the live `L^infinity` problem from the rejected
raw `L^2` estimate: a higher-moment, hypercontractive, or otherwise
class-sensitive bound could still work, but it must preserve enough structure
to avoid the extraneous square root of the number of classes.

The distribution-only executable
`axeyum-gf2-hayes-distribution` exposes this exact `L^infinity` diagnostic
without paying for the moment tables used by the broader research runner.  It
is resource-bounded to `ell<=23`, uses the same two-prime NTT plus exact CRT
reconstruction as the public CAS API, and reports the minimum, maximum, maximum
absolute deviation, conservation-compatible uniform mean, and whether every
class is positive.  Its bounded output is experimental evidence for choosing
the missing lemma; positivity in any finite range is not substituted for that
lemma.

The full distribution exposes a stronger, and apparently more structured,
route than the raw variance.  Put `D_e=N_n(e)-2^(n-ell)` and

```text
N_n(e) = sum_{F monic, deg F=n, <F>=e} Lambda(F).
```

Thus `N_n(e)` is the exact **Mangoldt population**, not the number of
irreducibles.  The mean `2^(n-ell)` and every moment below use this weighted
definition; irreducible positivity follows only after the separately checked
proper-prime-power subtraction and division by `n`.

Put

```text
M_r(ell,n) = sum_e |D_e|^r.
```

The weakest useful fourth-moment threshold must retain the proper-power
margin.  If `mu=2^(n-ell)` and `P_n` is the exact odd contribution `1` or the
proved even square/higher-power upper bound, then

```text
M_4 < (mu-P_n)^4                                      (weak target)
```

implies `N_n(1)>P_n` and hence an irreducible.  The tempting replacement
`M_4<mu^4` proves only `N_n(1)>0`; at an odd endpoint it still permits the bad
value `N_n(1)=1`.  `weak_fourth_moment_endpoint_ledger` retains both
thresholds under different names so this distinction fails closed.

Combining the weak target with the proved second-moment estimate gives the
exact sufficient root-ratio condition

```text
R_0 < 2^ell (mu-P_n)^4 / (mu Sigma(ell))^2,
Sigma(ell)=2^ell(ell^2-4ell+6)-6.
```

At `(ell,n)=(200,401)` and `(200,402)`, the base-two logarithms of the
allowed ratios are approximately `171.482426` and `173.482426`.  The old
`R_0<=4` target is therefore stronger than necessary by about `169` bits on
the first odd symbolic row.  Only a polynomial saving over the trivial
`R_0<=2^ell` is needed.  This is a major strategic relaxation, not a proof:
the weak uniform estimate remains conjectural.

Hast--Matei's Theorem 1.4 gives the closest published statement, but its
scope must be retained exactly.  With `H=mu=2^(n-ell)` their `m=4` estimate
translates to

```text
M_4 <= C_(4,n,h) 2^ell H^3,
```

so the exact proper-power-aware requirement is

```text
C_(4,n,h) < (H-P_n)^4/(2^ell H^3).
```

The right side tends to `2` at the odd endpoint and `4` at the even endpoint.
The published theorem does not supply this uniform constant: it fixes `n,h`,
allows its constant to depend on them, takes `q` to infinity, and assumes
`p>n` for `m>2`.  Consequently the live theorem is a **degree-uniform wild
characteristic-two fourth moment**, not merely deletion of the tameness
hypothesis.  Their proposed nontrivial `S_n^4` cohomology action and the
localized equivariant-trace route are two descriptions of the same missing
cancellation.  ADR-0567 records this boundary.  The weak ledger now exposes
the unit scale and exact allowed constant without granting theorem credit.

The even proper-power envelope is also sharpened before this normalization is
used.  Every odd exponent `k>=3` layer is empty, the square layer injects into
`E_ell[2]`, and the surviving even `k>=4` layers have base degree at most
`(ell+1)/2`.  Hence

```text
P_(2ell+2) <= (ell+1) 2^ceil(ell/2)
              +(2ell+2) 2^ceil((ell+1)/2).
```

This moves the exact even strong-target crossover from `ell=17` to `ell=13`.

The suggested Efron--Stein hypercontractive shortcut has also been audited
against this weaker allowance.  `efron_stein_spectral_weight_report` computes
the exact Fourier second-moment mass at every support weight by subgroup
Parseval and Boolean-lattice Moebius inversion.  The associated
`conditional_hypercontractive_root_ratio_proxy` is deliberately diagnostic:
the cited KLLM product-space theorem controls a strongly noised function and
does not imply the proposed unnoised, log-order-weighted inequality.  Exact
endpoint rows through `ell=17` miss the weak allowance by at least four
orders of magnitude even under the more favorable hypothetical constant
`C=2`.  ADR-0564 records the theorem mismatch and finite stopping test.  No
future ledger may credit that proxy without an explicit intervening theorem.

The CAS now returns the exact power sums for every caller-selected
`1<=r<=64`; the research runner records `r=2,4,6,8`.  It also records the
signed connected fourth-moment numerator

```text
K_4(ell,n) = 2^ell M_4(ell,n) - 3 M_2(ell,n)^2.   (fourth cumulant)
```

This separates the three Gaussian/Wick pairings from the genuinely connected
four-character correlations without floating-point normalization.  The finite
data become increasingly close to the pairing term rather than merely having a
small maximum.  For example, at `(ell,n)=(20,41)` and `(20,42)`, the exact
fourth moments are respectively

```text
4,499,025,619,307,287,799,932
18,063,544,808,537,013,332,672.
```

Both satisfy the deliberately simple experimental envelope

```text
M_4(ell,n) <= 64 ell^2 2^(3 ell).                (fourth-moment candidate)
```

The envelope is not a tautology: the exact even endpoint at `ell=5` has
`M_4=73,638,400`, exceeding its candidate bound `52,428,800`.  It holds at
both endpoints for every `6<=ell<=23` completed by the exact scan.  It is
mathematically sufficient if proved uniformly: since
`max_e |D_e|^4 <= M_4`, the envelope implies `max_e |D_e|<=2^ell` once
`64 ell^2<=2^ell` (from `ell=14` onward).  The exact arithmetic checker uses
the already certified degrees `1..=400`, starts the symbolic handoff at
`ell=200`, and verifies both proper-divisor margins; it reports the first
symbolic degrees as 401 and 402.  This checks the implication only.  The
fourth-moment candidate, or a comparable polynomial-times-`2^(3ell)` bound,
is now the missing theorem.

The high-memory level-23 scan gives

```text
M_4(23,47) = 3,119,070,106,577,995,866,919,000,
M_4(23,48) = 12,529,587,969,155,357,316,866,560.
```

Both are below `64*23^2*2^69`, and each is also below `2^92`, so the exact
fourth moment itself proves the finite `max_e |D_e|<=2^23` target.  The s6 run
exited 0 in 12m20.22s with 5,026,456 KiB peak RSS.  The executable SHA-256 is
`4e4745384abae683f9b021bbbedc79f807ce9f294d379ceef3848418152eeed7` and
the result/resource log SHA-256 is
`7f00ba5223b689bfa965cb12372109335bc8677b6904f2102d3586c8f76b0e8c`.
This is bounded evidence for selecting the lemma, not evidence for its
universal quantifier.

The conductor filtration of the fourth moment is now exact as well.  Let
`pi_j:E_ell->E_j` be coefficient truncation, put `f_e=D_e^2`, and define

```text
B_j(b) = sum_(pi_j(e)=b) f_e,
C_j    = 2^j sum_(b in E_j) B_j(b)^2.
```

Finite-group Parseval gives

```text
C_0 = M_2^2,                 C_ell = 2^ell M_4.
```

If `b0,b1` are the two children of a class at adjacent levels, then direct
expansion gives the nonnegative Haar increment

```text
C_j-C_(j-1) = 2^(j-1) sum_b (B_j(b0)-B_j(b1))^2.  (filtration identity)
```

Thus, if `E_j=C_j-C_(j-1)`, the connected numerator has the exact form

```text
K_4 = sum_(j=1)^ell E_j - 2 M_2^2.
```

`fourth_moment_conductor_decomposition` computes these integers without
complex roots of unity: it projects the stable mixed-radix class coordinates,
uses integer quotient buckets, and checks monotonicity plus both endpoint
Parseval identities.  The projection is independently controlled by comparing
every quotient through `E_7` against a fresh lower-level Hayes transform; the
separate Python recurrence also truncates explicit unit-polynomial bitsets and
reproduces every `ell=8` energy.  An explicit `ell*2^ell` work limit is checked
before bucket allocation, and
`axeyum-gf2-hayes-fourth-filtration` exposes the result.

The finite diagnostic does not reveal one exceptional conductor that can be
discarded.  At the odd `ell=16` endpoint, the last two exact energies are

```text
E_15 = 7,545,122,766,345,789,505,536,
E_16 = 14,760,487,533,964,220,694,528;
```

at the even endpoint they are

```text
E_15 = 30,738,353,465,097,337,700,352,
E_16 = 58,344,656,012,839,640,629,248.
```

The broadly geometric growth observed through `ell=16` makes a nested
martingale/large-sieve estimate more plausible than a one-level cancellation
lemma, but it is not such an estimate.  In particular, positivity of every
`E_j` does not prove the cancellation against `2 M_2^2` in `K_4`; the required
polynomial-times-`2^(4ell)` bound for their total remains open.

This formulation identifies what a proof must control.  Parseval handles the
three paired character quadruples; the new obstruction is the connected
off-diagonal quadruple sum represented by `K_4`.

The first gcd-stratification prerequisite is now exact.  For every
`1<=d<ell`, the CAS constructs the full class vector

```text
T_d(e)=d sum_(u in V_d) M_(n-d)(e u^(-1))
```

and independently checks `D_e=sum_d T_d(e)` in every Hayes class.  It then
forms the symmetric connected-order tensor

```text
K_(a,b,c,d)=2^ell sum_e T_a T_b T_c T_d
 -(C_ab C_cd+C_ac C_bd+C_ad C_bc),
```

where `C_ab=sum_e T_aT_b`.  Multiplicity-weighted summation over
nondecreasing order quadruples must reconstruct `K_4` exactly.  At
`(ell,n)=(9,19)`, `330` cells sum to `-2086965956608`, while the largest cell
is `K_(7,7,7,7)=-70637290307584`; the next two dominant cells have opposite
signs and comparable size.  Cancellation is already substantial **between
connected order cells**.  Gcd graphs must be classified inside this tensor
and recombined with sign; summing absolute cell bounds cannot be the proof.

A primary-source check prevents overextending that last sentence.  The gcd
matrix in Gorodetsky's Section 4 parametrizes an actual two-sided product
equation `f_1...f_r=g_1...g_s`, obtained by averaging powers of one
multiplicative character and its conjugate.  In contrast, Fourier inversion of
the spatial moment here gives

```text
sum_e D_e^4
 = |E_ell|^(-3) sum_(chi_1 chi_2 chi_3 chi_4=1)
     Dhat(chi_1)Dhat(chi_2)Dhat(chi_3)Dhat(chi_4).
```

These are four independently varying characters with one product constraint.
The one-character/conjugate diagonals that admit the standard gcd matrix are
pairing-like sectors, while `K_4` has already subtracted the three Wick
pairings.  Therefore the magic-square construction cannot simply be attached
to every connected tensor cell.  It remains available only after an exact
two-sided-product reduction for a specified sector.  The next representation
that still covers the **whole** cumulant is the existing exact-conductor
martingale; its actionable target is a local Carleson/square-function estimate
on every Witt cylinder.

That local target is now measurable without floating point.  Put `f_e=D_e^2`
and, for a level-`j` cylinder `b`, define

```text
R_j(b)=2^(ell-j) sum_(e below b) f_e^2
       / (sum_(e below b) f_e)^2.
```

The numerator and denominator are retained as exact integers.  The excess
over one is the normalized Haar square energy below `b`; at the root,
`R_0=2^ell M_4/M_2^2`.  At `(ell,n)=(9,19)`, the root ratio is about `2.813`
and the worst local ratio is the level-six value
`7244949696/1224440064<5.92`; singleton cylinders return to one.  The original
provisional ceiling `R_j(b)<=8` is false: the even `ell=12` row already has
`1226465917304832/149099338469376>8`, and the even `ell=15` row exceeds nine.
Both endpoint parities satisfy the replacement linear target
`R_j(b)<=ell` through `ell=23`.  This is finite evidence only.  The tempting
pointwise reduction `2^(ell-j) max f_e <= ell sum f_e` is already false at the
root of `(ell,n)=(8,17)`, where its exact ratio is
`6150400/693360>8` even though the aggregate concentration target holds.  Thus
the proof must retain distribution across descendants.  If proved uniformly,
the root case combines with the already proved exact-conductor Weil envelope

```text
M_2 <= 2^(n-ell) sum_(j=2)^ell 2^(j-1)(j-1)^2
```

and the elementary bound on the displayed sum to give

```text
M_4 <= ell M_2^2/2^ell <= 16 ell^5 2^(3ell)
```

at both endpoints.  The native implication ledger checks that this exact
envelope closes degrees from `401` and `402`, after the finite certificates
through degree `400`.  The implication is algebraic; the uniform linear local
ceiling remains the new theorem obligation.

The aggregate root is substantially more stable than the worst local
cylinder.  Since

```text
R_0 = 2^ell M_4/M_2^2 = 3 + K_4/M_2^2,
```

the candidate `R_0<=4` is exactly the signed connected statement
`K_4<=M_2^2`; it takes the full convolution-order sum before comparison and
therefore addresses the cross-order obstruction directly.  Both endpoints
satisfy it through `ell=23`.  The new exact ratios are

```text
R_0(22,46) = 2.999669624360008395435130475296692273575,
R_0(23,47) = 2.994842465247524680037501455785136891896,
R_0(23,48) = 3.001146364915799464504182706169550452291.
```

Thus the connected normalized cumulants `K_4/M_2^2=R_0-3` are respectively
about `-0.0003304`, `-0.005158`, and `0.001146`.  The three ignored probes
exited zero at exact commit `03d7502bb6ee430ebafd00365c2a2ccceca93a25`.
Their wall times and peak RSS were `2m56.58s/2,418,408 KiB`,
`6m42.70s/4,963,032 KiB`, and `7m00.90s/5,028,332 KiB`; the result/resource
log SHA-256 values are, in the same order,
`9aee051881a3086975dbd2ca8d5c842f2adaefb0e41ba763185b6ec584b744e6`,
`12c52b1525ac227064c776e10a7d355d2b415bdd2e6035ab623c8338713d27ba`,
and `9e3ea35c318f026bed6bf5d3c09c091c55c9578110812e8d88deb414d41c29fb`.
The four earlier root ratios at `ell=20,21` lie between `2.998` and `3.004`,
even though the worst local ratios exceed `10.6`.  If proved, the
second-moment envelope gives
`M_4<=64 ell^4 2^(3ell)`, which the exact endpoint ledger verifies is
sufficient after the degree-400 handoff.  This finite pattern is not a proof.

The point-counting version of this target is necessarily virtual.  The
Mangoldt population `N_e` is the fibre size of the characteristic-polynomial
class map from `GF(2^n)` to `E_ell`, so each positive integer

```text
C_r = sum_e N_e^r
```

counts an `r`-fold fibre product.  But expanding `(N_e-mu)^4` and subtracting
the three Wick pairings expresses `K_4` as a signed combination of `C_2`,
`C_3`, `C_4`, and uniform terms.  The public
`connected_fibre_product_report` reconstructs `M_2`, `M_4`, and `K_4`
independently from those raw counts.  Its pinned `(ell,n)=(9,19)` value is
`K_4=-2086965956608`.  Therefore the connected term is not the point count of
an honest off-diagonal variety; it is a virtual Frobenius trace.  A geometric
proof must retain the centering complex and all three pairing projectors (or
use the equivalent conductor-Haar differences), rather than proving only
irreducibility or Weil bounds for the positive fourfold fibre product.

Katz's big-Witt monodromy theorem explains the random-unitary heuristic but
does not bound this virtual trace.  In characteristic two and rank at least
three, the universal primitive-character sheaf has geometric monodromy
containing `SL`; hence its ordinary tensor fourth moment has only the expected
Wick invariants.  But Katz's Theorem 8.1 fixes the conductor and lets the field
size grow.  Its effective error is `C(p,n,Xi)/sqrt(q)`, where `C` is a sum of
compactly supported Betti numbers, and the source does not give the uniform
growing-conductor bound needed over `GF(2)`.

There is also an exact tensor-contraction mismatch.  The public
`character_fourth_moment_comparison` uses spatial autocorrelation to check

```text
sum_chi |S_chi|^4
  = 2^ell sum_h (sum_e D_e D_(e+h))^2,
```

whereas the spatial fourth moment and cumulant use

```text
sum_(chi_1 chi_2 chi_3 chi_4=1) product_i S_(chi_i)
  = 2^(3ell) M_4.
```

The latter is exactly the identity value of the fourfold convolution on the
character group.  Parseval supplies the value of each of the three Wick
pairings,

```text
P_2=sum_chi S_chi S_(chi^-1)=2^ell M_2,
Q_4-3P_2^2=2^(2ell)K_4.
```

The CAS retains `P_2`, one pairing, their threefold sum, and checks the final
subtraction against the independently computed cumulant.  These two fourth
moments already differ at the pinned level-seven endpoint.
Thus ordinary pointwise `SL`-monodromy moments do not prove the constrained
four-character statement.  A valid bridge requires a convolutional
four-design theorem plus effective Betti control, uniform while conductor,
rank, trace power, and representation complexity grow.  See
[Witt Vectors and a Question of Keating and
Rudnick](https://web.math.princeton.edu/~nmk/wittchar31.pdf), especially
Theorems 5.1 and 8.1.

Adams operations make the required geometric statement precise.  If
`V_chi` is the Frobenius space whose characteristic polynomial is the Hayes
`L`-polynomial, then

```text
S_n(chi)=Tr(Frob_chi^n|V_chi)=Tr(Frob_chi|psi^n V_chi).
```

Hence `Q_4` is the Frobenius trace of the external fourth tensor power of the
virtual Adams object on the product-one character fibre.  That fibre has
dimension `3ell`; unrestricted compactly-supported cohomology can therefore
reach degree `6ell`, while each Wick pairing diagonal has dimension `2ell`.
The connected Adams object still has nonzero generic virtual rank, so literal
support on those diagonals would be an unjustified and generally false target.
Removing the Adams weight `2^(2n)`, the following cohomological lemma would
instead imply the existing sufficient fourth-moment envelope:

```text
normalized connected complex is mixed of weights <=0,
H_c^i of the connected complex vanishes for i>4ell,
normalized total Betti number <= ell^4.                (AG)
```

Indeed, (AG) gives

```text
abs(2^(2ell) K_4) <= ell^4 2^(2ell+2n),
K_4 <= ell^4 2^(2n).
```

Together with the proved `M_2<=ell^2 2^n`, this yields
`M_4<=64 ell^4 2^(3ell)` at both endpoints, which the finite handoff already
checks from `ell=200`.  The native
`hayes_adams_identity_fibre_requirement` records the ambient dimension,
unrestricted and required top cohomology degrees, Betti budget, normalized
allowance, and restored-weight allowance exactly. At `ell=200`, the required
cancellation is a top-cohomology cutoff from degree `1200` to degree `800`,
not merely the half-weight saving supplied by a generic Weil estimate.

Neither cited monodromy source proves (AG).  Katz proves large monodromy for
one universal primitive-character sheaf.  His effective equidistribution
constant is the total compactly-supported Betti number and is used with fixed
conductor while the field grows.  Fresan's arithmetic Fourier formalism
correctly turns convolution into tensor product, but its moment theorem again
averages characters over extension fields for one fixed group and sheaf.  It
does not give four-pullback independence on the product-one fibre, the
degree-`4ell` cohomological cutoff, or a growing-conductor Betti bound over
`GF(2)`.  Those are now the exact geometric proof obligations rather than an
informal appeal to monodromy.

The combined budget in (AG) is already false as a universal all-level lemma.
The existing extension-field tracer measures only one zero-coefficient
long-cycle slice, so a separate bounded operation now retains every
`GF(2^r)` leading-coefficient class and computes the connected trace

```text
T_r=q^(2ell) (q^ell M_4-3M_2^2).
```

It cross-checks exactly with the independent base-field Hayes distribution.
At `(ell,n)=(2,5)`, the first five traces and the least integral coefficients
`B_r` in `abs(T_r)<=B_r q^(2ell+2n)` are

```text
r:       1             2               3
T_r:    -8192     -100663296     10582799417344
B_r:     1             1               3

r:       4                         5
T_r:     700872692009533440        29950594846676670742528
B_r:     10                        26.
```

Thus the `r=5` row violates `B_r<=ell^4=16`.  This distinguishes two proof
obligations that the sufficient ledger had bundled together: it refutes the
universal `ell^4` Betti coefficient, but does not refute the degree-`4ell`
cohomology cutoff, and it does not rule out a replacement estimate scoped to
`ell>=200`.  Any such replacement must expose its coefficient as a function
of `ell` and be replayed through the endpoint ledger before receiving credit.
See ADR-0540.

The connected extension-field computation is now deterministically
shardable.  Each shard retains its exact contiguous candidate range and a
partial vector of all `q^ell` Mangoldt class populations.  The checked merge
rejects missing, duplicate, noncontiguous, parameter-mismatched, or malformed
vectors, adds them componentwise, and requires the global Mangoldt sum to be
exactly `q^n` before forming either moment or the Wick subtraction.  The
monolithic API itself now uses the same one-shard merge path, and the
`axeyum-gf2-extension-trace` binary exposes canonical `--connected-shard` and
`--connected-merge` workflows.  This makes larger field rows reproducible
across the fleet, but it changes no evidence status: even a complete merged
row is a finite stopping test, not the required growing-conductor theorem
(ADR-0547).

The first fleet-sharded row stops the apparent level-three coefficient bound.
For `(q,ell,n)=(16,3,7)`, 100 shards cover all `16^7=268435456`
polynomials and conserve the same total Mangoldt population.  Their checked
merge gives

```text
M_2 = 267386880,
M_4 = 4433642394746880,
T_r = 301079086801372657987092480,
ceil(abs(T_r)/q^(2ell+2n)) = 250.
```

Thus the rows with `q=2,4,8`, whose minimum coefficients were `1,10,58`,
cannot justify the proposed `ell^4=81` coefficient: the `q=16` row exceeds it
by a factor of about `3.07465`.  The weaker one-extra-`q` stopping allowance
has coefficient `ell^4 q=1296` and survives this row.  This is an
extension-field Adams diagnostic, not a test of the separate binary Witt
off-diagonal inequality or of cancellation across Möbius orders (ADR-0548).

Gorodetsky's exact characteristic-two period-24 theorem determines the whole
level-three sequence without further enumeration.  For degree seven,
`7^(-1)=7 mod 24`; its coefficient power map reduces the normalized class
population to degree one.  Since both `binom(7,2)` and `binom(7,3)` are odd,

```text
N(t_1,t_2,t_3)=q^4-q+q^3  if t_2=t_1^2 and t_3=t_1^3,
                  q^4-q  otherwise.
```

There are `q` classes of the first kind and `q^3-q` of the second.  Hence

```text
M_2=q^5(q^2-1),
M_4=q^5((q^2-1)^4+(q^2-1)),
K_4=q^10(q^2-1)(q^4-6q^2+6),
T_r=q^16(q^2-1)(q^4-6q^2+6).                    (L3)
```

The native closed form agrees with exhaustive `GF(2)` and `GF(4)` class
populations and every integer in the sharded `GF(16)` report.  Formula (L3)
has leading degree 22; after removing the degree-14 Adams weight, its
normalized degree is 8.  This exceeds the proposed degree `2ell=6` by two and
also refutes the one-extra-`q` repair: at `q=128` the minimum coefficient is
`16378`, greater than `81q=10368`.  Gorodetsky's nonperiodicity theorem from
four prescribed coefficients onward simultaneously prevents promoting this
fixed-level compression to the growing endpoint (ADR-0549).

At level two the weight question can be decided without further enumeration.
The first two leading coefficients are the trace and subtrace.  Theorem 2 of
Ri--Myong--Kim--Rim's characteristic-two
[trace/subtrace formula](https://arxiv.org/abs/1304.0521) says that for
`q=2^r` and `n=5`, independently of `t`,

```text
N_(t,0)=q^3+(-1)^r(q-1)q,
N_(t,s)=q^3-(-1)^r q for s!=0.
```

The polynomial-Mangoldt class population equals this element count: an element
whose minimal polynomial has degree `m|n` contributes one of the `m` conjugate
roots, while the corresponding degree-`n` prime power has Mangoldt weight `m`.
There are `q` zero-subtrace classes and `q(q-1)` nonzero-subtrace classes, so
exact expansion gives

```text
M_2=q^4(q-1),
M_4=q^5((q-1)^4+(q-1)),
T_r=q^12(q-1)(q^2-6q+6).                         (L2)
```

The native `binary_extension_ell_two_degree_five_closed_form` reconstructs
all three identities and agrees with exhaustive enumeration through `r=5`.
Formula (L2) has leading degree 15 in `q`.  After removing the Adams weight
`q^(2n)=q^10`, the normalized trace has degree 5, while the proposed
degree-`4ell` cutoff at `ell=2` permits only `q^(2ell)=q^4`.  Therefore the
cutoff itself, not only the coefficient `ell^4`, is false as a universal
all-level statement.  This does not logically exclude a new theorem proved
only for `ell>=200`; it does show that Wick subtraction alone does not force
the desired top-degree cancellation.  See ADR-0541.

Parseval gives an equivalent conductor form.  If `E_j` is the exact Fourier
energy of `D_e^2` at conductor level `j`, the obligation is

```text
sum_(j=1)^ell E_j <= 3 M_2^2.
```

At `ell=12`, the top normalized layers are approximately
`1.05, 0.58, 0.27, 0.13`.  The literal all-level estimate
`E_j <= (3/2) 2^(j-ell) M_2^2` is false at conductor one for the even
`ell=20` endpoint, although that layer is negligible.  Put
`h=ceil(ell/2)`.  The corrected proof target is

```text
sum_(j<h) E_j <= (3/2) 2^(h-ell) M_2^2,
E_j             <= (3/2) 2^(j-ell) M_2^2  for j>=h.
```

The geometric tail plus the buffered low block sums to exactly at most
`3 M_2^2`.  The split fails at `ell=8` and both `ell=13` endpoints, but holds
at `ell=12` and both endpoints for every `14<=ell<=20`.  Its fact is explicitly
asymptotic from `ell>=200`; it remains a machine-visible conjectured sublemma,
not a uniform derivation.

The exact conductor energy has a concrete Haar form.  If a level-`j-1`
cylinder `b` has two level-`j` children and `B_j(b,i)` is the sum of `D_e^2`
below child `i`, direct expansion of `C_j-C_(j-1)` gives

```text
E_j = 2^(j-1) sum_b (B_j(b,0)-B_j(b,1))^2.
```

The CAS reconstructs both sides independently at every level and rejects a
nonbinary fibre.  Thus the live analytic lemma is an `L2` estimate for binary
Witt-refinement imbalances.  Generic martingale inequalities do not provide
it; an arithmetic pairing or relative Artin--Schreier estimate still must.

There is also an exact first-moment Haar route that avoids the fourth moment.
Aggregate the raw Mangoldt populations to every quotient `E_j`, and for a
level-`j-1` cylinder `b` put

```text
H_j(b)=N_j(b,0)-N_j(b,1),
H_j^*=max_b |H_j(b)|.
```

Successive binary splitting gives, for every full class `e`,

```text
2^ell N_ell(e)
 = 2^n + sum_(j=1)^ell sign_j(e) 2^(j-1) H_j(parent_j(e)).
```

The new native operation `population_refinement_triangle` reconstructs this
identity leaf by leaf with exact signed integers.  It follows immediately that

```text
T(ell,n)=sum_(j=1)^ell 2^(j-1) H_j^* <= 2^(2ell)       (Haar triangle)
```

implies `max_e |N_ell(e)-2^(n-ell)|<=2^ell`.  This is a sufficient
triangle inequality, not an equality with the observed maximum.  The low
control `(ell,n)=(4,9)` has `T=272>256`, so the finite check is not a
tautology.  Both level-12 endpoints pass, with numerators `8,213,504` and
`14,542,848` against `16,777,216`.

The level maxima suggest a concrete square-root-fibre theorem:

```text
H_j^* <= 3j 2^ceil((n-j)/2).                            (RF)
```

`population_refinement_envelope_implication` substitutes this displayed
bound into the exact sum.  Pure integer arithmetic shows that it closes the
odd endpoint for every `ell>=13` and the even endpoint for every `ell>=15`.
Thus a proof of (RF) for `ell>=200` would combine with the existing finite
certificates without any fourth-moment or cross-order remainder.  The
coefficient three is a real reserve: the initially tested coefficient two is
false at `(ell,n,j)=(19,40,4)`, where the exact maximum `2,112,512` exceeds
`2,097,152`.

Only a logarithmic top-conductor part of (RF) is actually needed.  Let `X_j`
be the `2^(j-1)` characters that are nontrivial on the kernel of
`E_j -> E_(j-1)`, and put

```text
S_n(chi)=sum_(deg f=n) Lambda(f) chi(<f>).
```

Fourier inversion on the two children of a parent gives the exact identity

```text
H_j(b)=2^(1-j) sum_(chi in X_j) conjugate(chi(b)) S_n(chi).   (HF)
```

The standard individual Weil estimate
`abs(S_n(chi)) <= (j-1)2^(n/2)` and the size of `X_j` therefore imply the safe
integer envelope

```text
H_j^* <= (j-1)2^ceil(n/2).                                  (W)
```

Set `L=ceil(log2 ell)`.  Substituting (W) for `j<ell-L` and (RF) only for
`ell-L<=j<=ell` closes both endpoints for every `ell>=200`.  At the worse even
endpoint, after division by the target `2^(2ell)`, the low part is at most

```text
(ell-L-3)/2^L + 2^(2-ell),
```

and the top part is at most

```text
3 ell (L+1) 2^(-floor(ell/2)).
```

Since `ell<=2^L`, the first expression leaves at least
`(L+3)/2^L-2^(2-ell)` of margin; the second is smaller than that margin for
`ell>=200` (for example, bound it by `3ell^2 2^(1-ell/2)` and use
`24ell^3<2^(ell/2)`, which holds at 200 and increases thereafter, together
with `2^(2-ell)<1/(4ell)`).  The odd
endpoint is no larger.  The native
`population_refinement_hybrid_implication` performs the exact integer
optimization: at `ell=200`, only the nine levels `192<=j<=200` require (RF).
Thus (RF) is needed only in a logarithmic top-conductor window, not across the
whole filtration.

There is now a sharper conductor-martingale reduction.  Put

```text
D_[j]=P_jD-P_(j-1)D.
```

These layers are pairwise orthogonal, and the proved exact-conductor second
moment is

```text
||D_[j]||_2^2 <= 2^(n-ell+j-1)(j-1)^2.                (CL2)
```

For a level-`j-1` Witt cylinder `b`, let `H_j(b)` be its two child population
difference.  Exact Haar inversion gives

```text
D_[j](e)=sign_j(e) H_j(parent_j(e))/2^(ell-j+1).
```

Consequently the whole fourth-moment argument reduces to the single
delocalization estimate

```text
max_e |D_[j](e)|^2
 <= C ell^a (j-1)^2 2^(j-1+n-2ell).                  (SUP-L)
```

Here `C,a` may be any fixed constants.  Interpolating `(SUP-L)` with (CL2),
summing the resulting `L4` norms by Minkowski, and using
`sum_(r<ell) r 2^(r/2)<(5/2)ell 2^(ell/2)` gives

```text
M_4 <= 625 C ell^(a+4) 2^(3ell).                     (CL4)
```

The proper-power-aware endpoint checker verifies that every fixed
polynomial-loss bound (CL4) eventually closes.  The current concrete target
`C=4,a=4` gives `M_4<=2500 ell^8 2^(3ell)` and completes the certified
degree-400 handoff at degrees 401 and 402.

The initially selected absolute-constant specialization `C=4,a=0` is false.
At the even endpoint `(ell,n)=(27,56)`, the level-four sibling-difference peak
is exactly `670285824`, so the required squared constant is

```text
3594264686842871808/648518346341351424 > 4.
```

The exact arbitrary-precision degree recurrence supplies a second violation at
`(ell,n,j)=(343,688,4)`, beyond both the asymptotic threshold and the certified
degree-400 handoff.  It seeds `j-1` rows from full population transforms and
checks the first propagated row against a fresh transform before proceeding.

There is also a structural obstruction to *every* absolute `K`.  For fixed
`j`, normalize all inverse roots of all primitive level-`j` Hayes
`L`-polynomials by `sqrt(2)`.  They form one finite vector on a compact torus.
Simultaneous recurrence supplies `n_k->infinity` for which every normalized
root to the power `n_k` tends to one.  Hence all normalized power sums tend to
`j-1` simultaneously, and Fourier inversion at the identity gives

```text
sup_(endpoint n>=2j+1) kappa_j(n)=2^((j-1)/2),
```

the trivial triangle ceiling.  Since every sufficiently large integer is one
of the two endpoint forms, an absolute `K` cannot be uniform in `j`.

This does not refute polynomial loss in `ell`: the recurrent degree can grow
rapidly with `j`.  Applying the individual Weil estimate inside (HF) proves
`(SUP-L)` whenever `2^(j-1)<=C ell^a`.  For the selected `C=4,a=4`, only

```text
2^(j-1)>4ell^4,
```

or roughly `j>4log2(ell)+3`, remains genuinely open.

That conductor-layer fourth-moment target is sufficient but is not the
shortest route.  Repricing the already proved weighted Haar triangle removes
one factor of `ell` from the required top-level saving.  In the ledger's
original sibling notation

```text
H_j^* = max_b |N_j(b)-N_j(b(1+x^j))|,
```

the selected residual statement is now

```text
(TOP-POLY)  (12ell H_j^*)^2 <= 25(j-1)^2 2^n
```

only for

```text
ell-4ceil(log2 ell) <= j <= ell.                     (TW)
```

Thus the proved individual-Weil estimate needs improvement by only
`12ell/5`, on `4ceil(log2 ell)+1` levels.  Below (TW), individual Weil is used
unchanged.

The implication is elementary and uniform.  Put `c=ceil(log2 ell)` and
`a=ell-4c`.  If

```text
S_low = sum_(j<a) (j-1)2^(j-1),
S_high = sum_(a<=j<=ell) (j-1)2^(j-1),
```

then `S_low<=ell 2^(ell-4c-1)<=2^ell/(2ell^3)` and
`S_high<=ell 2^ell`.  At an odd endpoint, `sqrt(2)<3/2` bounds the scaled Haar
triangle by

```text
2^ell ((3/2)S_low+(5/(8ell))S_high) < 2^(2ell).
```

At an even endpoint it is bounded by

```text
2^(ell+1) (S_low+(5/(12ell))S_high) < 2^(2ell).
```

Both strict inequalities follow already for `ell>=2`; the statement is used
only after the certified `ell>=200` handoff.  The native
`population_refinement_top_polynomial_implication` retains the exact scaled
integers and checks both parities without floating point.

`conductor_layer_sup_norm_diagnostic` records the exact rational squared
constant required at each enumerated level, using only integer sibling
differences.  `check_conductor_layer_sup_bound_sufficiency` separately checks
the symbolic implication and reports the unconditional Weil prefix.  It also
pins the degree-56 refutation, preventing the earlier finite fit through
`ell=20` from being promoted again.  The exact conductor energy also
telescopes multiplicatively as

```text
2^ell M_4/M_2^2 = product_(j=1)^ell (1+q_j),
0<=q_j<=1,
```

which is retained as an invariant rather than mistaken for a bound.
`(TOP-POLY)` remains a valid polynomial improvement over Weil on the moving
top logarithmic window, but the one-sided identity-path target below is
strictly closer to what the paper consumes.  The stronger polynomial-loss
`(SUP-L)` is also sufficient but is no longer selected.  See ADR-0570 and
ADR-0572.

There is a weaker and better-connected target.  Lemire needs only the identity
class, and along its path the weighted increments telescope.  Put

```text
L = ceil(log2 ell)+1,
a = ell-L.
```

Then

```text
sum_(j=a)^ell 2^(j-1) H_j(1)
  = 2^ell N_ell(1) - 2^(a-1) N_(a-1)(1).              (CT)
```

The cyclotomic compression above turns this into an exact relative point
trace.  If `C_j` is the Carlitz curve of conductor `t^(j+1)`, then

```text
(CT) = #C_ell(GF(2^n)) - #C_(a-1)(GF(2^n)).           (RC)
```

Moreover, coherent torsion generators satisfying
`C_t(lambda_(r+1))=lambda_r` give normalized variables
`y_(r+1)=lambda_(r+1)/t` with

```text
y_(r+1)^2+y_(r+1)=lambda_r/t^2.
```

Thus (RC) comes from a chain of `ell+1-a` quadratic Artin--Schreier steps.
The exact genus difference reproduces the separate top-conductor Weil
envelope: it does not yet improve it.

Fourier identity (HF) also shows that (CT) is one signed Mangoldt trace over
all characters of conductor level at least `a`.  No absolute value has been
taken between those levels.  The earlier symmetric target was

```text
abs(2^ell N_ell(1) - 2^(a-1) N_(a-1)(1))
  <= 2^(2ell-2).                                       (CRT)
```

The individual Weil estimate (W) below `a` contributes, after normalization
by `2^(2ell)`, at most

```text
(ell-L-3)/2^L + 2^(2-ell) < 1/2
```

for every `ell>=200`, because `2^L>=2ell`.  Bound (CRT) contributes one
quarter, so their sum is strictly below the endpoint target with reserve.  At
`ell=200`, this connected trace contains the ten levels `191<=j<=200`.
Compared with summing individual Weil bounds on those levels, (CRT) needs only
a polynomial conductor saving; the per-level (RF) estimate demands an
exponential family gain and is therefore a stronger fallback.

The separate-Weil loss can be stated exactly.  On the same top window its
numerator is

```text
2^ceil(n/2) sum_(j=a)^ell (j-1)2^(j-1).
```

At both degree-401 and degree-402 endpoints with `ell=200`, this is exactly
`50641/32` times the connected allowance, so an integral saving statement
must provide a factor at least `1583`.  In general the ratio is

```text
8 ((ell-2) - (a-3) 2^(a-ell-1)),
```

which is asymptotic to `8ell`.  Thus (CRT) asks for a linear conductor saving
over separate Hasse--Weil, not an exponential square-root gain in the number
of characters.  The CAS exposes both the raw separate-Weil numerator and its
exact ceiling saving factor so a proposed Witt/Heisenberg lemma can be tested
against the endpoint before it receives proof credit.

`population_refinement_connected_top_implication` checks the arithmetic
implication exactly.  The finite population report also computes the identity
path, reconstructs (CT) independently from the fine and coarse populations,
and tests (CRT).  At level 12 the odd and even connected traces are
`1,400,832` and `1,339,392`, both below `4,194,304`.  These finite values do
not prove (CRT).  Fresh exact fleet runs at both endpoints for every
`16<=ell<=20` also pass.  At `ell=20`, the traces are `2,381,365,248` and
`-6,237,356,032` against `274,877,906,944`, ratios about `0.0087` and `0.0227`.
The executable SHA-256 is
`ea8780c3914b139ad7dffbc9a9b69336120219782f72b88962fb6f58e2a90687`;
the five logs and their hashes are recorded on `s1,s4,s5,s6,s7` under
`/tmp/axeyum-gf2-hayes-refinement-connected-{16,17,18,19,20}.log`.  This is
still finite evidence only.

The paper-facing statement can be weakened once more because only a lower
bound for the identity population is required.  Retain the same
`c=ceil(log2 ell)` and `a=ell-c-1`, and put

```text
W_(ell,n) = 2^ceil(n/2) sum_(1<=j<a) (j-1)2^(j-1),
B_(ell,n) = 2^(2ell)-W_(ell,n).
```

The low Haar part is at least `-W_(ell,n)`.  It is therefore enough to prove
the one-sided relative trace estimate

```text
(REL)  (CT) > -B_(ell,n).
```

Positive values of (CT) are unrestricted.  At `ell=200`,
`B_(ell,n)` is just below `(81/128)2^(2ell)` and the separate-level Weil
envelope needs an integral saving of 626, rather than 1,583 for (CRT).  The
new requirement is asymptotic to a factor `4ell+O(log ell)`.
`population_refinement_one_sided_connected_implication` checks the strict
boundary and the exact allowance partition for both parities through
`ell=1024`.  It proves the implication, not (REL).  ADR-0572 selects (REL)
over both (CRT) and the stronger TOP-POLY statement.

A relative characteristic-two theorem should now target this one harmful
sign of the single trace (CT), preserving cross-conductor cancellation.

There is a strictly localized second-moment route to the same one-sided
target.  Put `c_0=a-1`, let `K=ker(E_ell -> E_(c_0))`, and write

```text
R = #K = 2^(ell-c_0),
x_e = N_ell(e)                  (e in K),
S = sum_(e in K) x_e = N_(c_0)(1).
```

The connected trace is exactly the displacement of the identity child from
the average of this one coarse cylinder:

```text
(CT) = 2^ell (x_1-S/R).
```

For the conditional variance

```text
V_id = sum_(e in K) (x_e-S/R)^2
     = sum_(e in K) x_e^2-S^2/R,                         (ICV0)
```

The binary quotient filtration gives an exact local Haar decomposition. If
`H_j(p)` denotes the difference of the two level-`j` child populations of a
parent `p` above the coarse identity, then

```text
R V_id = sum_(j=c_0+1)^ell 2^(j-c_0-1)
           sum_(p above 1 in E_(c_0)) H_j(p)^2.          (ICV-H)
```

The native report reconstructs every summand and fails closed unless their
sum equals the direct conditional variance. Thus the missing positive-square
statement is precisely a local Carleson-energy estimate on one ramified
identity subtree.

The sharp zero-sum point inequality gives

```text
(x_1-S/R)^2 <= (R-1)V_id/R.                              (ICV1)
```

Thus the exact sufficient threshold is

```text
2^(2ell)(R-1)V_id/R < B_(ell,n)^2.                       (ICV-exact)
```

A cleaner, slightly stronger premise is

```text
(ICV)  V_id <= 2^(2ell-2).                               (ICV)
```

For every `ell>=200`, the already checked low-Weil calculation gives
`B_(ell,n)>2^(2ell-1)`.  Since `(R-1)/R<1`, (ICV1) then gives
`abs(CT)<2^(2ell-1)<B_(ell,n)`, proving (REL).  The native operations
`identity_cylinder_conditional_variance` and
`identity_cylinder_quarter_variance_implication` retain both the sharp and
clean integer comparisons.  The symbolic implication is checked for both
endpoint parities through `ell=1024`.

This is not the old global variance in disguise.  If `eta` runs over the
characters of `K`, restriction Fourier inversion gives

```text
V_id = R^(-1) sum_(eta != 1)
          abs(2^(-c_0) sum_(chi restricted to K = eta) S_n(chi))^2. (ICV-F)
```

The inner sum combines every coarse-character twist **before** it is squared.
Applying Cauchy inside those twist blocks returns the global `M_2` envelope
and loses the localization.  At `ell=200`, (ICV) asks for integral savings
`313648` and `627296` over the proved individual-Weil global envelope at the
odd and even endpoints respectively.  These are polynomial, about
`7.84ell^2` and `15.68ell^2`, while a genuinely uniform distribution over the
`2^c_0` coarse cylinders would give an exponential gain.

The clean target is false in the finite prefix: for example the even
`ell=13` row has conditional-variance numerator `2181638144` against the
same-denominator target `1073741824`.  It holds at both endpoints for every
exact row `14<=ell<=23`.  At the first two-sided success `ell=14`, the odd and
even numerators are `1288331008` and `2905795008` against target
`4294967296`; by the even `ell=23` row the scaled square sum is
`1649531354734592` against the sharp REL ceiling
`709227422017958242`.  These are finite diagnostics, not a theorem.

The closest published fixed-field variance bounds do not supply (ICV-F).
Hast--Matei's `m=2` theorem averages over all short intervals and leaves its
constant dependent on the growing `(n,h)`.  Baier--Bhandari's fixed-`q`
hybrid variance also averages over centers and residue classes and explicitly
assumes `Q(0)!=0`; after reversal the present nested quotient has modulus a
power of `x`.  The missing statement is therefore a localized
coarse-twist/Carleson estimate at the ramified modulus, not another global
second moment.  ADR-0578 records this boundary and keeps (REL), rather than
(ICV), as the paper's sole minimal lemma.

There is now a weaker sufficient localization target.  For each retained
level let

```text
F_j(1)      = sum_(p above 1 in E_(c_0)) H_j(p)^2,
F_j(global) = sum_(all level-j parents p) H_j(p)^2.
```

Exact-conductor Parseval and individual-character Weil give
`F_j(global)<=(j-1)^2 2^n`.  Therefore the levelwise polynomial-share estimate

```text
(PL2)  16 ell^2 F_j(1) <= F_j(global)
       for every c_0<j<=ell
```

implies

```text
R V_id <= sum_(j=c_0+1)^ell 2^(j-c_0-1)
          floor((j-1)^2 2^n/(16 ell^2)),
```

and the right side is below `R 2^(2ell-2)` for both endpoint parities at
every `ell>=200`.  The implication is checked exactly through `ell=1024`.
This requires only a quadratic saving over the trivial concentration bound.

The stronger experimental inequality

```text
(LC2)  2^c_0 F_j(1) <= ell F_j(global)
```

also implies `(PL2)` with enormous asymptotic room.  At
`(ell,n)=(200,401)`, the largest integral localization multiplier allowed by
the clean variance target in the `(LC2)` normalization is
`5007710127439295349009662031980010502580210696737863`, greater than
`2^170`, whereas (LC2) assumes only `200`.

The stronger uniform share `2^c_0 F_j(1)<=F_j(global)` fails on many exact
rows.  By contrast (LC2) survives both endpoint parities through `ell=23`,
including pinned fleet runs for `19<=ell<=23`, but that is still finite
evidence and is much stronger than the selected `(PL2)`.
The natural prospective proof is a characteristic-free `m=2` Hast--Matei
short-interval variety sliced by the `c_0` fixed common leading
coefficients, with the level-`j` sibling twist retained.  Hast--Matei's
complete-intersection and singular-locus proof is characteristic-free for
`m=2`; their published point-count theorem, however, averages over all
centers and leaves degree-dependent constants.  An explicit bound for the
fixed cylinder slice remains unproved.  ADR-0580 selects `(PL2)`, retains
`(LC2)` only as a stronger diagnostic, and grants neither theorem credit.

The same target has a deliberately weak global fourth-moment sufficient form.
If `N_j=2^(j-1)`, `Q_j=sum_p H_j(p)^4`, and
`K_j=N_j Q_j/F_j(global)^2`, then Cauchy on the
`N_j/2^c_0` identity-cylinder parents proves `(PL2)` whenever

```text
K_j <= 2^c_0/(256 ell^4).                               (WK2)
```

Unlike the earlier Gaussian-scale proposals, `(WK2)` permits an exponentially
growing normalized kurtosis.  This is the correct price for importing an
`m=4` Hast--Matei-type estimate: an absolute constant is unnecessary, but the
published degree-dependent constant is still not explicit enough to compare
with `(WK2)`.

There is now a multiplicative localization of `(PL2)` which avoids asking for
one opaque cylinder estimate.  Fix a retained level `j`, put
`M_0=F_j(global)`, and for `1<=i<=c_0` let `M_i` be the same sibling square
mass restricted to parents above the identity in `E_i`.  These are nested
nonnegative masses,

```text
M_0 >= M_1 >= ... >= M_c0 = F_j(1).
```

Consequently `(PL2)` follows if, for every retained `j`, at least

```text
ceil(log2(16 ell^2))
```

of the binary path steps satisfy `2 M_i<=M_(i-1)`; every unselected step may
use only the tautology `M_i<=M_(i-1)`.  At `ell=200` this asks for 20
half-balanced steps among 190 available coarse levels.  Alternatively, 47
steps satisfying `4 M_i<=3 M_(i-1)` suffice.  The native
`identity_cylinder_path_split_implication` report computes both prices with
exact integers through `ell=1024`, while the exact finite conditional-variance
report now reconstructs every intermediate path mass and comparison.  This is
a stronger, potentially more local sufficient lemma rather than a proof:
neither the half-balanced step count nor `(PL2)` is established.  ADR-0581
records the boundary.

The first half-balanced split is universal whenever it lies on the path.
Translation `f(x)->f(x+1)` preserves degree and von Mangoldt weight.  If
`t=2^v_2(n)`, Lucas parity makes `t` the first positive odd binomial index in
row `n`; hence translation fixes the first `t-1` zero leading coefficients,
toggles coefficient `t`, and permutes the two children at every later Haar
level.  It follows exactly that `2M_t=M_(t-1)` whenever `t<=c_0`.  The native
translation-split report checks the index and residual ledger, and every exact
finite path independently reproduces the equality.  At `n=401` and `402` this
spends one of the 20 required half splits, leaving 19.  For power-of-two `n`,
however, `t=n` lies beyond the coarse path; translation alone cannot prove the
remaining logarithmic split count.

The separate levelwise path is stronger than the conditional-variance
argument needs.  Retain the Haar weights and combine every retained level
before imposing localization:

```text
A_i = sum_(j=c_0+1)^ell 2^(j-c_0-1) M_(i,j).
```

The masses remain nested and nonnegative, while the terminal identity is now
exactly

```text
A_(c_0) = R V_id,
```

the numerator of the conditional variance already used by the sharp
point-versus-variance implication to `(REL)`.  If `U_(ell,n)` is the
Haar-weighted individual-Weil envelope for `A_0` and `T_(ell,n)` is the
largest integral terminal mass permitted by the strict `(REL)` allowance,
then it is enough to have the least `r` with

```text
2^r T_(ell,n) >= U_(ell,n)
```

half-balanced steps on this **one aggregate path**.  The sharp integer ledger
asks for 18 steps at `(ell,n)=(200,401)` and 19 at `(200,402)`; translation
spends one, leaving 17 and 18.  The corresponding three-quarter prices are 43
and 45.  This is strictly weaker than asking for 20/47 steps separately on
every retained level.  The native aggregate implication and exact path
reconstruction preserve the strict boundary and all Haar weights.  The
remaining aggregate contractions are still unproved; ADR-0582 records the
new selected positive-square bridge without granting `(REL)` proof credit.
On the exact-source `e046d1d05` fleet controls for both endpoints and every
`19<=ell<=23`, all 140 aggregate path steps satisfy the weaker
`4A_i<=3A_(i-1)` comparison, whereas only 69 are half-balanced.  The contrast
shows that pooling repairs the levelwise three-quarter failures and that the
new diagnostic is non-vacuous.  It remains finite evidence: no universal
three-quarter contraction is claimed.

There is an exact spectral form of this aggregate path which prevents the
finite pattern from being mistaken for a generic martingale inequality.  On
the coarse quotient `Q=E_c`, let `w(q)` be `R` times the conditional variance
inside the fibre above `q`.  Then `A_i` is the sum of `w` over the identity
cylinder of `E_i`.  If `Dhat(psi)` is the unnormalised Fourier transform of the
centered Mangoldt populations, conditional-variance subtraction removes the
complete low-conductor block and leaves

```text
what(eta) = 2^(-c) sum_(cond(psi)>c)
              Dhat(psi) conjugate(Dhat(psi eta^(-1))).
```

Consequently

```text
2^i A_i - 2^(i-1) A_(i-1) = sum_(cond(eta)=i) what(eta).
```

The CAS now emits this signed layer sum as an exact integer reconstructed from
the spatial masses; the translation-forced split makes it zero.  Thus the
missing theorem is a low-twist decorrelation estimate for only the unresolved
high Hayes trace powers, not the earlier full squared-discrepancy spectrum.
Generic Cauchy and individual-Weil bounds remain trivial.  ADR-0583 records
the identity and the fixed-`q` literature boundary without claiming the
decorrelation.

Expanding that shifted moment through `Lambda=mu*deg` does **not** immediately
return to the restricted four-shift obstruction of ADR-0562.  Write

```text
D(g)=sum_(1<=d<ell) T_d(g),
T_d(g)=d sum_(u in V_d) M_(n-d)(g u^(-1)).
```

For two orders, polarize the conditional variance inside each coarse fibre:

```text
w_(d,e)(q)
 = R sum_(g in qK) T_d(g)T_e(g)
   -(sum_(g in qK)T_d(g))(sum_(g in qK)T_e(g)).
```

Then `w=sum_d w_(d,d)+2sum_(d<e)w_(d,e)`, including after identity-cylinder
selection and the exact-conductor layer difference.  Expanding the two
`T` factors gives a bilinear sum with weight `mu(A)mu(C)`, hence on the
squarefree locus the paired Berlekamp phase

```text
(-1)^(deg A+deg C+Berl(A)+Berl(C)).
```

There are exactly two Mobius factors before Cauchy; four appear only after
squaring this new signed sum.  The native
`identity_path_mobius_order_pair_report` reconstructs each layer from all
symmetric order pairs and checks it against the independent spatial value.
At `ell=8`, pairwise absolute values lose factors between about 26 and 57 on
the nonzero pinned layers.  Translation gives more than aggregate zero at its
forced layer.  The automorphism `f(x)->f(x+1)` preserves `mu`, every interval
space `V_d`, and hence every `T_d` separately.  At `t=2^v_2(n)`, Lucas parity
interchanges the two children after fixing their parent, so every `(d,e)`
order-pair layer is exactly zero.  Both pinned endpoint rows check all 28
cellwise equalities; the typed report fails closed on any contradiction.
Thus the live Berlekamp target is a combined two-polynomial phase under the
centered multiplicative Hayes-class kernel, with all orders retained.  The
older inverse-additive energy and four-shift theorems would be regressions if
inserted through another square.  ADR-0584 records the exact kernel and still
assigns no contraction or endpoint credit.

This target also sharpens the Hast--Matei boundary.  With
`h=n-ell-1`, their `X_(2,n,h)` is the natural two-polynomial coefficient-pair
space and their geometry is valid in characteristic two: the `p>n`
restriction applies only when `m>2`.  But their published arithmetic estimate
is untwisted, averages over all interval centers, and permits constants
depending arbitrarily on the growing `(n,h)`.  The needed new statement is a
rank-one principal-unit/Witt local-system trace bound on `X_(2,n,h)` after the
coarse component is removed, projected onto the two long-cycle factors.  It
must bound the complete signed `(BM2)` sum at the exact `(PRICE)` threshold.
No canonical lift of the principal-unit action to ordered roots, and no such
degree-uniform local-system theorem, has yet been proved; this is a precise
geometric bridge rather than proof credit.

The character-parameter presentation nevertheless proves one uniform piece
of that bridge.  Sawin's universal Witt family applied to the fixed pair of
rank-one sheaves `1,L_(eta^(-1))` has product geometric monodromy containing
the two special-linear factors, in characteristic two as well as in odd
characteristic.  The degree-`n` Mangoldt sum is the power-sum character
`p_n(U)=trace(U^n)`.  Its hook expansion contains no representation trivial on
`SL_(j-1)` because `n>j-1` and the only rectangular hook is `(1^(j-1))` at
`n=j-1`.  Hence the external shifted character has no invariant vector and
the top compactly supported cohomology of every nontrivial shift vanishes.

This is a real weight cancellation, but not yet the endpoint estimate.
Sawin fixes the conductor and sheaves while `q` tends to infinity and
explicitly does not provide uniformity in those inputs.  At fixed `q=2`, the
remaining degrees carry only a formal `2^(-1/2)` weight drop multiplied by
their conductor- and Adams-power-dependent Betti complexity.  The missing
statement `(WITT-LOW)` must bound their complete signed trace, summed over the
exact low-twist layer and all high conductors, by ADR-0584's native contraction
price.  ADR-0585 records the proved top vanishing and leaves that lower trace
open rather than importing a large-field asymptotic.

The most direct zero-`2`-rank shortcut is now priced exactly and gives no
endpoint information.  Deuring--Shafarevich gives `2`-rank zero at both
Carlitz levels, hence also on the relative Jacobian quotient.  But the general
Cramer--Xing trace theorem supplies only

```text
2^ceil(n/g_rel) | (CT),
g_rel = (2g_ell-2g_(a-1))/2.
```

Here `g_rel>n` for both endpoints throughout `ell>=200`, so the exponent is
one and the guaranteed divisor is two.  Rounding a Weil--Serre envelope to an
even integer can save at most one, versus the required multiplicative factor
626 at `ell=200`.  The native Carlitz geometry report checks this through
`ell=1024`.  Ma--Xing's stronger code bound concerns one
scalar Artin--Schreier character, while (CT) is a complete non-elementary Witt
zero fibre; summing scalar bounds separately recovers the existing relative
Hasse--Weil envelope.  Yoo--Lee's elementary-abelian applications likewise do
not apply to the cyclic `2`-power blocks of this quotient.  ADR-0573 records
the source-level audit and selects a collective Witt complete-weight or
zero-fibre estimate as the necessary form of any coding bridge.

The stronger characteristic-two Newton-over-Hodge result developed in the
separate `noh-p2-2026-08` review artifact can also be priced without importing
that artifact into this lane. An exact level-`j` Carlitz character has Hodge
slopes `1/j,...,(j-1)/j`, so the claimed polygon domination would make the
degree-`n` trace divisible by `2^ceil(n/j)`. Galois stability then makes the
connected trace divisible by `2^ceil(n/ell)=8` at both endpoints. At
`ell=200`, however, the existing Weil envelope is already a multiple of eight:
rounding saves zero, while divisibility-based rounding alone would need
exponent `409`, leaving `406` bits missing. The conditional native ledger
`carlitz_connected_top_newton_hodge_ledger` records this boundary. ADR-0579
therefore treats Newton-over-Hodge as a valuable independent theorem but not
as proof credit for `(REL)`.

The fixed-`q` Hankel route is now source-audited and natively representable,
but it does not yet improve this target.  Yiasemides's theorem computes the
second moment of the divisor function `d_2`, not a prime-weighted fourth moment.
The Lemire interval does lie in its favorable half-degree regime.  However, the
source's own higher-moment reduction stops at additively constrained triples
whose truncated Hankel sequences are all quasi-regular; its Dirichlet
`L`-function fourth-moment discussion separately retains simultaneous rank,
kernel, and truncation conditions.  Expanding `Lambda=mu*deg` additionally
restores the signed cross-order convolution already present in (HFC).

`binary_hankel_characteristic` now computes the exact balanced binary Hankel
rank and `(rho,pi)` characteristic under deterministic limits.  Exhaustive
tests through sequence length nine compare every output with independent
row-span enumeration.  This removes a CAS gap and permits a signed residual
stratum to be stated without external algebra software; it does not turn the
published divisor variance into a proof of (REL).  ADR-0574 requires any
further Hankel result to retain the Mobius signs and discharge an endpoint
ledger before receiving proof credit.

The top-conductor projector also has an exact Möbius-order decomposition.
Applying the fine-minus-coarse scales before absolute values gives, at
`ell=8`,

```text
n=17: [-768, 8192, -2304, 2048, 10240, 15360, -21504],
n=18: [-4096, 7168, 9984, 0, -5120, 13824, -3584].
```

These vectors sum to the independently selected traces `11264` and `18176`.
Order one survives in both rows; all seven orders survive in the odd row and
six survive in the even row.  Thus the projector does not turn (CT) into a
high-convolution-order tail.  The native
`connected_top_mobius_convolution` report checks the main-term cancellation,
every scaled order, and the final reconstruction.  A proof must preserve the
signed cancellation across these orders as well as across conductors; taking
orderwise absolute values is not a justified endpoint bridge (ADR-0543).

The fine and coarse Möbius Fourier expansions can in fact be placed in one
domain.  Projection from level `ell` to level `c=a-1` commutes with unit
inversion, so for every shared degree and `0<=alpha<2^c`,

```text
H_k^(ell)(alpha)=H_k^(c)(alpha).
```

If `alpha` is nonzero, its low-bit annihilator depth is below `c`, and the
eligible convolution orders at the two levels are identical.  At the zero
frequency, `H_k(0)=0` for every relevant `k>=2`.  Therefore the connected
projector cancels the complete inflated coarse spectrum and gives the exact
high-frequency identity

```text
(CT) = sum_(2^c<=alpha<2^ell)
         sum_(1<=d<=v(alpha)) d 2^d H_(n-d)^(ell)(alpha),       (HFC)
```

where `v(alpha)` counts vanishing low bits.  The native
`connected_top_inverse_mobius_fourier_regroup` checks the quotient embedding,
all `2^c` zero connected frequencies, both independent trace
reconstructions, and the final annihilator layers.  At `ell=8`, the raw
cellwise, connected-order, frequencywise, and layerwise absolute totals are
`313952,60416,162672,71280` for `n=17` and
`415264,43776,205856,70208` for `n=18`.  Order and annihilator regroupings are
thus cross-cutting: neither intermediate absolute total dominates the other.
Identity (HFC) is a sharper statement of the analytic target, but its
surviving support has size `2^ell-2^c`; it is not itself the missing
cancellation estimate (ADR-0544).

Even one Cauchy inequality after all of that exact cancellation is too lossy
on the pinned rows.  Write `F(alpha)` for the inner signed sum in (HFC).
The structural-support estimate would be

```text
abs((CT))^2 <= (2^ell-2^c) sum_alpha abs(F(alpha))^2.       (HC2)
```

At `ell=8`, the exact square sums at degrees 17 and 18 are `1541548032` and
`1604489216`.  The connected allowance square is `268435456`; after division
by the support size `248`, (HC2) can tolerate square sum only `1082401`.
Thus the exact rows would require further integral savings `1425` and `1483`,
although their original signed traces already satisfy (CRT).  The native
report pins the square sums, Cauchy products, thresholds, and rejection
predicate.  This is a finite stopping test, not an asymptotic counterexample:
a theorem only for `ell>=200` could still prove a new normalized norm collapse.
But absent that explicit saving, a positive `L2` argument still erases the
essential high-frequency phases and receives no endpoint credit (ADR-0545).

This exact tower does **not** by itself put (RC) under the available
Ito--Takeuchi--Tsushima theorem.  Their Heisenberg construction treats the
special one-equation curves `y^2-y=xR(x)` for linearized `R` and a length-two
Witt Lang torsor.  Here the number of Artin--Schreier steps grows like
`log ell` in the selected relative window.  A valid bridge must exhibit an
actual reduction of the relative Carlitz cohomology to that quadratic class,
or prove an analogous commutator-rank statement for the whole chain; matching
terminology is not enough.  See [The L-polynomials of van der Geer--van der
Vlugt curves in characteristic 2](https://arxiv.org/abs/2505.22036).

There is now an exact obstruction to the strongest possible version of that
bridge.  If a whole exact-conductor component were supersingular, then every
Frobenius eigenvalue would be `sqrt(2)` times a root of unity.  At even degree
`2m`, its integral trace would consequently be divisible by `2^m`.  The
native exact-conductor computation gives

```text
T_(10,22) = -5120,
```

which has remainder `1024` modulo `2^11=2048`.  Hence even the *new*
level-ten component is not supersingular; nonsupersingularity is not confined
to the inherited level-four factor.  This rigorously rejects a decomposition
of every new Carlitz layer into only the supersingular quadratic Heisenberg
pieces.  It does not reject a useful smaller subquotient or a
non-supersingular rank argument for the connected relative trace.

Nor does a direct family `L2` estimate preserve enough information.  Summing
the exact second moments of all top characters and applying Cauchy gives

```text
|sum_top S_chi(n)|^2
  <= (# top characters) sum_top |S_chi(n)|^2.
```

At `ell=12`, there are 4032 top characters.  The exact degree-25 moment is
`1326053720064`, making the Cauchy square `303.92` times the (CRT) allowance
square; degree 26 gives ratio `632.42`.  The required integral moment savings
are respectively `304` and `633`, even though the actual signed traces satisfy
(CRT).  The native `connected_top_second_moment_cauchy` report pins these
values and the exact threshold.  This finite failure is not an asymptotic
counterexample, but it shows that Cauchy discards precisely the phase
alignment the connected reformulation was designed to retain.

Exact fleet runs at both endpoints for every `16<=ell<=20` satisfy the Haar
triangle and (RF).  At `ell=20`, the odd and even triangle numerators are
respectively `64,147,961,856` and `96,723,105,792`, against the common target
`1,099,511,627,776`; their ratios are approximately `0.0583` and `0.0880`.
The release executable used for the original coefficient-two sweep has
SHA-256
`1d0092a8087a353a00e1d13725488cfec4b2c5001ea6f4339ebf8017c69eeecc`;
the per-level logs remain on `s1,s4,s5,s6,s7` as
`/tmp/axeyum-gf2-hayes-refinement-{16,17,18,19,20}.log`.  These rows select a
lemma; they do not prove its universal quantifier.

The raw refinement target is not the already refuted valuation-layer
square-root claim.  Each `H_j` first aggregates the complete degree-`n`
Mangoldt population in a quotient cylinder and only then compares its two
children.  Analytically, (RF) asks for square-root cancellation in the
residual fibre dimension `n-j`, with a linear conductor loss.  A relative
Artin--Schreier--Witt or fixed-long-cycle estimate at exactly that scale would
finish the proof, but the connected target (CRT) is weaker and preserves
cross-conductor cancellation.  Until one of these estimates is derived, this
remains a parallel local route beside the aggregate connected-cumulant bound,
not theorem credit.

The elementary-abelian generalization of Fomenko's fixed-coordinate character
map is now closed before any expensive `L`-factor enumeration.  The native cyclic
decomposition has one 2-typical Witt block for every odd `m<=ell`.  Reducing
each block coordinate modulo two is a surjective homomorphism

```text
E_ell -> GF(2)^ceil(ell/2),
```

but its kernel has dimension `floor(ell/2)` and order
`2^floor(ell/2)`.  `binary_witt_first_slot_projection_report` reconciles the
source, image, and kernel orders from the checked block decomposition; an
exhaustive small-level control independently verifies every fibre and every
homomorphism pair through `ell=8`.  Fomenko's useful kernel is small because
the number of prescribed coordinates is fixed.  Selecting the first active
coordinate from every growing Witt block instead leaves an exponentially
large unresolved family.  In fact this kernel is minimal for every map to a
binary vector space: such a homomorphism kills `2E_ell`, factors through
`E_ell/2E_ell`, and that maximal elementary quotient has rank
`ceil(ell/2)`.  Ordinary characterwise Weil bounds inside those fibres
therefore reproduce the endpoint loss for every additive-coordinate variant,
not only the first-slot presentation.  A non-elementary higher-Witt quotient
could still work if it brings new cross-block orthogonality (ADR-0516).

A different generalization, closer to Fomenko's literal restriction map, is
also now exact.  For `1<=t<ell`, let `H_t` be the subgroup of principal units
congruent to one modulo `x^(t+1)`.  Restriction of characters to `H_t` is
surjective and has kernel the inflated group `E_t^dual`, of order `2^t`.
Individual restriction fibres are cyclotomic rather than rational, so the
native `hayes_fomenko_restriction_packet_report` first closes each fibre under
odd-power Galois action.  It then reconstructs every integral packet trace
with two transform primes and requires their signed sum to equal the
independent exact-conductor trace.

The strongest one-unit packet estimate is false.  At `(ell,n)=(12,26)`, the
literal `t=1` choice has 256 rational packets, 233 of which exceed `2^13`;
the maximum is `226816`, requiring coefficient 28.  Their absolute sum is
`15422336`, versus signed total `933888`.  Matching the connected window with
`t=ceil(log2 ell)+1=5` leaves 32 packets, but 29 exceed `2^13`; the maximum
is `525056`, requiring coefficient 65, and the packetwise absolute sum is
`6433280`.  Thus the larger kernel compresses the number of packets without
creating the missing trace cancellation.

This pinpoints the nonformal ingredient in Fomenko's level-three theorem.  In
Gorodetsky's exposition, the restriction coordinates feed an explicit
degree-two `L`-polynomial formula; surjectivity and kernel size alone are not
the estimate.  A growing-conductor analogue would need a new uniform formula
or cross-packet orthogonality.  The exact quotient remains available for that
purpose, but it contributes no present endpoint credit (ADR-0538).

Existing geometric
higher-moment work of Hast and Matei treats fixed polynomial degree as the
field size tends to infinity, whereas this problem fixes the field at two and
moves both degree and conductor.  It therefore motivates the complete-
intersection interpretation but does not prove this envelope; see
[Higher moments of arithmetic functions in short intervals: a geometric
perspective](https://arxiv.org/abs/1604.02067).

### Why Sawin's binary square locus does not yet recurse

Sawin's complete-intersection geometry gives an exact and useful weight
cutoff.  For `X_(n,m,c)` in characteristic two, the bad locus has dimension at
most `floor(n/2)-floor(m/2)`, because at infinity its root polynomial has
zero derivative and therefore lies in `k[u^2]`.  At the Lemire endpoints this
would leave ample exponential room if the long-cycle part of the remaining
cohomology had only polynomial or partition-scale multiplicity.

That last implication is not present in the source.  The proof of Sawin's
vanishing lemma replaces the defining equations by a **generic** complete
intersection.  Those generic equations are not symmetric, so the smoothing
and its vanishing-cycle triangle do not carry the `S_n` action of the original
root variety.  Although `H_c^*(X_(n,m,c))` itself is an `S_n` representation,
the support argument used to bound its degrees cannot consequently be
projected onto the von Mangoldt long-cycle virtual character.

Nor is the support a recursive copy of a smaller short-interval variety.  The
logarithmic-derivative calculation says only that the finite symmetric
quotient sends the bad locus at infinity into the even-coefficient subspace.
It does not identify vanishing-cycle stalks, their multiplicities, or their
Frobenius actions there.  The quotient is wildly ramified on this repeated-
root locus in characteristic two, so those missing data cannot be discarded.

The exact character identity remains

```text
Tr(Frob * sigma_n | H_c^*(X_(n,m,0)))
  = sum_(f in I_0) Lambda(f)
  = # {alpha in GF(2^n): charpoly(alpha) is in I_0}.
```

The native `identity_class_count` reconstructs this population exactly over
the base field `GF(2)`.  It does **not** compute the fixed-degree interval over
`GF(2^r)` for `r>1`; those are higher Frobenius traces of the long-cycle
complex, not degree-`rn` Hayes populations over `GF(2)`.  ADR-0527 therefore
adds a separate bounded extension-field operation with certified field moduli,
exact prime-power recognition, and explicit population admission.

Its ordinary tests reproduce

```text
A_r(5,2)=(-4)^r-(-2)^r for r=1,2,3,
(A_1,A_2,A_3)(9,4)=(5,129,-1771).
```

The `r=1` rows cross-check the Hayes value layer.  The `r>1` rows are genuine
new trace coordinates, but remain finite diagnostics.  Applying the fixed-
point formula merely identifies what they count; it does not bound their
number of Frobenius modes as the prescribed-coefficient count grows.  A valid
geometric bridge must still construct an equivariant smoothing, bound the
twisted trace directly, or identify a recursive complex including its stalk
ranks and cyclic induction data (ADR-0526).

The explicit ignored release probe also enumerates the first
four-fixed-coefficient stopping row over `GF(32)`, using the certified modulus
`x^5+x^2+1`:

```text
n=9, m=4, candidates=32^5=33,554,432,
sum Lambda=33,525,757,
A_5(9,4)=-28,675.
```

It completed in 206.15 seconds and independently matches the earlier scratch
value.  A deterministic 64-shard run over `GF(64)`, with certified modulus
`x^6+x+1`, subsequently covered all `64^5=1,073,741,824` interval polynomials
and returned

```text
sum Lambda=1,073,464,057,
A_6(9,4)=-277,767.
```

ADR-0529 makes that split native and fail-closed.  Each coefficientwise
Frobenius orbit is owned by its least encoded representative, whose exact
Mangoldt weight is multiplied by its orbit size.  The merge rejects missing,
duplicate, noncontiguous, or differently parameterized shards.  A checked
hierarchical collapse also permits a commensurable fine partition to rebuild
one skewed coarse range without trusting an aggregate generated outside the
CAS.  Over `GF(128)`, with certified modulus `x^7+x+1`, this route covered all
`128^5=34,359,738,368` candidates and returned

```text
sum Lambda=34,357,258,693,
A_7(9,4)=-2,479,675.
```

Exact Hankel minors from `A_1,...,A_7` are nonzero at two consecutive
order-two offsets and at order three:

```text
det H_(1,2)=7,972,848,576,
det H_(2,2)=569,010,016,512,
det H_(1,3)=-6,852,895,898,075,136.
```

This rigorously rejects every constant-coefficient recurrence of order at most
three at the four-coefficient boundary.  It does not determine the reduced
zeta factor or its growth with `m`, so no asymptotic theorem credit is attached.

### Exact cyclic/Foulkes compression and its remaining theorem

The alternating-hook representation used for von Mangoldt is much smaller as
a virtual character than Sawin's parity split exposes.  If

```text
F_(n,r)=Ind_(C_n)^(S_n) theta_r,
```

Foulkes's formula and Ramanujan orthogonality give

```text
p_n = sum_(r mod n) c_n(r)/phi(n) F_(n,r)
    = sum_(k|n) mu(k) F_(n,n/k).                 (FC)
```

The second equality groups the `n` residue labels into the `tau(n)` distinct
induced characters.  Its exact coefficient mass is only

```text
sum_(k|n) |mu(k)| = 2^omega(n)=n^o(1).
```

The public `sawin_foulkes_endpoint_ledger` now certifies `(FC)` without a
character table oracle.  It evaluates each Ramanujan sum from both its divisor
formula and the independent von Sterneck totient formula, reconstructs every
power-sum coefficient by orthogonality, checks the grouped Möbius coefficients,
and admits the residue-by-divisor table only under explicit work limits.

This compression leaves a precise rather than qualitative endpoint margin.
For `ell=ceil(n/2)-1` and interval dimension `h=n-ell`, Sawin's binary weight
exponent is `W/2`, with

```text
W=h+floor(n/2)-floor(ell/2)+1
 =2h-floor(ell/2).
```

Consequently, if `B` uniformly bounds the effective Betti multiplicity of
each cyclic summand, the Foulkes triangle proves an irreducible exactly when

```text
(2^omega(n) B)^2 2^W < (2^h-P_n)^2,              (CF)
```

where `P_n=1` at the odd endpoint, while the even endpoint uses the proved
upper bound

```text
P_n <= (n/2)2^(n/2-floor(ell/2)) + n2^ceil(n/3).
```

At the first two degrees beyond the finite certificate, this allows
`B<=2^49-1` for `n=401` and `B<=2^47-1` for `n=402`.  A polynomial bound with
effective constants would therefore fit comfortably.  Sawin's published
generic bound `3(n+2)^(n+ell)` does not: substituting it into the same native
integer ledger fails.  Equation `(FC)` is proved representation theory;
inequality `(CF)` is only a checked implication.  No source currently proves
the required characteristic-two cyclic-eigenspace bound, so neither line is
endpoint theorem evidence (ADR-0550).

Wan--Zhang's 2026 complete-intersection theorem is a genuine improvement to
that comparison.  Applied to the first `ell` elementary-symmetric equations,
it gives the exact total-Betti bound

```text
B_WZ=binom(n-1,ell-1)(ell+1)^n.
```

The native ledger now inserts this value before the Foulkes coefficient mass
and Sawin weight.  It is smaller than Sawin's earlier generic bound at the
handoff, but still misses the squared endpoint margin by 6,829 bits at degree
401 and 6,851 bits at degree 402.  This positive general theorem therefore
confirms that the missing saving is representation-specific: one must bound
the cyclic eigenspace or the signed Frobenius--long-cycle trace, not merely
improve the total cohomology of the complete intersection (ADR-0561).

There is now also an all-degree arithmetic handoff with no asymptotic notation.
The coarse inequality `2^omega(n)<=n` shows that a uniform cyclic bound
`B(n,r)<=n^4` makes the squared Foulkes cost at most `n^10`.  The native
`check_sawin_foulkes_polynomial_betti_sufficiency` checks all twelve bases
`401<=n<=412`, reserving half the main term for proper prime powers, and checks
`413^10<8*401^10`.  The normalized squared margin grows by eight every twelve
degrees.  Over the same step the odd proper-power term stays one, while the
two terms in the even envelope grow by less than `16` and `32`; half the main
term grows by `64`.  This proves that the *hypothetical quartic Betti theorem*
would settle every remaining degree, including proper-power subtraction.  The
same ledger rejects power five at the degree-400 handoff.  This narrows the
geometric research target without asserting it.

There is now an exact localization theorem behind that target for `n>=5`,
where Sawin's strict top-cohomology hypothesis holds at the endpoint.  If `c`
is an `n`-cycle, then

```text
<character(H),p_n>=Tr(c|H),
```

because the long-cycle class has `(n-1)!` elements and `p_n(c)=n`.  On
`X_(n,ell,0)`, a tuple fixed by the full cycle is `(a,...,a)`, with prescribed
coefficients `binom(n,j)a^j`.  Lucas's theorem makes the first odd binomial
index `q=2^v2(n)`.  Hence the full fixed locus is a point except when `n` is a
power of two, where it is an affine line; both have compactly supported Euler
characteristic one.

For even `n`, that observation alone does **not** identify the cohomological
trace: the cycle is wild in characteristic two.  The correct
Deligne--Lusztig finite-order reduction writes `n=qb`, with `q` a power of two
and `b` odd, fixes the order-`b` part, and leaves the order-`q` part acting on
that fixed locus.  A fixed tuple for the order-`b` part has root polynomial
`G(x)^b` with `G` monic of degree `q`.  When `b>1`, one has
`q<=n/3<=ell`; the first `q` leading-coefficient equations are triangular
with diagonal coefficient `b=1` in `GF(2)`, so they force `G=x^q`.  The
reduced locus is a single point.  Therefore, for every non-power-of-two
degree,

```text
Tr(c | H_c^*(X_(n,ell,0)))=1.
```

At a power of two the odd part is the identity, so this finite-order reduction
alone says nothing.  The homogeneous cone supplies the uniform argument.
Because every prescribed coefficient is zero, `X_(n,ell,0)` is an affine cone.
Its punctured part is an `S_n`-equivariant `G_m`-torsor over the
projectivization.  The cycle acts trivially on the fibre and
`chi_c(G_m)=-1+1=0`, while the cone vertex contributes one.  Hence the total
alternating cycle trace is one at **every** degree `n>=5`, including powers of
two.  The one-dimensional top compactly supported cohomology is trivial under
`S_n`, also contributing one, so the complete non-top long-cycle complex has
exact alternating Euler trace zero.

The public `sawin_long_cycle_euler_report` certifies the lowest-set-bit
classification, tame/wild orders, reduced-locus dimension, cone/vertex
traces, Sawin's strict top-cohomology hypothesis, and the final subtraction;
an independent Pascal recurrence checks the Lucas index through degree 128.
It does not apply a tame fixed-point formula to a wild automorphism.

This exact cancellation is still unweighted.  The endpoint count requires

```text
Tr(Frob*c | H_c,non-top^*(X_(n,ell,0))),
```

and zero trace after forgetting Frobenius does not control distinct Frobenius
eigenvalues on the cancelling pieces.  In fact the cone decomposition gives

```text
Tr(Frob^r*c | H_c^*(X))
 =1+(2^r-1)Tr(Frob^r*c | H_c^*(P(X))).
```

At `r=1` the projective factor is one, so this identity supplies no numerical
saving.  The exact `(n,ell)=(5,2)` control makes the distinction concrete:
the non-top Euler trace is zero, while independent base-field enumeration
gives Frobenius-weighted error `-2`.  A cross-operation test pins both values.
The next theorem must bound that projective Frobenius--long-cycle
trace, not merely its zero unweighted Euler specialization or a generic total
Betti number.  No Lemire endpoint credit is attached (ADR-0552).

A projective cyclic quotient does not remove this trace.  Projective fixed
points are eigenlines, rather than only affine fixed vectors.  Write
`n=qb`, with `q=2^v2(n)` and `b` odd.  An eigenvalue of exact order `e|b`
has geometric-progression coordinates and root polynomial

```text
(x^e-A^e)^(n/e).
```

Its first potentially nonzero prescribed coefficient has index `eq`.  At the
endpoint `eq>ell` holds exactly for `e=b`: every proper divisor of odd `b` is
at most `b/3`, while `bq=n`.  The surviving eigenlines therefore have root
polynomial `x^n-A^n`, and the reduced projective fixed locus contains exactly
`phi(b)` points.  In particular it has `400` points at degree `401`, `132` at
degree `402`, and one even at the power-of-two degree `512`.  The full
projective long-cycle action is never free.  For odd `n` it is tame and its
ordinary projective Euler trace is exactly `phi(n)`; for even `n` no reduced
wild fixed-scheme claim is made.

The native `sawin_projective_eigenline_report` enumerates every divisor of
`b`, checks the endpoint inequality, and computes the totient.  This blocks a
plausible finite-etale torsor shortcut but supplies no bound on `Frob*c`; the
report keeps that obligation false (ADR-0553).

The odd-endpoint local scheme is now explicit.  For `n=2ell+1`, write a
surviving primitive eigenline as `a_i=A lambda^i`.  The generating identity

```text
product_i (1-u a_i)=1-u^n A^n
```

makes the `j`th endpoint Jacobian row
`(a_i^(j-1))_i`.  These are distinct Vandermonde rows for `1<=j<=ell`, so the
Jacobian has rank `ell`.  Fourier diagonalization of the cycle leaves affine
tangent modes `1,...,n-ell`; the first is radial, and the relative projective
tangent weights are exactly

```text
lambda, lambda^2, ..., lambda^(n-ell-1).
```

Thus every surviving odd-degree eigenline is a smooth isolated transverse
fixed point.  The report exposes the complementary normal weights and checks
the full nontrivial-character partition; an independent extension-field test
constructs and eliminates the literal Jacobians at degrees five, seven, and
nine.

This removes a local singularity question but not the endpoint trace.  The
ordinary trace formula for `Frob*c` is supported on `Fix(Frob*c)`, which is the
original short-interval point-count problem, rather than on `Fix(c)`.  The
relative Lefschetz--Verdier theorem of Lu--Zheng proves functoriality of trace
classes, not a numerical replacement of one fixed locus by the other.  A
previous research pointer also had the wrong identifier: arXiv `2309.02587` is
Barrett's singular-support paper; the Lu--Zheng paper is arXiv `2005.08522`,
and its Remark 2.24 explicitly says that its theorem does not cover a separate
twisted formula.  Consequently a localization on `Fix(c)` would still require
new Frobenius-dependent local terms and a uniform bound for their sum.  The
native report deliberately retains no Frobenius-weighted credit (ADR-0575).

The actual odd-endpoint `Frob*c` fixed locus now has a complete local
classification as well.  A fixed tuple is generated by one Frobenius orbit of
degree `e|n` and has root polynomial `Q^(n/e)`.  Because odd endpoint degree
`n=2ell+1` makes every multiplicity odd, triangular coefficient recovery
applies to every divisor stratum.  Every proper divisor satisfies
`e<=n/3<=ell-1`; the zero prefix therefore forces `Q=x^e`.  Thus all
proper-orbit strata collapse to the affine cone vertex, and every projective
fixed point has exact orbit degree `n` and distinct coordinates.

At any point of the zero-prefix fibre, division of the elementary-symmetric
generating series by `1+a_i t` gives

```text
d e_j / d a_i = a_i^(j-1),  1<=j<=ell.
```

The nonvertex Jacobian is consequently Vandermonde of rank `ell`.  Since
absolute Frobenius has zero differential, the graph of `Frob*c` meets the
diagonal transversely at every projective fixed point, with local intersection
multiplicity one.  The native
`sawin_odd_frobenius_cycle_fixed_locus_report` checks every divisor through
the degree-401 handoff, while literal `GF(2^5)` and `GF(2^7)` enumeration
independently rebuilds every Frobenius-root polynomial and confirms that every
shaped nonzero element has full orbit degree.

This closes the odd repeated-root and singular-local-term questions, but it
does not estimate the sum of local terms: that sum is the original unknown
point count.  The report therefore keeps
`frobenius_weighted_trace_bound_certified=false`, the manuscript keeps
`(REL)` open, and further local smoothness work receives no endpoint credit
(ADR-0576).

Nor is the resulting relative trace sign-definite.  Exact populations give

```text
C_(5,11)=-608,   C_(7,16)=-4608.
```

The degree-11 row is already in the smooth odd regime above.  Its negative
relative trace therefore cannot be blamed on singular local terms: `(REL)` is
a virtual difference of two positive fixed-point sums, and the differently
normalized coarse sum can exceed the fine sum.  A native regression pins both
negative integers while independently requiring positive underlying identity
populations.  Smooth localization cannot be upgraded to `C>=0`; only a genuine
global comparison can prove the weaker lower bound `C>-B` (ADR-0577).

Hast--Matei's explicit two-polynomial top-weight representation gives a
useful but insufficient positive comparison.  With short-interval tail
degree `h=floor(n/2)`, their partition cutoff is
`n-h-2=ell-1`.  Only hook representations see a long cycle, and exactly
`ell-1` hooks survive.  The resulting idealized top-weight global second
moment is `(ell-1)2^n`.  Cauchy compares this with the squared class mean and
leaves ratio `(ell-1)/2^(n-2ell)`: denominator two at the odd endpoint and
four at the even endpoint.  It therefore misses every unresolved degree.

Their `m>2` singular-locus proof excludes characteristic two through one
repeated-root fibre lemma.  On the long-cycle sector that defect can now be
localized exactly.  A repeated-root Frobenius tuple has polynomial
`Q(x)^(n/e)` for one orbit degree `e|n`.  Odd multiplicity makes the first
`e` output coefficients triangular in those of `Q`; even multiplicity makes
the polynomial a Frobenius square, with visible coefficient stride
`2^v2(n/e)`.  Thus all low-characteristic failures selected by the long-cycle
trace are square proper-power strata.  The native
`hast_matei_long_cycle_endpoint_report` checks the endpoint hook ledger and
every divisor stratum, but it does not yet prove that the connected virtual
projector cancels those square strata or bound the remaining Frobenius trace
(ADR-0554).

### A characteristic-delta least-period reduction

There is now a separate algebraic route that bypasses the connected trace if
one explicit cyclic-period lemma can be proved.  Put

```text
ell=ceil(n/2)-1,  N=2^n-1,
delta_j(a)=1 iff the canonical n-bit representative of a has weight j.
```

For a primitive `zeta in GF(2^n)`, Tuxanidy--Wang's characteristic-delta
identity is

```text
sigma_j(zeta^a)=DFT(delta_j)(a).
```

Since `sigma_j` is binary valued, `1+sigma_j` is the indicator that the
`j`-th leading coefficient vanishes.  Therefore

```text
F(alpha)=product_(j=1)^ell (1+sigma_j(alpha))
```

is exactly the complete Lemire-class indicator, and its inverse Fourier
coefficient function is the single group-algebra element

```text
Gamma_(n,ell)=*_(j=1)^ell (delta_0+delta_j)
               in GF(2)[Z/N].                       (CD)
```

Let

```text
M_n=lcm_(d|n,d<n)(2^d-1)=N/Phi_n(2).
```

The cited DFT support theorem proves that if the least translation period of
`Gamma_(n,ell)` does not divide `M_n`, then the support of `F` contains an
element of exact degree `n`.  Its minimal polynomial is irreducible and has
all the required coefficients zero.  Thus the following stronger statement
would prove Lemire directly:

```text
least_period(Gamma_(n,ell))=N.                     (MP)
```

The single-period condition is not the exact support condition when `n` has
more than one prime divisor: the subgroup killed by `M_n` then strictly
contains the union of the proper subfields.  The exact replacement is still a
short group-algebra formula.  For every distinct prime `p|n`, put

```text
T_p=2^(n/p)-1,
Q_n=product_(p|n)(1+tau_(T_p)).
```

Fourier transformation gives

```text
DFT(Q_n Gamma)(a)
 = F(zeta^a) product_(p|n)(1+(zeta^a)^(T_p)).       (ED)
```

The `p`-th factor vanishes exactly on `GF(2^(n/p))^*`, and those maximal
proper subfields contain every element of degree less than `n`.  Hence

```text
Q_n Gamma != 0
 iff an admissible element has exact degree n
 iff a Lemire irreducible of degree n exists.        (EQ)
```

For prime-power `n` there is only one maximal proper subfield, so the older
period criterion is exact.  For mixed-divisor `n` it remains sufficient but
is stronger than `(EQ)`.

The bounded native `tuxanidy_lemire_period_report` multiplies (CD) exactly in
the binary cyclic group algebra, computes the actual translation period, and
applies every maximal-subfield difference in `(ED)`.  It finds (MP), and hence
nonzero exact-degree difference, for every `3<=n<=12`.  An independent oracle
through degree eight instead enumerates `GF(2^n)^*`, constructs each
Frobenius-root characteristic polynomial, recovers the DFT period from the gcd
of the supported exponents, and directly tests membership in every maximal
proper subfield; the routes agree.  These are finite controls only.

Tuxanidy--Wang prove maximum period for each individual binary factor
`delta_0+delta_j` when `j<=n/2`, but that result cannot simply be multiplied.
At degree eight the product through weights `1,2,3,4`, including the middle
coefficient, has period `15`, even though every factor has maximum period;
the Lemire product through weight three has period `255`.  Consequently the
new universal obligation is genuinely the combined half-open convolution.
The minimal exact target is nonvanishing in `(EQ)`, not the stronger common-
period condition.  No theorem credit is attached to (MP) or to the finite
differences (ADRs 0555 and 0558).

The closest general symmetric-cohomology theorems do not fill that gap.
Chenevert's smooth projective hypersurface calculation assumes `n!` is
invertible in the ground field, excluding this characteristic-two `S_n`
action.  Basu--Riener instead bound rational cohomology of real
semi-algebraic sets.  Neither controls the hook-isotypic compactly-supported
etale cohomology of this singular wild affine quotient.  A valid bridge must
prove precisely that characteristic-two statement rather than transfer a
characteristic-zero Euler-characteristic formula.

The function-field Linnik--Selberg theorem also does not supply the missing
cross-order estimate. Its proved form is an untwisted average over **varying
moduli**,

```text
sum_(g monic, deg g=j) S(f,h;g) << 2^(j(1+epsilon)) |fh|^epsilon.
```

Florea--Lalín--Malik--Sahay use exactly this organization in their
[shifted-convolution theorem](https://doi.org/10.1007/s00208-026-03340-9):
after grouping by `deg(g_1)=j`, they apply Linnik--Selberg to the sum over
`g_1`; when a multiplicative twist remains, they explicitly return to the
pointwise Weil bound. In (MC), however, every inverse and Kloosterman phase is
modulo the one wild modulus `x^(ell+1)`. The interval variable `u` changes an
argument of that sum, not its modulus, and the Möbius transform supplies an
additional arithmetic weight. Polynomial reciprocity does not exchange these
roles. The stronger twisted/divisibility Linnik--Selberg statement is still
described by the published source as open and without the explicit parameter
dependence required here. ADR-0532 therefore records the exact domain
mismatch: the theorem is a model for a new fixed-wild-modulus trace formula,
not an input to the current endpoint ledger.

### Complete low-twist shells do not force repeated weight drops

Sawin's joint Witt monodromy kills the top cohomology of each nontrivial
shifted high-character trace, but the remaining lower trace is at fixed
`q=2`.  The possible refinement of summing the whole exact-conductor twist
shell has now been tested as a genuine Frobenius sequence.  Over `GF(q)`, put
`R=q^(ell-c)` and form the conditional-covariance masses

```text
w(a)=R sum_(g above a)D(g)^2-(sum_(g above a)D(g))^2,
A_i=sum_(a whose first i coordinates vanish)w(a).
```

The exact unnormalised joint trace is

```text
T_i(q)=q^c(q^i A_i-q^(i-1)A_(i-1)).
```

The bounded `binary_extension_witt_shifted_trace` operation reconstructs
every term from the extension-field Mangoldt class vector, after an
independent conservation check.  At `(ell,n,c)=(3,7,2)`, the exact
degree-seven population formula gives conditional covariance `q^6(q-1)` on
the graph `t_2=t_1^2` and zero off it.  Hence, for every `q=2^r`,

```text
T_1(q)=0,                 T_2(q)=q^9(q-1)^2.
```

The nonzero trace has q-degree `11`, while the two Adams traces and the joint
character/twist parameter space permit formal top degree `12`.  Thus the full
low-twist shell realizes only one full q-degree of cancellation, not one drop
per affine parameter.  Exhaustive `GF(2)` and `GF(4)` reconstruction gives
`T_2=512` and `2359296`.  At the next endpoint pair, unforced layer signs can
even change under extension, while only the translation-selected layer stays
zero.

This rejects generic affine/perverse concentration as the missing bridge.
The surviving `(WITT-LOW)` theorem must exploit the alternating lower trace,
the two-Mobius virtual representation, or cancellation across conductor
orders; dimension, lissity, and top-invariant vanishing alone cannot supply
the required repeated contractions (ADR-0586).

Translation has now been promoted from one path split to its complete dual
functional equation.  If `u(t)` is a truncated reciprocal class, direct
substitution gives

```text
sigma(u)=(1+t)^n tau(u),
tau(u)(t)=u(t/(1+t)) mod t^(ell+1).
```

Here `tau` is an involutive group automorphism and `sigma` is the class
involution induced by `F(x)->F(x+1)`.  Since translation preserves the
polynomial Mangoldt weight, both the Mangoldt spectrum and the Fourier
transform of the squared class discrepancy satisfy

```text
A(chi)=chi((1+t)^n) A(chi o tau).                         (TRANS-FE)
```

Put `K={tau(g)g^(-1)}`.  The `tau`-fixed dual is the dual of `G_ell/K`.
The count is exact for every level.  For odd `i<ell`, the first nonzero term
of `(tau-1)t^i` is `t^(i+1)`, giving `floor(ell/2)` independent image
directions.  The fixed element `z=t^2/(1+t)`, its powers, and (when `ell` is
odd) the top term `t^ell` give the complementary
`ceil(ell/2)`-dimensional fixed space.  Therefore
`|K|=2^floor(ell/2)` and the fixed dual has order `2^ceil(ell/2)`.
For odd `n`, the first-coordinate sign character proves `(1+t)^n notin K`,
so exactly half of the fixed dual has negative evaluation and vanishes in
`(TRANS-FE)`.  For even `n`, taking `g=(1+t)^(n/2)` proves
`tau(g)g^(-1)=(1+t)^(-n)`, so `(1+t)^n in K` and this mechanism forces no
fixed character to vanish.  The bounded
`hayes_translation_spectral_involution` operation checks every group element,
canonical generator, commutator-image class, and exact population permutation.
At `ell=8` the fixed dual has order `16`: degree `17` forces eight zeros and
degree `18` forces none.  This strictly generalizes the earlier odd
one-character zero, but the odd vanishing fraction shrinks with conductor and
the even endpoint receives no cancellation.  Thus it is reusable exact
structure, not a proof of `(WITT-LOW)` or `(REL)` (ADR-0587).

The conductor filtration prices that shrinkage exactly.  If `F_j` denotes the
fixed-dual count through level `j`, then `F_j=2^ceil(j/2)` and restriction gives
`f_j=F_j-F_(j-1)`: one fixed character at level one, none at even levels, and
`2^((j-1)/2)` at odd `j>=3`.  For odd polynomial degree the cumulative
negative-sign population is `F_j/2`, so differencing again gives one forced
zero at level one, none at even levels, and only `2^((j-3)/2)` at odd `j>=3`.
Thus the exact-level forced-zero fraction is `2^(-(j+1)/2)`, not
`2^(-(j-1)/2)`; at even polynomial degree it is zero.  The CAS enumerates the
complete admitted character group in Witt coordinates, checks these closed
forms at every level, and requires the rows to recover the cumulative totals
(ADR-0588).  This rules out extracting a conductor-uniform density saving from
translation alone.

Spending every one of those zeros in the selected endpoint ledger does not
change its integer-scale obstruction.  The adjusted report replaces the
level-`j` Weil population `2^(j-1)` by `2^(j-1)-z_(j,n)` both below and inside
the connected top window.  At `(ell,n)=(200,401)`, this removes exactly
`2^94` low-window characters and `31*2^94` top-window characters.  Both raw
envelopes improve strictly, but the saving required of the residual connected
trace still rounds to `626`.  At `(200,402)` translation removes no character
and changes nothing.  The symbolic ledger checks both parities through
`ell=1024` and retains the baseline and adjusted integers side by side
(ADR-0589).  Thus no translation cancellation remains unspent: the missing
theorem must act on residual nonfixed characters or cancel the signed trace
across conductors.

There is no second binary projective symmetry on this quotient.  For
`g=(a,b;c,d)` in `PGL_2(GF(2))`, the homogenized action preserves every monic
degree-`n` polynomial only when `c=0`, so that `g` fixes infinity.  Determinant
one then leaves only identity and `x->x+1`.  When `c=1`, the transformed
leading coefficient is `F(a)`, and `(x+a)^n` is an explicit monic degree-drop
witness.  Inversion can act on selected constant-one polynomials, but the
reciprocal class after inversion depends on their low coefficients and hence
is not an action on the present Hayes quotient.  The bounded CAS enumerates
all six matrices and checks the two surviving actions and four witnesses
(ADR-0590).  Consequently larger symmetry orbits cannot be obtained from
`PGL_2(GF(2))`; the residual theorem must use the connected signed trace.

The exact algebra is no longer trapped in that executable. ADR-0486 extracts a
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
