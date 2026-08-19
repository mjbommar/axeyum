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
  coefficients](https://pollack.uga.edu/prescribed.pdf).
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
  proof of this conjecture. See Hsu,
  [The Distribution of Irreducible Polynomials in
  F_q[t]](https://doi.org/10.1006/jnth.1996.0139), and Car's explicit
  [restatement](https://eudml.org/doc/207235).
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

A tempting shape-preserving induction also fails. If `f=x^n+q`, then `f^2+x`
has degree `2n` and tail degree at most `n`, but it is reducible for every
shaped irreducible in an exhaustive degree-2-through-12 test. The related
transforms `x f^2+1`, `f^2+f+x`, and `f^2+x f+1` fail the same falsification
range. None is used as a construction lemma.

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

`axeyum-gf2-hayes-endpoints` evaluates the group-ring recurrence after an exact
Fourier transform of the finite principal-unit group.  It uses two NTT primes,
CRT reconstruction, and the a priori bound `N_n(1) <= 2^n`; no floating-point
rounding is involved. Through `ell = 23` (endpoint degrees 47 and 48), the
candidate bound holds. The endpoint discrepancies for `ell = 13..23` are

```text
ell:                 13    14    15    16     17    18      19    20      21     22     23
Delta odd:         -345  -896   340  2744  -1988   928    4074  3115  -20938  -7582  57574
Delta even:         980   645 -1832   660   6587  9592  -13496 -4509   25007  28402 -88336
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
