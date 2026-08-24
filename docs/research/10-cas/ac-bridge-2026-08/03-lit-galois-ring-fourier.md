# AC-Bridge lane 03 -- Fourier analysis with values in `Z/2^k`: Galois rings,
# Witt vectors, and the Arf-sign family

Workstream: AC-Bridge (`docs/research/10-cas/ac-bridge-2026-08/00-charter.md`).
Agent: field specialist 03 (`Z/2^k`-valued and Witt Fourier analysis).
Opened: 2026-08-20.
Scope: ad hoc research, outside roadmap/gates/fact-ledger. Nothing here changes
lane state.

Epistemic law of this project (charter rule 3): finite computation is EVIDENCE,
never a theorem; every reference is FETCHED and verified, never recalled.
Every claim below is labelled **PROVED** (with argument or citation) /
**REFUTED** (with witness) / **OPEN** / **EVIDENCE** / **DERIVED** (a
consequence I worked out here from a cited theorem, not itself in the source).

Notation is the charter's: `G_ell` = principal units of `F_2[x]/x^(ell+1)`,
`G_ell ~ prod_(i odd, i<=ell) Z/2^(k_i)` with `k_i = min{m : i 2^m > ell}`;
`S_chi`, `M_2`, `M_4`, `K_4`, `D_e` as there.  From sweep-08 I import the fibre
notation: `F` an exact affine fibre, `c_F` its exact signed dyadic-character
correlation, `Delta = sum_F c_F`, `N_points` the number of contributing pairs,
and the split `(E2') sum_F c_F^2 <= N_points` + `(S) |sum_F c_F| <= C (sum_F c_F^2)^(1/2)`.

---

## Log

### [t0] 2026-08-20 -- orientation and the question I am actually being asked

Read in order: the charter; sweep-08 `08-boolean-complexity.md` (the `(E2')+(S)`
split, the powers-of-two fibre-coefficient finding, the `Z/8` Arf-sign structure,
the Bhowmick--Lovett pointer); sweep-02 `02-exponential-sums.md` (the
Schmid--Witt residue formula `chi_a(g) = (-1)^(res(a dlog g))`, verified there for
`ell <= 8`); `00-synthesis.md`.

Two sentences from those diaries define my target:

- sweep-08 [t6]/(b): "Exact `Z/8` (Galois-ring) quadratic Gauss-sum evaluation
  with the Arf/Brown sign ... is the only technique in this neighbourhood that
  returns *exact values* ... my measurement says it covers 96.4% of the nonzero
  fibre correlations".
- sweep-08 [t1]: "A `Z/8`-valued phase is a depth-2 nonclassical polynomial.
  **The Lemire blocker phase is literally a nonclassical polynomial of depth 2**."

My charge is to say precisely what the existing `Z/2^k` Fourier theory proves,
and precisely where it stops. The single most consequential thing I found is
that **those two sentences are in tension, and resolving the tension locates the
gap exactly.** That is [t3].

Sources read in full or in the relevant sections, all fetched live 2026-08-20,
PDF -> text with `pdftotext -layout` where the fetcher could not parse the
stream. Scratch copies under
`/tmp/claude-1000/.../scratchpad/gr-lit/` (session-local, nothing written into
the repository except this file).

---

### [t1] The `Z_4` program: what it is, and what it actually proves

**Hammons, Kumar, Calderbank, Sloane, Sole, "The `Z_4`-linearity of Kerdock,
Preparata, Goethals and related codes", IEEE Trans. Inform. Theory 40 (1994)
301--319.**
Fetched: <https://arxiv.org/abs/math/0207208> (arXiv posting of the paper);
also <https://www.itsoc.org/publications/papers/the-z4-linearity-of-kerdock-preparata-goethals-andrelated-codes>.
What it proves: the Nordstrom--Robinson, Kerdock, Preparata, Goethals and
Delsarte--Goethals codes -- famously *nonlinear* over `F_2` -- are binary Gray
images of *linear* codes over `Z_4`; Kerdock and (modified) Preparata are
`Z_4`-duals, which explains the long-standing formal duality of their Hamming
weight enumerators. The engine is the `Z_4` MacWilliams identity plus exact
evaluation of `sum_x i^(Q(x))` for `Z_4`-valued quadratic `Q`.
**Relevance to us: this is the origin of the whole exact-evaluation technique,
and the reason the sign in `+-2^j` is an Arf-type invariant. It is a
`Z_4` result, not a `Z_8` result. That distinction is [t3].**

**Kumar, Helleseth, Calderbank, "An upper bound for Weil exponential sums over
Galois rings and applications", IEEE Trans. Inform. Theory 41(3) (1995)
456--468.** Fetched: <https://ieeexplore.ieee.org/document/370147/>.
What it proves: an analogue of the Weil--Carlitz--Uchiyama bound for exponential
sums over Galois rings `GR(p^k, m)`, of `(d-1) sqrt(q)` shape, with examples
where it is tight. Follow-ups located and verified to exist:
Ling and Ozbudak, "Improved bounds on Weil sums over Galois rings and
homogeneous weights", 2006, <https://link.springer.com/chapter/10.1007/11779360_32>
(generalises to `GR(p^l, m)` for any `l` an improvement previously known for
`l = 2`, and derives a refined bound *in terms of genera of function fields*
plus a McEliece-type divisibility theorem for homogeneous weights).

**Verdict on the Weil-over-Galois-rings branch, and it is negative and firm.**
sweep-08 already priced this correctly: the bound carries exactly the degree
factor `(d-1)` that the Lemire endpoint must delete, and it is *tight* for
Kerdock/Delsarte--Goethals, so no sharpening of it can help. What I add is that
the *improved* versions do not change this: Ling--Ozbudak's refinement is
expressed through the **genus** of an associated function field, and sweep-07
already identified the blocker's log factor as the genus
(`00-synthesis.md`: "the Hast--Matei deficits `(ell-1)/2, (ell-1)/4` are the mean
L-degree, i.e. the genus -- the blocker's log factor IS the genus"). So the
improved Galois-ring Weil bound re-expresses the obstruction in the same
coordinate in which the lane already knows it is an obstruction. **REFUTED as a
route** (by composition of two cited results, not by measurement).

---

### [t2] The exact-evaluation catalogue: which Gauss sums are exactly evaluable, and by what mechanism

sweep-08's key measurement is that `12,456` of `12,915` nonzero `|c_F|` at the
pinned witness are exact powers of two. The question is which theorem forces
that. Here is the catalogue, mechanism by mechanism. All statements are as
printed in the source I opened.

#### (E1) Brown's theorem -- `Z/4`-valued quadratic forms on an `F_2`-space

Source read in full: **Jay A. Wood, "Witt's extension theorem for mod four
valued quadratic forms", Trans. Amer. Math. Soc. 336 (1993) 445--461**, fetched
<https://webhomes.maths.ed.ac.uk/~v1ranick/papers/woodj.pdf> (PDF decoded
locally; the same fetch failed for a parallel agent, so the quotations below are
from my own decode). Wood restates Brown [E. H. Brown, Jr., "Generalizations of
the Kervaire invariant", Ann. of Math. 95 (1972) 368--383] as:

> A `Z/4`-valued quadratic form `Q` on an `F_2`-vector space `V` associated to a
> symmetric bilinear `B: V x V -> Z/2` is a function `Q: V -> Z/4` with
> `Q(u+v) = Q(u) + Q(v) + j B(u,v)`, `j: Z/2 -> Z/4` the injection `j(1)=2`.

and Brown's Theorem 1.20, of which the parts that matter here are, verbatim from
Wood's rendering:

> (7) If `Q = jQ'`, where `Q'` is an ordinary (`Z/2`-valued) quadratic form on
>     `V`, then `sigma(Q) = I(Arf Q')`, where `I: Z/2 -> Z/8` sends `1` to `4`.
> (10) If `Q_1, Q_2: V -> Z/4` have the same bilinear form `B`, then
>     `Q_2(u) = Q_1(u) + j B(u,x)` for some `x` and
>     `sigma(Q_1) - sigma(Q_2) = w(Q_1(x))`, where `w: Z/4 -> Z/8` sends `1` to `2`.
> (11) `sigma(Q)` is related to `Q` by the formula
>     `sum_(u in V) i^(Q(u)) = sqrt(2)^(dim V) e^(2 pi i sigma(Q)/8)`.

**PROVED (by citation).** (11) is the exact evaluation: for a *nonsingular*
`Z/4`-valued quadratic form the Gauss sum has modulus exactly `2^(dim V / 2)`
and phase exactly an 8th root of unity, the exponent being Brown's `Z/8`
invariant `sigma`, which by (7) reduces to `4 * Arf` when `Q` is `2 x (F_2`-valued
quadratic form`)`. Wood's Section 3 adds the classification:

> **Theorem.** A nonsingular `Z/4`-valued quadratic form `Q` is determined up to
> isomorphism by `sigma(Q)` and whether its associated bilinear form `B` is
> alternating or not.

**Property (10) is the one nobody in the lane's documents has used, and it is
the most useful single line I found.** It says the Brown sign of a *linear
twist* of a fixed form is an explicit `Z/4`-quadratic function of the twist
parameter. Consequence, worked out in [t6] as the base case `(L2-1)`.

#### (E2) Taylor's general theory -- arbitrary finite abelian group, singular allowed

Source read in full: **Laurence R. Taylor, "Gauss Sums in Algebra and
Topology"**, fetched <https://webhomes.maths.ed.ac.uk/~v1ranick/papers/taylorg.pdf>
(arXiv version <https://arxiv.org/abs/2208.06319>, abstract confirmed to match).
Taylor works with *enhancements* `psi: T -> R/Z` on a finite abelian group `T`,
defined by the vanishing of the third additive derivative (his 1.5), which is
weaker than quadratic and, crucially, **allows the form to be singular**. What he
proves (verbatim, with his numbering):

> **Theorem 1.10.** Let `psi: T -> R/Z` be an enhancement and suppose
> `psi|_K = 0` for some subgroup `K`. Then `G(psi) = |K| . G(psi|_(K^perp/K))`.
>
> **Corollary 1.11.** Let `psi` be an enhancement. If `psi` is not tame then
> `N(psi) = 0` and if `psi` is tame then `N(psi) = sqrt(|T^perp| . |T|)`.
>
> **Proposition 1.13.** ... Then `beta(psi_h) = beta(psi) - psi(c)`.
>
> (1.18) `G(psi) = p^(e/2) omega^sigma` where `beta(psi) = sigma/8`, `omega = e^(2 pi i/8)`.

Here `N(psi) = |G(psi)|`, `beta` the phase, `T^perp` the radical, `p^e = |T/T^perp|`.
Taylor also records, before (1.18), that Connolly's argument gives
`beta(psi) in Z/8Z` for any tame quadratic enhancement, and Brown's characteristic-
element argument giving `2 beta(psi) = psi(omega) in Z/4Z`.

**This is the sharpest available answer to "why are the `|c_F|` powers of two".**
Corollary 1.11 is a *dichotomy with no error term*: the Gauss sum of an
enhancement is either exactly `0` (not tame -- the radical carries a nontrivial
character) or has modulus exactly `sqrt(|T^perp| |T|)`, a power of two on a
2-group. sweep-08's histogram `0: 5969, 2: 10281, 4: 1986, ...` is exactly the
shape Corollary 1.11 predicts, **including the large zero atom**, which the
nonsingular Brown statement (E1) does not predict at all. **This is the correct
citation for the lane's measurement, and it is not the one sweep-08 named.**

#### (E3) Turaev / van der Blij -- exact evaluation through a signature

Source read: **V. Turaev, "Reciprocity for Gauss sums on finite abelian groups",
Math. Proc. Camb. Phil. Soc. 124 (1998) 205--214**, fetched
<https://webhomes.maths.ed.ac.uk/~v1ranick/papers/turaev3.pdf>.
Normalisation `Gamma(G,q) = |G|^(-1/2) sum_x e^(2 pi i q(x))`.
The van der Blij evaluation, his formula (2), verbatim:

> `Gamma(G_f, q_(f,v)) = e^((pi i/4)(sigma(f) - f_Q(v,v)))`.

**Mechanism: the phase of the Gauss sum is the signature mod 8 of an integral
lattice `f` realising the form, corrected by a rational Wu class `v`.**
Hypothesis: `b_q` nondegenerate (his Remark 2: this is necessary and sufficient
for `q` to be presentable as some `q_(f,v)`). This is the deepest exact
evaluation in the area -- it is where "why 8" comes from -- and it is the reason
`Z/8` appears as the *target of the invariant* rather than as the phase group.

#### (E4) Schmidt -- the full distribution over a linear-twist family

Source read: **Kai-Uwe Schmidt, "`Z_4`-valued quadratic forms and quaternary
sequence families", IEEE Trans. Inform. Theory 55(12) (2009) 5803--5810**,
fetched <https://math.uni-paderborn.de/fileadmin-eim/mathematik/AG-Diskrete_Mathematik/Publications-schmidt/Z4seq.pdf>.
He studies `chi_Q(u) := sum_(x in V) i^(Q(x)) (-1)^(T(u,x))` for `Q: V -> Z_4`
a Brown quadratic form of rank `r` on `V = F_2^m`, and proves that the multiset
`{chi_Q(u) : u in V}` depends only on `r` and on whether `Q` is alternating.
Verbatim:

> **Result 4.** Let `Q: V -> Z_4` be an *alternating* `Z_4`-valued quadratic
> form of rank `r`. Then the distribution of the values in `{chi_Q(u)}` is
>
> | value | frequency |
> |---|---|
> | `0` | `2^m - 2^r` |
> | `+- 2^(m-r/2)` | `2^(r-1) +- 2^(r/2-1)` |
>
> **Theorem 5.** Let `Q` be *nonalternating* of rank `r`, `omega := (1+i)/sqrt 2`.
> If `r` is odd: values `0` (`2^m - 2^r` times), `+- omega 2^(m-r/2)`
> (`2^(r-2) +- 2^((r-3)/2)`), `+- omega^3 2^(m-r/2)` (`2^(r-2) -+ 2^((r-3)/2)`).
> If `r` is even: values `0` (`2^m - 2^r`), `+- 2^(m-r/2)` (`2^(r-2) +- 2^(r/2-1)`),
> `+- i 2^(m-r/2)` (`2^(r-2)` each).

Also Corollary 3, the normal form: alternating `Q(x) = 2 sum_(j<r/2) x_(2j) x_(2j+1) + 2 sum_j v_j x_j`;
nonalternating `Q(x) = sum_(j<r) x_j + 2 sum_j v_j x_j`; and (his (5))
`2Q(x) = 2B(x,x)`, whence **`Q` is `2Z_2`-valued iff `B` is alternating**.

**This is the closest published object to sweep-08's `(E2')`.** It is a complete
`(rank, alternating?)` stratification of a full linear-twist family, giving all
moments exactly. Note the sign discipline it enforces: the values are **real**
`+-2^j` exactly in the alternating case; the nonalternating case produces
`omega` and `i` phases. sweep-08 measures `c_F` real and (96.4% of the time) a
power of two, which places the Lemire family in the alternating / `2Z_2`-valued
stratum -- i.e. `Q = 2Q'` with `Q'` an ordinary `F_2`-valued quadratic form.
**That is a testable prediction about the lane's data and it is experiment (d1)
below.**

#### (E5) Gauss sums over Galois rings proper

- **Li, Zhu, Feng, "The Gauss sums and Jacobi sums over Galois ring `GR(p^2,r)`",
  Sci. China Math. 56 (2013) 1457--1465**,
  <https://link.springer.com/article/10.1007/s11425-013-4629-6> (abstract page
  reached; full text paywalled, redirect to an auth endpoint -- **the theorem
  statement is UNVERIFIED, I record only the abstract's claim**): the values of
  Gauss and Jacobi sums over `GR(p^2,r)` "can be reduced to Gauss sums and Jacobi
  sums over finite fields for all non-trivial cases".
- **"The Gauss sums over Galois rings and its absolute values", Korean J. Math.**,
  <https://koreascience.or.kr/article/JAKO201830540459566.page> -- abstract only;
  computes the *modulus* of Gauss sums over `GR(p^n, p^(ns))`. **Theorem
  statement UNVERIFIED.**

**Honest assessment of the Galois-ring branch:** the exact evaluations that exist
over `GR(p^2, r)` reduce to finite-field Gauss sums, i.e. they are the *`k = 2`*
story, and they are about *multiplicative* characters of the Galois ring. Our
object is additive, over `Z/8` (`k = 3`), on an `F_2`-vector space that is not
the additive group of a Galois ring. **I found no exact evaluation covering it,
and [t3] explains why one should not expect to.**

---

### [t3] THE GAP, stated exactly: over `F_2` the `Z/8` phase group collapses at degree two

This is the central finding of this diary. It resolves the tension noted in [t0]
and it is confirmed by **three independent sources**, one of which proves it as a
lemma and two of which state it as an elementary remark.

**Definition (Tao--Ziegler).** `P: F_p^n -> T = R/Z` is a *nonclassical
polynomial of degree at most `d`* if `Delta_(h_1) ... Delta_(h_(d+1)) P = 0`
identically. Its *depth* is the largest `j` occurring in the canonical expansion
(Tao--Ziegler Lemma 1.7(iii)); depth `k` means the values lie in a coset of
`(1/p^(k+1)) Z / Z`.

**Theorem (degree--depth inequality).** For `P: F_p^n -> T` nonclassical of
degree `d` and depth `k`,
```text
   k <= floor( (d-1) / (p-1) ),   equivalently   d >= (p-1) k + 1.
```
Sources, both opened: **Tao--Ziegler, arXiv:1101.1469, Lemma 1.7(iii),(vi)**
(<https://arxiv.org/abs/1101.1469>, and the ar5iv rendering
<https://ar5iv.labs.arxiv.org/html/1101.1469>) -- the support condition
`0 < i_1 + ... + i_n <= d - j(p-1)` and "takes at most `p^(floor((d-1)/(p-1))+1)`
distinct values"; cross-checked independently against **Berger--Sah--Sawhney--
Tidor, arXiv:2107.07495, Lemma 2.4** (<https://ar5iv.labs.arxiv.org/html/2107.07495>),
identical support condition. A third, independent formulation with the same
content: **Labib, "Stabilizer rank and higher-order Fourier analysis",
Quantum 6 (2022) 645, arXiv:2107.10551, Proposition 3.7 and the sentence after
it** (<https://arxiv.org/pdf/2107.10551v2>): "the depth of a nonclassical
polynomial is always at most `ceil(d/(p-1)) - 1`".

**At `p = 2` this reads `k <= d - 1`. Therefore:**

```text
   degree 1  ->  depth 0  ->  values in Z/2
   degree 2  ->  depth <=1 ->  values in Z/4       <-- Brown / Taylor / Schmidt live here
   degree 3  ->  depth <=2 ->  values in Z/8       <-- the first genuinely Z/8 degree
```

**PROVED (by citation, three sources): over `F_2` there is no such thing as a
`Z/8`-valued nonclassical polynomial of degree 2. "Depth-2 quadratic" is an
empty class.** Labib states exactly this consequence for the object in question,
verbatim (his Section 3.1, immediately after Theorem 3.2):

> "In [2] quadratic forms are considered that are maps `Q: H -> (1/8)Z/Z`. We
> will show that the only way that such a map has the property
> `Delta_(h_1) Delta_(h_2) Q(x)` being independent of `x in H` for all
> `h_1, h_2 in L(H)`, is if `Q` actually take values in `(1/4)Z/Z ⊂ (1/8)Z/Z`."

And **Turaev, Remark 1** (fetched above), the same fact stated group-theoretically:

> "The Gauss sum `Gamma(G,q)` is often considered in the case where `G` is a
> direct sum of a finite number of copies of `Z/2Z`. In this case any quadratic
> form `q: G -> Q/Z` takes values in `Z/4Z ⊂ Q/Z` (this follows from the
> bilinearity of the pairing `b_q: G x G -> Z/2Z ⊂ Q/Z` and the identity
> `2q(x) = 2q(x) - q(2x) = -b_q(x,x)`)."

I re-derived it by hand, and then verified the derivation exhaustively, because
the *coefficientwise* form of the statement is what the lane's report needs and
I got it wrong on the first pass. Recording both, including the error.

Hand derivation. For a quadratic monomial `psi(x) = c x_1 x_2` on `T = F_2^2`,
`b(x,y) = psi(x xor y) - psi(x) - psi(y)` gives `b((1,0),(0,1)) = c` and
`b((1,0),(1,1)) = -c`, while bilinearity forces
`b((1,0),(1,1)) = b((1,0),(1,0)) + b((1,0),(0,1)) = 0 + c = c`; so `2c = 0` in
`Z/8` and `c in {0,4}`. For a *linear* monomial `psi(x) = a x_1`,
`b(x,y) = -2a x_1 y_1`, and additivity in the first slot needs
`-2a (x_1 xor x_1') y_1 = -2a (x_1 + x_1') y_1`, whose difference is
`4a x_1 x_1' y_1`; so the condition is `a` **even**, not `a in 4Z/8`.
**My first pass asserted `a in {0,4}` for the linear coefficients too, and that
is FALSE.** The correct rule is:

```text
   psi: F_2^n -> Z/8 has vanishing third XOR-derivative
   <==>  every LINEAR    Z/8-ANF coefficient lies in 2Z/8 = {0,2,4,6},
         every QUADRATIC Z/8-ANF coefficient lies in 4Z/8 = {0,4},
         every coefficient of degree >= 3 vanishes
   <==>  psi = 2 Q' with Q' : F_2^n -> Z/4 a Brown quadratic form.
```

**Verified exhaustively** (external verifier, per charter rule 1; script
`chk.py` in the session scratchpad, runs in seconds, well inside the compute
bound). Enumerating every `Z/8`-ANF coefficient vector for `n = 1,2,3` and
testing `D_a D_b D_c psi == 0` over all `a,b,c,x`, the number of solutions is

```text
   n = 1: 4        n = 2: 32        n = 3: 512
```

which agrees exactly, for each `n`, with **both** the predicted count
`4^n . 2^(C(n,2))` from the rule above **and** the independent count of Brown
`Z/4`-valued quadratic forms `2^(n(n+1)/2 + n)` read off Schmidt's normal form
(6) (`Q'(x) = x B x^T + 2 v x^T`, `B` symmetric over `F_2`, `v in F_2^n`).
Two independent counts, exact agreement at three values of `n`: the map
`Q' -> 2Q'` is a bijection from Brown `Z/4`-forms onto `Z/8`-valued
enhancements. Consequently the summand `zeta_8^(psi) = i^(Q')` --
**the `Z/8` phase group here is not merely restricted, it is literally the `Z/4`
phase group in disguise.**

#### Consequence 1: the sweep's two notions of "quadratic" are different, and the gap between them is where the problem lives

sweep-08 measures the ANF degree of `Disc mod 8` as a `Z/8`-valued function
(`16,587` of `18,884` fibres "at-most-quadratic"). Translate: writing
`Q = sum_S c_S prod_(i in S) x_i` with `c_S in Z/8` and `P = Q/8`, the canonical
expansion assigns the monomial `c_S prod x_i / 8` the nonclassical degree
`|S| + 2 - v_2(c_S)`. Hence

```text
   nonclassical degree of the phase  =  max_S ( |S| + 2 - v_2(c_S) ).
```

(Check against the boxed rule: linear with `c` even gives `1+2-1 = 2`,
admissible; linear with `c` odd gives `3`; quadratic with `c = 4` gives `2`,
admissible; quadratic with `c` odd gives `4`; cubic with `c = 4` gives `3`.
Exactly reproduces the rule.)

So a fibre whose `Z/8` ANF degree is `2` has **nonclassical degree up to 4** (if
any quadratic coefficient is odd), and the pinned witness's "max `Z/8` ANF degree
`7`" corresponds to nonclassical degree up to `9`. **DERIVED; it is arithmetic
from the cited canonical form, but it is not a statement any source makes about
this family, and it is not how the lane's report is currently labelled.**

The two notions coincide only on the sub-class described by the boxed rule above
(linear coefficients even, quadratic coefficients in `4Z/8`, nothing higher), and
on that class `zeta_8^(Q) = i^(Q')` and Brown's theorem applies verbatim. **That, and not "88% of fibres are
quadratic", is the exactly-evaluable sector.**

#### Consequence 2: the exact-evaluation theory of [t2] does NOT cover the `Z/8` sector -- there is no theorem to transfer

Brown (E1), Taylor (E2), van der Blij/Turaev (E3), Schmidt (E4) are *all*
theorems about degree-`<= 2` / depth-`<= 1` objects, i.e. about `Z/4` values on
an `F_2`-space. By the degree--depth theorem this is not a limitation of those
authors' ambition; it is the whole class. **A "`Z/8` Gauss-sum evaluation with
the Arf/Brown sign" in the sense sweep-08 hoped for does not exist and cannot
exist, because its hypothesis class is empty.** The genuinely `Z/8` objects are
degree `>= 3`, and there the modulus is not a power of two and the phase is not
an 8th root of unity in general.

This is the precise explanation of sweep-08's own residue: `459` of `12,915`
nonzero `|c_F|` are **not** powers of two (`|c_F| in {6,10,12,14,18,20,22,26,34}`),
and `2,297` fibres are non-quadratic. Those are the fibres that have left the
Brown/Taylor class. sweep-08 [t9] item 4 already flagged them as "the precise
residue of the problem"; the degree--depth theorem says *why* they are a residue
and that no `Z/8` refinement of the exact-evaluation machinery will absorb them.

#### Consequence 3: the one published theorem about depth-2 `Z/8` phases over `F_2` points the wrong way

The canonical depth-2 `Z/8` phase over `F_2` is `P(x) = |x|/8` (`|x|` the integer
Hamming weight) -- the `n`-qubit magic state amplitude. Two verified facts about it:

- **Labib, arXiv:2107.10551, Section 4.1**: "the polynomial `P: F_2^n -> T:
  x -> |x|/8` is a nonclassical polynomial of degree exactly three."
- **Labib, Theorem 1.1**: the `n`-qudit magic state has *stabilizer rank*
  `Omega(n)` -- i.e. writing it as a linear combination of stabilizer states
  (equivalently: of exactly-evaluable degree-2/depth-1 Gauss-sum pieces on affine
  subspaces, his Theorem 3.2) requires `Omega(n)` pieces.
- **Berger--Sah--Sawhney--Tidor, arXiv:2107.07495, Theorem 1.2** instantiated at
  `p=2, k=4` (`r=1, l=2`): `f(x) = e(sum_i |x_i|/8)` satisfies
  `||f||_(U^4) = 1` while `|E_x f(x) e_2(-P(x))| = o(1)` for **every** classical
  cubic `P`. So the `Z/8` phase is exactly the witness that classical phases do
  not suffice from `U^4` up over `F_2`.

**REFUTED, with a cited lower bound, as a route: "decompose the `Z/8` phase into
exactly-evaluable `Z/4` Gauss sums and sum the Arf signs" needs `Omega(n)`
pieces.** This is sweep-08's "self-similarity" obstruction ([t7]/(c6):
"exact evaluation ... replaces `sum mu` at level `n` by a signed sum of Arf
invariants over an index set of size `~2^(n/2)`") upgraded from an observation to
a proved lower bound in the model where the pieces are stabilizer states.

#### Consequence 4: but structure DOES defeat the barrier -- and the mechanism is nameable

The counterweight, and it is the most transferable positive result I found:

> **Labib, arXiv:2107.10551, Proposition 4.2.** Let `P: F_p^n -> T` be the phase
> of the magic-state amplitude (for `p = 2`, `P(x) = |x|/8`). Then for **any**
> nonclassical polynomial `Q: F_p^n -> T` of degree at most two,
> `|<e(P), e(Q)>| <= 2^(-cn)` for some `c > 0` depending on `p`.
> (For `p = 2` the proof gives `|<e(P),e(Q)>|^4 <= (3/4)^n`.)

The proof is three steps and every one of them is available to us:
1. **Derivative descent.** `Delta_h P(x) = |h|/8 - |x o h|/4` -- taking one
   additive derivative drops depth 2 to depth 1, i.e. lands exactly in the
   Brown/Taylor exactly-evaluable class, *and* localises the support to the
   coordinates of `h`.
2. **Exact evaluation at depth 1.** The Fourier coefficients of
   `x -> e(|x o h|/4)` are computed exactly: they vanish unless
   `h_i = 0 => alpha_i = 0`, and then have modulus `2^(-|h|)` (so
   `|hat f(alpha)| = 2^(-|h|/2)`).
3. **Average over `h`** with Cauchy--Schwarz (his Lemma 4.1,
   `|<e(f),e(g)>|^4 <= E_h |<e(Delta_h f), e(Delta_h g)>|^2`), giving
   `E_h 2^(-|h|) = (3/4)^n`.

**This is a genuine positive result for a structured depth-2 nonclassical
polynomial over `F_2` with an explicit, exponentially small, effective bound --
exactly the class Bhowmick--Lovett say is a barrier for generic arguments.**
Where it breaks for us is stated in [t7](c) and is a *measured* break, not a
speculative one.

---

### [t4] Witt-vector Fourier analysis: what the Schmid--Witt residue pairing actually diagonalises

Charge item 3 asks: does the residue-pairing form of the characters diagonalise
any natural operator on `G_ell` that the plain character basis does not?
I can now answer this precisely, and the answer has two halves.

Source read in the relevant sections: **Michiel Kosters and Daqing Wan, "Genus
growth in `Z_p`-towers of function fields", Proc. Amer. Math. Soc. 146 (2018)
1481--1494; arXiv:1703.05420**, fetched
<https://arxiv.org/abs/1703.05420> (abstract) and the full text
<https://www.math.uci.edu/~dwan/genus.pdf>. Also fetched:
<https://arxiv.org/pdf/1607.00523> ("On the arithmetic of `Z_p`-extensions") and
M. Schmidt, arXiv:1709.04559.

**First half: the pairing is `Z_p`-bilinear, stated as such.** Kosters--Wan
Section 3, verbatim:

> "Theorem 2.2 gives an isomorphism `W(K)/wp W(K) -> Hom_cont(G_p, Z_p)`. If we
> combine both maps, we obtain a `Z_p`-bilinear, hence continuous, symbol
> `[ , ) : W(K)/wp W(K) x K^*-hat -> Z_p`, `(wp x, y) -> psi(y)x - x`.
> This symbol is often called the Schmid-Witt symbol. For `1 <= n <= infinity`,
> reducing modulo `p^n` gives the level `n` Schmid-Witt symbol
> `[ , )_n : W_n(K)/wp W_n(K) x K^*-hat -> Z_p/p^n Z_p`."

and their explicit formula, verbatim:

> **Theorem 3.2.** Let `x in W(K)` and `y in K^*-hat`. Then
> `[x, y) = Tr_(Z_q/Z_p)( Res( x~ . dlog y~ ) )`.
> Equivalently, let `x = c beta + sum_((i,p)=1) c_i [T]^(-i) (mod wp W(K))` and
> `y = T^e prod_((i,p)=1) prod_(j>=0) (1 - a_(ij) T^i)^(p^j)`. Then
> ```text
> [x,y) = c e Tr_(Z_q/Z_p)(beta)
>       - sum_(j>=0) p^j Tr_(Z_q/Z_p)( sum_((i,p)=1) c_i sum_(l | i) l [a_(lj)]^(i/l) ).
> ```

together with the conductor formula, verbatim:

> **Proposition 3.3.** ... `f_n := f(K(y_0,...,y_(n-1))/K) = p^(u_n)` with
> `u_n = 1 + max{ i p^(n - v(c_i) - 1) : i such that v(c_i) < n }` if such `i`
> exists, and `u_n = 0` otherwise.

**Second half (DERIVED here, from Theorem 3.2, at `q = p = 2`): the pairing is
DIAGONAL in the charter's canonical Witt decomposition, after one explicit
change of basis on the character side -- the divisor-sum (zeta) transform.**

Specialise `k = F_2`, `K = F_2((T))`, `Z_q = Z_2`, `Tr = id`, `alpha = 1`,
`beta = [1]`, `Tr(beta) = 1`. Then `a_(lj) in F_2`, so `[a_(lj)] in {0,1}` and
`[a_(lj)]^(i/l) = [a_(lj)]`. Theorem 3.2 becomes, for `y` a principal unit
(`e = 0`),
```text
[x,y) = - sum_(j>=0) 2^j sum_(i odd) c_i sum_(l | i) l a_(lj)
      = - sum_(l odd) sum_(j>=0) 2^j . l . d_l . a_(lj),     where
d_l := sum_(i odd, l | i) c_i        (the divisor / zeta transform of the
                                      character's Laurent coefficients).
```
Truncating to `G_ell` kills every generator with `l 2^j > ell`, so with
`e_l := sum_(j : l 2^j <= ell) 2^j a_(lj) in Z/2^(k_l)` -- which is **exactly the
`l`-th coordinate of `g` in the charter's `G_ell ~ prod_(l odd) Z/2^(k_l)`,
`k_l = min{m : l 2^m > ell}`** -- and `d'_l := l d_l` (`l` odd, hence a unit in
`Z_2`, so this is a relabelling):
```text
   [a, g)_r  ==  - sum_(l odd, l <= ell)  d'_l . e_l   (mod 2^r).            (*)
```

**Consistency check against sweep-02's verified computation.** At `r = 1` every
`2^j` with `j >= 1` dies, leaving `[a,g)_1 = sum_(l odd <= ell) d_l a_(l,0) mod 2`,
an `F_2`-bilinear form in `ceil(ell/2)` variables. Hence exactly
`2^(#{l odd <= ell})= 2^(ceil(ell/2))` distinct order-`<=2` characters. sweep-02
[t2] measured, for `ell = 1..8`: `#chi = 2, 2, 4, 4, 8, 8, 16, 16 == 2^ceil(ell/2)`.
**Exact agreement.** Likewise Proposition 3.3 at `n = 1` gives conductor exponent
`1 + max{i : c_i odd}` with `i` odd, hence always **even** -- sweep-02 measured
"realized exact conductor exponents `{0,2,4,6,8}` (EVEN only)". **Exact
agreement.** Two independent checks of `(*)`.

**So the answer to charge item 3 is: NO for the duality pairing, YES for the
filtration.**

- The Schmid--Witt residue form does **not** diagonalise the duality pairing
  better than the plain character basis: by `(*)` it *is* the plain basis, up to
  the invertible triangular substitution `c -> d = zeta(c)` on the character
  index. Pontryagin duality of a product of cyclic groups is diagonal in any
  adapted basis; there is no new diagonalisation of that operator to be had.
- What the residue coordinates **do** carry, and the plain coordinates do not, is
  the **conductor**: by Prop. 3.3 the conductor of `chi_a` is read off the
  `c_i` (the Laurent/pole coordinates), while the group decomposition of `G_ell`
  is adapted to the `d_l` (the divisor-transformed coordinates). **The
  conductor filtration and the Witt/exponent filtration on the dual `G_ell^*` are exchanged
  by the Mobius transform, and that is the operator the residue basis
  diagonalises.** `(*)` is the explicit intertwiner. **DERIVED, with two exact
  consistency checks; the underlying Theorem 3.2 is PROVED by citation.**

(Truncation, stated carefully: `(*)` is an identity in `Z_p`; it descends to
`G_ell` because the generator `(1 + T^(l 2^j))` is trivial in `G_ell` exactly when
`l 2^j > ell`, so `a_(lj) = 0` for those pairs and `e_l` is the coordinate in
`Z/2^(k_l)`. The character is therefore determined by
`(d'_l mod 2^(k_l))_(l odd <= ell)`, and the map from Laurent coefficients onto
that data is surjective. The divisor transform is invertible over `Z_2` by Mobius
inversion on odd indices.)

#### A free corollary: sweep-02's queued experiment (d3) is answered qualitatively

sweep-02 (d3) asks which Hayes characters correspond to **monomial** Witt vectors
(a single pole term), because Abbes--Saito's explicit local Fourier transform is
proved for monomial representations. `(*)` answers it: if `a = c_i [T]^(-i)` has a
single pole term, then `d_l = c_i` for **every** odd `l | i` and `d_l = 0`
otherwise. So a monomial Witt vector is spread across *all divisors of `i`* in the
group coordinates -- the monomial characters are those whose `d`-vector is
constant on the divisor set of a single `i`. At `r = 1` there are exactly
`#{i odd, i <= ell} = ceil(ell/2)` nonzero monomial characters out of
`2^(ceil(ell/2))` characters of order `<= 2`, i.e. a **linear-in-`ell` subfamily of
an exponential one**. That is thinner than the `2^(ceil(j/2))/2^(j-1)` fraction
sweep-02 offered as the threshold, so the Abbes--Saito bridge is priced
immediately: **on the monomial family it covers a vanishing fraction of the
characters.** (DERIVED from `(*)`; sweep-02's own `r=1` census supplies the
denominator.)

**Honest verdict on usefulness.** `(*)` is a clean change of coordinates and it
makes the charter's two filtrations simultaneously explicit for the first time.
It supplies **no cancellation**. It is an `L1`-rung identity, not an `L2`
inequality, and I record it as such.

**Negative result on "harmonic analysis on Witt groups".** I searched the arXiv
API for `abs:"Witt vectors" AND abs:"Fourier"`, `abs:"Witt group" AND
abs:"characters"`, `all:"Artin-Schreier-Witt" AND all:"duality"` (the last
returned **zero** hits). There is no body of harmonic analysis built on the Witt
filtration in the sense the charge contemplates: what exists is (i)
Artin--Schreier--Witt *class field theory* (Kosters--Wan, Schmidt), which is the
duality statement itself and is what `(*)` unpacks, and (ii) the `l`-adic local
Fourier transform (Laumon; Abbes--Saito, arXiv:0809.0180), which sweep-02
already identified as the untried bridge. **I am recording this as a coverage
statement, not a proof of nonexistence** -- per the repository's own gotcha, an
empty search whose coverage I have not audited is weak evidence. What I can
assert is that four targeted queries in the obvious phrasings returned nothing.

---

### [t5] Adjacent applications: MacWilliams, association schemes, and the `Z_4`-lift question

This section was run as a parallel literature sweep, which returned **two
independent passes**. The passes agree on every substantive result but disagree
about the provenance of two of them (the first attributed part of the
MacWilliams material to its own delegated sub-reviewers; the second reported that
those sub-reviewers never returned and re-derived the material itself). **Per
charter rule 3 I treated that disagreement as a reason to re-fetch rather than as
an embarrassment**, and the one load-bearing negative -- Wood's `Z/8` MacWilliams
failure -- I verified myself, directly, from the journal PDF; the verbatim
extraction is quoted below. Items neither pass could open are marked
**UNVERIFIED** and carry no theorem content.

#### (4) Do any character-sum estimates proved via `Z_4`/Galois-ring lifts beat the `F_2` Weil bound? **NO, and the reason is structural.**

This was the sharpest question in my charge and it has a clean negative answer.

**R. Blache, "Lifts of points on curves and exponential sums", arXiv:math/0202206**
(<https://arxiv.org/pdf/math/0202206>, extracted and read) quotes the
Kumar--Helleseth--Calderbank bound verbatim: for
`f = f_0 + p f_1 + ... + p^(l-1) f_(l-1)` over the ring of integers `O_m`, `T` the
Teichmuller set, `psi` an additive character of order `p^l`,

```text
   | sum_(x in T) psi(f(x)) |  <=  ( max_(0<=i<=l-1) ( p^(l-1-i) deg f_i ) - 1 ) . p^(m/2).
```

and states his own method verbatim: *"we use Artin-Schreier-Witt theory ... From
Riemann hypothesis for curves over a finite field (Weil's theorem), giving a bound
for the last character sum reduces to the calculation of the conductor."* His
Theorem 5.1 carries an explicit degree-and-genus factor
`(sum_i (A_i+1) deg P_i + 2g - 2) p^(m/2)`.

**So the Galois-ring bounds are *downstream* of Weil, not competitors to it.**
The lift buys two things and neither is "beat Weil": (a) square-root cancellation
for phases valued in `Z/2^k`, which the plain `F_2` Weil bound does not address at
all because the phase is not `+-1`; and (b) in the quadratic case, the **exact
evaluations** of [t2], which beat any Weil-type bound simply by being equalities
-- for a `Z_4` quadratic form of rank `r` on `F_2^m`, KHC gives
`(max(2 deg f_0, deg f_1) - 1) 2^(m/2)` while the truth is `2^(m - r/2)`.
Ling--Ozbudak's improvement (IEEE IT 50(10) (2004) 2529--2539, DOI
10.1109/tit.2004.834743; abstract verified through OpenAlex, **full text
UNVERIFIED**) improves the constant and re-expresses it "in terms of genera of
function fields" -- again the genus, again the quantity sweep-07 identified as the
blocker's log factor.

**Recorded as a stopping result: the exact rank theory, not the Weil-type
machinery, is what the Galois-ring world has to offer this problem.**

#### (5) An exact fourth moment of a `+-2^j`-valued Galois-ring family -- the closest published precedent for `(E2')`

**T. Feng, G. Ge, S. Hu, "Association schemes related to Delsarte--Goethals
codes", arXiv:1212.0347** (<https://arxiv.org/pdf/1212.0347v1>, extracted and
read; independently re-verified). Hypotheses: `R = GR(4,m)` with **`m` odd**,
`q = 2^m`, `T` the Teichmuller set, `G = Z_4 x R x F_q`, and
`S(u,a,b) = sum_(X in T) i^(u + Tr(aX + 2bX^3)) + c.c.`  Verbatim:
**"`S(u,a,b) in {+-2q, +-2 sqrt(2q), +- sqrt(2q), 0}`"** -- i.e. exactly the
`{0} union {+- 2^j}` value set of our `c_F`. The character-table row `E_0` gives,
exactly,

```text
   sum_G 1  = 4q^3,   sum_G S  = 0,   sum_G S^2 = 8 q^4,
   sum_G S^3 = 0,     sum_G S^4 = 16 q^4 (3q - 1).
```

so the normalized fourth moment is
`(sum S^4) |G| / (sum S^2)^2 = (3q-1)/q -> 3` -- **the Gaussian value, with an
absolute constant, for a real family of Gauss-sum-like `+-2^j` quantities.**

**This is the best precedent I found for `(E2')`/`M_4` and it is worth the lane's
attention.** Three honest caveats, all recorded: (a) `sum_G S = 0` holds for a
*trivial* reason (`S(u+2,a,b) = -S(u,a,b)`), i.e. by symmetry, not by arithmetic
cancellation -- so this family does **not** exhibit `(S)`-type behaviour, it
exhibits an exact symmetry; (b) the objects are `zeta_4`-valued sums over the
*multiplicative* Teichmuller set, not `zeta_8`-valued forms on affine subspaces --
structural analogy, not identity; (c) the value set is specific to the single
cubic term (`r = 2`); general `DG(m,r)` reintroduces a rank parameter.

#### (1) MacWilliams over `Z/2^k`: genus-`g` identities exist, but the `Z/8` collapse to a scalar weight is PROVABLY INVALID

**The positive half.** Genus-`g` / `m`-tuple MacWilliams identities do exist over
`Z_k` and over Galois rings, and at `g = 4` they are literally fourth-moment
identities:

- **N. Kaplan, "MacWilliams identities for `m`-tuple weight enumerators",
  arXiv:1205.1277v3** (<https://arxiv.org/pdf/1205.1277v3>; read on the sweep's
  *first* pass only, not reconfirmed on the second -- treat as
  **SINGLY VERIFIED**), **Theorem 4**
  (attributed to Ray-Chaudhuri--Siap): for linear `C_1,...,C_m  contained in  R^N` over a
  single Galois ring `R = Z_(p^e)[xi]` -- so `p=2, e=k` is exactly `GR(2^k, m)` --
  `CW^[m]_(C_1^perp,...,C_m^perp) = (1/prod|C_i|) CW^[m]_(C_1,...,C_m)(Y)` with
  `Y` the explicit character substitution. Hypotheses are minimal (linear codes,
  standard pairing; no self-duality, no freeness) and the constant is exactly
  `prod |C_i|^(-1)` -- **no degree or rank factor anywhere.**
- Genus-2 over `Z_k`: **Chakraborty--Miezaki, arXiv:2006.12781** (Des. Codes
  Cryptogr. 89 (2021)), Theorem 2.2, with independent dualisation of each slot.
  Genus-`g` Jacobi version: **Chakraborty--Miezaki--Oura, arXiv:2111.10162**,
  Theorem 4.1. Genus-`g` cwe over `Z_(2k)`: **Bannai--Dougherty--Harada--Oura,
  IEEE IT 45 (1999) 1194--1205**, Theorem 5.1 (scope verified at
  <http://sphere.w3.kanazawa-u.ac.jp/BannaiTypeII.pdf>; **the displayed formula
  is in bitmap fonts and did not extract -- UNVERIFIED**).

**The judgment, and it is the answer to my charge's question.** These are **exact
linear duality transforms, not evaluations**: a genus-4 MacWilliams identity
relates one unknown fourth moment to another. They become computational only when
one side is independently accessible -- either `C^perp` is small enough to
enumerate, or `C` is self-dual, in which case the identity becomes invariance
under a finite group and the enumerator is pinned by an invariant ring (the
Type II / Molien apparatus). **Neither holds for the Lemire family as posed, and
MacWilliams duality is positivity-free while `(S)` is a positivity statement, so
this branch cannot supply `(S)` at all.** There is also a structural mismatch:
these sums run over tuples of codewords of *fixed linear codes*, whereas
`zeta_8^(q_F(x))` with `q_F` quadratic is a Gauss sum, not a monomial in the
enumerator variables. The one route worth trying is to realise the fibres `{A_F}`
as the cosets of a *single* linear code over `Z/8` or `GR(8,m)`, so that the outer
fibre sum and the inner sums fuse into one genus-`g` enumerator -- then Kaplan's
Theorem 4 evaluates rather than merely transforms, *if* the dual is small.

**The negative half, and it is a hard one.**
**J. A. Wood, "Homogeneous weight enumerators over integer residue rings and
failures of the MacWilliams identities", Rev. Un. Mat. Argentina 64(2) (2023)
333--353**, DOI 10.33044/revuma.2807. **Fetched and extracted by me directly**
from <https://revistas.uns.edu.ar/revuma/article/download/3982/2188>; the
following are verbatim from that extraction. Abstract: *"The MacWilliams
identities for the homogeneous weight enumerator over `Z/mZ` do not hold for
composite `m >= 6`. For such `m`, there exist two linear codes over `Z/mZ` that
have the same homogeneous weight enumerator, yet whose dual codes have different
homogeneous weight enumerators."*  Example 3.5, verbatim: *"For `m = 8 = 2^3`,
`p = 2`, `a = 3`, the generator matrices of (3.2) are `G_3 = [4 2 2]`,
`G_4 = [[0 4 4],[4 0 4]]`. Then `howe_(C_3) = howe_(C_4) = 1 + 3t^4`, while a
computation gives"*

```text
   howe_(C_3^perp) = 1 + 2t + 31t^2 + 60t^3 + 31t^4 + 2t^5 + t^6
   howe_(C_4^perp) = 1 + 6t + 15t^2 + 84t^3 + 15t^4 +  6t^5 + t^6
```

and Remark 3.4, verbatim: *"The results of this section also hold for finite
commutative chain rings."* -- **which includes `GR(8,m)`.** Wood notes that `Z/4` is the
exception precisely because its homogeneous weight equals the Lee weight, which is
why HKCSS eq. (9) works there.

**PROVED (by citation, with published counterexample): any argument that collapses
`Z/8` phase data to a scalar Lee-like weight and then dualises is invalid.**
This is the `Z/2^k` incarnation of the same "`Z/4` is special, `Z/8` is not"
phenomenon that [t3] proves on the quadratic-form side, arriving from a completely
different direction. One must stay at the complete (8-variable) weight-enumerator
level. (A partial reprieve claimed by the sweep's reviewer -- that
Gluesing-Luerssen, arXiv:1304.6589, Thm 4.4 makes the 3-block homogeneous
*partition* reflexive over local rings -- is that reviewer's reconciliation and is
stated in neither paper. **UNVERIFIED; do not rely on it.**)

#### (3) Association schemes on Galois rings: exact eigenvalues, but no fourth-order object

**K.-U. Schmidt, "Quadratic and symmetric bilinear forms over finite fields and
their association schemes", arXiv:1803.04274** (<https://arxiv.org/pdf/1803.04274v1>,
read). The orbits of `Q(m,q)` and `S(m,q)` under `F_q^* x GL_m(F_q)` give mutually
dual translation schemes with `floor(3m/2)` classes; Proposition 2.2 (Dickson):
`floor(3m/2)+1` orbits, **two for each nonzero even rank** -- the Arf distinction
made into scheme classes. Theorems 3.1/3.2 give the `P`- and `Q`-numbers
explicitly as combinations of generalised Krawtchouk polynomials, **new for even
`q`**; Theorems 4.7--4.9 give closed-form inner distributions of maximal `d`-codes.
Schmidt notes the schemes are **neither `P`- nor `Q`-polynomial**, so no
orthogonal-polynomial shortcut exists.

**Verdict.** The inner distribution of a `d`-code *is* a rank-and-type
distribution, hence exactly `sum_F c_F^2` -- so this feeds `(E2')`, by the same
mechanism as `(GR-3)`. But association-scheme theory is second- and third-order
(Delsarte LP = pairs, Krein/Schrijver = triples): **there is no fourth-order
object in it**, and its exact moments are consequences of knowing the full
eigenmatrix `P`, which is a harder problem than the estimate we want. Also, every
Galois-ring scheme located (Kerdock 3-class, Delsarte--Goethals 9-class,
Ikuta--Munemasa cyclotomic, Feng--Ge--Hu) is `zeta_4`-valued over the
*multiplicative* Teichmuller set. **No association scheme in the literature is
built on `Z/8`-valued quadratic forms, `zeta_8` Gauss sums, or families of affine
subspaces of `F_2^m`.**

#### (6) The one place a SIGNED family distribution is known exactly

Worth separating out, because it is the only verified thing in this whole sweep
that speaks to `(S)` rather than `(E2')`. Schmidt's **Theorems 9 and 10**
(same paper as [t2](E4)) give the **full signed correlation distribution** of the
quaternary sequence families `S(t)` and `S*(t)` -- not just `|chi|`, but the
multiplicities of each of `+-2^j`, `+-i 2^j`, `+- omega 2^j`, `+- omega^3 2^j`.
The mechanism is Results 6/7: the **exact rank distributions** of the
Delsarte--Goethals-type sets
`Q(t) = {Q_a : Q_a(x) = Tr(a_0 x) + 2 sum_(j=1..t) Tr(a_j x^(2^j+1))}`, in closed
form as alternating sums of 4-ary Gaussian binomials, using the property that the
difference of two distinct elements has rank at least `m - 2t`.

**So there does exist a structured family of `Z_4` quadratic forms whose signed
Gauss-sum distribution is known exactly.** It is not our family -- the parameter
`t` enters as the analogue of a rank/degree factor (the maximum correlation is
`1 + 2^(m/2 + t)`), and the family is a *uniformly high rank* one, which the lane
has already REFUTED for the Lemire fibres (all even ranks `0..10`, including
rank 0). But it is the existence proof that `(S)`-type information is obtainable
when the rank distribution is under control, and it says exactly what one would
have to establish about the Lemire family to get there. `(GR-3)`'s rank-count
reformulation is the same requirement seen from the counting side.

#### (2) `Z/2^k`-valued quadratic forms for `k >= 3`: the gap is real

Searching arXiv and OpenAlex directly, the sweep found **no `Z/8`-valued (or
`Z/2^k`-valued, `k >= 3`) analogue of Schmidt's rank classification**. Taylor
covers the general case but gives a *dichotomy*, not a rank dictionary.
**By [t3] this is not an oversight in the literature: over `F_2` there is nothing
to classify, because the class is `2 x (Brown Z/4 forms)`.** The two negatives --
"no `Z/8` rank classification exists" and "`Z/8` quadratic enhancements are
`Z/4` in disguise" -- are the same fact reached from opposite directions, which is
the strongest form of confirmation available here.

One positive worth recording, because it bounds how far [t3] reaches:
**`Z/8`-valued generalized bent functions on `Z_2^n` do exist** for every even `n`
-- Liu, Feng, Feng, "Nonexistence of generalized bent functions from `Z_2^n` to
`Z_m`", arXiv:1507.05751 (<https://arxiv.org/pdf/1507.05751>), Lemma 1(2) with the
explicit construction in Remark 1(A); their nonexistence results are for odd
prime-power `m` and impose no obstruction at `m = 2^k`. This does **not** conflict
with [t3]: a generalized bent function need not be quadratic, and by [t3] a
genuinely `Z/8`-valued one cannot be. It does mean sweep-08's refutation of
generalized bentness (`0` of `18,884` fibres) is a statement about a **nonempty**
class, hence informative -- and by [t8](3) it is the same statement as "not full
rank".

Also verified, and it matters for `(GR-2)`: the sweep independently flags that
**"`G(p)` is `0` or `+-2^j`" is strictly stronger than the general theorem gives.**
Taylor yields `{0} union 2^j . mu_8`; the restriction to real `+-` needs the
alternating / `Q = 2h` hypothesis, at which point Brown's property (7)
(`sigma(Q) = 4 Arf(h)`) makes the sign exactly `(-1)^(Arf)`. That is precisely
hypothesis `(GR-2)`, arrived at independently.

---

### [t6] What the exact theory buys: `(E2')` becomes a rank-distribution count, and `(S)` becomes an Arf Mobius statement

Everything in [t2] is an *exact value*, so it can be pushed all the way through
sweep-08's split without losing a constant. Doing that is the main constructive
contribution of this diary.

#### The dictionary

Let `F` be an exact affine fibre, `n_F = dim F`, and suppose (this is hypothesis
`(GR-2)` below, and it is the thing to measure first) that the fibre phase is a
`Z/4`-valued Brown form `Q_F`, equivalently a nonclassical polynomial of degree
`<= 2`, equivalently `Q_F = 2 q_F` with `q_F: F -> F_2` an ordinary quadratic
function. Let `b_F` be the associated `F_2`-bilinear form and `r_F = rank(b_F)`.
Then Taylor Corollary 1.11 / Schmidt Result 4 give **exactly**

```text
   c_F = 0                     if q_F is not tame  (the radical carries a
                                                    nontrivial linear character);
   c_F = (-1)^(Arf(q_F^red)) . 2^(n_F - r_F/2)     if q_F is tame.
```

so that

```text
   c_F^2 = 2^(2 n_F - r_F)   on tame fibres,   0 otherwise,
   #points in F = 2^(n_F).
```

Note the coincidence that does the work: **a nonsingular fibre (`r_F = n_F`)
contributes `c_F^2 = 2^(n_F)` = exactly its own point count**, i.e. its within-fibre
off-diagonal correlation is exactly zero. So in sweep-08's identity
`sum_F c_F^2 = N_points + sum_F sum_(x != y in F) eps(x)eps(y)`, the entire
off-diagonal term is carried by the *degenerate* fibres, in two opposite
directions.

#### `(GR-4)` -- `(E2')` is exactly a rank-distribution inequality, with no signs at all

**DERIVED (exact, given `(GR-2)`).** Substituting,

```text
   (E2')   sum_F c_F^2 <= N_points
   <==>    sum_(F tame) 2^(2 n_F - r_F)  <=  sum_(F all) 2^(n_F)
   <==>    sum_(F tame) 2^(n_F) ( 2^(n_F - r_F) - 1 )  <=  sum_(F not tame) 2^(n_F).
```

**In words: `(E2')` holds if and only if the rank-defect mass of the tame fibres
is dominated by the point mass of the fibres whose Gauss sum vanishes.**

This is exactly the shape sweep-08 asked for in its experiment (d3) ("stratify
`c_F` by `(rank, Arf)` ... check whether `(E2')` is provable stratum by stratum")
and it answers the question there: **yes, stratum by stratum, and the
stratification is by `(n_F, r_F, tame?)` alone -- the Arf invariant does not
appear.** `(E2')` is a *pure counting statement about the rank distribution of the
second-trace-difference forms*, and the lane already computes those ranks
(`52-gf2-lemire.md`: "all even ranks `0..10` occur, including rank 0").

It also explains, and predicts, sweep-08's drift. At the pinned witness
`(ell,k,d) = (9,11,8)`: `5,969` of `18,884` fibres have `c_F = 0`, and the ratio
`sum c_F^2 / N_points = 120,680/130,048 = 0.928`. The two sides of `(GR-4)` are
close. **`(E2')` will hold or fail exactly according to whether the degenerate
fraction keeps pace with the rank defect as `ell` grows**, and that is a single
number to plot, not a search. If the lane wants to know whether to bet on `(E2')`
or fall back to `(E2)`, this is the cheapest possible instrument and it needs no
new measurement beyond the ranks the report already has.

#### `(GR-5)` -- `(S)` is exactly a weighted Mobius statement for the Arf invariant

**DERIVED (exact, given `(GR-2)`).** With the same substitution,

```text
   (S)   | sum_F (-1)^(Arf(q_F^red)) 2^(n_F - r_F/2) |
                <=  C ( sum_(F tame) 2^(2 n_F - r_F) )^(1/2).
```

Every trace of the `Z/8` phase, of the discriminant, and of the polynomial
arithmetic has been removed. **`(S)` is: square-root cancellation, with an
absolute constant, of `(-1)^Arf` over the fibre index, weighted by
`2^(n_F - r_F/2)`.** This is the sharpest form of sweep-08's Problem T that I can
state, and it is a strictly smaller statement than Problem T because the Gauss
sums have been evaluated away.

#### `(GR-1)` -- the base case where `(S)` is TRUE with `C = 1`, and what it costs

**PROVED.** Let `B` be a nonsingular symmetric bilinear form on `V = F_2^n`, `Q_0`
a Brown `Z/4`-form with bilinear form `B`, and let the family be the full
*linear-twist orbit* `{ Q_x := Q_0 + j B(., x) : x in V }`. By Brown's property
(10), `sigma(Q_x) = sigma(Q_0) - 2 Q_0(x)` in `Z/8`, so by (11)

```text
   G(Q_x) = 2^(n/2) zeta_8^(sigma(Q_0)) . i^(-Q_0(x)),
   sum_(x in V) G(Q_x) = 2^(n/2) zeta_8^(sigma_0) . conj(G(Q_0)) = 2^n,
   sum_(x in V) |G(Q_x)|^2 = 2^n . 2^n = 2^(2n).
```

Hence `|sum_x G(Q_x)| / (sum_x |G(Q_x)|^2)^(1/2) = 2^n / 2^n = 1` **exactly**.
(The identity is elementary -- expand and use orthogonality of `x -> (-1)^(B(u,x))`
-- but Brown (10) is what turns it into a statement about the *signs*, which is
the content `(S)` needs. Equivalently, Taylor Proposition 1.13
`beta(psi_h) = beta(psi) - psi(c)`, or the classical Arf-shift identity
`Arf(q + b(.,x)) = Arf(q) + q(x)` obtained from (10) by dividing (7) by 4.)

**And the immediate corollary that prices the obvious route. REFUTED.** If the
index set is a disjoint union of `M` *full* twist orbits of dimensions
`n_1,...,n_M`, then `Delta = sum_m 2^(n_m) > 0` and
`(sum_p G(p)^2)^(1/2) = (sum_m 2^(2 n_m))^(1/2)`, so

```text
   Delta / l2 = (sum_m 2^(n_m)) / (sum_m 2^(2 n_m))^(1/2)  ->  sqrt(M)
```
with equality when the dimensions agree. **Every orbit contributes with the same
sign, so decomposing the Lemire family into complete twist orbits produces zero
cross-orbit cancellation and `(S)` fails at any fixed `C` once `M > C^2`.** This
is the constant-phase adversary of sweep-08 [t5](1) reappearing at the level of
orbits, and it says: *`(S)` cannot be proved by completing orbits.*

The positive reading of the same computation is the important one:
sweep-08 measured `Delta / l2` with mean `-0.317` and sd `0.953` over twelve rows
-- indistinguishable from independent signs, and nowhere near `sqrt(M)`. **So the
Lemire fibre family is emphatically NOT a union of complete twist orbits; all of
its cancellation comes from the orbits being incomplete.** That reframes `(S)`:

> **`(S)` is a statement about INCOMPLETE Gauss sums in the twist parameter.**

Concretely, writing the family as `P  contained in  union_m O_m` with `S_m  contained in  V_m` the twist
parameters actually realised in orbit `m`,

```text
   Delta = sum_m (-1)^(Arf_m) 2^(n_m - r_m/2) . T_m,
   T_m := sum_(x in S_m) (-1)^(q_m(x)),
```
an incomplete quadratic character sum over `S_m`, and `(S)` requires square-root
cancellation **both** inside each `T_m` **and** across `m`. **This is sweep-08's
"self-similarity" obstruction ([t7]/(c6)) made exact and, for the first time,
split into two named halves.** It is also the point at which sweep-02's dismissal
of Burgess ("our sum is complete over its fibres; Burgess has nothing to give")
stops applying: at the *second* level -- the fibre/twist index -- the sums are
incomplete, which is Burgess's home ground. I did not test this; it is `(d4)`
below.

#### `(GR-7)` -- an EXACT fourth moment, and what it says about `M_4`

Charge item 4 asks whether a `Z/2^k` MacWilliams-type identity could re-express
the product-constrained `M_4` exactly. Schmidt's Result 4 answers the question in
the affirmative on the complete twist family, and does it without MacWilliams --
the mechanism is the rank stratification. Reading the moments straight off the
distribution table for an *alternating* `Z_4`-form of rank `r` on `V = F_2^m`:

```text
   sum_u chi_Q(u)   = (2^(r-1)+2^(r/2-1) - (2^(r-1)-2^(r/2-1))) . 2^(m-r/2) = 2^m
   sum_u chi_Q(u)^2 = 2^r . 2^(2m-r)                                        = 2^(2m)
   sum_u chi_Q(u)^4 = 2^r . 2^(4m-2r)                                       = 2^(4m-r)
```

so **`sum_u chi^4 = 2^(-r) (sum_u chi^2)^2` exactly**, with the *rank* the only
parameter. The first line is Parseval, the second is `(GR-1)`; the third is new
here and is the point: **a complete twist family has an exactly-computable fourth
moment, and its ratio to the squared second moment is `2^(-rank)`.** So the
Montgomery--Soundararajan-shaped question `K_4 <= M_2^2` (which sweep-09
identified as the fixed-`q` case of an open problem over `Z`) is, on this model
family, not merely true but an identity with an explicit deficit `2^(-r)`.

**What this does and does not give the lane.** It gives an exact benchmark: any
sub-family of a complete twist orbit has `sum chi^4` computable stratum by
stratum from the rank distribution alone, so the connected cumulant `K_4` on such
a family is a rank count. It does **not** give `M_4` for the Hayes family, which
is not a twist family. But it does say where to look: **if the lane can exhibit
its `M_4` as a sum over `(dim, rank)` strata of complete twist orbits, `M_4`
becomes exact, with no inequality anywhere.** That is a much more specific target
than "find a MacWilliams identity", and it is testable on the existing report.

---

### [t7] Verdicts on technique classes, against `(E2')` and `(S)`

Same table shape as sweep-08 [t7], restricted to my field and with the reasons
sharpened by [t3] and [t6].

| Technique | Reaches `(E2')`? | Reaches `(S)`? | Exact reason |
|---|---|---|---|
| Brown/Taylor/van der Blij exact Gauss-sum evaluation | **Yes, and it reduces `(E2')` to a rank count `(GR-4)` with no signs** | No | Exact values, no constant lost; but it is a per-fibre statement, blind to sign correlation across fibres. Applies only to the degree-`<=2`/`Z/4` sector -- see [t3]. |
| Schmidt's `(rank, alternating)` classification, IEEE IT 55 (2009) | **Yes, and it supplies the exact stratum populations for a full twist family** | No | Result 4 / Theorem 5 give the whole multiset `{chi_Q(u)}`; but the Lemire index set is a *sub*family, and Schmidt says nothing about subfamilies. |
| Weil bounds over Galois rings (Kumar--Helleseth--Calderbank 1995; Ling--Ozbudak 2006) | No | No | Carries the `(d-1)` degree factor and is tight for Kerdock/DG. The improved version re-expresses the loss through the *genus*, which sweep-07 already identified as the blocker's log factor. |
| Higher-order Fourier / inverse theorems over `F_2` | No | No | Dichotomies, with ineffective (Tao--Ziegler, BFHHL nilspace) or triple-exponential (Tidor `U^4`, arXiv:2109.13108) constants. Structurally cannot certify a constant-factor square-root bound. Confirmed independently by a parallel sweep of this literature. |
| Derivative descent (Labib Prop. 4.2 mechanism) | No | **Closest thing to a mechanism, but REFUTED for this family** | Needs `Delta_h`(phase) to have *uniformly* small Fourier coefficients, i.e. uniformly high rank in `h`. The lane's own uncollapsed pairwise-rank test finds all even ranks `0..10` **including rank 0**; at rank 0 the derivative's Fourier mass is a single atom and the step buys nothing. This is a measured break, not a speculative one. |
| Stabilizer-rank / magic-state machinery (Labib Thm 1.1) | No | No, and it is a lower bound in the wrong direction | Says `Omega(n)` exactly-evaluable pieces are needed to represent a depth-2 `Z/8` phase. That is the self-similarity obstruction with a proof behind it. |
| Schmid--Witt residue coordinates (Kosters--Wan Thm 3.2) | No | No | An `L1` change of basis `(*)`; makes the conductor and Witt filtrations simultaneously explicit; supplies no cancellation. |
| Completing twist orbits | -- | **REFUTED** | `(GR-1)` corollary: complete orbits all contribute with the same sign; `Delta/l2 -> sqrt(M)`. |

**Two things in this table are worth stating as stopping results in their own
right.** First, `(E2')` now has a *technique that reaches it* -- it is a rank
count and the exact evaluation delivers it without losing a constant. Second,
nothing in this field reaches `(S)`, and I can now say why in one sentence
rather than by enumeration: **every exact-evaluation theorem in the area
(Brown (11), Taylor 1.11/1.18, van der Blij (2), Schmidt Result 4/Thm 5) computes
the Gauss sum of ONE form, and the one identity that relates the signs of two
different forms -- Brown (10) / Taylor 1.13 / the Arf-shift formula -- expresses
that relation as a QUADRATIC function of the twist, so summing it reproduces a
Gauss sum of the same species one level down.** The self-similarity is not an
accident of the Lemire family; it is a structural property of the Arf sign.

---
### [t8] Dead ends, near-misses, and one deduplication for the ledger

1. **"`Z/8` Gauss-sum evaluation with the Arf/Brown sign" does not exist as a
   class of theorem.** I spent the first part of the sweep looking for it. The
   degree--depth theorem ([t3]) says the hypothesis class is empty over `F_2`.
   Recorded so no future lane looks again.
2. **`GR(2^k, m)`-valued quadratic forms are a different generalisation and not
   ours.** "An invariant for quadratic forms valued in Galois Rings of
   characteristic 4", Finite Fields Appl. (2007) -- fetch of
   <https://www.sciencedirect.com/science/article/pii/S1071579706000220> returned
   **HTTP 403**, so I have only the abstract as surfaced by search: it extends
   Brown's invariant to forms *valued in* `GR(4,m)`, with the invariant living in
   `GR(8,m)`. Related: Witt cancellation/extension for Galois-ring-valued
   quadratic forms, Finite Fields Appl. (2010),
   <https://www.sciencedirect.com/science/article/pii/S1071579710000286>
   (the PDF endpoint returned HTML, not PDF -- **UNVERIFIED**). Either way the
   generalisation direction is "enlarge the coefficient ring", not "deepen the
   phase group", so it does not reach `Z/8` phases on an `F_2`-space.
3. **Generalized bentness is not an independent measurement.** Qi--Mesnager--Tang,
   "Codebooks from generalized bent `Z_4`-valued quadratic forms", arXiv:1905.08834
   (fetched <https://arxiv.org/pdf/1905.08834>), their Lemma 3, verbatim:
   "A `Z_4`-quadratic form `Q(x)` has full rank `m` if and only if it is
   generalized bent." So the lane's two refutations -- "0 of 18,884 fibres have
   flat primitive `Z/8` Walsh spectra" and "all even ranks `0..10` occur,
   including rank 0" -- are **the same fact stated twice**. Worth recording as a
   deduplication; it also means the bentness test costs nothing to keep but adds
   nothing to the rank test.
4. **Postnikov-style linearisation of the *phase* (as opposed to the character).**
   sweep-02 closed the character side. I checked whether the `Z/8` phase itself
   linearises through `dlog`: it does not, for the reason in [t3] -- the depth-2
   part is genuinely cubic, and `dlog` is a group homomorphism, so it cannot
   produce a degree-3 object from a degree-1 one.
5. **Near-miss worth recording.** I first tried to read the powers-of-two
   measurement through Brown's *nonsingular* theorem (11), which predicts
   `|G| = 2^(dim/2)` always and therefore predicts **no zeros**. sweep-08 measures
   `5,969` zeros out of `18,884`. The nonsingular statement is the wrong citation;
   Taylor's Corollary 1.11, which allows a radical and gives
   `N = 0` or `sqrt(|T^perp||T|)`, is the right one. Had I stopped at the
   better-known reference I would have filed a false discrepancy.

---

## FINDINGS

### (a) Field map

Four bodies of work touch `Z/2^k`-valued Fourier analysis. They are not
interchangeable and only the first two are about our object.

1. **Quadratic forms/functions on finite abelian 2-groups with `Q/Z` values
   (Brown 1972; Wood 1993; Taylor; van der Blij; Turaev 1998; Deloup).**
   Topological in origin (Kervaire invariant, signature mod 8, linking forms).
   Delivers **exact evaluation** of the Gauss sum: modulus `0` or
   `sqrt(|T^perp||T|)`, phase an 8th root of unity given by a `Z/8` invariant
   which is `4 x Arf` in the `F_2`-valued case and a lattice **signature mod 8**
   in general. **This is our theory.** Its hypothesis class over an `F_2`-space is
   exactly "values in `Z/4`", i.e. nonclassical degree `<= 2`.
2. **The `Z_4` coding-theory program (Hammons--Kumar--Calderbank--Sloane--Sole
   1994; Kumar--Helleseth--Calderbank 1995; Schmidt 2009; Ling--Ozbudak 2006).**
   Same forms, used to compute *distributions over structured families*
   (Kerdock, Delsarte--Goethals, quaternary sequence families). Schmidt's
   `(rank, alternating)` classification is the sharpest tool here and gives the
   complete multiset of twisted Gauss sums. The Weil-bound branch is the part
   that carries a degree factor and is the part that cannot help us.
3. **Higher-order Fourier analysis with `T = R/Z` phases (Tao--Ziegler 2011;
   Bhowmick--Lovett 2015; Bhattacharyya--Fischer--Hatami--Hatami--Lovett 2013;
   Berger--Sah--Sawhney--Tidor 2022; Tidor 2022; Labib 2022; Candela--
   Gonzalez-Sanchez--Szegedy).** Provides the *definitions* (nonclassical
   polynomial, degree, depth, rank) that make the field map possible at all, and
   the degree--depth theorem that locates the gap. Its own theorems are
   dichotomies with ineffective or tower-type constants.
4. **Coding-theoretic duality over `Z/2^k` and Galois rings (Wood 1999, 2023;
   Kaplan; Bannai--Dougherty--Harada--Oura; Chakraborty--Miezaki(--Oura);
   association schemes: Schmidt 2018, Feng--Ge--Hu 2012).** Genus-`g` MacWilliams
   identities exist over `Z_k` and over Galois rings, and at `g = 4` they are
   fourth-moment identities -- but they are exact linear *transforms*, not
   evaluations, and they are positivity-free, so they can feed `(E2')` only when
   one side is independently accessible and can never feed `(S)`. This branch also
   supplies the sharpest independent confirmation of the `Z/4`-vs-`Z/8` boundary:
   the homogeneous-weight MacWilliams identity **fails** over `Z/8`.
5. **Artin--Schreier--Witt class field theory (Schmid 1936; Witt 1936;
   Kosters--Wan 2018; M. Schmidt 2017).** Supplies the *character* side: an
   explicit `Z_p`-bilinear residue pairing that coordinatises the dual
   `G_ell^*`. There is **no** harmonic analysis built on the Witt filtration beyond this duality;
   four targeted arXiv-API queries returned nothing (coverage statement, not a
   proof of nonexistence).

The Lemire fibre problem sits at the intersection of (1)+(2) for its
exactly-evaluable sector, spills out of it into (3)'s barrier class for the
residue, is bounded above by (4)'s duality transforms without being solved by
them, and is coordinatised by (5).

### (b) The exact gap between existing `Z/2^k`-valued Fourier theory and what the Arf-sign family needs

Stated as sharply as I can, in three lines.

> **Over `F_2`, the degree--depth inequality `depth <= floor((degree-1)/(p-1))`
> forces every nonclassical polynomial of degree `<= 2` to take values in `Z/4`.
> Every exact `Z/2^k` Gauss-sum evaluation in the literature -- Brown (11),
> Taylor 1.11/1.18, van der Blij (2), Schmidt Result 4/Theorem 5 -- is a theorem
> about that class. The genuinely `Z/8` (depth-2) objects begin at degree 3,
> where no exact evaluation exists, the one published theorem about the canonical
> example (`x -> |x|/8`) is a `Omega(n)` *lower* bound on its decomposition into
> the evaluable class, and the classical-phase inverse theorem provably fails
> from `U^4` up.**

Three consequences that price the gap:

- **The hoped-for tool does not exist and cannot.** sweep-08's finding (b),
  "exact `Z/8` (Galois-ring) quadratic Gauss-sum evaluation with the Arf/Brown
  sign", names a class with empty hypotheses. The correct statement of what is
  available is: *exact `Z/4` evaluation, which is exactly the sector where the
  phase is `(-1)^(F_2`-quadratic`)`.*
- **The lane's "quadratic" is not the literature's "quadratic".** `Z/8`-ANF
  degree and nonclassical degree differ: a monomial `c_S prod x_i / 8` has
  nonclassical degree `|S| + 2 - v_2(c_S)`. The `16,587` "at-most-quadratic"
  fibres at the pinned witness include fibres of nonclassical degree up to `4`.
  **The exactly-evaluable sector is
  `{F : linear Z/8-ANF coefficients even, quadratic ones in 4Z/8, none above}`,
  equivalently `{F : the fibre phase is 2 x (a Brown Z/4 form)}` -- which the lane
  has not measured.**
- **The same "`Z/4` is special, `Z/8` is not" boundary appears independently on
  the coding side.** Wood (Rev. Un. Mat. Argentina 64(2) (2023) 333--353) proves
  the MacWilliams identity for the *homogeneous* weight enumerator over `Z/mZ`
  **fails for composite `m >= 6`**, with an explicit `Z/8` counterexample, and
  the failure extends to finite commutative chain rings, hence to `GR(8,m)`.
  `Z/4` escapes only because its homogeneous weight equals the Lee weight. So
  two independent branches of the subject -- quadratic-form theory and weight
  enumerators -- both stop at `Z/4` over `F_2`, for reasons that are not the
  same but that bound the same object.
- **The residue is identified, and it is small.** The `459` fibres (of `12,915`
  nonzero) whose `|c_F|` is not a power of two are exactly the fibres that have
  left the evaluable class. sweep-08 [t9](4) already nominated them as the
  precise residue; [t3] supplies the theorem saying they are irreducibly so.

### (c) Transferable techniques, and where each breaks

1. **Taylor's singular Gauss-sum dichotomy (Corollary 1.11 + 1.18).**
   `N(psi) = 0` if not tame, else `sqrt(|T^perp| |T|)`; phase an 8th root of
   unity. *Transfers cleanly* and is the correct citation for the lane's
   powers-of-two measurement, **including the large zero atom that the more
   familiar nonsingular Brown statement does not predict**.
   **Breaks:** per-fibre only; blind to sign correlation across fibres; and
   applies only to nonclassical degree `<= 2`.
2. **Schmidt's `(rank, alternating)` stratification (IEEE IT 55 (2009),
   Result 4 / Theorem 5).** Gives the entire multiset `{chi_Q(u) : u in V}` for a
   *complete* linear-twist family, hence all its moments exactly, hence `(E2')`
   and even `M_4`-type quantities on such a family with no constant lost.
   **Breaks:** the Lemire index set is a proper subfamily. `(GR-1)`'s corollary
   shows that the complete family is precisely the case with *no* cancellation
   (`Delta/l2 -> sqrt(M)`), so the theorem's hypothesis is the adversarial case.
3. **Brown's twist-transfer identity (10) / Taylor 1.13 / the Arf-shift formula
   `Arf(q + b(.,x)) = Arf(q) + q(x)`.** The only identity in the area relating
   the signs of two *different* forms. *Transfers*; it is what turns `(S)` into a
   statement about incomplete sums (`(GR-5)`, `[t6]`).
   **Breaks, and this is the structural obstruction:** the relation is
   **quadratic** in the twist parameter, so summing the signs over the twist
   reproduces a Gauss sum of the same species one level down. Self-similarity is
   a property of the Arf sign itself, not of this family.
4. **Derivative descent (Labib, Quantum 6 (2022) 645, Prop. 4.2).** Take one
   additive derivative to drop depth `2 -> 1`, evaluate exactly there
   (Brown/Taylor), average over `h` with Cauchy--Schwarz. Gives a genuine
   *exponentially small, effective* correlation bound `(3/4)^(n/4)` for a
   structured depth-2 `Z/8` phase -- i.e. **structure does defeat the
   Bhowmick--Lovett barrier, and this is how.**
   **Breaks:** it needs `|hat(e(Delta_h P))|` uniformly small, i.e. the
   derivative uniformly high-rank in `h`. The lane's uncollapsed pairwise
   second-trace rank test finds **all even ranks `0..10`, including rank 0**; at
   rank 0 the derivative's spectrum is a single atom and the step gains nothing.
   Measured break.
5. **The Schmid--Witt residue pairing in Kosters--Wan's ghost-free form
   (Thm 3.2).** Coordinatises the dual `G_ell^*`; `(*)` in [t4] exhibits the
   pairing as diagonal in the charter's canonical Witt decomposition after the
   divisor-sum transform `c -> d`, and identifies the conductor filtration and the
   Witt filtration as Mobius transforms of each other.
   **Breaks:** it is a change of basis. `L1`, not `L2`. No cancellation.
6. **Exact SIGNED family distributions from an exact rank distribution
   (Schmidt 2009, Results 6/7 + Theorems 9/10).** The only verified instance in
   this literature of a structured `Z_4`-form family whose *signed* Gauss-sum
   distribution -- multiplicities of `+-2^j`, `+-i2^j`, `+-omega 2^j`,
   `+-omega^3 2^j` -- is known in closed form. The engine is a closed-form rank
   distribution (alternating sums of 4-ary Gaussian binomials) for the
   Delsarte--Goethals sets, resting on "the difference of two distinct elements
   has rank at least `m - 2t`".
   *Transfers as the template for `(S)`: it is the existence proof that signed
   information follows from rank control.*
   **Breaks:** it needs *uniformly high* rank, which the lane's own uncollapsed
   pairwise rank test REFUTES for the Lemire fibres (all even ranks `0..10`,
   rank 0 included); and the family parameter `t` enters the answer as a
   rank/degree factor (max correlation `1 + 2^(m/2+t)`).
7. **Exact moment computation on a Galois-ring family (Feng--Ge--Hu,
   arXiv:1212.0347).** The only published instance I found of an *exact* second
   AND fourth moment for a real family of `{0} union {+-2^j}` Gauss-sum-like
   quantities, with the normalized fourth moment `(3q-1)/q -> 3`, the Gaussian
   constant. *Transfers as a template for `(E2')`/`M_4`*: the mechanism is the
   association-scheme character table, i.e. again a rank/orbit count.
   **Breaks for `(S)`:** their `sum S = 0` is forced by the symmetry
   `S(u+2,a,b) = -S(u,a,b)`, not by arithmetic cancellation, so the family
   exhibits an exact symmetry rather than square-root cancellation; and the
   objects are `zeta_4`-valued over the multiplicative Teichmuller set, not
   `zeta_8`-valued on affine subspaces.

### (d) `L2` candidate statements, in the charter's notation

All are stated so that a single bounded run of the lane's existing fibre report
can falsify them. `n_F = dim F`, `r_F = rank(b_F)` the associated `F_2`-bilinear
form of the fibre phase, `q_F` its `F_2`-quadratic function, "tame" = the radical
carries no nontrivial linear character.

- **`(GR-1)` [PROVED, L1 -- the base case].** For a full linear-twist orbit
  `{Q_x = Q_0 + jB(.,x) : x in V}` of a nonsingular Brown form on `V = F_2^n`,
  `sum_x G(Q_x) = 2^n` and `sum_x |G(Q_x)|^2 = 2^(2n)`, so `(S)` holds with
  `C = 1` **as an identity**. Corollary, **REFUTED as a route**: a disjoint union
  of `M` complete orbits gives `Delta/l2 -> sqrt(M)` with all orbits contributing
  the *same* sign, so `(S)` cannot be obtained by completing orbits.

- **`(GR-2)` [L2 -- the structural hypothesis; falsify first].** Every fibre with
  `c_F != 0` and `|c_F|` a power of two lies in the **alternating** stratum:
  `c_F = (-1)^(Arf(q_F^red)) 2^(n_F - r_F/2)` exactly, with `r_F` the rank of the
  second-trace-difference form. Equivalently: the fibre phase is
  `2 x (a Brown Z/4 form)` -- linear `Z/8`-ANF coefficients even, quadratic ones
  in `4Z/8`, none above degree 2. Prediction from Schmidt Result 4 vs Theorem 5:
  **no fibre correlation is ever a nonreal multiple of a power of two** (no
  `omega`, no `i`), and the `459` non-power-of-two fibres are exactly the fibres
  violating that coefficient rule. *One pass over the existing report.*

- **`(GR-3)` [L2 -- the counting half, restated with no signs].** Given `(GR-2)`,
  ```text
  (E2')  <==>  sum_(F tame) 2^(n_F) ( 2^(n_F - r_F) - 1 )  <=  sum_(F not tame) 2^(n_F)
  ```
  i.e. **the rank-defect mass of the tame fibres is dominated by the point mass of
  the fibres whose Gauss sum vanishes.** Note the exact coincidence that makes
  this the right normalisation: a *nonsingular* fibre (`r_F = n_F`) contributes
  `c_F^2 = 2^(n_F)`, exactly its own point count, so its within-fibre off-diagonal
  correlation is exactly zero. At the pinned witness the two sides differ by
  `130,048 - 120,680 = 9,368` points, i.e. `7.2%`, while `31.6%` of fibres are
  degenerate -- so both terms are genuinely active and `(E2')` is a real
  inequality, consistent with sweep-08's finding that no closed form exists.
  **This converts sweep-08's highest-value open experiment (extend the `(E2')`
  ratio to `ell = 10,11,12`) into a statement about the rank distribution alone,
  which the lane already computes.**

- **`(GR-4)` [L2 -- the sign half, fully reduced].** Given `(GR-2)`,
  ```text
  (S)  <==>  | sum_F (-1)^(Arf(q_F^red)) 2^(n_F - r_F/2) |
                   <=  C ( sum_(F tame) 2^(2 n_F - r_F) )^(1/2),   C absolute.
  ```
  **Square-root cancellation of the Arf invariant over the fibre index, weighted
  by `2^(n_F - r_F/2)`.** No discriminants, no `Z/8`, no polynomial arithmetic
  remain. This is strictly smaller than sweep-08's Problem T (the Gauss sums have
  been evaluated away) and is the sharpest form of `(S)` I can state.

- **`(GR-5)` [L2 -- the reframing, and the one place a new mechanism could enter].**
  Write the fibre family as `P  contained in  union_m O_m` with `S_m  contained in  V_m` the twist
  parameters actually realised in the `m`-th complete orbit. Then
  ```text
  Delta = sum_m (-1)^(Arf_m) 2^(n_m - r_m/2) T_m,     T_m = sum_(x in S_m) (-1)^(q_m(x)),
  ```
  and `(S)` requires square-root cancellation **inside** each `T_m` (an
  *incomplete* quadratic character sum) **and across** `m`. Two consequences:
  (i) this is sweep-08's self-similarity obstruction split into two named halves,
  and (ii) sweep-02's dismissal of Burgess-type amplification ("our sum is
  complete over its fibres") **stops applying at this level** -- the `T_m` are
  incomplete by construction. Whether `|S_m|/|V_m|` is large enough for a
  Burgess-type gain is an unmeasured, cheap question.

- **`(GR-7)` [PROVED, L1 -- an exact fourth moment].** For a complete linear-twist
  family of an alternating Brown `Z_4`-form of rank `r` on `V = F_2^m`,
  `sum_u chi^4 = 2^(4m-r) = 2^(-r) (sum_u chi^2)^2` exactly. So on any family
  built from complete twist orbits the connected fourth cumulant is a **rank
  count**, not an inequality. Target for the lane: exhibit `M_4` as a sum over
  `(dim, rank)` strata of complete orbits, and `M_4` becomes exact. (This is the
  concrete form of charge item 4's "could a `Z/2^k` MacWilliams identity
  re-express `M_4` exactly" -- the answer is yes on that model family, and the
  mechanism is the rank stratification, not MacWilliams.)

- **`(GR-6)` [L2 -- a falsifiable prediction about a experiment the lane has
  already queued].** sweep-08 (d5) proposes testing the sign family for
  multiplicativity in the normalized parameter `h_0/w_0`. The Arf-shift formula
  predicts the answer: `sign(c_F)` is a **quadratic**, not linear, function of the
  twist parameter, so it is *not* a character, and the test will return "quadratic
  structure, not multiplicative". If it returns *linear*, that is a genuine
  surprise and would be the single most valuable datum in the split, because it
  would make the lane's Witt aggregation a second-level character sum and Weil
  would apply once more -- which is the mechanism sweep-08 named as the only
  concrete route to `(S)`.

### (e) Ranked references

Ranked by what they can actually do for `(E2')`/`(S)`, not by fame. Every URL was
opened; where I could reach only an abstract or nothing, it is marked.

1. **L. R. Taylor, "Gauss Sums in Algebra and Topology."**
   <https://webhomes.maths.ed.ac.uk/~v1ranick/papers/taylorg.pdf>;
   arXiv version <https://arxiv.org/abs/2208.06319>. **Read in full.**
   Cor. 1.11 (modulus, singular case allowed), Prop. 1.13 (twist transfer),
   (1.18) (`G = p^(e/2) omega^sigma`), Thm 1.17 (`beta(a.psi)`).
   *The correct citation for the lane's powers-of-two-and-zeros measurement.*
2. **K.-U. Schmidt, "`Z_4`-valued quadratic forms and quaternary sequence
   families", IEEE Trans. IT 55(12) (2009) 5803--5810.**
   <https://math.uni-paderborn.de/fileadmin-eim/mathematik/AG-Diskrete_Mathematik/Publications-schmidt/Z4seq.pdf>.
   **Read.** Cor. 3 (normal forms), Result 4 and Thm 5 (complete value
   distributions by rank and alternating/nonalternating).
   *The exact-moment machinery for `(E2')`, and the identification of our family
   as the alternating stratum.*
3. **J. A. Wood, "Witt's extension theorem for mod four valued quadratic forms",
   Trans. AMS 336 (1993) 445--461.**
   <https://webhomes.maths.ed.ac.uk/~v1ranick/papers/woodj.pdf>. **Read.**
   Brown's Thm 1.20 restated with properties (7), (10), (11); the classification
   by `sigma` + alternating.
   *Property (10) is the twist-transfer identity that reduces `(S)` to `(GR-5)`.*
4. **F. Labib, "Stabilizer rank and higher-order Fourier analysis",
   Quantum 6 (2022) 645; arXiv:2107.10551.**
   <https://arxiv.org/pdf/2107.10551v2>. **Read.** Thm 3.2 (stabilizer states =
   quadratic phases on affine subspaces), the `(1/8)Z -> (1/4)Z` collapse,
   Prop. 3.7 + depth bound, Prop. 4.2 (derivative descent, `(3/4)^n`),
   Thm 1.1 (`Omega(n)` stabilizer rank of `|T>^(x)n`).
   *Both the barrier and the only positive mechanism.*
5. **M. Kosters and D. Wan, "Genus growth in `Z_p`-towers of function fields",
   Proc. AMS 146 (2018) 1481--1494; arXiv:1703.05420.**
   <https://arxiv.org/abs/1703.05420>, full text
   <https://www.math.uci.edu/~dwan/genus.pdf>. **Read Sections 2--3.**
   Thm 3.2 (ghost-free Schmid--Witt residue formula, with the fully explicit
   coefficient expansion), Prop. 3.3 (conductor), and the statement that the
   symbol is `Z_p`-**bilinear**.
   *The source of `(*)` in [t4].*
6. **A. R. Hammons, P. V. Kumar, A. R. Calderbank, N. J. A. Sloane, P. Sole,
   "The `Z_4`-linearity of Kerdock, Preparata, Goethals and related codes",
   IEEE Trans. IT 40 (1994) 301--319; arXiv:math/0207208.**
   <https://arxiv.org/abs/math/0207208>. **Abstract read verbatim**; the
   MacWilliams/Lee-enumerator material is in the body, which I did not open.
   *Origin of the program; the reason the sign is an Arf-type invariant.*
7. **T. Tao and T. Ziegler, arXiv:1101.1469** (Lemma 1.7(iii),(vi): canonical
   form and the degree--depth bound) and **A. Berger, A. Sah, M. Sawhney,
   J. Tidor, arXiv:2107.07495**, Math. Proc. Camb. Phil. Soc. 173 (2022) 525--537
   (Lemma 2.4, same support condition; Thm 1.2 at `p=2,k=4` exhibits
   `e(sum_i |x_i|/8)` as the canonical `Z/8` witness).
   <https://arxiv.org/abs/1101.1469>, <https://arxiv.org/abs/2107.07495>.
   *The degree--depth theorem, cross-checked in two independent sources; this is
   what makes finding (b) a theorem rather than an impression.*
8. **V. Turaev, "Reciprocity for Gauss sums on finite abelian groups",
   Math. Proc. Camb. Phil. Soc. 124 (1998) 205--214.**
   <https://webhomes.maths.ed.ac.uk/~v1ranick/papers/turaev3.pdf>. **Read.**
   Formula (2) (van der Blij: phase = signature mod 8 corrected by a rational Wu
   class), Remark 1 (the `Z/4` collapse on an `F_2`-space, stated
   group-theoretically -- a third independent confirmation of finding (b)).

9. **T. Feng, G. Ge, S. Hu, "Association schemes related to Delsarte--Goethals
   codes", arXiv:1212.0347.** <https://arxiv.org/pdf/1212.0347v1>. **Read.**
   Value set `{+-2q, +-2sqrt(2q), +-sqrt(2q), 0}` and the exact moments
   `sum S^2 = 8q^4`, `sum S^4 = 16q^4(3q-1)` (`m` odd).
   *The closest published precedent for an exact `(E2')`/`M_4` on a `+-2^j`
   family, with the constant `3`.*
10. **J. A. Wood, "Homogeneous weight enumerators over integer residue rings and
   failures of the MacWilliams identities", Rev. Un. Mat. Argentina 64(2) (2023)
   333--353**, DOI 10.33044/revuma.2807.
   <https://revistas.uns.edu.ar/revuma/article/download/3982/2188>.
   **Fetched and extracted by me directly** (the parallel sweep's two passes
   disagreed on provenance, so I re-verified this one at source). MacWilliams for the homogeneous weight enumerator **fails** over
   `Z/mZ` for composite `m >= 6`; explicit `Z/8` counterexample (Example 3.5);
   extends to finite commutative chain rings, hence `GR(8,m)`.
   *The stopping result for any "collapse `Z/8` to a scalar weight and dualise"
   argument.*
11. **N. Kaplan, "MacWilliams identities for `m`-tuple weight enumerators",
   arXiv:1205.1277v3.** <https://arxiv.org/pdf/1205.1277v3>. **Read.** Theorem 4:
   genus-`m` MacWilliams over a Galois ring `Z_(p^e)[xi]`, constant
   `prod|C_i|^(-1)`, no rank/degree factor. *At `m = 4` this is a fourth-moment
   identity -- but a transform, not an evaluation.*
12. **R. Blache, "Lifts of points on curves and exponential sums",
   arXiv:math/0202206.** <https://arxiv.org/pdf/math/0202206>. **Read.** Quotes
   the KHC bound verbatim and states the method is *derived from* Weil via
   Artin--Schreier--Witt theory plus a conductor computation.
   *The citation for the clean negative in charge item 4.*
13. **K.-U. Schmidt, "Quadratic and symmetric bilinear forms over finite fields
   and their association schemes", arXiv:1803.04274.**
   <https://arxiv.org/pdf/1803.04274v1>. **Read.** Explicit `P`/`Q`-numbers for
   the quadratic-forms scheme in even characteristic; two orbits per nonzero even
   rank (the Arf split); neither `P`- nor `Q`-polynomial.
   *Feeds `(E2')` by the same rank mechanism as `(GR-3)`; has no fourth-order
   object, so it cannot feed `(S)`.*

**Priced at zero, with the reason (so nobody re-opens them):**
Kumar--Helleseth--Calderbank 1995 (<https://ieeexplore.ieee.org/document/370147/>)
and Ling--Ozbudak 2006 (<https://link.springer.com/chapter/10.1007/11779360_32>)
-- the Galois-ring Weil bound carries the degree factor to be beaten, is tight
for Kerdock/DG, and its improved form re-expresses the loss through the genus,
which sweep-07 already identified as the blocker's log factor.

**Reached but not verified (do not cite from this diary):**
Li--Zhu--Feng, Sci. China Math. 56 (2013) 1457--1465 (paywalled redirect);
"The Gauss sums over Galois rings and its absolute values", Korean J. Math.
(abstract only); "An invariant for quadratic forms valued in Galois Rings of
characteristic 4", Finite Fields Appl. (HTTP 403); "Witt index for Galois Ring
valued quadratic forms", Finite Fields Appl. (PDF endpoint returned HTML);
Kumar--Helleseth--Calderbank 1995 and Ling--Ozbudak 2004/2006 direct (IEEE /
Springer walls -- the KHC bound is nonetheless verified *verbatim as quoted by*
Blache, ref. 12); Wood, Amer. J. Math. 121 (1999) 555--575 (Project MUSE CAPTCHA;
abstract verified through OpenAlex); Bannai--Dougherty--Harada--Oura Theorem 5.1
(bitmap fonts, formula did not extract); Gluesing-Luerssen arXiv:1304.6589
Thm 4.4 as a reprieve for the 3-block homogeneous partition (a reconciliation
stated in neither source).

### Coverage statement (per the repository's own gotcha about empty results)

Two of the findings above are negatives, and I state their coverage rather than
their strength. (i) "No `Z/2^k`-valued (`k >= 3`) analogue of Schmidt's rank
classification" rests on arXiv + OpenAlex searches by a parallel reviewer, and is
*independently corroborated* by [t3], which proves there is nothing to classify --
that corroboration is what makes it safe. (ii) "No harmonic analysis on the Witt
filtration" rests on four arXiv-API queries of mine and is **not** corroborated by
a theorem; treat it as "four obvious phrasings returned nothing", not as
nonexistence.
