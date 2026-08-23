# The large-`q` threshold claim: what Bagshaw proves, and what it gives Kaser--Lemire

Status: verification note, 2026-08-23. Lane `lemire-signed-trace`. This note
audits one claim made in note 15 (the arXiv sweep) sections 2.2 and 3, namely
that Bagshaw arXiv:2401.10399 reframes the residual Kaser--Lemire problem from
"large `n`" to "small `q`". Primary source: the LaTeX source of
arXiv:2401.10399v1 (published as Can. J. Math. 78 (2026) 302--327), plus the
LaTeX source of Sawin--Shusterman arXiv:1808.04001 (Ann. Math. 196 (2022)
457--506) for the lemma Bagshaw's deduction rests on, and Keating--Rudnick
arXiv:1204.0708 (IMRN 2014) for the reversal duality.

## 0. Verdict, up front

The claim is **half right, and the half that is wrong is the half that was
quoted**.

- **Right.** Bagshaw's level-of-distribution theorem is an **individual-modulus**
  statement for an **arbitrary** (in particular non-squarefree, in particular
  `T^r`) modulus. It is not a Bombieri--Vinogradov average. The averaged
  statement is a *separate*, *stronger-exponent* theorem in the same paper, and
  the deduction does not use it. So the worry that "an averaged level of
  distribution says nothing about our single specific modulus `x^h`" does not
  apply.
- **Right.** The reversal duality does convert Kaser--Lemire into exactly this
  progression, the `q`-threshold that comes out is genuinely `n`-independent,
  and the constant `7101 p^2` re-derives correctly (`961 e^2 = 7100.8829...`).
- **WRONG, and fatally so for the quoted conclusion.** arXiv:2401.10399 fixes
  **`q = p^l` an ODD prime power** in its standing notation (Intro sec. 1.2,
  first line), and the one lemma the deduction cannot do without --
  Sawin--Shusterman's Mobius-in-progressions bound -- lives in a section that
  opens "*From now on, we will assume that the characteristic `p` of `F_q` is
  odd. Because of this, `F_q^x` admits a unique quadratic character*". The
  hypothesis is mechanism, not decoration: the whole Mobius cancellation runs
  through Jacobi symbols and the quadratic character of a resultant. **So there
  is no `p = 2` case, and note 15's "at `p = 2`, every `q >= 2^15 = 32768`" is
  a statement about a theorem that does not exist.**
- **WRONG in a second, independent way.** Even for odd `p`, the threshold
  `q > 7100.88 p^2` is a condition on `q/p^2`, i.e. on `p^{l-2}`. It is
  therefore satisfiable **only when `l >= 3`**. No prime field `F_p` clears it
  at any size, and no `q = p^2` clears it either. The admissible set is the
  sparse set `{p^l : p odd, p^{l-2} > 7100.88}` -- `O(X^{1/3})` values below
  `X`, against `~X/log X` primes -- so it is not remotely cofinite. "The open
  set has collapsed to `q < 2^15`" is false; the open set still contains **every
  prime `q`, however large**, every `q = p^2`, and every `q = 2^k`.

Bottom line: Bagshaw does give a real, new, `n`-independent theorem for a
sparse infinite set of `q`. It does **not** reframe the residual problem as
"small `q`". The correct reframing is narrower and less quotable: *the residual
problem is characteristic 2, prime fields, and low-degree extensions.*

## 1. The theorems, verbatim, with every hypothesis

Numbering is `\numberwithin{thm}{section}` with Introduction = sec. 1,
Results = sec. 2, so the source labels map to printed numbers as
`thm:bilinear_savings` = Thm 2.1, `thm:mobius_r/2` = Thm 2.2,
`thm:mobius_3/4` = Thm 2.3, `thm:irving` = Thm 2.4, `cor:vonmangoldt` =
Cor. 2.5, `thm:bombierivinogradov` = Thm 2.6. Journal numbering may differ; the
source labels are unambiguous and are given throughout.

### 1.0 The standing hypothesis (Intro, sec. "General notation")

> We fix an **odd** prime power `q = p^l` and let `F_q` denote the finite field
> of order `q`.

This is the paper's global convention, stated before any theorem. Every result
below inherits it.

### 1.1 The individual-modulus level of distribution -- `cor:vonmangoldt` (Cor. 2.5)

Verbatim (transcribed from `Files/Results.tex`, math in backticks):

> **Theorem.** Fix `omega < 1/2 + 1/62`, and suppose
> `q > p^2 e^2 ((16 - omega)/(16 - 31 omega))^2`.
> Then for any coprime `a, F` in `F_q[T]` with `deg F = r`, and any positive
> integer `n` satisfying `r <= omega n` we have
> `sum_{x in M_n, x = a mod F} Lambda(x) - q^n/phi(F) <<_omega q^{n - r(1+delta)}`
> for some `delta = delta(omega) > 0`.

(The source writes the summation condition as `f = a mod F` while the summation
variable is `x`; an obvious typo.)

Hypotheses, itemised:

| hypothesis | value here |
| --- | --- |
| modulus `F` | **arbitrary**; explicitly *not* restricted to squarefree or prime |
| `gcd(a, F)` | `= 1` |
| individual or averaged | **individual** -- a single `F`, no sum over moduli |
| `q` | odd prime power with `q > p^2 e^2 ((16-omega)/(16-31 omega))^2` |
| `n` | any positive integer with `r <= omega n` |
| uniformity | implied constant depends on `omega` only; **not effective** |
| `omega` range | `omega < 1/2 + 1/62 = 16/31`; no stated lower bound |

The sentence immediately following it in the paper: *"While the holds for
arbitrary modulus `F`, we do note that for square-free modulus Sawin's result
[Sawin2023, Theorem 1.2] always gives a more relaxed condition on `q`."*

### 1.2 The AVERAGED statement -- `thm:bombierivinogradov` (Thm 2.6)

> **Theorem.** Fix `omega < 1/2 + 1/38`, and suppose
> `q > p^2 e^2 ((10 - omega)/(10 - 19 omega))^2`. Then for any positive integers
> `R` and `n` satisfying `R <= omega n` we have
> `sum_{deg F < R} max_{(a,F)=1} | sum_{x in M_n, x = a mod F} Lambda(x) - q^n/phi(F) | <<_omega q^{n - R delta}`
> for some `delta = delta(omega) > 0`.

This is the Bombieri--Vinogradov analogue. It has the better exponent
(`1/2 + 1/38` vs `1/2 + 1/62`) and the better `q`-constant, and it is **useless
for us**: a bound on a sum over all `F` of degree `< R` gives nothing for the
single modulus `T^r`, whose individual contribution could be as large as the
whole bound. **The deduction below uses Cor. 2.5 and never Thm 2.6.** This is
the distinction the audit was asked to settle, and it settles in the deduction's
favour.

### 1.3 The `q`-free ingredients -- `thm:bilinear_savings`, `thm:mobius_r/2`, `thm:mobius_3/4`

> **Theorem** (`thm:bilinear_savings`, Thm 2.1). Let `eps > 0`, and let `a, F`
> in `F_q[T]` be coprime with `deg F = r`. Then for any positive integers `n`
> and `m` satisfying `n >= r eps` and `m >= r(1/4 + eps)` and weights as in
> (2.1), we have `W_{F,a}(m,n;alpha,beta) <<_eps q^{m + n - r delta}` for some
> `delta = delta(eps) > 0`.

> **Theorem** (`thm:mobius_r/2`, Thm 2.2). Let `eps > 0` and `a, F` in `F_q[T]`
> with `deg F = r`. For any positive integer `n` satisfying `n > r(1/2 + eps)`,
> `sum_{deg x < n, (x,F)=1} mu(x) e_F(a/x) <<_eps q^{n(1-delta)}` for some
> `delta = delta(eps) > 0`.

> **Theorem** (`thm:mobius_3/4`, Thm 2.3). Let `a, F` in `F_q[T]` with
> `deg F = r` and let `n` denote a positive integer. Then for any `eps > 0`,
> `sum_{deg x < n, (x,F)=1} mu(x) e_F(a/x) <<_eps q^{15n/16 + eps n} + q^{2n/3 + r/4 + eps n}`.

These three carry **no explicit `q`-hypothesis beyond the global odd-`q`
convention**. Note 15 sec. 2.2 is right that this is where the paper's novelty
lies. They are bounds on *additive* characters `e_F(a/x)` of the modular
inverse, not on the ray-class (multiplicative) characters our lane needs; note
15's Postnikov remark on why that gap does not close at `p = 2` stands and is
untouched by this audit.

### 1.4 The `q`-hypothesis's actual source -- Sawin--Shusterman Thm 4.5

Bagshaw's Cor. 2.5 is proved (`Files/ProofVonMangoldt.tex`) by substituting his
Thm 2.3 for [SS, Thm 1.8] in the proof of [SS, Thm 1.9]. Every occurrence of `p`
and of the `q`-threshold in that proof enters through one lemma, quoted by
Bagshaw as `lem:sawinshusterman_mobius_dist`:

> **Lemma** (special case of [Sawin--Shusterman, Thm 4.5]). Let `eps > 0` and
> `0 < beta < 1/2`, and suppose `q > (((eps+2)/eps) p e)^{2/(1-2beta)}`. Then
> for any non-negative integer `n >= (1+eps) r` and any `a` in `F_q[T]` coprime
> to `F` we have
> `sum_{x in M_n, x = a mod F} mu(x) <<_{eps,beta} q^{(n-r)(1 - beta/p)}`.

In arXiv:1808.04001 this is `LinearFormsMobThm` with `n = 1`:

> **Theorem** (SS, `LinearFormsMobThm`). Fix `eps, delta > 0`, `0 < beta < 1/2`,
> and a positive integer `n`. Let `q` be a power of an **odd** prime `p` such
> that `q > (p n e / min{eps/(eps+2), eps delta/(eps+delta)})^{2/(1-2beta)}`. ...
> then `sum_{g in M_d} prod_{i=1}^n mu(a_i + g M_i) << |M_d|^{1 - beta/p}`.

and it sits in SS's section "The Mobius Function", which opens:

> **From now on, we will assume that the characteristic `p` of `F_q` is odd.
> Because of this, `F_q^x` admits a unique quadratic character, which we denote
> `psi`. We use freely the basic properties of resultants and the Jacobi symbol.**

**Verdict on the oddness hypothesis: it is mechanism, not bookkeeping.** SS's
Mobius cancellation is a quadratic-reciprocity argument -- `mu` is detected
through the Jacobi symbol via `(f/g) = psi(a_n)^{max(d(f),0)} psi(Res(g,f))`
(their `JacobiLem`), and a unique quadratic character of `F_q^x` exists exactly
when `q` is odd. There is no `p = 2` version of this lemma in either paper, and
none of the three `q`-free Bagshaw theorems can replace it (they bound additive
character sums, not `mu` in a progression).

Consequence: **arXiv:2401.10399 Cor. 2.5 is vacuous at `p = 2`.** Every number
note 15 quotes for `p = 2` (`q > 28404`, `q >= 2^15`) is the value the formula
*would* produce if the hypothesis could be dropped. It cannot, and the note
presented the arithmetic as a theorem.

## 2. The reversal duality, with the exact index -- verified

The duality is Keating--Rudnick's involution (arXiv:1204.0708 sec. 5.1--5.2;
"Lemma 4.2" in the IMRN pagination the lane's diary cites). Verbatim from the
arXiv source:

> For `0 != f` in `F_q[T]` we define `f^*(T) := T^{deg f} f(1/T)` ... Note that
> `f^*(0) != 0` and `f(0) != 0` if and only if `deg f^* = deg f`. Moreover
> restricted to polynomials which do not vanish at `0` ... `*` is an involution
> ... **Lemma.** For `f` in `P_n` with `f(0) != 0`, we have
> `Lambda(f^*) = Lambda(f)`.

and the fundamental relation

> **Lemma.** For `B` in `P_{n-h-1}`, `nu(T^{h+1} B; h) = Psi~(n; T^{n-h}, B^*)`.
> *Proof.* ... `f = T^{h+1}B + g` in `I(T^{h+1}B; h)`, `g` in `P_{<=h}`, if and
> only if `f^* = B^* + T^{n-h} g^*`, and thus `f in I(T^{h+1}B; h)` iff
> `f^* = B^* mod T^{n-h}`.

**Instantiation for Kaser--Lemire.** The window is `deg(f - T^n) <= floor(n/2)`,
i.e. `h = floor(n/2)` and `T^{h+1} B = T^n`, so `B = T^{n-h-1}` and `B^* = 1`.
The modulus exponent is

```text
n - h = n - floor(n/2) = ceil(n/2) =: r.
```

So, writing `ell = ceil(n/2) - 1` for the lane's own conductor index
(note 01: `<F>_ell` is reduction mod `x^{ell+1}`), we have `r = ell + 1`, and:

```text
{ f monic irreducible, deg f = n, deg(f - T^n) <= floor(n/2), f(0) = 1 }
    <--- P |-> P^* --->
{ P monic irreducible, deg P = n, P = 1 mod T^{ceil(n/2)} }
```

and more generally the full window is the union over units,
`|W| = sum_{c in F_q^x} |{P irred monic, deg n, P = c mod T^r}|` (a monic `f`
in the window has `f(0) = a_0 != 0`, and `f^*` has leading coefficient `a_0`, so
the monic representative is `a_0^{-1} f^*`, which is `= a_0^{-1} mod T^r`).
Over `F_2` the two coincide because `a_0 = 1` is forced.

**The brief's index is off by one at even `n`.** The task brief states
"Kaser--Lemire needs `m = floor(n/2)+1`". That agrees with `ceil(n/2)` at odd
`n` but is one too large at even `n` (`n = 4`: `floor+1 = 3`, `ceil = 2`).
Note 15 sec. 2.2 has it right (`ceil(n/2)`). The difference is not cosmetic:

- it changes the level of distribution needed from `r/n = 1/2` **exactly** (even
  `n`, `r = n/2`) to `r/n = 1/2 + 1/n`, hence changes whether `omega = 1/2` is
  admissible at all;
- it can change the answer. Measured (`data/largeq-reversal-duality.txt`): over
  `F_3` at `n = 4` there are **6** in-window irreducibles and **2** with
  `f(0) = 1`, matching `|A_1| = 2` at `r = 2`; at the brief's `r_alt = 3` the
  progression is **empty**. An argument run at `r_alt` would have concluded
  "no in-window irreducible of degree 4 over `F_3`", which is false.

**Numerical verification** (`scripts/lemire-signed-trace/lemire_largeq.py`,
check 1): the bijection is confirmed on **89 `(q,n)` pairs and 24,090
polynomials**, `q` in `{2,3,4,5,7,8,9}`, `n` up to 24 (`q = 2`). Irreducibility,
monicity and degree are all re-checked on the image, and the union identity
`|W| = sum_c |A_c|` is checked separately. Two positive controls: the
`r_alt = floor(n/2)+1` count differs somewhere (so the index check is not
vacuous), and reversal provably drops the degree when `P(0) = 0` (so the
`P(0) != 0` hypothesis is load-bearing). A mutation of `r` to `floor(n/2)+1` in
the checker kills exactly checks C1.1--C1.3 and nothing else.

## 3. The deduction, step by step

Take `F = T^r`, `r = ceil(n/2)`, `a = 1`. Then:

1. `gcd(1, T^r) = 1`. **OK.**
2. `F` is arbitrary in Cor. 2.5's sense -- and `T^r` is the maximally
   non-squarefree modulus, which is exactly why Sawin--Shusterman (Ann. Math.
   2022 Thm 1.9) and Sawin (Acta, Thm 1.2) do **not** apply and Bagshaw does.
   **OK, and this is the substance of the claim.**
3. `r <= omega n`: `ceil(n/2) <= omega n`. Even `n`: holds for `omega = 1/2`
   with equality. Odd `n`: needs `omega >= 1/2 + 1/(2n)`. **OK for
   `n >= 1/(2(omega - 1/2))`.**
4. Main term: `q^n / phi(T^r) = q^{n-r} * q/(q-1) = q^{n-r+1}/(q-1)`.
   Error: `<<_omega q^{n - r(1+delta)} = q^{n-r} * q^{-r delta}`. Ratio
   `-> 0`. **OK.**
5. **The step nobody wrote down:** `Lambda` counts prime *powers*, and at the
   endpoint `r = n/2` the main term is `q^{n/2+1}/(q-1)` while the number of
   proper prime powers of degree `n` is already `~ q^{n/2}`. So the
   `Lambda`-sum being positive does *not* on its face give an *irreducible*.
   It does, for a structural reason: if `x = P^k` with `deg x = n` and
   `x = 1 mod T^r`, write `k = p^A k'` with `gcd(k',p) = 1`; since
   `(F_q[T]/T^r)^x = F_q^x x (1 + T F_q[T]/T^r)` and the second factor is a
   `p`-group, `z^{p^A} = 1 mod T^r` iff `z = 1 mod T^{ceil(r/p^A)}` and
   `y^{k'} = 1` forces `y = zeta` there. Counting monic `y` of degree `n/k`
   in that class gives `q^{max(0, n/k - ceil(r/p^A))}`, maximised at `k' = 1`,
   `k = p^A`, i.e. `<= q^{n/(2p)}` up to `O(1)`. Weighted by
   `Lambda(P^k) = n/k <= n/2` this is `O(n q^{n/(2p)}) = o(q^{n-r})`.
   **OK -- but note the saving is only by a factor `1/p` in the exponent, so
   at `p = 2` it would be `q^{n/4}` against `q^{n/2}`: comfortable, but not
   free.** Verified numerically (check 3): the structural bound
   `#{proper prime powers in the class} <= 4 q^{n/(2p)}` holds on every row of
   `data/largeq-prime-powers.txt`, and the `Lambda`-weighted share of the main
   term is `<= 0.141` for `n >= 12`. Positive control: without the congruence
   the proper-power count exceeds the whole class size, so the check is a fact
   about the congruence and not about the sizes chosen.
6. Therefore `#{P monic irreducible, deg n, P = 1 mod T^r} > 0` for all `n`
   large enough in terms of `omega` and `q`; reverse it (sec. 2) to get the
   Kaser--Lemire polynomial. **OK.**

Nothing in steps 1--6 fails. The deduction is sound *given Cor. 2.5*, and
Cor. 2.5 requires `p` odd.

## 4. The threshold, re-derived from scratch

Bagshaw's proof (`Files/ProofVonMangoldt.tex`) parametrises by
`omega' := (2 omega - 1)/omega` (from `d = n - r >= r(1-omega)/omega =
r(1 - omega')`) and lands on

```text
q > p^2 e^2 (1 + 30/(1 - 16 omega'))^2.
```

Substituting `16 omega' = (32 omega - 16)/omega` gives
`1 - 16 omega' = (16 - 31 omega)/omega`, hence
`1 + 30/(1 - 16 omega') = (16 - 31 omega + 30 omega)/(16 - 31 omega) =
(16 - omega)/(16 - 31 omega)`, which is Cor. 2.5's stated form. **Re-derivation
confirms the paper's algebra.**

Write `g(omega) := e^2 ((16 - omega)/(16 - 31 omega))^2`, so the hypothesis is
`q > g(omega) p^2`. Then:

- `g` is strictly increasing on `[1/2, 16/31)` (checked, C2.3), so the cheapest
  admissible `omega` is the smallest the window allows;
- the window forces `omega >= 1/2`, with equality attainable at even `n`;
- `g(1/2) = e^2 * (15.5/0.5)^2 = 961 e^2 = **7100.882911...**`;
- `g(omega) -> infinity` as `omega -> 16/31` (C2.2: `1.8e18` at `16/31 - 1e-9`).

**The constant `7101 p^2` in note 15 is therefore correct as a rounding of
`961 e^2 = 7100.8829`.** I re-derived it rather than accepting it, and it holds.

To cover **all** large `n` (both parities) take `omega = 1/2 + eta` for small
`eta > 0`; by continuity the open condition is still `q > 961 e^2 p^2`, at the
price of `n >= 1/(2 eta)`. So:

> **Theorem (conditional only on arXiv:2401.10399 Cor. 2.5 as stated).**
> Let `p` be an **odd** prime and `q = p^l` with `q > 961 e^2 p^2 =
> 7100.883 p^2`. Then there is `n_0 = n_0(q)` such that for every `n >= n_0`
> there is a monic irreducible `f` in `F_q[T]` of degree `n` with
> `deg(f - T^n) <= floor(n/2)`.

`n_0` is **not effective**: Bagshaw's implied constant `<<_omega` is not made
explicit, and SS's `<<_{eps,beta,n,q}` behind it is not either.

**The threshold is `n`-independent.** That much of note 15's claim survives, and
it is the interesting part: Hsu/Cohen's `q > (n+1)^2/4` is not.

## 5. Which `q` actually clear it

`q > 7100.883 p^2` with `q = p^l` is `p^{l-2} > 7100.883`. Hence:

- **`l = 1` is impossible.** No prime field `F_p` clears the threshold, at any
  size. (`q = p > 7100.9 p^2` has no solutions.)
- **`l = 2` is impossible** for the same reason.
- **`l >= 3` always**, and `l >= 3` suffices only once `p > 7100.883`, i.e.
  `p >= 7103`.

Computed (`data/largeq-threshold-table.txt`, check C2.4--C2.9):

| `p` | minimal `l` | minimal admissible `q` |
| --- | --- | --- |
| 2 | -- | **none: excluded by hypothesis** |
| 3 | 11 | `3^11 = 177147` |
| 5 | 8 | `5^8 = 390625` |
| 7 | 7 | `7^7 = 823543` |
| 11 | 6 | `11^6 = 1771561` |
| 13 | 6 | `13^6 = 4826809` |
| 23 | 5 | `23^5 = 6436343` |
| 83 | 5 | `83^5 = 3939040643` |
| 89 | 4 | `89^4 = 62742241` |
| 7103 | 3 | `7103^3 = 358364881727` |

Smallest admissible `q` overall: **`3^11 = 177147`**.

**External control on the enumeration rule.** Bagshaw's own closing remark
(`Files/comments.tex`) states that improving the Sawin--Shusterman twin-prime
constant `685090` to `181157` newly covers exactly
`3^14, 5^10, 13^7, 23^6, 59^5, 61^5, 67^5, 71^5, 73^5, 79^5, 83^5`. Applying
the rule "`p^l` admissible iff `p` odd and `p^{l-2} > C`" with `C = 181157` and
`C = 685090` and taking the difference reproduces **that exact eleven-element
list** (check C2.8). The rule is right; so is the table above.

**Sparsity.** `#{admissible q <= X}` is `O(X^{1/3})` (all admissible `q` are
`p^l` with `l >= 3`), against `~X/log X` primes below `X`, none of which
qualify. Measured: 165 admissible `q <= 10^12` with `p < 200` (C2.7). The
complement of the admissible set is not "small `q`"; it is almost all `q`.

## 6. Comparison for the specific question (top `ceil(n/2) - 1` coefficients)

The question is: **an irreducible of degree `n` over `F_q` whose top
`ell = ceil(n/2) - 1` coefficients (below the leading one) all vanish** --
equivalently a prime `= 1 mod T^{ceil(n/2)}`. "Full window" below means it
reaches `ell = ceil(n/2) - 1` exactly, not `(1/2 - eps) n`.

| result | what it gives | modulus / positions | `q` hypothesis | `n` hypothesis | reaches the full window? | applies to `q = 2`? |
| --- | --- | --- | --- | --- | --- | --- |
| Hayes 1965 / Weil, sharp form Hsu 1996 Thm 2.4 = Cohen 2005 Thm 2.1 | count `>= q^{n-l}/n - (l+1) q^{n/2}/n` for the top `l` coefficients | top positions, any `q` | none | none | **yes**, iff `l < n/2 - log_q(l+1)`, i.e. `q > n/2` (even `n`) / `q > (n+1)^2/4` (odd `n`) | yes, but only for `n < 2q`, so **`n <= 3` at `q = 2`** |
| Pollack FFA 22 (2013) Prop. 10 | any `s + t <= (1/2 - eps) n` LOW + HIGH coefficients | top and bottom, any `q` | **none** | `n >= n_0(eps)` | **no** -- `eps n` short, and `eps` cannot go to `0` at fixed `q` (see below) | yes, at `(1/2-eps)n` |
| Pollack FFA 22 (2013) main thm | `floor((1-eps) sqrt n)` coefficients in ARBITRARY positions | arbitrary positions | none | -- | no | yes |
| Ha FFA 40 (2016) | `(1/4 - eps) n` arbitrary positions | arbitrary positions | `q >= q_0(eps)` | -- | no | `n/10` only (their Thm 1.3, `n >= 52`) |
| Sawin--Shusterman Ann. Math. 2022 Thm 1.9 | level of distribution `omega < 1/2 + 1/126` | **squarefree `F` only** | `p` odd, `q > p^2 e^2 (...)^2` | `r <= omega n` | would, but | **inapplicable**: `T^r` is not squarefree |
| Sawin, Acta (Thm 1.2) | level of distribution `omega < 1` | **squarefree `F` only** | `q` large in `omega` | `r <= omega n` | would, but | **inapplicable**: same reason |
| **Bagshaw arXiv:2401.10399 Cor. 2.5** | level of distribution `omega < 1/2 + 1/62` | **arbitrary `F`, incl. `T^r`** | **`p` odd**, `q > 7100.883 p^2` | `n >= n_0(q)`, ineffective | **yes** | **no** -- `p` odd; and `p^{l-2} > 7101` excludes all prime fields |
| Bagshaw arXiv:2401.10399 Thm 2.6 | `omega < 1/2 + 1/38` | **averaged over `deg F < R`** | `p` odd, `q > p^2 e^2 (...)^2` | `R <= omega n` | n/a | **n/a**: says nothing about one modulus |

**Does Bagshaw beat Hsu/Cohen for this question?** For the `q` in its
admissible set, yes, and structurally: Hsu/Cohen's condition is `q > n/2` (even)
or `q > (n+1)^2/4` (odd), which *fails for every fixed `q` once `n` is large*;
Bagshaw's condition is on `q` alone. For `q = 3^11 = 177147`, Hsu/Cohen settles
even `n <= 354292` (`q > n/2`) and odd `n <= 839` (`2 sqrt q = 841.8`); Bagshaw
settles all `n >= n_0(q)`. Because `n_0` is ineffective, the two do **not**
combine into an unconditional "all `n`" statement even for admissible `q` --
there is a possible gap at odd `n` in `[841, n_0)`. Making `n_0` effective would close it, and that is a
concrete, bounded piece of work (track the constants through SS's Thm 4.5 and
Bagshaw's sec. 5).

**Can Pollack's `eps` be taken to `0` at fixed `q`?** No. Prop. 10 is Hayes's
explicit formula plus Weil, so the honest fixed-`q` ceiling from that route is
the *sharp* form, Hsu 1996 = Cohen 2005: positivity needs
`l < n/2 - log_q(l+1)`. The `eps n` in Prop. 10's statement is a convenient
weakening of a `log_q n` deficiency; the deficiency itself is real and does not
vanish. At `q = 2` it is `~ log_2 n`, which is exactly the lane's standing
diagnosis (note 00 Barrier III: Kaser--Lemire is `~log_2 n` past Weil). So an
`n`-independent `q`-threshold for the FULL window *is* a genuine improvement
over Pollack -- for the `q` that clear it.

## 7. Is "the residual problem is small `q`" a correct reframing?

**No.** Three reasons, in decreasing order of severity:

1. **`p = 2` is excluded by hypothesis and by mechanism.** Kaser--Lemire *is*
   the `q = 2` statement. The route says nothing about the conjecture. Note 15's
   own sentence "at `q = 2` it is still everything" is true; the sentence that
   precedes it, that the open set "has collapsed to `{q < ~2^15} x {all n}`",
   is not.
2. **Even at odd `p`, the admissible set is sparse, not cofinite.** `l >= 3` is
   forced, so all prime fields and all quadratic extensions are open at every
   size. "Small `q`" describes the complement of a set of density zero as if it
   were a finite set.
3. **`n_0(q)` is ineffective.** "For all sufficiently large `n`" with no bound
   is weaker than the lane's own certified handoff to `n = 3000`, in the sense
   that it cannot be combined with a finite computation to close a `q`.

**The correct reframing**, which is still worth recording because it is new:

> For a sparse infinite set of `q` -- `q = p^l`, `p` odd, `p^{l-2} > 7101`,
> smallest member `3^11` -- Kaser--Lemire holds for all sufficiently large `n`,
> with an `n`-independent hypothesis on `q`. This is the first `n`-independent
> `q`-criterion for the full half-degree window; every earlier one
> (Hayes/Weil, Hsu, Cohen, Pollack, Ha) has a threshold that grows with `n`.
> It does not touch characteristic 2, prime fields, or `q = p^2`, and its
> `n_0(q)` is ineffective.

The lane's `q = 2` problem is untouched, and the barriers of notes 06/07/09
apply verbatim.

## 8. Exactly what to change in note 15

Note 15 must be corrected in **four** places. (Per the lane's split, this note
does not edit note 15; the coordinator or the note-15 owner should apply these.)

1. **Sec. 3(iii) item 3.** Delete "at `p = 2`, `q >= 2^15`" and "The correct
   framing of the residual problem is therefore *small `q`*, not *large `n`*."
   Replace with the boxed reframing in sec. 7 above.
2. **Sec. 2.2, "What it gives this lane", last paragraph.** The sentence
   "Taking `omega = 1/2 + eps` ... at `p = 2` that is `q > 28404`, i.e.
   `q >= 2^15`" applies a theorem outside its hypotheses. Replace with: the
   threshold is `q > 961 e^2 p^2 = 7100.883 p^2` **for odd `p` only**; it forces
   `l >= 3`, so no prime field qualifies; smallest admissible `q` is `3^11`.
   Add the "where `q -> infinity` enters" paragraph's missing half: `p` odd
   enters through SS's `LinearFormsMobThm` (their Thm 4.5), whose proof needs
   the unique quadratic character of `F_q^x`.
3. **Headline answer 2 at the top of the note** ("The lane's residual problem is
   a small-`q` problem, not a large-`n` problem, and that is now a theorem").
   This is the load-bearing claim and it is wrong as stated. Rewrite to the
   sec. 7 form, and drop "and that is now a theorem" for `p = 2`.
4. **Sec. 3(i) item 2 and sec. 3(iv) "The reframing".** Same correction; in
   3(i) the parenthetical "*Positive, at large `q`*" should read "*Positive,
   at odd `p` and `l >= 3`*".

Note 15's sec. 2.2 statement of the reversal index (`r = ceil(n/2)`) is
**correct** and should not be changed; the task brief's `floor(n/2)+1` is the
one that is off by one.

Notes 00 and 09 have **not** been edited by this lane and, on the strength of
this audit, should **not** acquire the `n`-independent sentence proposed in
note 15 sec. 3(iii) item 3 in its current form. If they acquire anything, it is
the sec. 7 box, marked "odd `p`, `l >= 3`, ineffective `n_0`".

## 9. Reproducibility

- Checker: `scripts/lemire-signed-trace/lemire_largeq.py`
  (`/data0/axeyum/scratch/lemire-signed-trace-lemire-venv/bin/python`). Exits
  nonzero on failure; 17 checks, of which 5 are positive controls
  (C1.4, C1.5, C2.3, C2.8, C3.3).
  Runtime `~2 min`.
- Data: `scripts/lemire-signed-trace/data/largeq-reversal-duality.txt` (89
  `(q,n)` rows), `largeq-threshold-table.txt` (per-`p` minimal `l`),
  `largeq-prime-powers.txt` (37 rows).
- Mutation control performed out of tree (a copy under the session scratch
  dir, never the shared checkout): replacing `r = ceil(n/2)` by
  `floor(n/2)+1` kills exactly C1.1, C1.2, C1.3 and leaves the rest green.
- Primary sources read as LaTeX: arXiv:2401.10399 (`Files/Results.tex`,
  `Files/ProofVonMangoldt.tex`, `Files/CharSums.tex`, `Files/Intro.tex`,
  `Files/comments.tex`), arXiv:1808.04001 (secs. 1, 4), arXiv:1204.0708
  (sec. 5).
- Not verified from primary sources: Hsu 1996 Thm 2.4, Cohen 2005 Thm 2.1,
  Pollack FFA 22 (2013) Prop. 10, Ha FFA 40 (2016) -- all taken from the
  lane's own diary literature section (2026-08-22), which records Pollack and
  the Ha arXiv v1 as primary reads there. Sawin's Acta theorem is quoted only
  as Bagshaw quotes it.
