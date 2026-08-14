# Diary — creative telescoping (lane `telescoping`), 2026-08-14

Opening a domain: **certified proof of definite hypergeometric summation
identities**. Zeilberger's algorithm produces the certificate; a checker that
shares no code with it verifies the certificate; five classical identities land
as facts.

The fit is exact. "Untrusted fast search, trusted small checking" is the
project's identity, and a Zeilberger certificate is the purest instance of it in
mathematics: finding it is linear algebra over a guessed ansatz, and verifying it
is **one rational-function identity**, decidable by expanding polynomials.

---

## What was already here, and what was actually missing

`crates/axeyum-cas/src/gosper.rs` (1,469 lines) does *indefinite* hypergeometric
summation. `crates/axeyum-cas/src/lib.rs` also already carried a WZ layer —
`prove_wz_sum`, `certifies_wz_sum`, `prove_fixed_shift_binomial_convolution`,
`prove_squared_binomial_moment` — which discovers a certificate by running Gosper
at ~16 concrete `n` and interpolating the coefficients over `n`, then verifies it
with `equal()`.

That is real work and it is not what this lane duplicates. Three things were
missing, and they are the three the task asked for:

1. **The certificate was never an object.** `prove_wz_sum` returns a `CasExpr`
   held in memory. Nothing serialises, nothing outside the call can re-check it,
   and no fact in `artifacts/facts/` rests on one.
2. **The checker was not independent.** `certifies_wz_sum` lives in the same file
   as its producer, uses the same `equal`/`normalize`/`simplify` stack, and its
   fallback path calls `wz_symbolic_ratios` — *the very function the producer
   calls to build its samples*. Compare `groebner_cert.rs`, whose consumer in
   `axeyum-solver` re-expands the generators from the original terms and shares
   nothing. The WZ layer did not have that property.
3. **It was WZ, not Zeilberger.** WZ needs the answer up front: you hand it
   `summand` *and* `rhs`, it normalises `F = summand/rhs`, and it proves the
   normalised sum is constant. Zeilberger's algorithm needs no answer — it
   derives a recurrence. That is the half that was missing, and it is strictly
   more general (WZ is the `Σ_j a_j = 0` special case).

---

## The class of sums this lane actually handles — precisely

A summand is given as a **`HyperTerm`**: a product of factors, each one of

| factor | meaning | shift ratio, from `Γ(x+1) = x·Γ(x)` alone |
|---|---|---|
| `Gamma { form, exponent }` | `Γ(L)^e`, `L` an **integer-linear** form | `Γ(L+d)/Γ(L)` = an explicit rising/falling product |
| `Power { base, form }` | `c^L`, `c ∈ ℚ` | `c^d`, a rational constant |
| `Poly { poly, exponent }` | `p(vars)^e` | `p(shifted)/p` |

Everything is over ℚ, exactly. This covers, honestly:

- factorials and binomial coefficients raised to any integer power
  (`C(n,k)`, `C(n,k)²`, `C(2n,n)⁻¹`, …);
- geometric factors `2ⁿ`, `(−1)ᵏ`, `2^{−n}`;
- polynomial weights `k`, `k²`, `2k+1`;
- several symbolic parameters at once — Chu–Vandermonde is carried with `m`, `n`,
  `p`, `k` all symbolic.

It does **not** cover: `q`-analogues; parameters entering an argument
non-linearly (`Γ(n²+1)`, `Γ(nk)`); non-hypergeometric summands (harmonic numbers,
Stirling numbers, `⌊·⌋`); multiple summation variables; and irrational or
symbolic bases in `Power`.

**The `Γ` arguments must be integer-linear.** That is not a soft limit, it is the
whole reason the shift ratios are computable in closed form, and therefore the
reason the certificate is checkable by polynomial algebra. It is the boundary of
the fragment, not a to-do.

---

## The certificate

For `S(n) = ∑_k F(n,k)`:

```
recurrence            a_0(n) … a_J(n)     polynomials, not all zero
certificate           R(n,k) = P(n,k)/Q(n,k)
```

asserting exactly one thing:

```
Σ_j a_j(n)·S_j(n,k)  =  R(n,k+1)·r(n,k)  −  R(n,k)          (★)

  S_j(n,k) = F(n+j,k)/F(n,k)          r(n,k) = F(n,k+1)/F(n,k)
```

Every `F` has cancelled. `S_j` and `r` are rational functions read off the term
specification. So (★) is an identity in `ℚ(vars)`: cross-multiply, expand, and it
is either exactly the zero polynomial or it is not. Multiply (★) by `F(n,k)`:

```
Σ_j a_j(n)·F(n+j,k) = G(n,k+1) − G(n,k),     G = R·F
```

and sum over the finite support of `F`; the right side telescopes to zero, giving
`Σ_j a_j(n)·S(n+j) = 0`.

The certificate is small. For `∑_k C(n,k)` it is the whole of
`a = (2, −1)`, `R = k/(n−k+1)` — that is the entire proof that the row sums of
Pascal's triangle double.

### The five certificates found

| identity | order | recurrence | `R(n,k)` |
|---|---|---|---|
| `∑_k C(n,k) = 2ⁿ` | 1 | `2·S(n) − S(n+1) = 0` | `k/(n−k+1)` |
| `∑_k (−1)^k C(n,k) = 0`, `n ≥ 1` | **0** | `n·S(n) = 0` | `−k` |
| `∑_k C(n,k)² = C(2n,n)` | 1 | `(4n+2)·S(n) − (n+1)·S(n+1) = 0` | `k²(3n+3−2k)/(n−k+1)²` |
| `∑_k k·C(n,k) = n·2^{n−1}`, `n ≥ 1` | 1 | `(2n+2)·S(n) − n·S(n+1) = 0` | `(k−1)(n+1)/(n−k+1)` |
| `∑_k C(m,k)C(n,p−k)` (Chu–Vandermonde) | 1 | `(m+n−p)·S(p) − (p+1)·S(p+1) = 0` | `k(k+n−p)/(p−k+1)` |

The alternating sum is the nicest result of the five and I did not plan it. The
search returned **order 0** — the summand telescopes in `k` all by itself — with
leading coefficient `a_0 = n`. So the recurrence is literally `n·S(n) = 0`, which
gives `S(n) = 0` for every `n ≠ 0` with no base case and no induction, *and whose
leading coefficient vanishing at `n = 0` is exactly why the identity excludes
`n = 0`, where `S(0) = 1`*. The certificate carries its own domain restriction.
The same thing happens for `∑_k k·C(n,k)`: leading coefficient `−n`, zero at
`n = 0`, and the identity genuinely starts at `n = 1`.

---

## The search (untrusted)

Fix a denominator `Q`, bound the total degree of `a_j` and of `P`, and (★)
becomes **one homogeneous linear system over ℚ** whose unknowns are those
coefficients. Any nullspace vector with a nonzero `a`-part is a certificate.
Iterate order `J = 0, 1, 2, …` and take the first that works, so the recurrence
found is of minimal order.

Two design notes worth recording:

- **`Q` is guessed from a ladder** — `1`, `lcm_j den(S_j)`, that times `den(r)`,
  that squared. Enlarging `Q` never loses a certificate (a smaller true
  denominator is absorbed into `P`), it only demands a larger degree bound on
  `P`. And any factor of the true denominator that depends on the *shift*
  variable alone is absorbed by the `a_j`, which is why bare `1` is worth trying
  first — it is what finds the order-0 alternating certificate, whose true `R`
  scaled by `n` is the polynomial `−k`.
- **The nullspace is computed in `BigRational`, not `i128`.** The ansatz
  coefficients outgrow `i128` well before the certificate does; the answer is
  rescaled to a primitive integer vector at the end. This was not optional.

The search is genuinely untrusted: a wrong ansatz, a wrong degree bound, an
overflow, or a bug in the elimination loses a certificate and cannot produce one,
because nothing downstream believes its output.

---

## The checker (`telescoping_check.rs`) and why it is independent

Six layers:

1. **Shape** — nonempty recurrence, not all zero, `Q ≠ 0`, and no `a_j` mentions
   the summation variable.
2. **The rational identity** — accumulate `Σ_j a_j·S_j` and `R(k+1)·r − R` as
   ordinary fractions (`p/q + r/s = (ps+rq)/(qs)`) and compare by one
   cross-multiplication. No lcm, no linear system, no monomial ordering: a
   different route to the same identity than the producer's.
3. **Ratio integrity** — at a grid of integer points, confirm
   `num(pt)·F(pt) = den(pt)·F(shifted)` where `F` is computed **from actual
   factorials in exact bignum rationals**.
4. **Pointwise telescoping** — at every integer `k` of a scanned window,
   `Σ_j a_j(n)·F(n+j,k) = G(n,k+1) − G(n,k)`, exactly.
5. **Boundary** — `G` vanishes at both ends of the window, so the telescoped sum
   really is zero. A window that clips the support is rejected, not truncated.
6. **The recurrence itself** — `Σ_j a_j(n)·S(n+j) = 0` by exact finite summation.

The honest statement of the independence: I wrote both the producer's ratio
derivation and the checker's, and no two people writing `Γ(L+d)/Γ(L)` will write
genuinely different mathematics. So layer 2 alone would be weak evidence. **The
independence is carried by layer 3.** It computes `F` by multiplying real
factorials at integer points — a code path that shares nothing with the symbolic
route — and demands that the symbolic ratios reproduce it. The symbolic half and
the concrete half agree only if the ratios really are the term's ratios; a bug in
either is caught by the other.

A pleasant side effect of the concrete evaluator: `Γ` at a non-positive integer
is a pole, so in a denominator it makes the term **zero**. That gives
`C(n,k) = 0` outside `0 ≤ k ≤ n` for free, from the definition, with no special
case anywhere.

### From recurrence to closed form

`check_closed_form` closes the induction, and each piece is decided rather than
sampled:

- the recurrence annihilates the claimed closed form `T` — a rational-function
  identity in `T`'s own shift ratio, so it holds for all `n`;
- the base cases agree, by exact summation at concrete integers;
- the leading coefficient `a_J(n)` has **no integer zero at or above `base`** —
  decided by the rational-root theorem (clear denominators, strip the factors of
  `n`, enumerate the divisors of the constant term), not by evaluating at a few
  points.

---

## Tamper control — the result

Ten perturbations, all **rejected**
(`crates/axeyum-cas/tests/telescoping_identities.rs`):

| perturbation | rejected by |
|---|---|
| `P + 1` | the rational identity |
| `2·P` | the rational identity |
| `Q + k` | the rational identity |
| `a_0 = −3` instead of `−2` | the rational identity |
| `a_1 + n` (degree bump) | the rational identity |
| recurrence zeroed | the shape layer |
| a valid certificate re-pointed at a **different summand** | the rational identity |
| summation window narrower than the support | the boundary layer |
| closed form `3ⁿ` (wrong ratio) | the annihilation check |
| closed form `3·2ⁿ` (right ratio, wrong base) | the base case |

The two that matter most are the last three, because they are the ones a
sloppy checker would wave through: a certificate for the wrong term, a window
that silently truncates, and a closed form that satisfies the recurrence but not
the initial condition.

---

## Where it fails — measured, not guessed

- **Chu–Vandermonde's closed form is not established, only its recurrence.**
  The certificate is symbolic in all of `m, n, p, k`, so
  `(p+1)S(p+1) = (m+n−p)S(p)` is proved for symbolic `m` and `n`. Turning that
  into `C(m+n,p)` needs the base case `S(0) = 1` at *symbolic* `m` and `n`, and
  `check_closed_form` only evaluates base cases at concrete integers. The fact is
  therefore filed as the recurrence. This is the sharpest gap in the lane and the
  first thing worth fixing.
- **`leading_integer_zeros` declines when `a_J` mentions more than the shift
  variable.** Same root cause: no symbolic-parameter reasoning.
- **Four variables are expensive.** With default limits the Chu–Vandermonde
  search took ~250 s in a debug build, because the order-0 sweep over the full
  degree ladder runs first and each ansatz builds ~130 multivariate columns. With
  `max_order: 1, max_recurrence_degree: 1, max_certificate_degree: 3` the same
  certificate comes out in a few seconds. **The search cost is dominated by the
  degree ladder, not by the linear algebra.** A real implementation would bound
  degrees from the term's structure (Abramov–Petkovšek) instead of sweeping.
- **The `Q` ladder is a heuristic, and it is where completeness is lost.** It is
  not derived from a Gosper–Petkovšek normal form. It happened to contain the
  right denominator for all five identities here; it will not always.
- **No `q`-analogues, no multi-sums, no non-linear `Γ` arguments.**

### The assumption that is *not* discharged

Layer 2 establishes an identity in `ℚ(vars)`. Layers 4–6 confirm its integer
consequences **at the sampled points only**. Going from "holds in `ℚ(n,k)`" to
"holds at every integer of the summation range, for every `n`" needs the standard
side condition that `G = R·F` has the same natural boundary as `F` and acquires
no pole inside the range (A=B, §7). That is assumed, and it is named in the
`axiom_footprint` of every fact as
`cas.telescoped-term-natural-boundary`. Layers 4–5 are the evidence that it is
not vacuous — the checker counts and reports poles found inside the window rather
than skipping them — but they are evidence, not a proof. Discharging it properly
means proving `R·F` is a proper hypergeometric term with the same support, which
needs `Γ`-cancellation machinery this lane did not build.

---

## `proof_route`

None of `kernel-lean`, `smt-term-level`, `smt-clausal`, `search-certificate`,
`none` fits, and the near-miss is instructive.

`search-certificate` is "a combinatorial search whose result carries a replayable
witness or cover". Ours is a search whose result carries a replayable
certificate — so far so similar. **The difference is what a replay establishes.**
A witness or cover settles a *finite* statement: replay it and you have re-derived
one instance, and a claim about all `n` needs one certificate per `n`. A
telescoping certificate is an identity in `ℚ(vars)`, so a single polynomial
zero-test settles **every instance at once**. It is the only route in this
repository that establishes a universally quantified arithmetic statement without
a kernel proof term.

Filing these under `search-certificate` would make `axiom_footprint`
incomparable in exactly the way the field exists to prevent, because the two
footprints differ in *kind*: a replayed witness assumes the replay semantics,
while an algebraic identity assumes characteristic zero, that the declared term
specification denotes the intended summand, and the boundary condition above.

**Added `cas-certificate`** to the enum (`artifacts/ontology/fact.schema.json`
and `scripts/validate-facts.py`), scoped to cover the Gröbner-cofactor route in
`groebner_cert.rs` too, since it has exactly the same trust shape. Also added
`cas-term` to `formal.language`: a definite hypergeometric identity is not
`smtlib2` (it quantifies over ℕ) and not `lean4` (no kernel declaration for `Γ`,
`∑` or binomial coefficients exists, so writing it as Lean would name a theorem
the kernel cannot state).

`axiom_footprint` for all five facts, naming the real assumptions:

```
cas.exact-rational-polynomial-normal-form
cas.gamma-functional-equation
cas.hyperterm-specification-denotes-the-summand
cas.telescoped-term-natural-boundary
```

`[]` is not available here and would be a lie if it were.

---

## Scaling to hundreds of identities

The certificate format and the checker scale as they stand — checking is
milliseconds and is not the bottleneck. Four things gate the *search*:

1. **Degree bounds instead of a sweep.** The single biggest win. Today the search
   sweeps `certificate_degree ∈ 0..5` and `recurrence_degree ∈ 0..2` for every
   `Q` candidate and every order. Abramov's universal-denominator bound and the
   Gosper–Petkovšek normal form give `Q` and the degree of `P` directly from the
   term, turning a ladder of dozens of linear systems into one. This is a
   well-specified, bounded piece of work and it subsumes the `Q` heuristic.
2. **A corpus and a front door.** The identities here were hand-written as
   `HyperTerm` values. Hundreds needs a parser from a compact surface syntax
   (`sum(binomial(n,k)^2, k) == binomial(2*n,n)`) and a committed corpus file, so
   a regression sweep is one command. Bridging `CasExpr` → `HyperTerm` would also
   let the existing `prove_wz_sum` callers migrate onto the checkable route.
3. **Symbolic base cases.** Without them every multi-parameter identity stops at
   its recurrence, as Chu–Vandermonde did. This needs evaluating a `HyperTerm`
   at a *symbolic* point where the support collapses to one term — tractable, and
   it converts the whole Vandermonde/Gauss/Saalschütz family.
4. **Serialisation.** `TelescopingCertificate` is a Rust value. For a fact ledger
   with hundreds of entries the certificate should be a JSON artifact under
   `artifacts/` that `check_certificate` reads, so the evidence row points at the
   certificate rather than at a test that reconstructs it.

Order matters: (1) makes the search affordable, (2) makes it repeatable, (3)
widens the class, (4) makes the evidence self-contained. Higher-order
recurrences (`J ≥ 2`, Apéry-style) come free once (1) lands — the machinery
already iterates `J`, it just cannot afford the sweep.

---

## Files

| path | what |
|---|---|
| `crates/axeyum-cas/src/telescoping.rs` | `HyperTerm`, shift ratios, the Zeilberger search — untrusted |
| `crates/axeyum-cas/src/telescoping_check.rs` | the independent checker; shares no code with the above |
| `crates/axeyum-cas/tests/telescoping_identities.rs` | five identities end to end + ten tamper controls |
| `artifacts/facts/F-binomial-row-sum-two-power.json` | `∑_k C(n,k) = 2ⁿ` |
| `artifacts/facts/F-alternating-binomial-row-sum-zero.json` | `∑_k (−1)^k C(n,k) = 0` |
| `artifacts/facts/F-squared-binomial-row-sum-central.json` | `∑_k C(n,k)² = C(2n,n)` |
| `artifacts/facts/F-weighted-binomial-row-sum.json` | `∑_k k·C(n,k) = n·2^{n−1}` |
| `artifacts/facts/F-chu-vandermonde-convolution-recurrence.json` | the Chu–Vandermonde recurrence |
