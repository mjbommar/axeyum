# Diary — scaling creative telescoping (lane `telescoping-scale`), 2026-08-14

Continuation of [`diary-telescoping.md`](diary-telescoping.md), which opened the
domain: Zeilberger's algorithm producing certificates, a checker sharing no code
with it, five classical identities as facts on a new `cas-certificate` route.

That lane ended with four ranked recommendations. This lane took them in order.
All four landed; (1) and (2) landed properly, and the honest limit moved from
"the search is a sweep" to somewhere much more specific.

---

## 1. The degree sweep is gone, and so is the `Q` ladder

### What was there

For each order `J`, the old search fixed a certificate denominator `Q` from a
**ladder of four guesses** (`1`, `lcm_j den(S_j)`, that times `den(r)`, that
squared), then swept `certificate_degree ∈ 0..5` and `recurrence_degree ∈ 0..2`
— up to 72 homogeneous linear systems per order, each with as many unknowns as
there are monomials of bounded total degree in *all* the variables. For
Chu–Vandermonde (four variables) that is 126 unknowns per system.

The previous lane recorded this precisely: "the search cost is dominated by the
degree ladder, not by the linear algebra", and "the `Q` ladder is a heuristic,
and it is where completeness is lost."

### What is there now

The textbook structure, which removes both. Write

```text
S_j = F(n+j,k)/F(n,k) = E_j(k)/D(k),        D = lcm_j den(S_j)
t(k) = Σ_j a_j F(n+j,k) = F(n,k)·N(k)/D(k), N(k) = Σ_j a_j E_j(k)
```

so the unknown `a_j` enter `N` **linearly** and the shift quotient splits into a
known part and an unknown one:

```text
t(k+1)/t(k) = ρ(k)·N(k+1)/N(k),   ρ(k) = r(k)·D(k)/D(k+1)
```

Put the *known* `ρ` into **Gosper–Petkovšek normal form**
`ρ = (a(k)/b(k))·(s(k+1)/s(k))` with `gcd(a(k), b(k+h)) = 1` for every integer
`h ≥ 0`. Gosper's criterion becomes one polynomial equation

```text
a(k)·x(k+1) − b(k−1)·x(k) = s(k)·N(k)                     (†)
```

and the certificate falls out of its solution:

```text
R(n,k) = b(k−1)·x(k) / (s(k)·D(k))
```

Three consequences, and they are the whole of item (1):

- **`Q` is derived.** It is `s·D`, read off the normal form. There is no ladder,
  no guess, and the completeness that the ladder was losing is recovered — the
  Gosper–Petkovšek denominator is *the* denominator, not a candidate.
- **`deg_k P` is derived**, by Gosper's classical degree bound applied to (†):
  compare the leading behaviour of `a(k)` and `b(k−1)`, and when they cancel take
  the exceptional value `(subleading(B) − subleading(A))/leading` if it is a
  non-negative integer constant. No sweep.
- **The recurrence degree is not bounded at all.** The system is solved over the
  **field `ℚ(parameters)`**, so `a_j` come out as polynomials of whatever degree
  they need. `Limits::max_recurrence_degree` is deleted, not defaulted.

What is left is one linear system per order. For Chu–Vandermonde: 3 unknowns and
2 equations, instead of 72 systems of up to 126 unknowns.

### Measured, same identity, same machine, release build

`cargo run -p axeyum-cas --release --example telescoping_search_cost`
(the example is committed, so this is reproducible).

| identity | before | after | ratio |
|---|---|---|---|
| `∑_k C(n,k)` | 55.7 ms | 1.3 ms | 43× |
| `∑_k (−1)^k C(n,k)` | 104 µs | 366 µs | 0.3× (already trivial) |
| `∑_k C(n,k)²` | 137.5 ms | 3.8 ms | 36× |
| `∑_k k·C(n,k)` | 40.2 ms | 1.3 ms | 31× |
| `∑_k C(m,k)C(n,p−k)` **default limits** | **18.5 s** | **46.7 ms** | **396×** |
| `∑_k C(m,k)C(n,p−k)` hand-tightened budget | 319 ms | — (no budget needed) | — |
| `∑_k C(n,k)³` (Franel) | **declined after 9.8 s** | **found, order 2, 109 ms** | new capability |

The Chu–Vandermonde row is the headline and it is the one the previous lane
measured: 18.5 s in release (~250 s in its debug build) down to **46.7 ms**, and
the hand-tightened `Limits` the test file needed are gone. The alternating row
sum got *slower* in relative terms because it was already sub-millisecond and now
pays for one Gosper–Petkovšek normal form; in absolute terms it is 366 µs.

The debug-build integration suite is the same story from another angle: the whole
of `telescoping_identities.rs` — nine tests then, seventeen now, including three
new identities — runs in **3.2 s**.

### Does the derived bound subsume the heuristic? Yes, and here is the check

The task asked me to say plainly if it did not. It does, and the evidence is that
**every identity the old engine found, the new one finds with the same
recurrence** — the tests assert the exact classical coefficients
(`(4n+2, −(n+1))`, `(2n+2, −n)`, `(m+n−p, −(p+1))`, …) and they pass unchanged.
The derived `R` for `∑_k C(n,k)²` is `k²(3n+3−2k)/(n−k+1)²`, byte for byte the
one the ladder guessed, and there is now a unit test asserting the *denominator*
`(n−k+1)²` specifically, so a regression to guessing would be visible.

One caveat, stated because it is real: the degree bound and the normal form are
derived **generically** — leading coefficients are compared as polynomials in the
parameters, so a parameter value at which a leading coefficient happens to vanish
is not accounted for. That is sound in the only sense that matters here. A wrong
bound loses a certificate; it cannot manufacture one, because the checker still
decides.

### `J ≥ 2` did come free, and it is a fact now

`∑_k C(n,k)³` (Franel) needs a second-order recurrence whose certificate numerator
has degree 3 in `k` with coefficients of degree **5** in `n`. The old total-degree
ansatz would have needed `certificate_degree ≥ 8` over two variables; it declined
after 9.8 s. The new engine finds

```text
8(n+1)²·S(n) + (7n²+21n+16)·S(n+1) − (n+2)²·S(n+2) = 0
```

in 109 ms, the checker verifies it, and the test additionally replays it against
the Franel numbers 1, 2, 10, 56, 346, 2252, 15184 in `i128`. Filed as
`F:franel-numbers-recurrence` — a **recurrence**, honestly, because the Franel
numbers have no hypergeometric closed form and there is nothing further to claim.

### Two places the exact-field solve needed help

Both are recorded because they are the seam where this work will next break.

- **`solve_over_parameters` carries `i128` coefficients.** The elimination over
  `ℚ(parameters)` uses `MvPoly` for its entries, and `MvPoly::gcd` is a primitive
  PRS whose pseudo-remainder step multiplies by leading coefficients. On Franel's
  7×7 system it overflows. So there is a **fallback**: give every unknown a
  bounded parameter-degree ansatz and solve over ℚ in exact bignum rationals
  (`solve_by_parameter_ansatz`, sweeping degree 0..6 — the *only* sweep left
  anywhere in the module, over tiny systems). Franel needs degree 5 and the
  fallback finds it. Overflow makes the exact-field solve return `None`, never a
  wrong answer, so this is a completeness measure and not a soundness one.
- **Reduction became optional.** `RationalFunction::reduced()` failing (an
  overflowing GCD) used to cost a certificate: `finish` returned `Declined` even
  though it already held a perfectly good unreduced `P/Q`. Same for reducing `ρ`
  before the normal form, and for the GCD inside the normal-form loop. All three
  are now tolerant. The last one deserves a note: **Gosper's identity does not
  depend on the coprimality condition at all** — that condition is what guarantees
  a *polynomial* `x` exists when the term is summable, so skipping a shift can
  only lose a solution. I verified the derivation before relying on it.

---

## 2. Symbolic base cases — the sharpest limit, closed

The previous lane's own words: Chu–Vandermonde "is the sharpest gap in the lane
and the first thing worth fixing", because `check_closed_form` evaluates base
cases at concrete integers while the identity's base case `S(0) = 1` lives at
symbolic `m` and `n`.

### The mechanism, which is decidable rather than sampled

At the base index, substitute **only the shift variable**. Then:

1. **Forced support.** Every `Γ` factor with a negative exponent whose argument
   has become *parameter-free* forces `c·k + d ≥ 1` or the term is zero. For
   Chu–Vandermonde at `p = 0`, `Γ(k+1)⁻¹` gives `k ≥ 0` and `Γ(−k+1)⁻¹` gives
   `k ≤ 0`. The support is the single point `k = 0`. Two-sided bounds make the
   sum over all integers a *finite explicit sum*.
2. **Vanishing outside is checked, not assumed.** Every point of the scanned
   window outside the forced support must evaluate to zero, and the window must
   **strictly** contain the support. This is the symbolic counterpart of the
   concrete checker's boundary layer, and it is a rejection reason, not a
   truncation.
3. **Symbolic `Γ` cancellation.** At each surviving point, `Γ` factors whose
   argument still mentions a parameter are accumulated by argument. At `k = 0`
   Chu–Vandermonde's summand is `Γ(m+1)·Γ(m+1)⁻¹·Γ(n+1)·Γ(n+1)⁻¹` times two
   `Γ(1)`s: every symbolic power cancels and the value is the **rational 1**, for
   every `m` and `n`. The claimed `C(m+n,p)` at `p = 0` evaluates the same way.

The accept condition is exactly "both sides reduce to a rational". A base case
that leaves an uncancelled `Γ` is **refused as not comparable**, not compared by
coefficient — there is a tamper control for precisely that.

### What it converts

- `F:chu-vandermonde-convolution` — `∑_k C(m,k)C(n,p−k) = C(m+n,p)`, the closed
  form, at symbolic `m` and `n`. The lane that opened the domain could only file
  the recurrence.
- `F:cross-binomial-row-sum` — `∑_k C(m,k)C(n,k) = C(m+n,n)`, symbolic in `m`.
  Stated alongside the first one deliberately: the point is that the mechanism is
  general, not tuned to one summand.

The other half of what a closed form needs was already symbolic and already
worked: the annihilation check is a rational-function identity, and
`leading_integer_zeros` decides "no integer zero at or above `base`" by the
rational-root theorem. For Chu–Vandermonde `a_1 = −(p+1)` mentions only the shift
variable, so it goes through unchanged.

### The new axiom, named

`cas.symbolic-gamma-arguments-avoid-poles`. An uncancelled symbolic `Γ` power is
treated as nonzero and finite; for a parameter ranging over the integers that
holds away from the non-positive integers. In the two facts here every symbolic
`Γ` cancels, so the assumption bites only on definedness, not on values — but it
is a real assumption and it is in both footprints. It is **not** in
`F:franel-numbers-recurrence`, which involves no symbolic base case.

### Tamper controls for the symbolic route (all rejected)

| perturbation | rejected by |
|---|---|
| `2·C(m+n,p)` — right ratio, wrong symbolic base | the base case |
| `C(m+n,p+1)` — right base *value* (both are 1 at `p=0`), wrong ratio | the annihilation check |
| `C(m+n,p)·Γ(m+1)` — leaves an uncancelled `Γ` | refused as not comparable to a rational |
| a window that does not **strictly** contain the forced support | the window check |
| a summand with unbounded support (`1/k!`) | declines, naming the support |

Plus a consistency control that is not a tamper: at every point where *both*
apply, the symbolic evaluator and the concrete factorial evaluator are asserted
equal (77 points on `C(n,k)²`). The two are separate code paths; this is what
keeps them honest.

---

## 4. Certificates are artifacts now

Taken next because it is what makes the facts stand on their own.

`artifacts/cas-certificates/*.json` — seven files, one per identity, each
carrying the summand as a `HyperTerm` **specification**, the shift and summation
variables, the recurrence, `R = P/Q`, the check grid, and (where claimed) the
closed form and its base index. Rationals are `[numerator, denominator]` integer
pairs; there are no decimals anywhere in the format, so a round trip is exact and
a diff is readable.

The codec (`telescoping_json.rs`) is hand-rolled and dependency-free — the crate
still depends on nothing but `axeyum-ir` and the `num-*` bignums.

Two programs, sharing nothing:

- `examples/emit_telescoping_certificates.rs` writes a file **only after** the
  independent checker has accepted what it is about to write.
- `tests/telescoping_certificate_artifacts.rs` reads every committed file and
  re-checks it. **Nothing in that path calls the search.** That is the point: the
  facts' evidence rows now name `artifacts/cas-certificates/<id>.json`, so the
  claim no longer rests on re-running the producer.

Tamper controls on the artifacts: a numerator edited by one, a recurrence
coefficient edited by one, and each certificate re-pointed at its neighbour's
summand are all rejected; a truncated file, a foreign format tag, and a decimal
where an integer belongs are refused by the reader before the checker sees them.
There is also a byte-identity test — a committed file that does not round-trip
means the emitter and the reader have drifted, which would make a regeneration
produce a spurious diff and hide a real one.

---

## 3. The front door — not built

`CasExpr` → `HyperTerm` plus a committed surface-syntax corpus is the one
recommendation not taken. Depth over breadth was the instruction and I spent the
budget on (1) and (2). What exists instead is the serialised format above, which
covers part of the same need: a certificate corpus is now a **directory**, and
one command sweeps it. A surface parser would still be worth having, and it now
has an obvious target — emit a `CertificateDocument`, not a Rust value.

---

## The next honest limit, measured rather than guessed

**`MvPoly`'s `i128` coefficients, specifically inside `MvPoly::gcd`.**

The frontier case is Apéry's summand `∑_k C(n,k)²C(n+k,k)²`. It declines, and I
established *why* rather than assuming:

- The derived degree bound for it is **2**. I checked independently (SymPy, out of
  tree) that the certificate exists at exactly `dx = 2`, with
  `a_0 = (n+1)³`, `a_1 = −(2n+3)(17n²+51n+39)`, `a_2 = (n+2)³` — Apéry's
  recurrence. **So the search design is not what fails.**
- What fails is `MvPoly::gcd` on the degree-8 shift quotient the term produces:
  the primitive-PRS pseudo-remainder multiplies by leading coefficients at every
  step and overflows `i128`. It fails at order 0 already, inside the
  normal-form loop.

So the binding constraint on this route has moved from *the algorithm* to *the
coefficient type*. The fix is a subresultant PRS (which controls exactly this
growth) or bignum coefficients in `MvPoly`. Both are changes to a module the rest
of the crate depends on, which is why this lane did not make them at the end of
its own work.

Three smaller limits, unchanged or newly visible:

- `leading_integer_zeros` still declines when the leading recurrence coefficient
  mentions more than the shift variable. It did not bite here (Chu–Vandermonde's
  `−(p+1)` mentions only `p`), but a Saalschütz-type identity will hit it.
- The symbolic base case needs the support pinned by **parameter-free** `Γ`
  factors. A summand whose bounds stay parametric at the base index declines —
  correctly, and loudly.
- No `q`-analogues, no multi-sums, no non-linear `Γ` arguments. Same fragment
  boundary as before; nothing here moved it.

---

## Files

| path | what |
|---|---|
| `crates/axeyum-cas/src/telescoping.rs` | Gosper–Petkovšek normal form, derived degree bound, the `ℚ(parameters)` solve and its bignum fallback — all untrusted |
| `crates/axeyum-cas/src/telescoping_check.rs` | symbolic evaluation, forced support, `check_closed_form_symbolic`; still shares no code with the producer |
| `crates/axeyum-cas/src/telescoping_json.rs` | the deterministic certificate codec |
| `crates/axeyum-cas/tests/telescoping_identities.rs` | 7 identities end to end + 15 tamper/limit controls (9 tamper tests) |
| `crates/axeyum-cas/tests/telescoping_certificate_artifacts.rs` | re-checks every committed certificate **from the file**, plus artifact tamper controls |
| `crates/axeyum-cas/examples/telescoping_search_cost.rs` | the measurement above, reproducible |
| `crates/axeyum-cas/examples/emit_telescoping_certificates.rs` | regenerates the artifacts, checker-gated |
| `artifacts/cas-certificates/*.json` | seven certificates, the evidence itself |
| `artifacts/facts/F-chu-vandermonde-convolution.json` | the closed form, symbolic base case |
| `artifacts/facts/F-cross-binomial-row-sum.json` | `∑_k C(m,k)C(n,k) = C(m+n,n)` |
| `artifacts/facts/F-franel-numbers-recurrence.json` | the first order-2 certificate on this route |
