# Kaser--Lemire over F_2: state of the problem

Status: synthesis, 2026-08-22. This is the map. It states what is proved, what
is open, and -- the point of the lane -- why the open part is open, from every
side we could reach. Nothing here is a claim that the conjecture is proved; it
is not. The individual notes carry the details and the machine checks.

## The conjecture

For every `n` there is a monic irreducible `f` of degree `n` over `F_2` with
`deg(f - x^n) <= floor(n/2)` (Kaser--Lemire; equivalently a prime `P` of degree
`n` with `P = 1 mod x^{ceil(n/2)}`, i.e. Legendre's conjecture for `F_2[t]` at
the square-root scale). It is the identity ray class of
`E_ell = (1 + x F_2[x])/x^{ell+1}`, `ell = ceil(n/2)-1`.

## What is proved (this lane, machine-checked)

1. **Certified to `n = 3000`.** A doubly-certified half-degree irreducible for
   every `n <= 3000` (note: the finite handoff; 2600/2600 for `401..3000`,
   both checkers plus an independent flint re-check).
2. **Unconditional infinite families, one per seed** (note 08 Theorem A, fact
   `F:gf2-lemire-monomial-composition-family`): if `f` is an in-window
   irreducible of degree `m` and order `e`, and `rad(t) | e`,
   `gcd(t,(2^m-1)/e) = 1`, then `f(x^t)` is an in-window irreducible of degree
   `mt` (Lidl--Niederreiter Thm 3.35 plus the fact that monomial substitution
   scales tail and degree by the same factor). `m = 2` is the cyclotomic family
   `Phi_{3^{k+1}} = x^{2*3^k}+x^{3^k}+1`, `n = 2*3^k` (fact
   `F:gf2-lemire-cyclotomic-infinite-family`); `m = 3` gives the ODD family
   `n = 3*7^k`. Applied to this lane's certified seed ledger the reachable set
   covers 9.3% of the composites below `10^5` and has density zero
   asymptotically; it never contains a prime `n`.
3. **An almost-all theorem** (note 05, public PDF): all but `< 4 ell^2 2^{-ell}`
   of the `2^ell` top-half patterns are realized by an irreducible of degree
   `n`; sharp constant `ell^2-4ell+6`. Lemire is exactly the claim that the one
   named all-zero pattern is not in the exceptional set.

## What is open

The all-`n` statement. It reduces (proved: the Haar telescope, proper-power
count, and endpoint ledger of the roadmap) to a single estimate: a factor
`~ 4 ell` of signed cancellation in the high-`2`-power-order character layers
`T_{j,s}` (equivalently `(REL)`, `(HWO)`, `(NSD)/(RSD)`, or the cylinder form
`(CYL)` / fact `F:gf2-lemire-cylinder-twist-sup-bound`). This is a phase-aware
cancellation estimate for a complete character family at **fixed** `q = 2` and
growing conductor.

## Why it is open: three barriers and one wall

The identity class is genuinely distinguished -- it is the short interval
`{x^n + g : deg g <= floor(n/2)}`, the locus where all odd-power Galois-ring
traces vanish -- and every general method reduces to the same missing estimate.

- **Barrier I (moduli-only), note 03 section 5.** An explicit nonnegative fake
  population has the true low-conductor Fourier data, all high moduli inside
  Weil, second moment below the truth, and empty identity class. So no argument
  from mass, nonnegativity, Fourier moduli and low moments can prove `(REL)`.
  Averaging (note 05) goes exactly as far as this allows and no further.
- **Barrier II (symmetry), note 06.** Every degree-preserving symmetry lies in
  `PGL_2(F_2)`; only the Borel `{id, x -> x+1}` descends to `E_ell`, translation
  is an involution and Adams fixes the identity, so the orbit of the identity
  has size `<= 2 < 4 ell^2`; the Hecke action is transitive but degree-shifting.
  No group action moves the identity into the non-exceptional set.
- **Barrier III (construction), note 09.** Every provable irreducibility-
  preserving construction multiplies the degree, so it transports the conjecture
  from known degrees to their multiples and is structurally silent at **prime**
  `n` (`n = m*t` has no factorization with both factors `>= 2`) and at powers of
  two. For a fixed finite seed ledger the reachable set has counting function
  `O((log N)^W)`, hence density zero; a positive-density explicit family would
  need in-window seeds at a positive density of degrees, which is the conjecture
  itself. Separately -- and this is a counting theorem, not a construction, so it
  is not what Barrier III blocks -- the provable prescribed-coefficient ceiling
  for the TOP positions at `q = 2` is `n/2 - log_2 n` (Hayes/Weil, sharp form
  Hsu 1996 = Cohen 2005), so Kaser--Lemire is `~log_2 n` coefficients past Weil:
  the classical square-root barrier, not a power gap. (`sqrt n` is the ceiling
  for *arbitrary* coefficient positions -- Pollack 2013 -- and quoting it here
  was an error in the first version of note 09.)
- **The wall (phase correlation), note 07.** The one input no barrier blocks is
  a phase-aware correlation among the `S_n(chi)` -- the cylinder covariance
  `C = sum_{chi != chi'} S_n(chi) conj(S_n(chi'))`. Measured exactly: random in
  aggregate, bulk-negative per character, with an unbounded-above tail (so a
  uniform `|C| <= (1-eps)D` is false), and pair correlation pseudorandom. The
  one exact fixed-`q` mechanism, the Witt carry formula, provably collapses to
  Weil above the Kerdock level (boundary `s-1 = 1`). The required input --
  fixed-`q` pair-correlation delocalization for a fixed-conductor family -- is
  a recognized frontier open problem: its integer analogue is conditional (GRH
  + pair correlation, Kandhil--Languasco--Moree), its function-field analogues
  are all `q -> infinity` (Katz, Sawin, Keating--Rudnick).

## The five mechanism shapes (note 04)

Before the barriers were isolated, five candidate solution shapes were each
worked to a verdict (all negative, each with exact obstructions): a small
virtual Witt-tower trace (effective dimension is `~ 2^{j-2}(j-1)`, exponential,
not polynomial); a horizontal Sato--Tate via automorphy (circular -- Weyl at
frequency `n` is orthogonality); 2-adic arithmetic uncertainty (refuted -- the
product formula and rounding both run toward archimedean largeness);
manifest positivity (a new exact Chebyshev/Type-I identity, one `ell` factor
short); and Clifford-hierarchy aggregate cancellation (every even moment is
Gaussian above order 4). All five reduce to the same wall.

## Reproducibility

Notes 01--09 in this directory; scripts and exact data in
`scripts/lemire-signed-trace/` (flint-backed, cross-checked against the branch
CAS and the paper's pins); facts `F:gf2-lemire-cylinder-twist-sup-bound`
(open, the minimal sufficient statement) and
`F:gf2-lemire-cyclotomic-infinite-family` (proved) in the ledger. Public
documents: `lemire-proof-roadmap.pdf` (the reduction and the open estimate,
with the infinite family and finite handoff) and `lemire-almost-all.pdf` (the
almost-all theorem and Barriers I--II) in the sibling repository.

## Honest bottom line

Kaser--Lemire is not proved for all `n`. What is established is a complete map:
two proved theorems (almost-all; the family `n = 2*3^k`), three proved barriers
(moduli, symmetry, construction), the single unblocked analytic target isolated
with a new structural fact (the carry-collapse boundary), and certified
evidence to `n = 3000`. The all-`n` statement requires a phase-aware fixed-`F_2`
pair-correlation estimate that no current technique provides; it is open for
the same reason its integer analogue (Legendre under RH; Linnik exponent 2 for
prime-power moduli) is open.
