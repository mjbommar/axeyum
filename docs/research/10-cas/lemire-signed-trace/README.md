# Lemire signed-trace lane

Research notes for the lane whose goal is a new fixed-`F_2`, growing-conductor
signed-trace theorem closing the open estimate `(HWO)` / `(REL)` in the
Kaser--Lemire half-degree-irreducibles chain (sibling repository
`lemire-half-degree-irreducibles`, roadmap paper of 21 Aug 2026).

- [00-state-of-the-problem.md](00-state-of-the-problem.md) -- **start here**:
  the synthesis. What is proved, what is open, and why -- two theorems, three
  barriers, one wall.
- [01-target-and-toolkit.md](01-target-and-toolkit.md) -- the exact open
  statement, three equivalent formulations (paper, Witt / Galois-ring,
  short-interval), the scale of the required saving, primary-source literature
  verdicts, ranked candidate mechanisms with the experiment that kills each,
  and the checked tooling inventory.
- [02-mechanism-hunt.md](02-mechanism-hunt.md) -- what the exact layer data
  to `ell = 22` say, four further exact reformulations (Type I / Moebius
  second difference, Teichmueller curve against the Witt trace-zero subgroup,
  power-map pullbacks, `Z/2^e` code), the shortcuts killed in this rung
  (parity, Swan, explicit-formula LP, Cauchy--Schwarz over twists), and the
  next experiments.
- [03-uncertainty-analogy.md](03-uncertainty-analogy.md) -- the gap as a
  Fourier-uncertainty gap on `E_ell` (exact), the Witt-order filtration as
  the Clifford hierarchy of diagonal gates with Kerdock at the stabilizer
  boundary (exact), and the interference / delocalization reading of the
  missing inequality (analogy), with what each would have to become.
- [04-shape-verdicts.md](04-shape-verdicts.md) -- running diary of the five
  'of course' solution shapes (Opus agents): literature, exact tests with our
  tools, and verdicts, appended as they land.
- [05-almost-all-theorem.md](05-almost-all-theorem.md) -- an unconditional,
  machine-checked theorem: all but `< 4 ell^2 2^{-ell}` of the `2^ell` top
  halves are the top half of an irreducible of degree `n` (sharp constant
  `eps(ell) = ell^2-4ell+6`); Lemire is exactly the claim that the one named
  all-zero pattern is not exceptional. Script `lemire_almostall.py`.
- [06-symmetry-barrier.md](06-symmetry-barrier.md) -- the second barrier:
  no degree-preserving symmetry has an orbit of the identity class larger than
  2, so a group action cannot prove Lemire (corrects the earlier claim that
  translation fixes the identity class).
- [07-covariance-phase-face.md](07-covariance-phase-face.md) -- the phase-aware
  face: the exact cylinder covariance C/D (bulk-negative, random in aggregate,
  unbounded-above tail), the pseudorandom pair correlation, and an exact proof
  that the Witt carry formula collapses to Weil above the Kerdock level
  (boundary s-1=1). Verdict: the one unblocked target, not reachable now.
- [08-infinite-family.md](08-infinite-family.md) -- the monomial-composition
  window family (Theorem A): for every in-window irreducible seed of degree
  `m` and order `e`, `f(x^t)` is in-window irreducible of degree `mt` whenever
  `rad(t) | e` and `gcd(t,(2^m-1)/e) = 1` (LN Thm 3.35; the window is free).
  `n = 2*3^k` is the `m = 2` case (pointed out by E. Jerabek on MathOverflow,
  Nov 2011); `m = 3` gives odd `n = 3*7^k`. Exact coverage to `10^5`; density
  zero; never a prime `n`. Rewritten 2026-08-22; the first version's
  "first/unique family, even n only" claims were wrong.
- [09-construction-barrier.md](09-construction-barrier.md) -- the third
  barrier: provable irreducibility-preserving constructions multiply the
  degree, so window families are lacunary (density zero) and cannot cover a
  residue class; honest scope (known toolbox, not a logical impossibility).
- [10-open-problem-statement.md](10-open-problem-statement.md) -- the missing
  estimate `(HWO)` stated for a specialist (Katz--Sawin monodromy / ASW towers
  / fixed-q pair correlation), with its three equivalent faces and the three
  precise questions whose answer would close the chain.
- [11-backward-chains-diary.md](11-backward-chains-diary.md) -- running diary
  of the five backward-chain angles (construction, geometry, sieve, Frobenius
  angles, uniformization), one Opus agent each, with the ground truth and the
  primary-source literature check every agent starts from.
- [12-horizontal-deligne-budget.md](12-horizontal-deligne-budget.md) -- angle 4:
  what a cohomological bound on Katz's `Prim_j` would have to look like.
  Proposition 1 (the Deligne budget: a Betti bound ALONE can never give
  `(HWO)`; the binding constraint is the top cohomological DEGREE, and a
  logarithmic number of top degrees must vanish), Proposition 2 (`Prim_j` is
  `G_m x A^{j-1}` and the trace function is `G_m`-invariant, so middle
  concentration is impossible and `i_max >= j+1`), Proposition 3 (`j = 2`
  solved exactly: `C = 2`, `i_max = 2j-1` or `2j`), and the exact `q`-aspect
  experiment that measures the top weight at small `(n,j)`. Rewrites Q1 of
  note 10 as (Q1'). Script `lemire_horizontal_weights.py`.
- [13-sieve-face.md](13-sieve-face.md) -- angle 2: the sieve face. Lemma 1 (the
  window has EXACT Type-I data, `A_d = 2^{floor(n/2)+1-k}` with identically zero
  remainder, hence level of distribution `D = |W_n|` and sifting parameter
  `s = 1` at the prime level; and no level beyond it, even on average). What the
  linear sieve does prove: `P_4` with all factors of degree `> (1/4-eps)n`, `P_3`
  with all factors of degree `> alpha n` for `alpha < 1/6` (Kuhn weights), a
  fully explicit Brun form, and an exact Selberg Brun--Titchmarsh with no error
  term. The parity barrier as a theorem with an exact rational witness: for
  `10 <= n <= 15` a nonnegative prime-free population on the degree-`n` monics
  reproduces the window's Type-I data exactly, so no lower-bound sieve at level
  `|W_n|` can prove a prime.  The first level that does is `k_max(n) = h+1`
  for `10 <= n <= 15` and `h+2` at `n = 16`; for `n <= 9` there is no barrier.
  Proposition 11: any such sieve proof would prove Legendre for `F_2[t]`
  (angle 5's uniform conjecture). Proposition 13: Type II transplants onto the
  same `S_n(chi)` family. Script `lemire_sieve_face.py`.
- [14-horizontal-unblocked.md](14-horizontal-unblocked.md) -- angle 4b: is the
  horizontal route unblocked? **Verdict: ALIVE.** The budget restated for the
  range `(HWO)` actually uses (`a <= j <= ell`, so `ell/(j-1) -> 1`): only the
  top `~6 + 2 log2 C` degrees need vanish, not concentration in degree `j+1`.
  Proposition A (explicit basis `E_j = prod_{k odd} prod_l <1 + z^l x^k>`,
  orders `2^{e_k}`, which makes the whole computation exact in `Z[zeta_8]`),
  Proposition B (the `G_m`-action is free iff `gcd(j, q-1) = 1` -- corrects
  note 12's "`j | q-1`"), Lemma C (`2j - i_max = min{k : H^k(B, G^v) != 0}`
  after Leray descent along the `G_m`-torsor), Lemma D (`H^{2j}_c = 0` for
  every `j >= 4`, `n != j-1`, from Katz's `SL(j-1)` monodromy). New engine
  `axeyum-lemire-lfunc` (`L`-function route, cost independent of `n`) reaches
  `j = 4..7`; every exactly resolved cell with `j >= 4` has top weight
  `n + j` or `n + j + 1`, every one with `j <= 3` sits at `n + 2j - 1` or
  `n + 2j`. The monodromy transition is at `j_0 = 4` and is a theorem
  (Katz IMRN 2013 Thm. 5.1; Gorodetsky FFA 2019 Lemma 3.5), confirmed here
  mechanically. What remains: (T1) the degree/weight statement -- the `w ~ j-7`
  case of Sawin's Hypothesis H, whose only unconditional input is vacuous at
  `p = 2` -- and (T2) a Betti bound, where the best in print is short by an
  exponential. Script `lemire_horizontal_quotient.py`.

Executable companions live in
[`scripts/lemire-signed-trace/`](../../../../scripts/lemire-signed-trace/README.md).

The previous lane's ledger (branch `agent/gf2/lemire-proof`, unmerged) is the
negative-route record; nothing there is repeated here without a new input.
