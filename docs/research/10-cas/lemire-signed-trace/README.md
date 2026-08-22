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

Executable companions live in
[`scripts/lemire-signed-trace/`](../../../../scripts/lemire-signed-trace/README.md).

The previous lane's ledger (branch `agent/gf2/lemire-proof`, unmerged) is the
negative-route record; nothing there is repeated here without a new input.
