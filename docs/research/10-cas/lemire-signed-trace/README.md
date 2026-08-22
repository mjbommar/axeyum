# Lemire signed-trace lane

Research notes for the lane whose goal is a new fixed-`F_2`, growing-conductor
signed-trace theorem closing the open estimate `(HWO)` / `(REL)` in the
Kaser--Lemire half-degree-irreducibles chain (sibling repository
`lemire-half-degree-irreducibles`, roadmap paper of 21 Aug 2026).

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

Executable companions live in
[`scripts/lemire-signed-trace/`](../../../../scripts/lemire-signed-trace/README.md).

The previous lane's ledger (branch `agent/gf2/lemire-proof`, unmerged) is the
negative-route record; nothing there is repeated here without a new input.
