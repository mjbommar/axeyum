# Lane: lemire-signed-trace — a fixed-`F_2`, growing-conductor signed-trace theorem for the Kaser--Lemire chain

<!-- plan-section: lane-status -->

**Bottom rung laid: target pinned, three formulations checked, toolkit
verified (`WIP`, lemire-signed-trace, 2026-08-21).**
The sibling roadmap paper (`lemire-half-degree-irreducibles`, 21 Aug 2026)
leaves one open estimate, `(HWO)` (equivalently `(NSD)`), any proof of which
gives `(REL)` and the conjecture. [The lane note](../../research/10-cas/lemire-signed-trace/01-target-and-toolkit.md)
states it exactly, adds the Witt / Galois-ring form (the class of `alpha` in
`E_j` is the vector of Galois-ring traces `Tr(teich(alpha)^k) mod 2^{e_k}`,
`k` odd; verified bijective numerically, source Katz IMRN 2013 Lemma 2.2) and
the short-interval form (Legendre over `F_2[t]` centred at `x^n`), records why
Cauchy--Schwarz, large sieve, and Type I/II each lose exactly the needed
logarithm, and tabulates primary-source verdicts (Katz, KHC, Davis--Wan--Xiao,
Sawin--Shusterman with its explicit `(n+2)^{2n-h}` constant, Gorodetsky, Gao,
Pollack/Ha/Granger): nothing reaches the endpoint at fixed `q`.

Tooling is checked rather than assumed. `main` has no `F_2[x]`/Hayes CAS; the
unmerged branch `agent/gf2/lemire-proof` has a 26k-line one, built in 16 s
from a lane snapshot. An independent flint-backed Python anchor
(`scripts/lemire-signed-trace/`) reproduces the branch's pinned
`C_{5,11} = -608`, `C_{7,16} = -4608`, matches `axeyum-gf2-hayes-endpoint 12`
exactly (`359`, `335` = `N_12(1) - 2^{n-12}` at `n = 25, 26`), and verifies
`L`-polynomial RH, power sums, four-population identity, and character counts
at `(5,11)`. One speculative shortcut already killed: the Teichmueller-trace
Gauss sums at Witt order `>= 8` are generic (within 2% of the KHC bound), so
the top Witt direction carries no rigid structure.

**Next:** candidate A of the note, the Witt-tower bit-balance experiment:
tabulate `delta_s - delta_{s-1}` and the conditional biases of Witt digit
`s-1` given all lower Witt data, `ell <= 13` in Python and `ell <= 23` through
the branch binaries, and look for structure in `s` beyond the four-population
identity before writing any statement. Then candidate B (tower relations
`chi, chi^2, chi^4`). Nothing receives proof credit until it closes the
endpoint ledger.

<!-- plan-section: landed-changes -->
