# Lane: lemire-signed-trace — a fixed-`F_2`, growing-conductor signed-trace theorem for the Kaser--Lemire chain

<!-- plan-section: lane-status -->

**Bottom rung laid: target pinned, three formulations checked, toolkit
verified (`WIP`, lemire-signed-trace, 2026-08-21).**
The sibling roadmap paper (`lemire-half-degree-irreducibles`, 21 Aug 2026)
leaves one open estimate, `(HWO)`, any proof of which gives `(REL)` and the
conjecture. [The lane note](../../research/10-cas/lemire-signed-trace/01-target-and-toolkit.md)
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

**Correction before candidate A:** `(HWO)` has two exact population-side
reductions. For `q=2^s` with `q/2` not dividing `j`, the nonresonant layer is
the adjacent-precision difference `(NSD)`; its normalized `delta_s` form has
an essential `2^{-floor((j-1)/q)}` factor. When `q/2 | j` but `q` does not,
the conductor/order resonance instead gives the direct sparse-discrepancy
target `4 ell |Delta_{j,s}| <= (j-1)2^{ceil(n/2)}`. The independent anchor
now asserts both reductions against the four-population identity through its
existing endpoints. These resonant rows occur in the intended range (for
example `ell=j=200`, `q=16`), so they cannot be folded into a Witt-digit
martingale argument.

**Next:** candidate A must tabulate the two targets separately: nonresonant
conditional-zero-versus-unconditional means and resonant direct sparse
discrepancies, then conditional Witt-digit biases only for the first class,
through `ell <= 23` using branch population dumps. The first direct data at
orders `q >= 8`, `ell=14..22`, are comfortably below the `1/(4ell)` HWO ratio
from `ell=16` onward (worst observed factor `0.219` at `(ell,n)=(22,46)`),
but this is finite evidence and its low-`ell` cutoff is not the eventual
`Q=8` regime. Then candidate B (tower relations `chi, chi^2, chi^4`). Nothing
receives proof credit until it closes the endpoint ledger.

<!-- plan-section: landed-changes -->
