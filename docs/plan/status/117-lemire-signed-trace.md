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
example `ell=j=200`, `q=16`) and include the top order whenever `j` is a power
of two, so they cannot be folded into a Witt-digit martingale argument.

**Next:** candidate A must tabulate the two targets separately: nonresonant
conditional-zero-versus-unconditional means and resonant direct sparse
discrepancies, then conditional Witt-digit biases only for the first class,
through `ell <= 23` using branch population dumps. For the eventually relevant
orders `q >= 16`, the first direct data are below the `1/(4ell)` HWO ratio from
`ell=16` onward and fall to a worst observed factor `0.219` at
`(ell,n)=(22,46)`, but this is finite evidence and not the eventual `Q=8`
theorem regime. The dump analyzer now also computes every nonresonant coset of
`2^s E_j` in `2^{s-1}E_j` exactly. At `ell=22`, in the first genuinely
multi-coset (`R=4,8`) rows, the identity coset supplies only `7%..37%` of the
absolute coset deviation and is usually not maximal. Thus a theorem saying all
Witt fibres have the same bias is false as a formulation; an identity-specific
argument or a separately proved uniform upper bound remains open. Then
candidate B (tower relations `chi, chi^2, chi^4`). Nothing receives proof
credit until it closes the endpoint ledger.

**Evidence correction:** the cylinder-variance analyzer now accumulates every
cylinder's scaled variance numerator as an integer.  This preserves all
identity-cylinder values in the checked `ell <= 22` table, while correcting
only the two `ell=22` rank positions (`12773/32768` and `10742/32768`).  The
strong finite `(ICV)` margins remain evidence for a possible localization
bridge, never an established inequality.

**Rung 2 (lemire-signed-trace, 2026-08-21 evening):** exact layer tables now
reach `ell=23` (`data/layers-ell23-n47.txt`): worst high-order ratios relative
to the `1/(4ell)` threshold are `0.21x` (orders `>= 8`), `0.10x` (`>= 16`),
`0.04x` (`>= 32`), continuing the monotone fall from `2.2x` at `ell=12`. The
one-sided `(ICV)` object is measured directly: the identity cylinder's
variance is typical (rank mid-pack among all `2^{a-1}` cylinders at every
`ell`, max/avg `<= 1.8`), the average matches the Sato--Tate prediction to
10--16%, and the twisted cylinder sums have rms equal to the random-phase
prediction to three digits with sup over all cylinders `0.36..0.94` of the
`2^{ell-1}` target (Weil: `76..84x`). Note 02 records four further exact
reformulations (Type I exactness making the top layer a second difference of
Moebius interval sums, checked; Teichmueller curve against the Witt trace-zero
subgroup; power-map pullbacks for prime `n`; `Z/2^e` trace code) and the
shortcuts killed (parity of `I_n(1)` irregular for `n <= 38`; Swan; Oesterle
LP; Cauchy over twists). A primary-source check found no integer- or
function-field method beating Weil/GRH by a logarithm for a single
prime-power modulus (best: Banks--Shparlinski exponent `2.1115`; DPR averages
over moduli). The 2025 Sawin--Shusterman short-trace theorem was checked at
source level too: it requires large fixed `q` and squarefree modulus, so it
excludes both `q=2` and `x^j` rather than supplying the wild Witt estimate.
The minimal sufficient statement is now the open fact
`F:gf2-lemire-cylinder-twist-sup-bound` (empty evidence, by design). The
theorem state is unchanged: Lemire's conjecture is not proved.

<!-- plan-section: landed-changes -->
