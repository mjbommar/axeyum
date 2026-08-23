# Lane: lemire-signed-trace — a fixed-`F_2`, growing-conductor signed-trace theorem for the Kaser--Lemire chain

<!-- plan-section: lane-status -->

**Rung 7 -- backward chains, five angles run as Opus agents (`WIP`,
lemire-signed-trace, 2026-08-22).** Diary
[note 11](../../research/10-cas/lemire-signed-trace/11-backward-chains-diary.md);
notes 12--14. Verdicts: (angle 3) the construction route is a textbook
theorem applied to the certified seed ledger (`f(x^t)` for any in-window
seed; 9.3% of composites below `10^5`; never a prime `n`) -- two false
lemmas in note 09 and a priority error in note 08 (Jerabek, MathOverflow
2011) corrected, public PDF fixed; (angle 4/4b) Katz's Betti question was
mis-posed -- a Betti bound alone cannot give `(HWO)`; the real question is a
cohomological DEGREE statement plus a `~2^{j/2}` Betti bound; big monodromy
at `p = 2` holds for `j >= 4` by theorem (Katz 2013 Thm 5.1, Gorodetsky
2019 for `j = 3`), `H^{2j}_c = 0` proved for `j >= 4`, and every exactly
resolved cell past the transition has top weight `n + j + O(1)` -- the route
is ALIVE, reduced to the `p = 2` case of Sawin's Hypothesis H plus a Betti
bound (notes 12, 14); (angle 2) exact Type I to level `|W_n|`, `P_4`/`P_3`
with large factors and an exact Brun--Titchmarsh proved; the parity barrier
made exact by LP duality with rational prime-free witnesses `10 <= n <= 15`;
a sieve proof of Lemire would prove Legendre for `F_2[t]` (note 13).
**Rung 8 -- arXiv sweep and its two leads, both closed (2026-08-23).**
[Note 15](../../research/10-cas/lemire-signed-trace/15-arxiv-techniques-2023-2026.md)
reads the SOURCES of 20 papers (2022--26): fixed `q` is untouched, and
Hu--Teyssier arXiv:2502.11060 answers note 14 sec. 11.4 NEGATIVELY (their
graded Betti recursion gives `2^{Theta(j log j)}`; the budget series diverges).
Its three candidate findings were then checked and two were withdrawn.
(a) The `gcd(k,q^n-1)` lever of arXiv:2307.01344 is real per character but
does NOT lift: single-position characters number `~2 j ln j` against `2^j`
(`2^{-1011}` of the dual at `j = 1024`), and the lemma's power-map proof IS the
Adams action already barriered in note 06 (note 15 sec. 4).
(b) [Note 16](../../research/10-cas/lemire-signed-trace/16-large-q-threshold.md):
Bagshaw's `n`-independent `q`-threshold is INDIVIDUAL-modulus and admits the
non-squarefree `T^r`, but holds only at ODD `p` (standing hypothesis; the
mechanism is quadratic reciprocity), and `q > 7101 p^2` forces `l >= 3`, so
no prime field and no `q = p^2` qualifies -- smallest admissible `q = 3^11`.
The `p = 2` reframing is refuted.
(c) [Note 17](../../research/10-cas/lemire-signed-trace/17-cylinder-plancherel.md):
Sawin's sparsity+Plancherel DISPROOF template cannot refute `(CYL)` -- `Z = 0`
at all 26 endpoints (a proof, not a measurement, where `A_1` is odd), and
`|K| < 8 ell` caps the forcing at `sqrt(8 ell)` against an rms that is
`Theta(ell 2^{-ell/2})` of the threshold (`3e25` short at `ell = 200`). The
public PDF's `(CYL)` claim is confirmed verbatim and extended to `ell >= 12`.

**Next:** the lane is at a natural stopping point -- every route now ends at a
named open statement, and the deliverable is the map plus the re-posed
specialist question (notes 10, 14 sec. 10--11). If work resumes, the one
decisive computation is note 14 sec. 10 (`Z[zeta_16]` engine, `delta(2j+1,j)`
for `j = 8..10`), which separates the alive law `delta ~ j` from the dead
`delta ~ 2j`; angles 1 and 5 remain unrun and are subordinate to it. Nothing
in this lane is a proof of the conjecture.


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

**Asymptotic-calibration correction:** the `ell <= 24` exact dumps cannot
test the large quotient in candidate A. Their cutoff is `Q=1`, and every
nonresonant `q >= 8` row has `R <= 8`. At the first theorem row `ell=200`,
`Q=8`; its first unpaid nonresonant row `(j,q)=(199,16)` has
`R=2^(floor(198/8)-floor(198/16))=4096`. The existing rows are therefore
valuable to falsify fibrewise claims but not evidence for a uniform large-`R`
bit-balance theorem. A relevant scaled probe must retain `(j/q,R)`, target
the identity path, and separately cover the resonant direct-discrepancy rows.

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
The original conjecture citation was corrected too: it is Lemire's 2011
MathOverflow question, not the unrelated Kaser--Lemire hashing preprint
`arXiv:1202.4961`; the proposed degree-`<=2` construction in an MO answer is
over the integers and fails over `F_2` already at `x^5+x+1`.
The minimal sufficient statement is now the open fact
`F:gf2-lemire-cylinder-twist-sup-bound` (empty evidence, by design). The
theorem state is unchanged: Lemire's conjecture is not proved.

**Rung 3 (lemire-signed-trace, 2026-08-21 night):** data closed at `ell=24`
(both endpoints; worst open-layer ratio `0.12..0.19x` threshold, twisted-sum
sup over all 131072 cylinders `0.21..0.31` of `2^{ell-1}`). Three parallel
mechanism attempts (note 02 section 5): the Witt-digit tower yields an exact
carry calculus (`c_k = ab(a+b)^{2^k-2}`, checked) but no inequality; the
coset-product Weil polynomial has exact integral power sums and Newton
polygons but the `Q^k` construction shows no generic invariant can force the
saving; additive/multiplicative and constructive routes are closed. The
remaining step is a single open statement, `F:gf2-lemire-cylinder-twist-sup-
bound`, at the edge of every known method; the next rung needs a new input
that controls a constrained character sum over a sparse set of size `2^{n/2}`.

**Rung 4 (lemire-signed-trace, 2026-08-22):** candidate B's apparent
degree-doubling relation is now exact and closed.  For polynomial Liouville
`lambda(P^r)=(-1)^r`, Euler products give `L(lambda chi,u) =
L(chi^2,u^2)/L(chi,u)`, hence `S_m(lambda chi)+S_m(chi) =
1_{2|m} 2S_{m/2}(chi^2)`.  The direct prime-power checker
`lemire_adams_check.py` verifies all 620 instances for every character of
`E_j`, `j<=5`, `m<=10`.  This does not transport `(HWO)` to an easier degree:
`lambda chi` is not a Hayes character, its new weighted sum is exactly the
uncontrolled companion term, and squaring does not preserve exact conductor.
The Hsu/Voloch forward citation graph was also checked to 2026; later work
retains the logarithmic prescribed-coefficient gap or treats only boundedly
many coefficients.  No endpoint theorem was found, and the open fact is
unchanged.

**Certified finite handoff extended to n<=3000 (2026-08-22).** One monic
irreducible with `deg(f - x^n) <= floor(n/2)` for every degree `401 <= n <=
3000` (1334 trinomials, 1266 pentanomials), produced by the branch CAS
`axeyum-gf2-search` and verified by `axeyum-gf2-check` -- every row passed
BOTH the primary Frobenius/Bezout certificate and the independent re-check
(2600/2600, 0 failures), plus an independent flint re-verification of a
204-degree sample. Table:
`scripts/lemire-signed-trace/data/witnesses-401-3000.txt`. This raises the
finite-handoff insurance from `n<=400` to `n<=3000` (covers any future
effective threshold `ell <= 1499` on the open estimate); it does not touch
the open estimate, which is uniform in `ell`.

**Five "of course" shapes closed and an unconditional theorem landed
(2026-08-22).** Five Opus agents each took one candidate solution shape
(small virtual Witt-tower trace; horizontal Sato--Tate/automorphy; 2-adic
arithmetic uncertainty; manifest positivity; Clifford-hierarchy aggregate
cancellation): all negative, each with exact new facts and a precise
obstruction (note 04). The Fourier-uncertainty reading is now made rigorous
as a barrier lemma (note 03 section 5): an explicit nonnegative fake
population with the true low-conductor Fourier data, Weil-admissible high
moduli, and empty identity class, so moduli-only methods provably cannot
prove `(REL)`. A separate agent proved the unconditional almost-all theorem
(note 05): all but `< 4 ell^2 2^{-ell}` of the `2^ell` top-half patterns are
realized by an irreducible, sharp constant `ell^2-4ell+6`; Lemire is exactly
the residual claim that the one named all-zero pattern is not exceptional. The
public companion PDF `lemire-almost-all.pdf` carries Theorems A/B and the
barrier; the roadmap PDF carries the AP/Witt restatement, `(CYL)`, and the
generic-invariant obstruction. Theorem state unchanged: Lemire is not proved.

**Three post-barrier approaches worked (2026-08-22, Opus agents).** After the
moduli barrier, the almost-all trichotomy left three admissible input types;
all three are now investigated. (1) The **almost-all theorem** is proved and
machine-checked (note 05): all but `< 4 ell^2 2^{-ell}` of the `2^ell` patterns
are realized; public companion PDF `lemire-almost-all.pdf`. (2) The **symmetry
route is a second barrier** (note 06): no degree-preserving symmetry has an
orbit of the identity class `> 2` (Borel of `PGL_2(F_2)` + Adams; Hecke
transitive but degree-shifting), machine-checked `3 <= ell <= 8`. This
corrected a real error -- translation `x -> x+1` does NOT fix the identity
class in general (it sends `1 -> <(1+x)^n>_ell`, verified `N`-preserving) --
fixed in notes 05/06 and the public PDF. (3) The **phase-aware covariance**
(note 07) is measured exactly: aggregate `C/D ~ 0` (random), median `~ -0.55`
(bulk-negative), unbounded-above tail (so `|C| <= (1-eps)D` uniformly is
false); pair correlation pseudorandom; and a new exact fact -- the Witt carry
formula collapses to Weil above the Kerdock level, boundary `s-1 = 1`. The
cylinder form carries doubly-exponential margin (weaker than `(HWO)`'s
`4 ell`), but is unreachable now: fixed-`q` pair correlation is unproved
(integer analogue conditional, function-field analogues all `q -> infinity`).
Theorem state unchanged: Lemire is not proved; the two barriers plus the
almost-all theorem narrow it to exactly one unblocked analytic target.

**Construction barrier (note 09) and synthesis (note 00), 2026-08-22.** The
fourth side is closed: every provable irreducibility-preserving construction
multiplies the degree, so window families are lacunary (density zero) and no
finite union covers a residue class (Barrier III, machine-checked; honest
scope -- the known toolbox, not a logical impossibility; a new
arithmetic-progression seed would evade it, but the `sqrt n`
prescribed-coefficient ceiling at `q=2` shows none is within reach). Note 00
is the synthesis: two proved theorems (almost-all note 05; family `n=2*3^k`
note 08), three proved barriers (moduli note 03, symmetry note 06,
construction note 09), the one unblocked analytic target isolated (note 07,
with the carry-collapse boundary), certified to `n=3000`. Every side goes as
far as it can and stops at the same wall -- a phase-aware fixed-`F_2`
pair-correlation estimate, open for the reason its integer analogue is open.
Theorem state unchanged: Kaser--Lemire is not proved for all `n`.

<!-- plan-section: landed-changes -->
