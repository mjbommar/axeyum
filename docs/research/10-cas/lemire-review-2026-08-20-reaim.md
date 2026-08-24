# Lemire endpoint: external review and re-aim proposal

Date: 2026-08-20
Author: second-opinion review (Claude), requested by the project owner
Status: ad hoc research handoff. This challenge is deliberately outside the
normal Axeyum test suite and roadmap; nothing here changes lane gates,
PLAN.md, or the fact-ledger rules. It is a strategy review for the
`agent/gf2/lemire-proof` lane, written after reading the full lane status
(`docs/plan/status/52-gf2-lemire.md`), the canonical note
(`lemire-half-degree-irreducibles.md`), the bridges audit
(`lemire-proof-unblocking-bridges.md`), and the landed-changes ledger at
`4f083f52a`.

## Verdict in two sentences

The lane is not idle and its discipline is excellent -- no unearned theorem
credit, every shortcut closed with an exact witness.  But it is stuck in a
diagnosable way: the last ~100 commits follow one loop -- propose candidate
lemma, build exact CAS diagnostic, refute it or leave it open, propose the
next -- and every route terminates in a new open lemma of the same depth as
the original problem.  The status file itself says so: "the
characteristic-delta period lemma and the connected trace remain the two
honest universal frontiers."  That pattern is the signature of a genuine
barrier, not a missing trick.

## Why every analytic route dies in the same place

The lane's own ledgers quantify the wall precisely.  The needed discrepancy
bound is `abs(Delta) <~ 2^ell`; RH/Weil -- which is *proved* over function
fields -- gives `<~ ell * 2^ell`.  The entire remaining gap is **one factor
of `log n`, exactly at the square-root barrier**.

This is the function-field twin of "primes in `[x, x + sqrt(x)]`", which is
open in `Z` *even assuming RH*: RH-pointwise bounds saturate one log short of
the truth, and closing that log requires cancellation among the
zeros/characters themselves, which no known unconditional or
GRH-conditional technique supplies.  The ledgers rediscover this wall from
every direction:

- Bagshaw exponent pairs cover only the tail `d > (14/15) ell`;
- the honest energy column is `106/16` bits short at `ell = 300`;
- Cauchy across the top character family loses factors `304`/`633`;
- Hast--Matei's idealized second moment misses by squared ratios
  `(ell-1)/2` and `(ell-1)/4`;
- the relative Carlitz route needs a saving of about `8 ell` beyond relative
  Hasse--Weil.

No further Vaughan/bilinear/fourth-moment refinement will manufacture that
log; in `Z` the identical log has resisted everyone since Selberg.  The
candidate-lemma mining subprogram (Heisenberg cocycles, Kerdock families,
magic-square gcd strata, plateau spectra) has sharply declining expected
value.  Recommendation: close it explicitly with a stopping ADR so the lane
stops paying for refutations of its own guesses.

## Restart, or move up the chain?

**Do not restart.**  The reduction chain is sound, the negative-results
ledger is genuinely valuable, and a fresh lane would re-derive the same wall
at full price.  **Do re-aim.**  Three moves, in priority order.

### Move 1 (primary): elevate the 2-adic congruence route

This is the one direction in the ledger that bypasses analysis entirely, and
the lane has already tripped over it without promoting it.

The odd endpoint identity is exact: `N_(2ell+1)(1) = 1 + (2ell+1) I_(2ell+1)(1)`.
So the odd half of the conjecture is precisely the statement
`I_n(1) != 0` -- and the fleet run found `I_51(1) = 1315030 == 6 (mod 8)`,
with the "observed odd-count 2-adic nonvanishing" pattern surviving every
computed row, currently flagged in the status as "an unproved congruence."

A proved congruence of the form `I_n(1) !== 0 (mod 2^k)` -- or any exact
statement pinning `v_2(I_n(1))` below a computable bound -- **is the whole
odd-endpoint theorem**: positivity from exact algebra, with no square-root
saving needed anywhere.  It is also the right shape for this project:

- the candidate tools are Deuring--Shafarevich p-rank formulas for the
  Artin--Schreier--Witt / Carlitz conductor tower (the lane already built
  the relative-tower genus ledger and the quadratic-step chain);
- the Stickelberger/Swan machinery is already native and proved:
  `mu(f) = (-1)^degree chi_8(Disc(F))`, including squareful zeros;
- the objects are finite Witt-vector algebra -- exact, checkable,
  kernel-admittable, unlike any analytic saving.

Concrete plan, cheapest first:

1. Sweep `v_2(I_n(1))` (and `I_n(1) mod 8`, `mod 16`) across every existing
   fleet row and as many new odd `n` as are cheap.  Find the actual
   invariant: a fixed bound on `v_2`?  an explicit `c_n mod 8` depending on
   `n mod something`?  This costs almost nothing against data already
   computed and decides whether the route lives before any proof investment.
2. If a pattern survives, derive the candidate congruence from the exact
   2-adic slope decomposition of the new-layer trace on the exact-conductor
   filtration (NOT from Deuring--Shafarevich alone -- see the correction
   below; the lane's refuted "all supersingular" witness at level ten is
   consistent with this -- a congruence route wants the exact slope
   decomposition, not maximal divisibility).
3. Prove it, then attack the even endpoint by induction: the even
   endpoint's `k = 2` divisor term is `g^2 == 1 (mod x^(ell+1))`, which in
   characteristic 2 is `x^ceil((ell+1)/2) | g - 1` -- i.e. a **half-size
   Lemire-type count**.  So the even case plausibly inducts on odd/smaller
   cases with the certified range through 400 as the base.

Known risk, stated honestly: `v_2(I_n(1))` may be unbounded over `n`, in
which case a fixed-modulus congruence is false and the route needs an
`n`-dependent exact formula or dies.  Step 1 tests exactly this for pennies.

#### Correction (2026-08-20, from the lane): the 2-rank is zero, so p-rank
#### alone cannot carry the congruence

The lane's pushback is correct and the reviewer agrees.  For `q = 2` the
infinite place of the Carlitz cyclotomic cover is tame of index `q - 1 = 1`
(split), and the finite place `x` is totally ramified, so Deuring--
Shafarevich gives, at every level,

```text
gamma - 1 = 2^ell (0 - 1) + (2^ell - 1) = -1,   i.e.  gamma = 0.
```

Recovering `I_n mod 8` at the odd endpoint needs `Delta mod 8`, hence the
curve trace modulo `2^(ell+3)` -- far beyond what a p-rank (slope-zero)
count supplies.  So the target must be the **normalized near-half-slope
trace**, as the lane proposes.  Three sharpenings:

1. Zero 2-rank is structurally *favorable*, not just an obstruction: there
   are no slope-zero eigenvalues at any level, so the count's 2-adic
   structure is purely positive-slope and the minimal-slope stratum is the
   whole game.  An eigenvalue orbit of slope `lambda` contributes
   2-valuation `n*lambda` to the trace, so everything with
   `lambda >= (ell+3)/(2*ell+1)` vanishes mod `2^(ell+3)` automatically,
   and integrality forces the lower-slope strata to cancel to at least
   `2^ell` in aggregate.  The conjecture is an exact residue for the thin
   window that survives in between.
2. The existing fleet table already measures this window: from the
   `Delta` rows at `ell = 13..24`, `v_2(Delta)` is `0..7` -- the trace sits
   2-adically as low as integrality permits, i.e. the near-half-slope
   stratum is nonempty and tight in every computed row.  Pinning
   `v_2(Delta)` (not `Delta mod 8` directly) as a function of `(ell, n)` is
   the sharpest cheap invariant to sweep first.
3. Literature for exactly this object (verified by web search 2026-08-20,
   not from memory):
   - **Closest published technology**: Kramer-Miller, "p-adic
     estimates of abelian Artin L-functions on curves" (arXiv:2006.04936;
     single-author — corrected 2026-08-20 by the p-adic sweep agent, which
     also verified both this and the joint Kramer-Miller--Upton papers
     assume p >= 3 verbatim, so they do NOT apply at p = 2; see diary
     adhoc-blocker-sweep-2026-08-20/04-p-adic-geometry.md)
     and "Newton polygons of sums on curves I: local-to-global theorems"
     (published July 2024; part II, "Variation in p-adic families",
     arXiv:2110.08657).  These treat Newton-versus-Hodge polygons for
     general abelian covers of curves, with local-to-global vertex-contact
     criteria -- the tower here is exactly an abelian 2-group cover of
     `P^1`, wildly ramified at one point, so this is the right frame for a
     lower bound on the Newton polygon sharp enough to control the trace
     modulo `2^(ell+3)`.
   - Davis--Wan--Xiao, "Newton slopes for Artin--Schreier--Witt towers"
     (Math. Ann. 2016, arXiv:1310.5311): proved arithmetic-progression
     slope structure, but for `Z_p`-towers (rank one).  Ren--Wan--Xiao--Yu,
     "Slopes for higher rank Artin--Schreier--Witt towers"
     (arXiv:1605.02254, Trans. AMS) extends to `Z_(p^ell)` -- an unramified
     coefficient extension, still not the product-of-cyclic-2-groups
     Galois group here.  X. Li, "The stable property of Newton slopes for
     general Witt towers" (J. Number Theory) is nearby.  None applies
     verbatim; the exact-conductor filtration the lane already built is
     the multi-character bookkeeping these would need.
   - Demoted from the earlier draft of this note: Thakur's function-field
     Gauss sums (Inventiones, "Gauss sums for F_q[T]") carry a
     Stickelberger analogue, but the values live in characteristic `p` and
     the controlled valuations are `v`-adic/infinity-adic there -- not the
     characteristic-zero 2-adic valuations of Hayes--Frobenius eigenvalues
     needed here.  Adjacent at best; a 2025 preprint, "Geometric Gauss
     sums and Gross--Koblitz formula over function fields"
     (arXiv:2502.01109), and Hodge--Stickelberger polygon results for
     exponential-sum L-functions (arXiv:0706.2340) are the nearest
     relatives.

Concrete next experiment: the lane already has the exact integral
`Z[zeta_(2^r)]` Hayes `L`-polynomial evaluator with two NTT-prime controls.
Compute exact 2-adic Newton polygons per character at low conductors,
aggregate the minimal-slope mass by exact conductor, and check that it
reproduces the measured `v_2(Delta)` row by row.  That converts "normalized
higher-slope trace" from a phrase into a measured, conjecturable object
before any theorem work.

### Move 2: ship the paper that already exists

The lane already holds a publishable package with no new mathematics:

- the reciprocal equivalence (identity ray class mod `x^ceil(n/2)`);
- the classical near-endpoint theorem: every conductor level below
  `ell - ceil(log2 ell)` is discharged by exact Fourier inversion plus the
  individual Weil bound, i.e. `deg(f - x^n) <= n/2 + O(log n)`
  unconditionally;
- independently checked certificates through degree 400;
- two proved infinite families: the cyclotomic `Phi_(3^r)` degrees and the
  Capell towers (138 committed seeds generating 95 infinite 3-free degree
  rays);
- the complete characteristic-two Q-transform classification: the
  `x^3+x+1 -> x^6+x^3+1` pair is the *only* shaped irreducible exception --
  a clean standalone theorem;
- the Swan/Arf/`chi_8` Mobius identity and the parity-barrier proof for the
  half-level sieve.

"Lemire's conjecture: a near-endpoint theorem, infinite families,
verification to degree 400, and the exact obstruction" is a real paper
today.  Shipping it converts 212 commits into admitted, citable results and
produces the artifact needed for Move 3.

### Move 3: externalize the two reduced frontier lemmas

Two reductions are now crisp enough to state in one page each, and both are
proven-sufficient with replayable implications:

1. **Cyclic Betti bound.**  The cyclic/Foulkes compression proves that a
   uniform effective bound `B(n, r) <= n^4` for the specific cyclic rank-one
   local systems closes *every* degree past the certified 400 handoff
   (twelve base rows and a strict twelve-degree induction step are
   replayable).
2. **Relative Carlitz trace.**  The connected top-conductor trace is the
   point-count difference of two explicit Carlitz curves; the missing
   saving beyond relative Hasse--Weil is polynomial -- about `8 ell`
   (exactly `50641/32` at `ell = 200`).

These are precisely the language of Sawin, Gorodetsky, Entin, and
Bank--Bary-Soroker.  An expert can evaluate either statement in an
afternoon, and both possible answers ("here is the idea" / "that is as hard
as the original") are worth more than another month of internal
candidate-lemma mining.  The repository's role is to make the reductions
independently checkable; they already are.

## Literature verification sweep (web, 2026-08-20)

The first draft of this note was written from repository documents plus
model background only.  A web sweep was then run to check the frontier
claims; results:

- **No resolution or claimed proof of the Lemire conjecture found** under
  any framing (prescribed coefficients, short intervals, sparse high half),
  consistent with the canonical note's literature boundary.
- **The `q = 2` endpoint remains outside published bilinear technology.**
  Sawin's short-interval square-root cancellation (Duke 2021,
  arXiv:1809.05137) and squarefree-progression level of distribution
  (Acta Math. 2024, arXiv:2102.09730) both approach square-root savings
  only as `q -> infinity`.  Sawin--Shusterman's level of distribution
  beyond `1/2` (arXiv:1808.04001 and successors) requires `q > 29`.
  Bagshaw's weighted bilinear Kloosterman bounds (Canad. J. Math. 2024,
  arXiv:2401.10399) are the ones the lane already audited at equation
  level.  This confirms, from the outside, the lane's own conclusion that
  no published estimate closes the endpoint.
- The Move 1 literature list above was corrected accordingly: Kramer-Miller
  --Upton added as the closest tool, Ren--Wan--Xiao--Yu scoped precisely,
  Thakur demoted to adjacent.

## Ledger meta-point

`F-gf2-lemire-half-degree-all-degrees` should be treated as a long-horizon
open fact with *bounded* probes (the Move 1 congruence sweeps), not a lane
grinding daily against the square-root barrier.  The problem has been open
since Lemire posed it in 2011.  Moves 1 and 2 grow the trusted base now;
Move 3 buys outside leverage.

## Housekeeping observed during review

- `docs/research/10-cas/lemire-proof-unblocking-bridges.md` is untracked in
  the `axeyum-gf2-lemire` worktree; commit it.
- `/tmp/axeyum-lemire-altfields.5wVQlT/worktree` has an uncommitted edit to
  `crates/axeyum-cas/src/gf2_hayes.rs` sitting on the 81%-full tmpfs; one
  OOM kill from being lost.  Commit or copy it off RAM.
