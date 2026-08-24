# AC-Bridge 23 (phase 3): assembling the standalone artifact

Charge: assemble the phase-1/2 proved corpus into a standalone novel-mathematics
artifact, `30-paper-draft.md`, re-deriving every proof rather than copying it,
downgrading anything whose diary sketch has a gap, and reconciling against the
parallel phase-3 verifier (`20-verify-chains.md`) and assault diaries
(`21-supl-assault.md`, `22-cdl-assault.md`).

Date opened: 2026-08-20T17:40-04:00.
Worktree: `/home/mjbommar/projects/personal/axeyum-gf2-lemire`, branch
`agent/gf2/lemire-proof`.
Write scope: this file and `30-paper-draft.md` only.  No source file, no
example, no git mutation.

Epistemic labels are the charter's.  This file records **decisions**: what went
in, what was downgraded, what was excluded, what I re-derived differently from
the diary, and what I could not do.

## Log

### 17:40 -- required reading

Read in full: `00-charter.md`; `10-angles-board.md`; `04-weak-target-verification.md`
(716 lines); `11-angle-cab.md` (859); `13-angle-dichotomy.md` (832);
`14-angle-rank-arf.md` (761); the Lemma-W sections of `12-angle-wild-hm.md`
and `02-lit-energy-fourth-moments.md`; the `(WICK)` section of
`05-resurrection-audit.md`; the reference lists of `01`, `02`, `03`.
Also read, to pin definitions the diaries assume rather than state:

* `crates/axeyum-cas/src/gf2_hayes.rs:13475-13560` (`accumulate_binary_dyadic_shift_fibres`)
  and `:14045-14135` (`binary_dyadic_autocorrelation_fibre_report`) -- needed to
  write down diary 14's fibre family precisely enough to prove anything about it;
* `docs/research/10-cas/lemire-half-degree-irreducibles.md:160-215` (the exact
  `L`-degree distribution `d_h = 2^h`, `D = (ell-2)2^ell+2`) and `:2386-2470`
  (the conductor telescope, the translation-paired level, `low_conductor_weil_split`)
  -- these are the lane facts the diaries import as "proved".

`20-`, `21-`, `22-` did not exist at the start of this run.  Reconciliation pass
at the end.

### 17:50 -- naming decisions

Three collisions had to be resolved before anything could be written down.

1. **"Lemma W" is used for two unrelated statements.**  Diary 02's is the
   `sup ||f||_4/||f||_2 = M^(1/4)` weight-blindness lemma; diary 12's is the
   characteristic-free singular-locus bound.  Renamed **Lemma WB** and
   **Lemma SL** respectively, and numbered 2.35 and 2.36 in the artifact.
2. **`D1 ... D5` is used twice.**  Diary 13 uses `D1, D2, D3, D4, D5` for the
   `C_j` step / the `q`-product / the dichotomy / the increment / the
   sufficiency lemma; diary 14 uses `D1, D1a, D2, D3, D4, D6` for shift
   stability / the corrected `E2'` identity / the orbit theorem / square
   divisibility / surjectivity / the completion identity.  Everything is
   renumbered sequentially (`2.1 ... 2.36`, `3.1`) with a provenance table in
   section 1.6 mapping back.
3. **`mu` is used both for the Moebius function and for the class mean
   `2^(n-ell)`.**  The charter fixes `mu = 2^(n-ell)`, so the Moebius function is
   written `mob` throughout the artifact.  This one is not cosmetic: diary 14's
   `eps(m) = mu(f_m) mu(f_(m+h))` and diary 04's `mu - Pi_n` are two different
   `mu`s three lines apart in the same corpus.

### 18:00 -- re-derivations: what changed against the diary text

Everything in section 2 of the artifact was re-derived from the definitions.
Fifteen proofs came out identical to the diary; the following did not.

**(a) Corollary 2.6 (WK): diary 04's `<=` must be `<`.**  Diary 04 states
`K_4 <= 2^ell (mu-P_n)^4 - 3 (mu Sigma)^2`.  Chasing it through gives
`2^ell M_4 <= 2^ell (mu-P_n)^4`, i.e. `M_4 <= (mu-P_n)^4`, and Theorem 2.4 needs
a **strict** inequality (equality leaves `N_n(1) >= Pi_n`, i.e. `I_n(1) >= 0`).
Stated strictly in the artifact, with the integrality refinement
`M_4 <= (mu - Pi_n - n)^4` noted as the alternative repair.  **Downgrade: none;
correction only.**

**(b) Remark 2.16a: diary 11's sensitivity claim is wrong.**  Diary 11 says the
(SUP-L) crossover "moves by one level per doubling of `K`".  Its own table
contradicts this (`K = 2 -> 4` moves `22 -> 25`).  I recomputed the crossovers
independently in 80-digit decimal (`cross.py`, below) and reproduced diary 11's
table **exactly** for `K in {1.6, 2.0, 2.5, 4.0}`, then extended it:

```text
   K      odd   even          K        odd   even
  1.6      21     19          8.0       28     25
  2.0      22     20         16.0       31     28
  2.5      23     21         64.0       36     33
  4.0      25     23         10^3       45     43
                             10^6       67     65
```

so the cost is about three levels per doubling, and the qualitative conclusion
("insensitive to the constant") survives in a stronger form than diary 11 claimed
-- `K = 10^6` still closes from `ell = 67`.  Corrected in the artifact.

**(c) Theorem 2.29(3): diary 14's dimension formula is right, but its proof
sketch is not the proof.**  Diary 14 cites the lane's "proved truncated
Artin--Schreier kernel dimension" and asserts
`dim T_h = [v+1 if 2v < r-v else floor((r-v)/2)] + max(0, d-(r-v)+1)`.  My first
attempt to re-derive it by computing the rank of `tau -> tau^2 + h tau` on the
basis `{x^j}` gave a **different and wrong** answer, because for `j = v` the
leading terms of `x^(2v)` and `h x^v` cancel.  I then did the case analysis on
`v(z)` directly and recovered the diary's formula exactly, including the switch
at `2v = W`:
* `2v < W`: case `v(z) < v` is **empty** (it would need `v(z) >= ceil(W/2) > v`),
  and `K = {v(z) >= W-v} (+) F_2 h`, dimension `v + 1`;
* `2v >= W`: `K = {v(z) >= ceil(W/2)}`, dimension `floor(W/2)`.
Checked against the measured histogram at `ell = 9, d = 8`
(`2:128, 4:64, 6:56, 7:6, 8:1`, 255 shifts): the formula reproduces it exactly,
including the two levels (`6` and `7`) that pool three and two valuation classes.
The `+ max(0, d-W+1)` term needs `d >= W-1`, which holds for every `v >= 1` at
the charter's `d = ell-1`; noted in the artifact.  **Result: PROVED as stated,
with the proof written out (so (I3) is re-derived, not imported).**

**(d) Lemma 2.31 (diary 14's Lemma D4): the diary's containment is wrong at
large `v`, and its corollary is false at small `ell`.**  Diary 14 writes
`T_h contains span{x^j : max(1, ell+1-2v) <= j <= d}` and concludes
"dimension `min(2v-1,d) >= 3`".  The correct lower endpoint is
`max(v+1, ell+1-2v)`, and at `v = ell-1` the diary's span is empty while `T_h` is
in fact everything.  I restructured the proof into the two regimes of
Theorem 2.29(3) and proved only what is needed -- that `T_h` contains **two
consecutive powers** `x^j, x^(j+1)`, which is enough for surjectivity of
`(lambda_1, lambda_2)` -- and verified both regimes for every `v >= 2`,
`ell >= 4`.  Separately, diary 14's corollary "`n = 2` exactly when `v = 1`,
`n >= 4` when `v >= 2`" is **false** at small `ell`: at `(ell,v) = (5,2)` the
dimension is `3`, at `(4,2)` it is `2`.  The artifact drops the dimension claim
and keeps the one that matters (`v >= 2` implies not zero-free), which survives
those cases.  **Partial downgrade: the dimension characterisation is not
asserted; the conclusion is.**

**(e) Model 2.34 (diary 14's `(R1a)`): DOWNGRADED from "partially proved" to
heuristic.**  Diary 14 says "the proof is complete on the full polynomial domain;
what remains is the equidistribution sub-lemma".  It is not: the step
"the doubly-squarefree density for shift `h` is at most `prod_p b_p(h)`" treats
the conditions `p^2 | f` and `p^2 | f+h` as independent across `p`, which is a
sieve statement with an error term that the diary does not supply.  A complete
proof of the *upper* bound is available by a truncated sieve with CRT
equidistribution below a slowly growing cutoff, but it is not written out
anywhere in this corpus, so I did not claim it.  The artifact states the Euler
product as a **prediction**, records the exact agreement (`8/9` predicted,
`0.8888 +- 0.0002` measured, and the two shift strata splitting in the exactly
predicted ratio `2/3`), and separately states the part that **is** proved: the
`p = x+1` factor, exactly, from Lemmas 2.30-2.31.

**(f) Theorem 2.11(b) (`V_2` exact) now carries a named hypothesis.**  Diary 11
derives `V_2 = 2^(n-ell+1)` from "deg L = 1, hence `|S_chi| = 2^(n/2)` exactly".
That needs the level-2 `L`-polynomial to be **pure** of weight one -- no trivial
zero -- which is a real hypothesis over `F_2`, where every Hayes character is
even.  Isolated as **(I1')** and used in exactly two places (`V_2`, and the new
Proposition 3.1).  Nothing in the main chain depends on it.

**(g) Theorem 2.36 (Lemma SL) keeps diary 12's own OPEN(bk) flag**, restated in
the artifact rather than buried.  I did not close it.

**(h) Proposition 2.8 is stated grading-free.**  Diary 05 proves
`sum P = 3 M_2^2` for the convolution-order grading and diary 11 re-proves it for
the conductor grading.  The proof uses only `sum_a T_a = D`, so the artifact
states it once, for an arbitrary grading, and derives both instances.  This is
the honest form: what is special about the conductor grading is not the *signed*
Wick total, which is grading-free, but the fact that every individual pairing is
**nonnegative** (Proposition 2.9), so that the signed and absolute totals
coincide.

### 18:20 -- one new result

**Proposition 3.1** is not in any diary.  While writing section 6.3 I noticed
that the trivial bound on `kappa_j` is `2^((j-1)/2)`, so:

* `K = 2` is exactly the trivial bound at `j = 3` -- and the global maximum of
  diary 11's 341-pair table is `2.0000` at `(ell,n,j) = (11,24,3)`.  **The
  headline number of the (SUP-L) evidence table is the trivial bound, attained.**
  It is not evidence for (SUP-L); it is a witness that no cancellation at all is
  available at `j = 3` in that row (all four level-3 characters saturate Weil and
  align in phase).
* `j = 2` is a *theorem*: `G_ell/H_2 ~ Z/4`, its two faithful characters are
  complex conjugates, so `D_[2](e) = 2^(1-ell) Re(S_chi conj(chi(e)))` and
  `chi(e) in {1,i,-1,-i}` gives
  `max_e |D_[2](e)| = 2^(1-ell) max(|Re S_chi|, |Im S_chi|)`.  With
  `|S_chi| = 2^(n/2)` (I1'), `kappa_2 = 2^(1/2) max(|Re|,|Im|)/|S|` lies in
  `[1, 2^(1/2)]` -- **exactly** the measured `min = median = 1.0000`,
  `max = 1.4142`.

So two of the ten rows of the (SUP-L) evidence table carry no information, and
the artifact says so in section 6.3.  This materially changes how the evidence
should be described, and it is the single most useful thing this workstream
found that was not already in a diary.

### 18:30 -- what was excluded, and why

* **All `(GR-2)` .. `(GR-7)` verdicts (diary 14, diary 03).**  These are
  refutations of candidate statements, not part of a proved corpus.  The
  *mechanism* behind the refutation is kept (Lemmas 2.30-2.31, Corollary 2.32),
  because it is proved and because it explains the measurement; the verdict table
  is summarised in one line of section 6.5.
* **Diary 12's Hast--Matei budget arithmetic and the `(HM4-2)` retirement.**  Not
  a proved mathematical statement; it is a strategic verdict.  Kept as the scope
  note on Theorem 2.36 and one paragraph in section 6.
* **Diary 13's Green--Sawhney import refutation** and **diary 13's `(L2-3)`
  refutation**.  Both are refutations of imports; they belong in related work
  (section 4.3) and in section 6.5, not in the corpus.
* **Diary 11's `(CAB-const)` fallback** (`A <= c M_2^2` with `c ~ 1900`).  It is
  a measured statement with no proof and it is strictly weaker in usefulness
  than `(CAB-L)`; keeping it would have added a fourth open conjecture without
  adding a route.  Excluded; one line in the (E-2) discussion.
* **Diary 04's `(E2')` / `(S)` tables (22 rows).**  The split is demoted by
  diary 14 itself to "the cheapest available falsification instrument", not a
  route; the corrected identity (Corollary 2.28) is what is worth keeping, and it
  is kept.
* **Diary 13's `(INC-CYL)` collision refutation** is kept, but moved into the
  honesty section (6.2) rather than the corpus, because its content is a
  *barrier*, and barriers belong with the honest accounting.
* **All `M_4` growth-law fits, `R_0 -> 3`, `sum_j q_j -> 1.26`, the
  `(j-2)/(ell-2) 2^(j-ell)` mass law.**  Kept as evidence tables in section 3,
  never as claims.

### 18:35 -- computations run in this workstream

Only re-verification; no new example files were written (the charter permits new
`acb_*` examples, but nothing here needed one).

```sh
# scratchpad/cross.py  -- (SUP-L) crossovers, 80-digit decimal
#   reproduces diary 11's K = 1.6/2.0/2.5/4.0 table exactly, extends to K = 10^6
# scratchpad/cross2.py -- Sigma(ell) closed form checked for 1 <= ell <= 400;
#   (WK) right-hand-side positivity crossovers (odd 14, even 13) and
#   R_0^suf > 4 crossovers (odd 15, even 13), reproducing diary 04 independently
```

Both are pure Python with `decimal`, run in under two seconds, and are the only
numbers in the artifact that this workstream produced itself.  Every other number
is quoted from a phase-2 diary **with its example program and parameters
attached**, as the charge requires.

### 18:40 -- the prior-art search, and its failure

The charge requires a `WebSearch` for prior art on each headline claim.  **The
session's `WebSearch` budget was exhausted (200 of 200 calls) before this
workstream started**, and every call returned the budget message rather than
results.  I fell back to the arXiv API through `WebFetch`, which works, and ran
eight queries; the results are recorded verbatim in section 4.6 of the artifact.
Summary:

```text
  "conductor filtration" + "character sums"                          0 entries
  conductor + equidistribution + Dirichlet characters + function field 0 entries
  conductor + Hayes + character sums                                 0 entries
  "dyadic martingale" + "fourth moment"                              0 entries
  "short interval" + "fourth moment" + "function field"              1 (Yiasemides)
  "von Mangoldt" + "short intervals" + "function field"              2 (Hast-Matei,
                                                                       Kuperberg-Lalin)
  "Chowla" + "function field"                                       10, all large-q
  "irreducible polynomials" + "prescribed coefficients"              5, Gao et al.
```

I also re-fetched Sawin--Shusterman (arXiv:1808.04001) to try to settle whether
its "simple condition" on `q` admits `q = 2`; the abstract does not state the
condition, so it remains **UNVERIFIED**, exactly as diary 14 left it.

**Decision.**  This is a weak negative and the artifact says so.  Section 6.4
states the priority claim at the strength the evidence supports: the proofs are
re-derived and correct, the combination survived a weak arXiv-abstract search and
the phase-1 sweeps, and **whether the combination is new is UNVERIFIED**.  A
proper priority search is listed as a prerequisite for any external novelty
claim.  I would rather ship that sentence than a novelty claim I did not earn.

### 18:45 -- the export appendix

Eight targets, chosen by the rule "export the algebraic skeleton, never the
arithmetic".  The two I think are actually worth admitting first:

* **(X3)**, the involution lemma behind `E_1 = 0`: `f(s a) = f a`,
  `g(s a) = - g a`, `s` an involution, implies `sum_a f a * g a = 0`.  Completely
  general, no arithmetic, two lines in Lean, and it is the exportable core of the
  only unconditional *new arithmetic* result in the artifact.
* **(X5)**, `0 <= q_j <= 1`: the only inequality in the entire (D-PROD) machine,
  everything else there being an identity.  `u^2+v^2 <= (u+v)^2 <= 2(u^2+v^2)`
  for `u,v >= 0`, summed.

The appendix ends with an explicit statement of what a green Lean run would
**not** establish -- (I1), (I2), Corollary 1.2, Theorem 2.11, (SUP-L), (CDL) --
because a "Lean-verified" label on this artifact would otherwise be read as
verifying the endpoint.  No Lean was run.

## Reconciliation with the parallel phase-3 diaries

### Pass 1 (18:50)

`20-verify-chains.md`, `21-supl-assault.md` and `22-cdl-assault.md` do not exist
in the directory.  Nothing to reconcile yet.

### Pass 2 (19:10) -- `20-verify-chains.md` landed; full reconciliation

The verifier's 29-entry table was read in full and every entry checked against
the artifact.  **20 CONFIRMED, 7 GAP, 2 FALSE.**  Both load-bearing chains are
CONFIRMED end to end including every constant; the verifier reproduced all eight
`K in {1.6, 2.0, 2.5, 4.0}` crossovers at 80 digits, which is now a *third*
independent computation of them (diary 11, `cross.py` here, `acb_ver_supl`).

Actions taken, one per entry that required one.

**(1) Entry 23 -- diary 12's Lemma W: PROVED label WITHDRAWN at `m >= 4`.**
This is the largest change the reconciliation forced.  The verifier exhibits a
real hole: the third case of the Jacobian argument is stated as
"`u != 0` with `|V| >= 2`, **or** `u = 0` with `|V| >= 3`", and then
dimension-counted as if `z_1 in T_s` -- which is forced in the first sub-case
and **vacuous** in the second, where `u^T A_1 = 0` says nothing.  I re-derived
the count for the missing component: `dim <= n + 3 delta + (m-4)(h+1)`, so
`codim >= 3(h+1) - 3 delta`, which reaches `2h+3` only if `h >= 3 delta` -- not
the advertised `2 delta <= h+1`.  At the odd endpoint `h = ell` and diary 12's
own `delta >= ceil(ell/2) - 2` give `3 delta > ell` for every `ell >= 13`, so
the hypothesis does not cover it.  The sub-case cannot occur at `m = 3`
(`|V| <= 2` there), which is why the lemma reads correctly at `m = 3` -- and
`m = 4` is the only case this project uses.
I had copied diary 12's case structure and inherited the hole; my own
re-derivation did not catch it, which is exactly what an adversarial verifier is
for.  Theorem 2.36 in the artifact now reads **PROVED for `m = 3`, GAP at
`m >= 4`, statement not claimed there**, with the corrected fourth case written
out, and section 6.4 item 6 and section 6.6 item 6 say so.

**(2) Entries 13-14 -- the (SUP-L) evidence.**  The verifier and I reached the
same conclusion about the `2.0000` maximum by different routes (my
Proposition 3.1(a): `kappa_j <= 2^((j-1)/2)`, so `K = 2` is the a-priori ceiling
at `j = 3`; their route: `V_3` saturates the Weil envelope at `(11,24)` and all
four level-3 characters align in phase **at the identity class**).  But they
found something I did not: diary 11's per-level table prints **even `j` only**,
and the maximum over the *open* levels `j >= 4` is `1.9922` at `(ell,n,j) =
(11,24,5)` -- a `0.4%` margin, not the quoted `31%` (which is `2/1.5234`, over
`j >= 6`).  Added as **table (E-1b)** with the verifier's provenance, and
section 6.3 is rewritten around it.  This materially weakens the case for
(SUP-L) with `K = 2` and it should be the headline number, not `2.0000`.

**(3) Entry 22 -- (WK) strictness.**  Independently found by both; already fixed
in the artifact (Corollary 2.6).  No further action.

**(4) Entry 27 -- diary 14's Lemma D4.**  Independently found by both, with the
same repair.  The verifier's explicit witness (`ell = 13, v = 5, h = x^5,
tau = x^4`, where `v(tau)+v(tau+h) = 8 < 9`) is now quoted in section 6.5, since
a witness is worth more than a description.

**(5) Entry 19 -- (TWIST).**  Correct form is `S_(psi chi^(-1))`, not
`S_(psi chi)`.  I had copied diary 13's version; re-derived it and the verifier
is right.  Fixed in section 3.2 with a note that the sum over all `psi` makes
`|fhat(chi)|` insensitive to the error, which is why it survived.

**(6) Entry 12 -- (CAB)/(CAB-L) stated against the insufficient budget
`2^(ell+4(n-ell))`.**  The artifact never states those candidates, and table
(E-2) is explicitly against the diary-04 budget -- but I had quoted diary 11's
*closure* column (audit budget) rather than its *strict* column for the `A_L`
row.  Corrected to the strict column, which differs materially only on the even
rows below the (WK) crossover (`ell = 8` even becomes `inf`, `ell = 12` even
`0.000665 -> 0.002168`).

**(7) Entries 28-29 -- two FALSE verdicts on bridges between the conjectures.**
Neither is claimed in the artifact, but they strengthen section 3.3, so both are
now quoted there with their witnesses: "`q_j <= 1` implies (SUP-L) at some
levels" has an exponential deficit (`208x` at `j = 2`, `3.3x` at `j = ell`, at
`(11,24)`), and the best layer-to-`E_j` transfer between (SUP-L) and (CDL) is
worse than trivial.  So "incomparable" is now measured, not asserted.

**(8) Entry 24 -- the `s = h` identification in diary 14's Lemma D1.**  The
artifact's section 2.6 setting defines `h := x * s(x)` and `f_(m xor s) = f_m + h`
explicitly before Lemma 2.27, so the non-sequitur the verifier flags is already
absent.  No action.

**(9) Entry 7 -- diary 11's Lemma 7 displayed multiplier is a typo.**  The
artifact's Theorem 2.12 derives the `1/4` with the factors accounted separately
(`2^(-4)` from the four halved components, `2` from the doubled class sum, `2`
from the prefactor), so the typo is not inherited.  No action.

**(10) Entries 1-11, 15-18, 20-21, 25-26 -- CONFIRMED.**  These cover Lemmas 1-7
of diary 11, the whole reduction chain, the `K = 2` arithmetic, Lemmas A and B,
the `q`-product identity, `E_1 = 0`, Lemma D5 and the `4.1 log2 ell` constant,
Theorem D2 and Lemma D3.  Nothing to change.  Noted in the artifact's front
matter and in section 6.4, since independent confirmation of the four items of
the candidate novel core is the strongest external evidence this corpus has.

`21-supl-assault.md` and `22-cdl-assault.md` had still not landed at the end of
this run; anything they find will need a further pass.

## FINDINGS

### (a) What made it into `30-paper-draft.md`

Thirty-eight numbered statements, thirty-seven with a complete proof written out
in the artifact and one (Theorem 2.36) proved only at `m = 3` and explicitly not
claimed at `m >= 4`:

* **Endpoint sufficiency** (from diary 04): Lemmas 2.1 (`Pi_n = 1` at odd
  endpoints), 2.2 (the even-endpoint bound, with every odd prime-power layer
  proved empty), 2.3, Theorem 2.4 (`(W4-exact) => I_n(1) >= 1`), Corollaries
  2.5-2.6 (the strict (WK)), Proposition 1.1, Corollary 1.2.
* **The conductor grading** (from diary 11): Theorem 2.7 (orthogonality),
  Propositions 2.8-2.9 (the Wick total, grading-free; and nonnegativity, which is
  what is special), Theorem 2.10 (the parity selection rule), Theorem 2.11 (layer
  energies), Theorem 2.12 (the exact `1/4`-per-level recursion),
  Propositions 2.13-2.15 and 2.17 (the reduction chain), and **Theorem 2.16**:
  (SUP-L) with `K = 2` implies the Lemire endpoint for every `ell >= 22` (odd) /
  `ell >= 20` (even), with the crossover table recomputed independently.
* **The multiplicative dichotomy** (from diary 13): Proposition 2.18,
  Theorem 2.19 (`R_0 = prod_j (1 + q_j)`, `0 <= q_j <= 1`), Theorem 2.20,
  Corollary 2.21, Proposition 2.22, and Theorem 2.23 (`E_1 = 0` at odd endpoints,
  by the translation involution -- the only unconditional new arithmetic input).
* **The order grading** (from diary 11): Lemmas 2.24-2.26, including the exact
  termination `sum_(d=1)^(ell-1) T_d = D` and hence the cell count
  `C(ell+2,4)`.
* **The dyadic fibre family** (from diary 14): Lemma 2.27, Corollary 2.28 (the
  corrected `sum_F c_F^2 = 2 N_sf + Theta` identity), Theorem 2.29 (fibres are
  complete `T_h`-orbits, with the dimension formula re-derived), Lemmas 2.30-2.31
  and Corollary 2.32 (forced square divisibility), Proposition 2.33 (the exact
  index-two completion `2 Delta = A + B`).
* **Two blindness lemmas**: Lemma 2.35 (WB, diary 02) and Theorem 2.36 (SL,
  diary 12) -- the latter **downgraded** after reconciliation to `m = 3`, with
  the fourth case of the argument written out and the `m >= 4` gap and its
  corrected hypothesis `h >= 3 delta` stated.
* **New here**: Proposition 3.1 (`kappa_j <= 2^((j-1)/2)` trivially, and
  `kappa_2 in [1, 2^(1/2)]` as a theorem).
* The two conjectures **(SUP-L)** and **(CDL)**, stated precisely, with five
  evidence tables carrying their example programs, parameters and ranges.
* Related work (verified citations with URLs), the export appendix, and an
  honesty section.

### (b) What was downgraded or excluded, with reasons

```text
  Theorem 2.36 (diary 12 Lemma W) PROVED label WITHDRAWN at m >= 4 after
                                  reconciliation with 20-verify-chains.md; the
                                  fourth Jacobian case needs h >= 3 delta, which
                                  FAILS at the odd endpoint for ell >= 13.
                                  Proved at m = 3; m = 4 is the case we need.
  Model 2.34 (diary 14 (R1a))     "partially proved" -> heuristic + exact
                                  sub-statement.  The sieve independence step is
                                  not supplied anywhere in the corpus.
  Theorem 2.11(b) (V_2 exact)     now conditional on the new named input (I1').
  Corollary 2.6 (WK)              stated strictly; diary 04's `<=` is not enough.
  Remark 2.16a                    diary 11's "one level per doubling" corrected
                                  to about three, by independent recomputation.
  Lemma 2.31                      diary 14's containment corrected; its dimension
                                  corollary dropped (false at ell = 4, 5).
  table (E-1) reading             diary 11's "31% margin" restated: the binding
                                  measured value is 1.9922 at (11,24,5), a 0.4%
                                  margin (table (E-1b), verifier entry 14).
  table (E-2) A_L row             switched from diary 11's audit-budget column to
                                  its strict diary-04-budget column.
  (TWIST)                         S_(psi chi) -> S_(psi chi^(-1)).
  (GR-2..7) verdicts              excluded (refutations, not corpus).
  (CAB-const)                     excluded (a fourth open conjecture, no route).
  (CAB)/(CAB-L) as named          excluded: as stated by diary 11 they use the
                                  budget 2^(ell+4(n-ell)), which yields only
                                  M_4 < mu^4, the refuted criterion.
  Green-Sawhney / (L2-3) refutations  moved to related work and honesty.
  (INC-CYL) collision refutation  moved to the honesty section as a barrier.
  all growth-law fits             kept only as labelled evidence.
```

### (c) The three things a reader should be most suspicious of

1. **The (SUP-L) evidence, which is much thinner than the corpus advertised.**
   After Proposition 3.1 two of the ten level-rows of the headline table are
   controls and the global maximum `2.0000` is the a-priori ceiling attained;
   after the verifier's entry 14, the binding measured value on the open levels
   is `1.9922` at `(11,24,5)` -- a `0.4%` margin below `K = 2`, from a table
   reaching only `ell = 12`.  If one number from this artifact is going to be
   quoted, it should be that one and not `2.0000`.
2. **The novelty claim.**  It is stated as UNVERIFIED and it should stay that way
   until a proper priority search is run.  The `WebSearch` budget failure is
   recorded in the artifact itself, not just here.
3. **Theorem 2.36.**  A diary label was withdrawn, not repaired.  If anyone wants
   the characteristic-free Hast--Matei replacement at `m = 4`, the fourth case
   (`u = 0`, `|V| >= 3`) is the whole job.
4. **(I1').**  Purity at level 2 is imported, is used for the exact `V_2` and for
   Proposition 3.1, and would be the first thing I would check if I were
   refereeing.

### (d) What I did not do

* No Lean.  The export appendix prepares statements; nothing was run or checked.
* No new measurement, and no row beyond what phase 2 computed
  (`ell <= 20` for the conductor layers, `ell <= 19` for the profile,
  `ell <= 14` for the fibre census).
* No attempt on (SUP-L) or (CDL) beyond Proposition 3.1 -- those are workstreams
  21 and 22.
* No proof of the sieve step in Model 2.34, and no closing of OPEN(bk) in
  Theorem 2.36.
* No verification of the lane's separately certified finite range through
  degree 400, which Theorem 2.16 leans on for `ell <= 21`.  It is cited, not
  claimed.

### Epistemic ledger for this file

**PROVED (arguments written out in `30-paper-draft.md`)**: all thirty-eight
numbered statements listed in (a), each with its hypotheses named -- in
particular which of (I1), (I1'), (I2) each one uses, and which are
unconditional (Lemmas 2.1-2.3, Theorem 2.4, Theorems 2.7, 2.10, 2.12, 2.19,
2.23, 2.29, Lemmas 2.24-2.27, 2.30-2.31, 2.35, Propositions 2.8-2.9, 2.13-2.15,
2.18, 2.33).

**CORRECTED, with the correction proved**: diary 04's (WK) strictness; diary 11's
`K`-sensitivity claim; diary 14's `T_h` containment and its dimension corollary;
diary 13's `(TWIST)` exponent; diary 11's `A_L` closure column.

**DOWNGRADED**: diary 12's Lemma W from PROVED to *proved at `m = 3`, GAP at
`m >= 4`* (the case this project uses), on the verifier's finding; diary 14's
`(R1a)` to a heuristic with an exact sub-statement; diary 11's `V_2` to
conditional on (I1'); diary 11's `31%` (SUP-L) margin to `0.4%`.

**NEW IN THIS WORKSTREAM**: Proposition 3.1, and the reading of the (SUP-L)
evidence table that follows from it.

**EVIDENCE ONLY**: every table in section 3 of the artifact, each carrying its
example program, parameters and range of validity.

**RECONCILED**: against `20-verify-chains.md` (29 entries: 20 CONFIRMED, 7 GAP,
2 FALSE); every GAP and FALSE is incorporated, and the three corrections both
workstreams found independently ((WK) strictness, Lemma D4's containment, the
`j = 3` ceiling) are marked as such.  `21-supl-assault.md` and
`22-cdl-assault.md` had not landed; a further pass is owed if they do.

**UNVERIFIED**: the novelty of the combination (weak arXiv-abstract search only,
`WebSearch` budget exhausted); Sawin--Shusterman's field condition at `q = 2`;
the lane's finite certification through degree 400.

**NO THEOREM CREDIT** is claimed for the Lemire endpoint or for any uniform
estimate.
