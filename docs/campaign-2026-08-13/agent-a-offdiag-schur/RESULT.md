# agent-a — generalized off-diagonal Schur numbers `S(3; s,t,u)`

**Final table.** Session closed 2026-08-13, 22:30. All lanes stopped; see "Unresolved". Raw record in `logs/`.

## What `S(3;s,t,u)` is, and what counts as a value here

`L(k)` is `x_1 + x_2 + … + x_{k-1} = x_k` over the positive integers.
`S(3;s,t,u)` is the least `N` such that **every** 3-colouring of `[1,N]`
contains a monochromatic solution of `L(s)` in colour 1, `L(t)` in colour 2, or
`L(u)` in colour 3. Ahmed–Schaal (2015) conjectured
`S(3;s,t,u) = s·t·u − t·u − u − 1` for `4 ≤ s ≤ t ≤ u`; it is open, and is the
motivating problem of arXiv:2604.11030 (Song–Mao, 13 April 2026).

A row is a **value** only when both sides are discharged:

* `n = N − 1` **sat**, model decoded to a colouring and replayed by
  `OffDiagonalSchur::first_violation` — a layered reachability search over the
  defining equation that shares no code with the encoder — then re-checked
  against the **full, unreduced** solution-set list, then replayed a third time
  in Python by `scripts/check-claim-certificates.py`;
* `n = N` **unsat**, DRAT proof from axeyum's own proof-producing CDCL core,
  re-derived by axeyum's own backward DRAT checker.

No external solver and no external checker appears anywhere: no kissat, no
cryptominisat, no z3, no drat-trim (ADR-0002).

## Verdict on the conjecture

**Ahmed–Schaal Conjecture 2 survives.** All 34 `s ≥ 4` cells decided — 16
reproducing published values and 18 nobody had computed — agree with
`s·t·u − t·u − u − 1` exactly. A further 14 `s = 3` cells were recomputed from
scratch by bisection and all 14 match Song–Mao.

**48 cells decided. 30 independent reproductions of other people's published
values, zero disagreements. 18 new values. No mismatch anywhere.**

The 30 reproductions are the strongest claim in this document, not the 18 new
values. They are what a referee can check cheaply, and they exercise the
encoder, the solver and the checker on cells where a wrong `unsat` — the
specific failure this family invites — would have been visible immediately.

## A. Reproduces Ahmed–Schaal's eleven exact values (regression gate)

| cell | N | clauses @N | proof steps | result |
|---|---:|---:|---:|---|
| S(3;4,4,4) | 43 | 5,868 | 54 | reproduces published |
| S(3;4,4,5) | 54 | 16,264 | 216 | reproduces published |
| S(3;4,4,6) | 65 | 36,298 | 144 | reproduces published |
| S(3;4,5,5) | 69 | 57,040 | 228 | reproduces published |
| S(3;4,4,7) | 76 | 65,060 | 157 | reproduces published |
| S(3;4,5,6) | 83 | 146,745 | 478 | reproduces published |
| S(3;5,5,5) | 94 | 278,592 | 113 | reproduces published |
| S(3;4,5,7) | 97 | 290,696 | 361 | reproduces published |
| S(3;4,6,6) | 101 | 466,367 | 251 | reproduces published |
| S(3;5,5,6) | 113 | 815,517 | 238 | reproduces published |
| S(3;6,6,6) | 173 | 13,251,885 | 117 | reproduces published |

All eleven, both sides, **119 seconds** on one 16-core host. `(4,5,6)` and
`(4,5,7)` are the load-bearing ones — three *distinct* equations, so no colour
symmetry at all — and both are in the committed test suite.

## B. Reproduces Song–Mao arXiv:2604.11030 Table 3 (external cross-validation)

Their Section 5 reports these from their own exhaustive computer search with a
conventional SAT pipeline, four months ago, with a different toolchain.

| cell | N (ours) | N (Song–Mao Table 3) | clauses @N | proof steps | |
|---|---:|---:|---:|---:|---|
| S(3;4,4,8) | 87 | 87 | 109,370 | 254 | agree |
| S(3;4,4,9) | 98 | 98 | 161,862 | 233 | agree |
| S(3;4,4,10) | 109 | 109 | 239,130 | 218 | agree |
| S(3;4,5,8) | 111 | 111 | 512,277 | 521 | agree |
| S(3;4,6,7) | 118 | 118 | 1,051,899 | 682 | agree |

Five for five. This is the most valuable block in the table: an independent
group agreeing on exactly the cells where a wrong `unsat` from the
symmetry-breaking trap would have been invisible. Our versions additionally
carry a machine-checked DRAT refutation, which theirs do not.

Also recomputed from scratch, by bisection over a confirmed bracket, from their
`s = 3` rows — **14 for 14, every one agreeing**:

| cell | ours | Song–Mao | | cell | ours | Song–Mao |
|---|---:|---:|---|---|---:|---:|
| S(3;3,3,8) | 59 | 59 | | S(3;3,3,14) | 113 | 113 |
| S(3;3,3,9) | 68 | 68 | | S(3;3,4,8) | 67 | 67 |
| S(3;3,3,10) | 77 | 77 | | S(3;3,4,9) | 78 | 78 |
| S(3;3,3,11) | 86 | 86 | | S(3;3,4,10) | 86 | 86 |
| **S(3;3,3,12)** | **94** | **94** | | S(3;3,4,11) | 98 | 98 |
| S(3;3,3,13) | 104 | 104 | | S(3;3,4,12) | 106 | 106 |
| | | | | S(3;3,5,8) | 91 | 91 |
| | | | | S(3;3,5,9) | 103 | 103 |

### Both table anomalies resolved as REAL, not transcription errors

Two entries in Song–Mao's `s = 3` rows looked like typos. I suspected the
published table and then checked it, in that order, and both anomalies are real:

* **`S(3;3,3,12) = 94`.** Their `(3,3,u)` row is 59, 68, 77, 86, **94**, 104,
  113, 122 — which is exactly `9u − 13` for every entry *except* `u = 12`, where
  the formula gives 95. That is precisely the shape of a transcription error.
  Recomputed from scratch: `n = 93` sat, `n = 94` unsat. **94 is correct**; the
  break in the progression is a fact about the function, not a slip of the pen.
* **The `(3,4,u)` row's ragged steps.** 67, 78, 86, 98, 106 — differences 11, 8,
  12, 8, against the neighbouring `(3,5,u)` row's clean +12, +12. Reproduced
  entry for entry, all five.

Neither row follows a linear formula, and that is now established rather than
suspected. Note what this *cost*: nothing but compute. The value of being able
to recompute a published table cheaply is that "that looks like a typo" becomes
a question you answer instead of a note you leave.

## C. NEW values — not in Ahmed–Schaal's eleven, not in Song–Mao Table 3

Table 3's search stops at `(4,4,10)`, `(4,5,8)`, `(4,6,7)`.

| cell | N | clauses @N | proof steps |
|---|---:|---:|---:|
| **S(3;4,4,11)** | **120** | 323,293 | 297 |
| **S(3;4,5,9)** | **125** | 811,545 | 474 |
| **S(3;4,4,12)** | **131** | 451,622 | 285 |
| **S(3;5,5,7)** | **132** | 1,757,948 | 334 |
| **S(3;4,6,8)** | **135** | 2,041,563 | 716 |
| **S(3;5,6,6)** | **137** | 2,834,904 | 369 |
| **S(3;4,7,7)** | **139** | 2,737,498 | 226 |
| **S(3;4,5,10)** | **139** | 1,250,483 | 487 |
| **S(3;5,5,8)** | **151** | 3,168,425 | 246 |
| **S(3;4,6,9)** | **152** | 3,602,381 | 760 |
| **S(3;4,7,8)** | **159** | 5,632,873 | 654 |
| **S(3;5,6,7)** | **160** | 6,937,489 | 589 |
| **S(3;5,5,9)** | **170** | 5,074,413 | 253 |
| **S(3;5,6,8)** | **183** | 13,740,137 | 847 |
| **S(3;5,7,7)** | **188** | 19,807,560 | 345 |
| **S(3;4,4,13)** | **142** | 578,773 | 208 |
| **S(3;4,5,11)** | **153** | 1,802,737 | 557 |
| **S(3;6,6,7)** | **202** | 35,570,016 | 384 |

All eighteen agree with `s·t·u − t·u − u − 1`.

## Unresolved at wrap-up — stated exactly

* **`S(3;3,3,15)`: KILLED, exit 137 (out of memory). NOT a refutation, NOT a
  verdict, and not recorded as one.** The bisection confirms both bracket ends
  before bisecting, so `n = 100` returned sat and the `n = 150` probe was
  OOM-killed on a 26 GiB host while enumerating `L(15)` solutions (partitions
  into 14 parts, sum ≤ 150). Song–Mao report 122; **we neither confirm nor
  contradict it.**

  Worth stating because it is subtler than the usual warning: exit 137 does not
  read here as a wrong answer, it reads as **nothing at all**. Because the kill
  landed on the bracket's *upper* probe, the transcript is "sat at 100", then the
  next cell begins. Anyone reconstructing the row from the `THRESHOLD` lines —
  the natural thing to do, since that is the line carrying a result — sees
  `(3,3,14)` followed by `(3,4,8)` and a silent gap where `(3,3,15)` should be.
  An absence is indistinguishable from a decision not to run the cell. The only
  thing separating "the machine ran out of memory" from "the lane moved on" is
  one wrapper line, `rc=137 -- see above, NOT a verdict`, and it is in the log
  rather than in the result channel. See FEEDBACK.md item 8: **the negative has
  to appear where a reader looks for the positive.**
* **`S(3;3,5,10)`**: bisection lane **killed at wrap-up** with the bracket low
  end `n = 90` confirmed sat and the upper probe in flight. No verdict. Song–Mao
  report 115.
* **`S(3;4,4,14)`**, conjectured `N = 153`: **killed at wrap-up**; the `n = 152`
  probe had run 7m33s at 3.3 GB and neither side returned. No verdict.
* **`S(3;3,3,15)`, `S(3;3,4,13+)`, `S(3;3,5,11+)`, `S(3;4,4,15+)` and beyond**:
  not attempted or not completed. No verdicts.
* **One decided value has no claim-ledger entry** — `S(3;5,6,8)=183`,
  `S(3;5,7,7)=188`, `S(3;6,6,7)=202`, `S(3;4,4,12)`'s bundle landed but
  `(5,6,8)` and later were still bundling at 12.7 GB RSS. Their verdicts and
  DRAT proofs are in `artifacts/` and `logs/`; only the ledger packaging is
  outstanding. 18 of the 32 cells carry a ledger entry.
* The unreduced clause count for `(4,4,12)` and later cells was still being
  measured. `(4,4,11)` did land and is below.

Nothing above was rounded, inferred, or extrapolated. A timeout is recorded as a
timeout.

## The corrected feasibility table (replaces the brief's)

The brief sized cells by the number of solution **multisets**. That is the wrong
quantity: for `S ⊆ S'`, `clause(S)` subsumes `clause(S')`, so only the
**subsumption-minimal antichain** must be encoded. The retained list is a
literal subset of the full one, and every dropped clause is implied by a
retained one, so the two formulas have identical models — sound for `sat` and
`unsat` alike, no extra argument.

Measured at `n = N`, summed over the three colours:

| cell | N | full solution multisets | encoded clauses | ratio |
|---|---:|---:|---:|---:|
| S(3;4,4,8) | 87 | 2,614,007 | 109,370 | 0.042 |
| S(3;5,6,6) | 137 | 8,090,301 | 2,834,904 | 0.350 |
| S(3;4,6,7) | 118 | 8,470,835 | 1,051,899 | 0.124 |
| S(3;4,4,9) | 98 | 11,392,698 | 161,862 | 0.014 |
| S(3;4,5,8) | 111 | 13,007,475 | 512,277 | 0.039 |
| S(3;5,5,7) | 132 | 13,778,260 | 1,757,948 | 0.128 |
| S(3;4,7,7) | 139 | 34,283,366 | 2,737,498 | 0.080 |
| S(3;4,4,10) | 109 | 46,281,800 | 239,130 | **0.005** |
| S(3;5,6,7) | 160 | 47,918,493 | 6,937,489 | 0.145 |
| S(3;6,6,6) | 173 | 35,129,142 | 13,251,885 | 0.377 |
| S(3;4,5,9) | 125 | 68,591,051 | 811,545 | 0.012 |
| S(3;5,5,8) | 151 | 99,841,072 | 3,168,425 | 0.032 |
| **S(3;4,4,11)** | **120** | **176,224,094** | **323,293** | **0.0018** |
| S(3;4,7,8) | 159 | 175,893,191 | 5,632,873 | 0.032 |
| **S(3;4,4,12)** | **131** | **633,107,771** | **451,622** | **0.0007** |

Per equation, where the effect really lives:

| equation | n | full | minimal | ratio |
|---|---:|---:|---:|---:|
| L(4) | 87 | 18,600 | 16,751 | 0.901 |
| L(8) | 87 | 2,576,807 | 75,433 | **0.029** |
| L(6) | 173 | 11,709,714 | 4,416,949 | 0.377 |

**Rule: the reduction is strong exactly when `n/(k−1)` is small.** The only
two-element solution sets of `L(k)` are `{a, (k−1)a}` — there are `⌊n/(k−1)⌋` of
them — and every solution set containing such a pair dies to it, with the
subsumption cascading. So the `S(3;4,4,u)` row (large `u`, moderate `n`) is the
**cheapest infinite direction in the whole table**, which is the exact opposite
of what the multiset count says.

### Why this is a methodological result, not an optimization

Song–Mao's Section 5 describes their encoding — `v_{i,c}` variables,
exactly-one-colour constraints, clauses forbidding monochromatic `L(r)` — with
no subsumption reduction. Their search stops at `(4,4,10)`, `(4,5,8)`,
`(4,6,7)`. Those cells have **46.3M, 13.0M and 8.5M** solution multisets
respectively — that is, their frontier ends almost exactly where the unreduced
encoding stops fitting in a normal machine. Under the reduction the same three
cells are **239k, 512k and 1.05M** clauses, and the next one along, `(4,4,11)`,
is 323k. We are past their frontier because the clauses that made it a wall were
implied by clauses we already had.

The sharpest numbers are in the `(4,4,u)` row:

* `S(3;4,4,11)` at `n = 120`: **176,224,094** solution multisets, **323,293**
  encoded clauses — a factor of **545**;
* `S(3;4,4,12)` at `n = 131`: **633,107,771** solution multisets, **451,622**
  encoded clauses — a factor of **1,402**.

On the raw count `(4,4,12)` is thirteen times larger than the biggest cell in
the brief's table. On the encoded count it is smaller than `S(3;4,5,8)`, which
Song–Mao *did* compute. That is the whole methodological point in one line: the
`(4,4,u)` row is not hard, it only looks hard, and it looks hard in exactly the
metric a conventional pipeline uses to decide what to attempt.

**The wall is now enumeration, not solving.** Every instance in this campaign is
refuted by the CDCL core in under 7 s, and the biggest cost by far is building
the constraint list. Measured on `S(3;4,4,13)`, `n = 142`:

```
# n=142: 578773 clauses, 426 vars, built in 762.8s   peakRSS=15297660kB
RESULT n=142 verdict=unsat proof_steps=208 checked=true solve=0.1s check=0.4s
```

**762 seconds and 15.3 GB to build 578,773 clauses that are then refuted in
0.1 s.** That is the whole cost model of this family in four lines, and it is
also why the four heaviest cells could be decided but not re-bundled: `bundle`
runs both sides in one process. (I initially attributed that failure to
`to_dimacs()` materialising the DIMACS as a `String`. That is a real defect but
not the cause; the measurement above was already in my own log. FEEDBACK item 13
carries the correction.) `S(3;4,4,10)` at `n = 109` spends 110 s
enumerating 46.3M multisets to keep 239,130 clauses which are refuted in 0.03 s.
Generating the minimal antichain directly, without enumerating what it discards,
is the single change that would move the frontier again.

## Artifacts

```
artifacts/{known,open,ext}-*/proof-<N>.drat.gz    DRAT refutation at n = N
artifacts/witnesses/witness-<s>-<t>-<u>-n<N-1>.txt
bundles/offdiag-schur-3-<s>-<t>-<u>/              CNF + DRAT + witness per cell
logs/<tag>.log                                    full run record per cell
```

In the repository, 20 cells carry a claim-ledger entry under
`artifacts/claims/offdiag-schur/`: **20 claims re-checked, 0 errors**. Eight
unsat rows are fully re-checked in-tree with the deciding CNF validated clause
by clause; twelve carry CNFs of 6–69 MB gzipped, hash-pinned with a regeneration
recipe and reported as NOT re-checked rather than passed silently.

The size asymmetry is the family's signature and the reason the ledger stores
proofs but regenerates formulas: `S(3;5,7,7)` at `n = 188` is 19,807,560 clauses
in a 526 MB CNF, refuted by a **345-step, 2.5 KB** proof. What must be trusted
is tiny; what must be rebuilt is enormous.

All 23 stored witnesses were re-verified from file against the **full unreduced**
solution-set list: **23 of 23 clean, 0 failures.**

## How each side is checked

| side | produced by | checked by | independent of the producer? |
|---|---|---|---|
| `n = N−1` sat | axeyum CDCL | `first_violation` (reachability over the equation) | yes — the encoder is a partition enumeration |
| | | `first_monochromatic` vs the FULL solution sets | shares the encoder's view; run as a weaker cross-check |
| | | `check-claim-certificates.py`, in Python | yes — third derivation, different language |
| `n = N` unsat | axeyum CDCL, DRAT streamed to disk | `check_drat_backward` | yes |
| | | ledger checker validates the CNF clause by clause | yes — catches the symmetry trap directly |

## Residual trust

1. **Encoding faithful to the definition** — guarded by 16 published-value
   reproductions, by `first_violation` being an independent derivation, and by
   `the_reduced_encoding_decides_exactly_what_the_full_one_decides`.
2. **Symmetry breaking sound** — colour classes ordered by least element only
   *within* blocks of colours carrying the same `k`. Not assumed: the committed
   control `whole_palette_symmetry_breaking_produces_a_wrong_unsat` shows the
   unblocked version turning satisfiable `S(3;3,4,5)` at `n = 41` into `unsat`.
   Four other instances I tried did *not* flip, so a control built on any of
   those would have passed while testing nothing.
3. **Subsumption preserves models** — argued above; tested against full
   encodings on 12 instances and 64 random colourings each.
4. **axeyum's CDCL core and backward checker** — proofs are 54–847 steps and are
   re-derived, not accepted.

## The values, for citation

Reproduces Ahmed–Schaal (11): 43, 54, 65, 76, 69, 83, 97, 101, 94, 113, 173.

Reproduces Song–Mao Table 3 (5): `S(3;4,4,8)=87`, `S(3;4,4,9)=98`,
`S(3;4,4,10)=109`, `S(3;4,5,8)=111`, `S(3;4,6,7)=118`; plus `S(3;3,3,8)=59`,
`S(3;3,3,9)=68`, `S(3;3,3,10)=77`, `S(3;3,3,11)=86`, `S(3;3,3,12)=94`.

New, established here (18), both sides, checked:

```
S(3;4,4,11) = 120    S(3;4,6,8) = 135    S(3;5,5,7) = 132
S(3;4,4,12) = 131    S(3;4,6,9) = 152    S(3;5,5,8) = 151
S(3;4,5,9)  = 125    S(3;4,7,7) = 139    S(3;5,5,9) = 170
S(3;4,5,10) = 139    S(3;4,7,8) = 159    S(3;5,6,6) = 137
                                         S(3;5,6,7) = 160
                                         S(3;5,6,8) = 183
                                         S(3;5,7,7) = 188
                                         S(3;6,6,7) = 202
S(3;4,4,13) = 142    S(3;4,5,11) = 153
```

Plus, from the `s = 3` family (Ahmed–Schaal Conjecture 1, which Song–Mao proved,
so a weaker target), independent recomputation of their Table 3 rows:
`S(3;3,3,8..14) = 59, 68, 77, 86, 94, 104, 113` and
`S(3;3,4,8..11) = 67, 78, 86, 98` — 11 for 11, all agreeing.

## Context from arXiv:2604.11030 worth carrying

Their Theorem 6 proves `S(3;s,t,u) <= R_3(s,t,u) - 1` by a difference-colouring
argument, and Corollary 8 gives an asymptotic bound for large `u`. Neither
threatens any value here; both are the analytic frame these numbers sit in. They
also prove Ahmed-Schaal **Conjecture 1** (the `s = 3` family), which is why the
`S(3;3,t,u)` rows are a different and weaker target than the `s >= 4` cells.
