# agent-c RESULT — the `a^k` line for `R_k(a(x-y) = bz)`

Standing table. Updated as runs land. **A row is a value only when both sides
are established**: a replayed witness at `n = N-1` AND a checked refutation at
`n = N`. Anything else is a bound and is labelled as one.

## Headline

> **1. The conjecture `R_k(a(x-y)=bz) = a^k` for `gcd(a,b)=1`, `a >= b+2`, all
> `k >= 3` is FALSE.** It fails at the first point tested beyond the
> published range: `R_5(3(x-y)=z) > 243 = 3^5`, established by a 5-colouring
> of `[243]` found by axeyum's cube-and-conquer harness in 35.8 s and
> verified four independent ways. (Independently reproduced from an existing
> preprint's artifacts — see C1. Not claimed as new; claimed as certified.)
>
> **2. `R_4(5(x-y)=2z) = 625` is a NEW exact four-colour Rado number.** The
> cell is blank in Chang-De Loera-Wesley's Table 10, the only published
> four-colour table for this family, and lies inside the `a >= b+2`,
> `gcd(a,b) = 1` hypotheses. Both sides certified with no external solver or
> checker: a construction witness at 624 and a 103,409,097-step DRAT
> refutation at 625, produced on one host and re-checked on another.
>
> **3. `R_4(5(x-y)=z) = 625` replicated** end to end inside axeyum, filling
> the last exact Table 10 cell in the coprime `a >= b+2` region that had no
> ledger claim.

## Table

| (a,b,k) | predicted `a^k` | `n = a^k - 1` | `n = a^k` | verdict | evidence | published / new |
|---|---:|---|---|---|---|---|
| (3,1,5) | 243  | **SAT** (valuation, 0.02 s) | **SAT** (cover cell 137, 35.8 s) | `R_5 > 251` (climbed), **prediction REFUTED** | claim `rado-r5-a3-b1-frontier`, rows `witness-243`, `witness-251`, `deciding-instance` | see census C1 |
| (5,1,4) | 625  | **SAT** (valuation, 0.02 s) | **UNSAT**, checked (24,184,646 DRAT steps; solve 1044.2 s, check 1368.1 s) | **`R_4(5(x-y)=z) = 625`** | claim `rado-r4-a5-b1` | **published** (CDLW Table 10) — replication |
| (5,2,4) | 625  | **SAT** (valuation, 0.02 s) | **UNSAT**, checked (103,409,097 DRAT steps; solve 6576 s on s1, check 8703 s on s4) | **`R_4(5(x-y)=2z) = 625`** | claim `rado-r4-a5-b2` | **NEW exact value** — blank in Table 10 |
| (5,3,4) | 625  | **SAT** (valuation, 0.01 s) | **KILLED mid-solve** at 3 h 11 m, 15.51 GB of proof, no verdict | `R_4 > 624` only | `artifacts/witnesses/val-a5-b3-k4-n624.txt` | blank in Table 10; **still open** |
| (2,1,5) | n/a (a=2 is exceptional: `R_3 = 14 != 8`, `R_4 = 56 != 16`) | — | **UNRESOLVED** — see below | — | — | no published k=5 value |
| (6,1,4) | 1296 | **SAT** (valuation, 0.07 s) | **KILLED mid-solve** at 1 h 49 m, 6.03 GB of proof, no verdict | `R_4 > 1295` only | `artifacts/witnesses/val-a6-b1-k4-n1295.txt` | outside Table 10's range; **still open**, and open in Li's artifact set ("n=1296 UNSAT needs cluster") |
| (4,1,5) | 1024 | **SAT** (valuation, 0.07 s) | **KILLED undecided** (cover 658/15,625 cells in 1 h 35 m; batsat 2 h 17 m) | `R_5 > 1023` only | `artifacts/witnesses/val-a4-b1-k5-n1023.txt` | **still open**; would decide Li's threshold conjecture |
| (7,1,4) | 2401 | **SAT** (valuation, 0.21 s) | not attempted | `R_4 > 2400` | `artifacts/witnesses/val-a7-b1-k4-n2400.txt` | outside Table 10's range |
| (4,3,4) | n/a (a < b+2) | `R_4 > 255` | — | lower bound only | `artifacts/witnesses/val-a4-b3-k4-n255.txt` | BLANK in Table 10; ledger has 313 |

All `n = a^k - 1` rows are **not searched**: the colouring is written down
from Chang-De Loera-Wesley's Lemma 4.1 (`c(j) = v_a(j) + 1`) and then checked.
Three checks per row (encoder view, independent brute-force enumerator,
`CnfFormula::evaluate`). Total cost for all eight: under one second.

## Table 10 census (the basis for every "published / new" label)

Read from the **rendered** arXiv PDF of 2210.03262 (v1 is the only version;
its compiled PDF does contain Tables 9-15 — the missing-tables issue is
tarball-vs-PDF, not a version difference).

`R_4(a(x-y) = bz)`, columns `a`, rows `b`:

```
        a=1     a=2      a=3    a=4    a=5
b=1      45      56       81    256    625
b=2     171      45      103     56      -
b=3     469    >225       45      -      -
b=4    1037       -        -      -      -
```

20 cells, 13 populated, 7 blank — confirmed. **Only 12 are exact**: (2,3) is
the bare `> 225` (closed at 226 by this project's previous session).
Blank: **(5,2), (4,3), (5,3)**, (2,4), (3,4), (4,4), (5,4).

The paper contains **no k=5 value and no k=5 upper bound** for any member of
the family. It does contain a k=5 *lower* bound: Lemma 4.1 is stated for
general `k`.

### C1 — novelty status of `R_5(3(x-y)=z) > 243`

**Not claimed as new — now confirmed from the authors' own artifacts.**
A. C. Li, SSRN 6814341 (3 June 2026), "On Rado Numbers for `x + by = bz`:
The `b^k` Pattern and a Threshold Conjecture". The preprint 403s, but its
artifact repository does not: `crabsatellite/rado-numbers-sat` (MIT, Zenodo
DOI 10.5281/zenodo.18957993) ships `data/results/R5_witness_243.json` and
`R5_witness_296.json`, and states "Explicit R_5(3) > 296 witness and
verifier. The exact value is not claimed." So `R_5(3) > 296` is theirs, our
`> 243` is a weaker independent reproduction, and **the exact value is open
for both of us**. Their conjecture is `R_k(b) = b^k iff k <= 2(b-1)`; their
own status line reads "k=1 trivial, k=2 Landman-Robertson 2014, k=3-4 Key
Lemma + SAT, k>=5 OPEN".

**The delta that is ours:** their route is CaDiCaL 1.5.3 via PySAT with no
proof certificate recorded; every UNSAT in this lane carries a DRAT proof
produced and re-checked by axeyum's own code (ADR-0381, ADR-0382).

The renaming that connects the two families was **verified mechanically**,
not assumed (`artifacts/verify-renaming.py`): `x + by = bz` <=>
`x = b(z-y)`, a permutation of coordinates, so the two equations induce the
*same* 3-uniform hypergraph on `[n]`; checked equal as sets-of-sets for
`b = 1..7` and `n in {1,2,5,13,40,97,200}`, 49/49 identical. Hence Li's
`R_k(b)` is exactly our `R_k(b(x-y) = 1z)`.

**Caveat that must travel with this:** SSRN returns HTTP 403 to every fetch
we attempted; Li's numbers are search-engine summaries of the abstract page,
**not directly read text**. They are treated as a hypothesis. Our verdict at
243 is independent of them.

What IS ours: the refutation is certified end to end inside axeyum with no
external solver or checker, and it is the first time this project's own
machinery has falsified a conjecture it was sent to confirm.

Also worth recording from the census: Li's `R_4(b) = b^4 for b in {3,4,5}`
is **not new** — it is Table 10 row `b=1`, columns `a=3,4,5` (81, 256, 625),
ISSAC 2022. And Li's `R_3(b) = b^3 for b in {4..10}` is strictly weaker than
CDLW Theorem 1.2(3).

### C2 — OEIS

`"Rado number"` full-text search returns 7 sequences, none for this family
with `k >= 3` colours. The three governing polynomials are present as bare
polynomials with **no** Rado/Schur cross-reference: A083074 (`n^3-n^2-n-1`,
CDLW Thm 1.2(1)), A168297 (`n^3+(1-n)^2`, Thm 1.2(2)), A125082
(`n^4-n^3-n^2-n-1`, the Table 10 `a=1` column). The Table 10 vectors
themselves (45, 171, 469, 1037 and 45, 56, 81, 256, 625) are **absent from
OEIS**.

## C3 — Ledger-vs-literature audit (all cells, not a chosen subset)

| table | cells | ledger coverage | mismatches |
|---|---:|---|---:|
| Table 1 (k=3), `1<=a,b<=5` | 25 | 25/25 | **0** |
| Table 10 (k=4), exact cells | 12 | 10/12 | **0** |

`(2,3)` is the published `> 225`, improved by the ledger to the exact 226.
`(4,3)` is BLANK in Table 10 and the ledger carries 313. Published cells with
**no ledger claim** at the start of this lane: `(5,1) = 625` (**now landed**,
claim `rado-r4-a5-b1`), `(1,3) = 469`, `(1,4) = 1037`.

35 published values, 35 agreements, zero disagreements — which is also the
strongest available check that the Table 1 / Table 10 transcription in C2 is
correct.

## Where the unresolved targets stopped, exactly

- **`R_5(2(x-y)=z)`** (the `14, 56, ?` sequence). Two SAT hunts at `n = 224`:
  a batsat probe ran 29 minutes without deciding, and a depth-6 cube cover
  finished **3,306 of 15,625 cells** before its cells started costing 190 s
  and 4.9M proof steps each; at that point four workers held 6 GiB and were
  no longer making progress. Both were killed to protect the `(5,3)`
  refutation's check phase. **Nothing is established beyond the trivial
  `R_5 >= R_4 = 56`.** No lower-bound construction is known for `a = 2`: the
  valuation colouring gives only `> 31`, far below the known `R_4 = 56`, so
  the satisfiable side here is a genuine search problem and not a write-down.

- **`R_5(4(x-y)=z) = 1024?`** The lower bound `R_5 > 1023` is established by
  the valuation colouring (0.07 s, four checks). The interesting half is the
  SAT question at `n = 1024`: Li's threshold conjecture (`k <= 2(a-1)`, so
  `k <= 6` at `a = 4`) predicts the `a^k` law **survives** there, which makes
  a SAT answer a refutation of the conjecture and an UNSAT answer the first
  five-colour Rado number in this family. A batsat probe is running; it was
  killed once at 6.7 GiB to protect a refutation and restarted. **Not
  decided.**

- **`R_4(6(x-y)=z) = 1296?`** Lower bound `R_4 > 1295` established. The
  refutation at `n = 1296` (5184 vars, 1,038,958 clauses) started on s1 after
  the `(5,1)` slot freed. **Not decided.**

- **`R_4(1,3) = 469` and `R_4(1,4) = 1037`** are published Table 10 values
  with no ledger claim. Not attempted here — the `a = 1` column is the
  hardest in the table and is not on the `a^k` line this lane is about.

### C4 — the `(5,1)` census dispute, resolved against Li

Li's `main_results.json` marks `b=5 -> R_4 = 625` as `"NEW": true`. That is an
**overclaim**. The rendered CDLW PDF, at the table itself:

```
                        Table 10: R4 (a(x − y) = bz)
                       a
                                 1       2       3       4        5
               b
                   1             45   56   81 256                625
                   2             171  45   103 56
                   3             469 > 225 45
                   4            1037
```

Row `b=1`, column `a=5`, value **625**, ISSAC 2022. Under the verified
renaming Li's `b` is our `a` with our `b` fixed at 1, so their `b=5` cell is
exactly this one. Our `rado-r4-a5-b1` is therefore correctly labelled a
replication, and Li's novelty flag on that row should not be relied on.

Two independent transcriptions of Table 10 now agree, and they agree with 35
independently computed ledger values (C3), which is why this reading is
trusted over anyone's recollection.

### C5 — what Li's artifact set leaves open, and where we are aimed

From `data/results/main_results.json` (dated 2026-03-10, i7-12700K / 64 GB):

| their cell | our cell | their status |
|---|---|---|
| `b=5, k=4` | `(5,1,4)` | 625, verified, 523.4 s (**published by CDLW; their "NEW" flag is wrong**) |
| `b=6, k=4` | `(6,1,4)` | **null** — "n=1295 SAT confirmed, n=1296 UNSAT needs cluster" |
| `b=7, k=4` | `(7,1,4)` | **null** — "too large for desktop" |
| any `k>=5` | any | **OPEN** by their own status line |

Their family is `x + by = bz`, which the verified renaming maps onto our
`a(x-y) = 1z` **only**. It says nothing about our `b = 2` and `b = 3` columns,
which CDLW leaves blank. So `(5,2,4)` and `(5,3,4)` remain unaffected by any
of this and are the cleanest new four-colour values available.

Their repo also carries a Lean 4 + Mathlib formalization with an axiom audit.
The "SAT + Lean + claim ledger" architecture is not unique to this project —
which raises, not lowers, the value of our certificates actually existing.
