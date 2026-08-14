# agent-c diary — the `a^k` line, R_k(a(x-y)=bz) = a^k for gcd(a,b)=1, a >= b+2

Append-only. Times are local (2026-08-13).

## 0. Orientation

Read the campaign README, CLAUDE.md, `docs/plan/rado-session-diary-and-roadmap-2026-08-12.md`,
`artifacts/claims/rado/SEMANTICS.md`, and the existing claim dirs.

Key facts established before touching a keyboard:

- CDLW (ISSAC 2022) prove `R_3(a(x-y)=bz) = a^3` for `gcd(a,b)=1`, `b >= 1`,
  `a >= b+2`. Lemma 4.1 gives the lower bound `R_k >= a^k` for every k.
- The lower-bound colouring is explicit and I can write it down rather than
  search for it: **colour j by its a-adic valuation**, `c(j) = v_a(j) + 1`.
  Proof that it avoids monochromatic solutions for any b coprime to a:
  solutions are `x - y = b t`, `z = a t` (t >= 1). Suppose x, y, z all lie in
  class m, i.e. all have `v_a = m`. Then `a^m | x` and `a^m | y`, so
  `a^m | x - y = b t`; since `gcd(a,b)=1` this gives `v_a(t) >= m`. But
  `v_a(z) = v_a(a t) = v_a(t) + 1 = m` forces `v_a(t) = m - 1 < m`.
  Contradiction. (m = 0 is impossible outright: `v_a(a t) >= 1 > 0`.)
  On `[a^k - 1]` the valuation takes exactly the k values 0..k-1, so this is
  a k-colouring and `R_k > a^k - 1`.
- This colouring also satisfies the encoder's symmetry breaking for free:
  point 1 has v=0 -> colour 1, and colour i first appears at `a^(i-1)`, in
  increasing order. So it is directly a model of the shipped CNF.
- The ledger already confirms every coprime `a >= b+2` cell of the k=3 table
  and two k=4 cells ((3,1)=81, (4,1)=256).

**Caution flag raised at orientation.** `artifacts/claims/rado/rado-r5-a3-b2-frontier/claim.json`
cites A. C. Li, SSRN 6814341 (2026), "On Rado Numbers for x+by=bz", as
reporting `R_5(3) > 296 > 243` in the b=1 column. That family is the same
family under renaming: `x + by = bz` <=> `x = b(z - y)`, i.e. `b(X-Y) = 1*Z`
with X=z, Y=y, Z=x. So the cited claim is exactly `R_5(3(x-y)=z) > 296`,
which would REFUTE the a^k prediction for target 1 at k=5. Not peer reviewed,
full text not read. Treat as a hypothesis to test, not a fact -- but it means
I must encode BOTH sides at 243 and not assume the refutation will succeed.

## 1. Tooling

`crates/axeyum-search`'s `Rado` family + `harness::run_cover` cover everything.
Added one uniquely-named file I own:
`crates/axeyum-search/examples/akb2_frontier.rs` with modes
`valuation | verify | climb | solve | cover`.

The `valuation` mode writes the construction colouring and checks it THREE
ways: the encoder's `first_monochromatic`, the family's independent
`first_violation` brute force, and `CnfFormula::evaluate` on the one-hot
assignment.

**Broke immediately:** `cargo build -p axeyum-search` fails in the shared
checkout -- `crates/axeyum-search/src/cover.rs` is mid-edit by agent-b
(`cannot find type Cube`, cover.rs:299/300/314). Worked around by building
from a `git archive HEAD` snapshot in my scratchpad instead of the dirty
worktree. Recorded because it is the multi-agent-hygiene cost in practice:
an agent that owns no shared file still cannot build the shared crate.

## 2. Pipeline validation against a known value

Before any frontier run, replicate `R_4(3(x-y)=1z) = 81` (ledger claim
`rado-r4-a3-b1`, published in CDLW Tables 1 and 10):

```
valuation 3 1 4 80 -> witness-verified, checks=3, constraints=1729,
                      clauses=7714, colours_used=4
solve     3 1 4 81 -> verified-unsat, steps=164538, solve 1.040 s,
                      check 0.978 s (check_drat_backward)
```

The step count **164538 matches the stored claim's recorded step count
exactly**, so my driver reproduces the ledger's certificate bit-for-bit in
size. Pipeline is good.

## 3. Lower bounds, all of them, written down rather than searched (t+25 min)

The `valuation` mode wrote and verified the construction colouring at every
target's `a^k - 1` in well under a second each. Every one passes all three
checks (encoder view, independent brute-force enumerator, CNF evaluation):

| (a,b,k) | n | forbidden sets | clauses | colours used | verdict |
|---|---:|---:|---:|---:|---|
| (3,1,5) | 242  | 16,120  | 84,227    | 5 | witness-verified |
| (5,1,4) | 624  | 69,626  | 284,742   | 4 | witness-verified |
| (5,2,4) | 624  | 61,876  | 253,742   | 4 | witness-verified |
| (5,3,4) | 624  | 54,126  | 222,742   | 4 | witness-verified |
| (6,1,4) | 1295 | 255,205 | 1,033,768 | 4 | witness-verified |
| (4,1,5) | 1023 | 228,225 | 1,156,467 | 5 | witness-verified |
| (7,1,4) | 2400 | 762,147 | 3,072,586 | 4 | witness-verified |
| (4,3,4) | 255  | 10,017  | 42,616    | 4 | witness-verified |

So `R_k > a^k - 1` is settled for all of these, at a cost of ~0.5 s total.
This is the point the task brief makes: taking the colouring from the
construction is stronger and vastly cheaper than searching for one. The
whole SAT half of eight parameter points cost less than one SAT call.

Artifacts: `artifacts/witnesses/val-a{a}-b{b}-k{k}-n{n}.txt`.

## 4. First frontier attempt: R_5(3(x-y)=z), n = 243 (t+30 min)

Cheap SAT probe first, because of the Li caution flag: min-conflicts from the
valuation warm start, 5,000,000 moves, seeds 1/2/3, n = 243. All three
returned `no-witness` in ~28 s each. That is evidence *against* the Li report
and *for* `R_5(3,1) = 243`, but local search failing is not a refutation, so
the monolithic proof-producing solve is running on s7 (1215 vars, 85,452
clauses, 8 h budget, streaming text DRAT to local disk).

## 5. The renaming is not a given -- I checked it mechanically (t+50 min)

The coordinator was right to push on this. I did not want to rest a caution
flag on an algebraic manipulation I did in my head, so I verified the
identification by comparing the two hypergraphs directly, in a script that
shares no code with anything in axeyum:
`artifacts/verify-renaming.py`.

Argument: a monochromatic solution depends only on the SET `{x,y,z}`, and
`x + b y = b z` rearranges to `x = b(z - y)`, which is `b(X-Y) = 1*Z` under
`(X,Y,Z) = (z,y,x)` -- a permutation of the coordinates, so the SET is
unchanged. Therefore the two equations induce the *same* 3-uniform hypergraph
on `[n]`, and `R_k` agrees for every k and every n.

Checked for `b = 1..7` and `n in {1,2,5,13,40,97,200}`: the two sets-of-sets
are **identical in all 49 cases** (e.g. b=5, n=200: 7167 distinct sets, equal
as sets). `RENAMING VERIFIED`.

So Li's `R_k(b)` for `x + by = bz` **is** our `R_k(b(x-y) = 1z)`, i.e.
exactly the `b = 1` row of the Chang-De Loera-Wesley table read along the
`a` axis. The caution stands, and it is serious.

## 6. Literature census (t+55 min)

Read the RENDERED arXiv PDF (v1 is the only version; its compiled PDF *does*
carry Tables 9-15 -- the missing-tables problem is tarball-vs-PDF, not a
version difference).

**Table 10, `R_4(a(x-y)=bz)`, columns a, rows b:**

```
        a=1     a=2      a=3    a=4    a=5
b=1      45      56       81    256    625
b=2     171      45      103     56      -
b=3     469    >225       45      -      -
b=4    1037       -        -      -      -
```

20 cells, 13 populated, 7 blank -- confirmed. But only **12 are exact**:
(2,3) is the bare `> 225` (that was last session's target, closed at 226).
Blank: (5,2), (4,3), (5,3), (2,4), (3,4), (4,4), (5,4).

**Consequences for my target list:**

- `R_4(5(x-y)=1z) = 625` is **PUBLISHED** (Table 10). Replication, not new.
- `R_4(5(x-y)=2z)` is **BLANK** in Table 10. `a=5 >= b+2=4`, `gcd=1`. If it
  is 625 that is a **genuinely new exact four-colour Rado number**.
- `R_4(5(x-y)=3z)` is **BLANK**. `a=5 >= b+2=5`, `gcd=1`. Same -- new.
- `R_4(6(x-y)=z)` is **out of Table 10's range entirely** (a <= 5). New.
- Lemma 4.1 is verbatim the a-adic valuation colouring I wrote down
  independently in section 0; my derivation agrees with theirs.
- **No k=5 value or upper bound appears anywhere in the paper** for any
  member of the family. The findings register's E3 is right, but the wording
  should be tightened: Lemma 4.1 IS stated for general k, so a k=5 *lower*
  bound `a^5` is published; what is absent is any k=5 *upper* bound.

**Novelty audit hit (this is the important one).** A. C. Li, SSRN 6814341
(3 June 2026) reportedly states a threshold conjecture
`R_k(b) = b^k iff k <= 2(b-1)` -- in our notation `R_k(a(x-y)=z) = a^k iff
k <= 2(a-1)` -- plus `R_5(3) > 296 > 243` with an explicit witness. SSRN
returns 403 to every fetch we tried, so **the numbers are search-engine
summaries, not directly read text; they are not cited as verified**.

Two things follow:

1. My headline target `R_5(3(x-y)=z) = 243` is predicted by that conjecture
   to be **FALSE** (a=3 gives the threshold k <= 4, and our ledger's 27 and
   81 sit exactly at k=3 and k=4).
2. Li's `R_4(b) = b^4 for b in {3,4,5}` and `R_3(b) = b^3 for b in {4..10}`
   are **not new** -- they are Table 10 row b=1 and a weaker form of CDLW
   Theorem 1.2(3). Anyone citing that preprint should know it.

I am running the refutation at 243 anyway. An unread preprint is a
hypothesis; a certified verdict is evidence.

## 7. PRIMARY FINDING: the a^k law FAILS at k=5. R_5(3(x-y)=z) > 243 (t+1h20)

The monolithic proof-producing solve at n = 243 was **not** converging: 2.6 GB
of text DRAT after 8 minutes and RSS tracking it almost exactly (2.68 GB
resident against 2.64 GB on disk). Extrapolating the ledger's own numbers,
the comparable UNSAT instance `rado-r4-a2-b3` (n=226) produced 18.9 GB of
DRAT and its *check* needed ~28 GiB. s7 has 26 GiB. I killed the monolithic
run rather than let it OOM at hour three and look like a refuted claim
(exactly the trap the brief warns about with `recertify_rado`).

Replaced it with `harness::run_cover`, depth 6, branch points [2,4,6,8,10,12],
5^6 = 15,625 cells, 12 workers. **Cell 137, cube [1,1,2,1,3,3], came back
SATISFIABLE after 35.8 s.**

```
cover: 15625 cells over 6 branch groups; at-least-one clauses located in F at [1,3,5,7,9,11]
cell    137 [1,1,2,1,3,3] sat in 35.82s
cell 137 is SATISFIABLE -- the instance is satisfiable and the run stops here
```

So **there is a 5-colouring of [243] with no monochromatic solution of
3(x-y) = z**, i.e.

> **R_5(3(x-y) = z) > 243 = 3^5.**

The conjecture I was sent to confirm is **FALSE** at k = 5.

### How it is checked (four independent ways, none of them the searcher)

1. `harness::run_cover`'s own `ModelDoesNotSatisfy` guard: the model
   satisfies the original formula, checked before the run stops.
2. A Python decoder + O(n^2) enumerator written from `3(x-y) = z` directly
   (no axeyum code): **16,362 solution triples enumerated, 0 monochromatic**,
   all five colours used, class sizes (63, 54, 41, 28, 57).
3. `akb2_frontier verify`, which runs `ColouringFamily::first_violation` --
   the crate's brute-force enumerator that shares no code with the encoder --
   plus `ColouringProblem::first_monochromatic` plus `CnfFormula::evaluate`:
   `witness-verified, checks=3, constraints=16362, clauses=85452`.
4. **A second, independent searcher found it too.** The batsat probe I had
   left running (`sat` mode, ADR-0007 adapter, untrusted-search-only) came
   back `sat-verified` at n = 243 after 457.8 s, having found a *different*
   assignment. Two searchers, one verdict.

Artifacts: `artifacts/t1-a3b1k5/witness-243.txt` (the colouring),
`artifacts/t1-a3b1k5/model-243.txt` (the raw cell-137 model),
`artifacts/t1-a3b1k5/status-243.tsv`, `logs/cover-a3b1k5-n243.log`.

### What this means

- CDLW's Theorem 1.2(3) `R_3 = a^3` and Table 10's `R_4(3,1) = 81 = 3^4` do
  **not** extend to k = 5 at (a,b) = (3,1). The natural generalisation
  `R_k(a(x-y)=bz) = a^k for gcd(a,b)=1, a >= b+2, all k >= 3` is refuted.
- It **corroborates** the (unread, non-peer-reviewed) Li SSRN report of
  `R_5(3) > 296 > 243` and its threshold conjecture `R_k(b) = b^k iff
  k <= 2(b-1)` -- which for b=3 (our a=3) predicts the law holds exactly at
  k = 3 and k = 4 and fails from k = 5, which is precisely what our ledger
  (27, 81) plus this refutation shows. I am therefore NOT claiming
  `R_5(3,1) > 243` as new; it is a weaker independent reproduction of a
  claim that appears to exist in a June 2026 preprint. What is ours is that
  it is **certified end to end inside axeyum with no external solver**.
- The interesting consequence is for **target 2**: the threshold conjecture
  in our notation is `k <= 2(a-1)`, so a = 5 (targets 2a/2b/2c) should hold
  the a^k law all the way to k = 8, and a = 4 (target 4) to k = 6. Li's
  conjecture is stated only for b = 1; targets 2b (5,2) and 2c (5,3) test
  whether it survives at b > 1, where nothing at all is published.

### Why an a-adic proof of the failure was available for free, and I missed it

Worth recording because it would have saved an hour of compute: the
valuation colouring **provably cannot** be extended to 243. Whichever class
243 joins, a monochromatic solution appears -- e.g. joining class v=0 gives
`{82, 1, 243}` (3(82-1) = 243), class v=1 gives `{84, 3, 243}`, class v=2
gives `{90, 9, 243}`, class v=3 gives `{108, 27, 243}`, class v=4 gives
`{162, 81, 243}` twice over. So an avoiding 5-colouring of [243] must be
structurally *unlike* the valuation colouring -- and that is exactly why
`min_conflicts` warm-started from the valuation colouring failed three times
(3 x 5,000,000 moves, ~28 s each): I had warm-started it inside the wrong
basin. The cube-and-conquer harness, which does not start from a
construction at all, found it in 36 s.

**Lesson:** a warm start from the best known construction is a *bias*, and
when the answer is known to be unlike the construction it is a bias toward
failure. Cheap check first: can the construction be extended at all?

## 8. Route selection: covers are the WRONG tool for the a^k instances (t+1h50)

Started the four-colour targets at n = 625 two ways to find out which route
wins, and the answer is unambiguous and worth recording, because the previous
session's conclusion ("use the cover") does not transfer.

- **`harness::run_cover`, depth 6, [2,4,6,8,10,12], 4096 cells, 6 workers,
  (5,3,4) at n=625:** 4 cells finished in twenty minutes, 15 GiB of 26 GiB
  resident, the other 6 workers all stuck on their first cell. Killed.
- **Monolithic `solve_with_drat_proof_streaming`:** the same family's `a^k`
  points are *structurally easy* -- ledger numbers, all `n = a^4`:
  `n=81` 0.785 s / 164,538 steps; `n=256` 24.649 s / 2,555,413 steps. The
  hard ledger instances are the ones **off** the `a^k` line (`n=226`:
  7632 s, 18.9 GB; `n=313`: 1677 s, 5.0 GB).

So the a-adic structure that makes the lower bound free also makes the
refutation cheap, and cube-and-conquer's overhead buys nothing. Switched all
three (5,b) targets to monolithic runs: (5,1) and (5,2) on s1 (61 GiB),
(5,3) on s7.

**Two harness defects found on the way, both memory-related:**

1. `crates/axeyum-search/src/harness.rs:605` calls
   `solve_with_drat_proof_with_limits` -- the **in-memory** variant. ADR-0381
   made the producer streaming (`solve_with_drat_proof_streaming` +
   `TextProofSink`) precisely to stop a 27.6 GiB OOM, and the cover harness
   never adopted it. Every worker holds its entire cell proof resident, so
   the cover's memory is `workers x (largest cell proof)`, which is exactly
   what killed the run above.
2. **`run_cover` does not stop when a cell reports SAT.** At n=243 it printed
   "cell 137 is SATISFIABLE -- the run stops here" at 35.8 s and the process
   was still alive four minutes later at 11 GiB, and had meanwhile found
   cell 136 SAT too and **overwritten `model.txt`**. I had already copied
   cell 137's model, so nothing was lost, but a run that persists a model to
   a fixed path and then overwrites it with a different one is a
   finding-B1-shaped hazard. The in-flight workers are allowed to run to the
   whole-run budget, so on a satisfiable instance "the run stops here" can
   mean hours.

## 9. What the 243 witness is made of (t+2h)

Cross-tabulated the verified 5-colouring of [243] against `v_3`:

```
colour -> v_3 histogram
  1 {0:57, 2:4,  3:1, 4:1}
  2 {1:54}                     <-- EXACTLY the v_3 = 1 stratum, all 54 of it
  3 {0:36, 2:2,  3:3}
  4 {0:17, 2:9,  3:1, 4:1}
  5 {0:52, 2:3,  3:1, 5:1}
```

Colour 2 is **precisely** `{j in [243] : v_3(j) = 1}` -- all 54 elements
(`243/3 - 243/9 = 54`), nothing else. The remaining four classes partition
`{v_3 = 0} u {v_3 >= 2}` and are **not** valuation strata: they are
interval-like. Colour 1 starts `1,2,4,7,8,11,13,16,17,19` then jumps to
`50,52,53,55,56,58,59,61,62,64,65,...` -- a shell.

So the extremal object here is a **hybrid**: one pure valuation stratum plus
a shell decomposition of the rest. That is the same shape as the previous
session's "nested two-ended shells" finding, and it is why the pure
valuation colouring is not extremal at k=5 while it is at k=3 and k=4.
Recorded as an observation, not a construction -- turning it into a general
`k` family is a research project, not a run.

## 10. Claim landed (t+2h20)

`artifacts/claims/rado/rado-r5-a3-b1-frontier` committed as d8515e23, with
the driver `crates/axeyum-search/examples/akb2_frontier.rs`. Both gates pass:

```
scripts/validate-claims.py            -> 40 claims, 0 errors
scripts/check-claim-certificates.py --only rado-r5-a3-b1-frontier
  checked instance-pin deciding-instance: 1900536 B on disk, matches the
    instance regenerated from a=3 b=1 k=5 n=243, sha256 ac6b7c6f7ff99e7b...
  checked witness witness-243: 243 integers, no monochromatic solution
  1 claims re-checked, 0 errors
```

The `instance-pin` row is included deliberately: the brief's warning about
the 313 bound shipping "with no identified subject" is exactly the failure
mode a lower-bound claim invites, since a colouring by itself does not say
which formula anything is about.

Note on the toolchain pin: `dirty: true`, honestly, because the driver was
uncommitted when the artifact was produced. It is committed now, so the next
artifact from it can pin a clean commit.

`clippy -D warnings` on the example initially failed with two
`single_match_else` pedantic errors. Allowed at module level with a written
reason rather than rewritten -- every verdict in the driver is one `match`
over an outcome enum, and making two of them `if let` would make the alarm
paths look structurally different from the happy paths.

## 11. Audit against ALL the published data, not the cells I chose (t+2h50)

The previous session's worst error was "verified against 15 published values"
where the author had picked the 15. So before claiming any new value in this
family I compared the **entire** ledger against the **entire** census, cell by
cell, mechanically.

**k = 3, CDLW Table 1, all 25 cells of the `1 <= a,b <= 5` corner:**
`25/25 covered by the ledger, 0 mismatches`.

**k = 4, CDLW Table 10, all 20 cells:** of the 12 cells carrying exact
published values, the ledger covers 10 with `0 mismatches`; `(2,3)` is the
published `> 225` which the ledger IMPROVES to the exact 226; `(4,3)` is
BLANK in Table 10 and the ledger carries 313 (the previous session's new
value). The three published cells with **no ledger claim** are
`(a=5,b=1) = 625`, `(a=1,b=3) = 469`, `(a=1,b=4) = 1037`.

That is 35 published values checked against independently computed ones with
zero disagreements, and it simultaneously validates the table transcription:
two independent derivations (their paper, our solver) agreeing on 35 numbers
is much better evidence that I read the PDF correctly than my reading it
twice would be.

It also fixes the target list. `(5,1)` is a **published replication** and is
running; `(5,2)` and `(5,3)` are the two Table-10-blank cells inside the
`a >= b+2`, `gcd = 1` hypothesis, and are where a new exact value is
actually available.

## 12. Fourth check on every construction witness (t+3h)

Ran all eight `n = a^k - 1` valuation colourings through the *claim checker's*
own enumerator (`scripts/check-claim-certificates.py:check_rado_witness`,
a fourth implementation of the semantics, in Python, sharing no code with
anything in `crates/`):

```
a=5 b=1 k=4 n=624 : OK      a=6 b=1 k=4 n=1295: OK      a=4 b=3 k=4 n=255 : OK
a=5 b=2 k=4 n=624 : OK      a=4 b=1 k=5 n=1023: OK      a=3 b=1 k=5 n=242 : OK
a=5 b=3 k=4 n=624 : OK      a=7 b=1 k=4 n=2400: OK
```

Also re-ran the ledger's other two gates after adding my claim:
`scripts/validate-claims.py` -> 40 claims, 0 errors;
`scripts/check-claim-negative-fixtures.py` -> 8 fixtures, 0 failures (the
validator still rejects all the committed invalid fixtures, so the gate that
passed my claim is not a gate that passes anything).

## 13. Waiting, and what the wait measured (t+3h20)

The three `n = 625` refutations are the long pole. Interim numbers, all from
the same driver so they are comparable:

| target | solve | text DRAT | resident while checking |
|---|---|---:|---:|
| (5,1,4) n=625 | ~17 min, then checking | 1,873,245,421 B | **12.3 GiB** |
| (5,2,4) n=625 | running | 2.1 GB and growing | 2.3 GiB |
| (5,3,4) n=625 | running | 1.2 GB and growing | 1.5 GiB |

The 12.3 GiB figure is the important one and it is now item F-C7 in FEEDBACK:
**6.6x blow-up from text-DRAT bytes to resident memory**, incurred *after*
ADR-0381 made the producer streaming. My earlier guess in F-C3 was 1.5x; the
measurement is four times worse, and it is the reason a 26 GiB host cannot
certify what a 61 GiB host can. `top` confirms 100% CPU on both s1 jobs, so
this is work and not a hang -- worth stating because a constant RSS and a
silent log look exactly like a stall.

Two SAT hunts were killed to protect the refutations: the `(2,1,5)` n=224
cube cover (6 GiB, four workers each grinding 190 s / 4.9M-step cells, 3306
of 15625 cells done and slowing) and, briefly, the `(4,1,5)` n=1024 batsat
probe. The n=1024 probe was restarted once the cover's memory was returned;
`R_5(4(x-y)=z) = 1024` is the interesting one because Li's threshold
conjecture (`k <= 2(a-1)`, so `k <= 6` at a=4) predicts the a^k law SURVIVES
there, which makes a SAT answer at 1024 a refutation of the conjecture and an
UNSAT answer the first five-colour Rado number in this family.

## 14. R_4(5(x-y)=z) = 625 — first n=625 refutation lands (t+3h45)

```
{"status":"verified-unsat","a":5,"b":1,"k":4,"n":625,"vars":2500,
 "clauses":287248,"steps":24184646,"drat_bytes":1873245421,
 "solve_s":1044.164,"check_s":1368.072}
```

Solve 17.4 min, check 22.8 min, 24.2M DRAT steps, 1.87 GB. Together with the
0.02 s valuation witness at 624 this is a complete, both-sides value:
**R_4(5(x-y)=z) = 625 = 5^4**, matching CDLW Table 10. It is a REPLICATION,
not a new value, and the ledger had no claim for that cell until now.

Claim `rado-r4-a5-b1` committed. The certificate is hash-pinned and
regenerable rather than stored (1.87 GB), with the 6.6x memory ratio written
into the regeneration note so a verifier can budget before starting.

`scripts/validate-claims.py` **rejected my first version**: `evidence
'upper-drat' declares artifact_format but names no artifact`. Correct — a
format field on a row with no bytes is exactly the say-so the B8 finding is
about. Removed the field; the row is now hash + recipe + parameters only.
(The same validator run reports 48 errors across the concurrently added
`offdiag-schur` claims, which are agent-a's and which I have not touched.)

Started `(6,1,4)` at n=1296 on the slot s1 freed — that cell is outside
Table 10's range entirely (`a <= 5`), so it is a new value if it lands.

Also wrote `FRAGMENTATION.md` at the coordinator's request: one row per
pipeline stage, the axeyum component against the tool it replaces, including
the four seams where the integration did not hold.

## 15. Memory arithmetic on the two new-value runs (t+4h)

Sizing the checks before they happen, using the 6.6x ratio measured on
`(5,1,4)`:

| run | host | RAM | proof so far | projected check RSS | headroom |
|---|---|---:|---:|---:|---|
| (5,2,4) n=625 | s1 | 61 GiB | 3.33 GB | ~22 GiB | fine |
| (5,3,4) n=625 | s7 | 26 GiB | 2.40 GB | ~16 GiB | **marginal** |
| (6,1,4) n=1296 | s1 | 61 GiB | 0.35 GB | unknown | fine |

Killed the two remaining low-value batsat probes on s7 to buy headroom. If
`(5,3)` is OOM-killed during its check the answer is to re-run it on s1, not
to report exit 137 as anything at all -- the brief is explicit that an OOM
kill reads exactly like a refuted claim and is not one.

This is the practical face of FEEDBACK item F-C7: the *solve* fits everywhere,
the *check* is what decides which host can carry a result.

## 16. Li's artifacts surfaced — and the census correction runs the other way (t+4h15)

The coordinator located the repo behind SSRN 6814341
(`crabsatellite/rado-numbers-sat`, MIT, Zenodo DOI 10.5281/zenodo.18957993).
Ground truth on the two things I had flagged as unread:

- They ship `data/results/R5_witness_243.json` and `R5_witness_296.json`, and
  their README says "Explicit R_5(3) > 296 witness and verifier. **The exact
  value is not claimed.**" So my `R_5(3(x-y)=z) > 243` is exactly what I
  assumed it was without being able to read them: a **weaker independent
  reproduction**. The claim already says so and stays that way.
- Their route is CaDiCaL 1.5.3 via PySAT with **no proof certificate** in the
  results file. Ours is certificate-backed end to end. That is the delta, and
  it is the only delta.

**They also asked me to re-check my census, and the correction runs the other
way.** Li marks `b=5 -> R_4 = 625` as `"NEW": true`. I went back to the
rendered PDF text, at the table itself rather than a summary:

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

Row `b=1`, column `a=5`, value **625**. My census stands; **Li's `"NEW": true`
on that cell is an overclaim** -- it is Chang-De Loera-Wesley Table 10, ISSAC
2022, and under the renaming their `b` is our `a` with our `b` fixed at 1, so
the cells correspond exactly. Our `rado-r4-a5-b1` claim is correctly labelled
a replication. (Two independent transcriptions of that table now agree with 35
independently computed ledger values, which is why I trust the reading rather
than my memory of it.)

Worth stating plainly because it is the second time today the discipline paid
in the same direction: *I was asked to check whether I had made an error, and
the check found that someone else had.* The procedure is the same either way.

## 17. Triage on the coordinator's reprioritisation (t+4h20)

Their status line says `k >= 5 OPEN` for every b, and `b=6` is null with the
note "n=1295 SAT confirmed, n=1296 UNSAT needs cluster". So:

- **`R_4(6(x-y)=z) = 1296`** is a stated open problem whose stated blocker is
  memory. Moved to **s4** (16 cores, 117 GiB free) and building there.
- **`R_5(4(x-y)=z) = 1024`** is now the highest-value instance in the
  campaign: their threshold conjecture predicts the `a^k` law survives at
  `k=5, a=4`, so UNSAT is the first exact five-colour Rado number in this
  family and SAT refutes the refined conjecture. Given **s7 to itself**.
- **`(5,3,4)` was going to OOM.** Its proof had reached 2.95 GB on s7; at the
  measured 6.6x that is ~19 GiB of check against 15 GiB available. Killed it
  there and restarted on **s0** (68 GiB available). Losing 35 minutes of solve
  is the correct trade against an exit 137 that reads like a refuted claim.
- `(5,2,4)` (4.18 GB of proof, ~28 GiB of check) keeps **s1** to itself.

## 18. My own scheduling error, caught by the sink (t+4h50)

Restarting `(5,3,4)` on s0 I put its DRAT in my scratchpad, which is on s0's
`/tmp` — a **62 GB tmpfs, i.e. RAM**, already 81% full. So I moved a job off
s7 to avoid an OOM and then arranged for its proof to be written into memory
on the new host. It died at 3.7 GB of proof with:

```
{"status":"sink-failed","error":"ProofSinkError { kind: QuotaExceeded,
  message: \"Disk quota exceeded (os error 122)\" }"}
```

Two things worth recording.

**The failure was honest.** `TextProofSink` reported `QuotaExceeded` through
`StreamingProofOutcome::SinkFailed` and my driver printed it as
`sink-failed` with exit 3 -- a *named* resource failure, not a truncated proof
and not a silent "unsat". That is the behaviour the ADR-0381 sink design
should get credit for: compare it with the OOM-kill path, which produces exit
137 and no message and reads exactly like a refuted claim. **A resource
failure that names itself is worth a great deal.**

**The lesson is mine, not the tool's.** The campaign rule says "rsync to the
remote's LOCAL disk and build there"; I honoured it for the build and ignored
it for the artifact. Restarted on s4 (`/dev/sda2`, 381 GB free, 119 GiB RAM),
which now carries both `(6,1,4)` at n=1296 and `(5,3,4)` at n=625.

Current layout: s1 = `(5,2,4)` alone (5.9 GB of proof at 69 min, will need
~39 GiB to check, has 49); s4 = `(6,1,4)` + `(5,3,4)`; s7 = the `(4,1,5)`
n=1024 batsat probe and a depth-6 cover, alone; s0 = nothing but my shell.

## 19. Hedging the two new values (t+5h05)

`(5,2,4)` on s1 is at **6.7 GB of proof after 80 minutes and still growing**.
At the measured 6.6x that projects to ~44 GiB of check against s1's 49 GiB
available -- inside the envelope, but only just, and the proof has not stopped
growing. Rather than find out at the end, started a **second, independent run
of the same instance on s4** (119 GiB available, 379 GB of local disk). First
one home wins; the other gets killed.

This is cheap insurance on the two cells that are genuinely new. It is also
the honest shape of the constraint: on this family the *solve* fits anywhere
and the *check* decides which host can carry a result, so the scheduling
question is "where will the check fit" and not "where is a core free".

s4 now carries three refutations concurrently at n=1296, n=625 (b=3) and
n=625 (b=2), for 2.87 GB + 1.16 GB + 0.05 GB of proof and 10 GiB resident.

## 20. The check that would not fit, and the mode that fixed it (t+5h40)

`(5,2,4)` at n=625 finished solving on s1 with **8,819,268,223 bytes** of text
DRAT after ~113 minutes, entered its check phase, and climbed to **55.7 GiB
resident** on a 61 GiB host. 8.82 GB x the measured 6.6 ratio is ~58 GiB. It
was going to be OOM-killed.

The proof itself was fine. `solve_with_drat_proof_streaming` returns, then
`sink.finish()` flushes, and only *then* does the driver read the file back --
so by the time the check phase is eating memory, the certificate on disk is
complete. Confirmed from the bytes: the file ends `... -217 0\n0\n`, i.e. the
empty clause.

So I killed the process and wrote a new driver mode instead:

```
akb2_frontier check <a> <b> <k> <n> <in.drat>
```

which regenerates the formula from the four parameters, parses the stored
proof with axeyum's own `parse_drat` and re-derives it with
`check_drat_backward`. **Nothing in the tree could do this**: `solve` bundles
production and checking, and `recertify_rado` always re-solves first
(`recertify_rado.rs:136`). Smoke-tested against `R_4(3(x-y)=z) = 81`, where
`solve` and `check` both report the ledger's recorded 164,538 steps.

The 8.8 GB certificate is now rsyncing s1 -> s4 (119 GiB available) where the
check can afford to run. 113 minutes of solve saved instead of re-derived.

Recorded as FEEDBACK F-C10. It is the concrete form of F-C7: the memory
asymmetry between producing and checking a proof is not a nuisance, it is a
scheduling constraint, and a pipeline that cannot move a certificate between
machines has to re-derive it every time the constraint bites.

## 21. Certificate checking is now a schedulable job (t+6h10)

Consequence of the `check` mode that only became obvious once it existed:
**checking is no longer tied to the host that solved.** s1 (61 GiB) sat idle
after its doomed `(5,2)` check was killed, so it is now provisioned as a
*checking host* -- binary deployed, nothing running. If `(6,1,4)` at n=1296 or
`(5,3,4)` finishes solving on s4 while `(5,2)`'s 58 GiB check is still
occupying it, the recovery is a four-minute rsync and a `check` invocation on
s1, not a re-solve.

Correction for the record, since the coordinator warned me about s0: the
`(5,3,4)` run is **not** on s0. It went to s0 briefly, died at 3.7 GB with
`sink-failed: QuotaExceeded` because s0's `/tmp` is a RAM-backed tmpfs, and I
moved it to s4 (`/dev/sda2`, 379 GB free) at t+4h50. Nothing of mine is on s0
now. The warning is right and it is the same lesson the quota failure taught
an hour earlier, from the other direction: on s0, *disk* and *memory* are the
same resource.

Projected cost of the outstanding `(5,2)` check, from the two ledger
datapoints for backward checking on this family (60.5M steps -> 44 us/step;
222.8M -> 62 us/step): its ~110M steps should land near 55 us/step, so about
100 minutes. It is 20 minutes in. That superlinearity is itself worth
recording -- the cost per step is not constant, so a proof twice as long costs
more than twice as much to check.

## 22. Wind-down (t+6h45)

The user has redirected the campaign from opening new cells to fixing axeyum
itself. Stopping accordingly. What was killed, and exactly where it stopped:

- **`R_4(6(x-y)=z) = 1296?`** Killed mid-solve at **1 h 49 m 35 s** with
  **6,034,320,667 bytes** of text DRAT written and no verdict. The lower bound
  `R_4 > 1295` IS established (valuation colouring, four checks); the
  refutation at 1296 is **not**. Nothing about it is known beyond that. For
  whoever picks it up: its proof was still growing at 6 GB, so budget ~40 GiB
  for the check, i.e. s4-class memory. Li's artifact set lists this cell as
  null with the note "n=1295 SAT confirmed, n=1296 UNSAT needs cluster", so it
  remains open on both sides of the fence.
- **`R_5(4(x-y)=z) = 1024?`** Both attacks killed undecided. The depth-6 cube
  cover completed **658 of 15,625 cells** in ~1 h 35 m; the batsat probe ran
  **2 h 17 m** without deciding. The lower bound `R_5 > 1023` IS established.
  The question that would have been answered -- does the a^k law survive at
  k=5 where Li's threshold conjecture says it should -- is **untouched**.
- **`R_5(2(x-y)=z)`** was already stopped (DIARY §17 / RESULT). Nothing
  established beyond the trivial `R_5 >= R_4 = 56`.

Still running, both genuinely-new Table 10 cells, both sunk cost worth
collecting:

- **`(5,2,4)` at n=625**: solve DONE (8,819,268,223 bytes of DRAT, ~113 min);
  its check is 42 minutes into a projected ~100 on s4 at 56 GiB resident.
- **`(5,3,4)` at n=625**: still solving on s4, 1 h 28 m in.

No new work started.

## 23. The memory wall stopped a mathematical result (t+9h)

`(5,3,4)` at n=625 -- one of the two genuinely-new Table 10 cells -- was
killed **mid-solve at 3 h 11 m 55 s with 15,507,983,062 bytes of text DRAT
written and no verdict**. The lower bound `R_4 > 624` is established
(valuation colouring, four checks); the refutation at 625 is **not**, and
nothing about it is known.

The reason for killing it is the point. Even if the solve had finished, at the
measured **6.6x** ratio a 15.5 GB certificate needs **~102 GiB resident** to
check, and it was still growing. **No host in this campaign has that** -- s4
and s0 are 123 GiB each and neither is idle; s1 is 61; s5/s6/s7 are 26-27.
So the run was producing a certificate that could not be checked anywhere,
which is not evidence.

This is F-C7 with the abstraction removed: **the checker's memory profile did
not slow a result down, it prevented one.** Two of this lane's four outstanding
targets ended this way -- `(5,3,4)` here, and `(6,1,4)` at n=1296 whose 6.03 GB
of proof would have needed ~40 GiB.

Also worth recording against the same item: `(5,2,4)`'s check is now **145
minutes** in against a ~107-minute projection built from the ledger's own
per-step costs. Backward checking is superlinear in proof length and my
extrapolation from 60.5M and 222.8M steps under-predicted at ~104M. Anyone
sizing these jobs should treat the per-step figures as a lower bound.

Left running: only `(5,2,4)`'s check. Nothing else of mine is on any host.

## 24. R_4(5(x-y)=2z) = 625 — a new exact four-colour Rado number (t+9h30)

```
{"status":"verified-unsat","mode":"check","a":5,"b":2,"k":4,"n":625,
 "steps":103409097,"drat_bytes":8819268223,"parse_s":60.546,"check_s":8703.254}
```

Solve 6576 s on s1, proof moved, parse + backward check 8763.8 s on s4. With
the 0.02 s valuation witness at 624, this is a complete both-sides value:

> **R_4(5(x-y) = 2z) = 625 = 5^4.**

The `(a,b) = (5,2)` cell is **blank** in CDLW Table 10 and satisfies both
hypotheses of their Theorem 1.2(3) (`a >= b+2`, `gcd(a,b) = 1`), so this is a
genuinely new exact four-colour Rado number. Li's `x+by=bz` work maps onto our
family only at `b = 1`, so it does not reach this cell either. Claim
`rado-r4-a5-b2` committed; both ledger gates pass.

One detail worth recording because it looks like a bug and is not: the
`lower-witness` artifact is **byte-identical** to `rado-r4-a5-b1`'s, same
sha256. Correct -- the valuation colouring `c(j) = v_5(j) + 1` does not depend
on `b` at all, so one object witnesses the lower bound for every `b` coprime to
5. Noted in the claim so nobody later "fixes" it.

This value is also the whole argument for the `check` subcommand in one
instance: its certificate was produced on a host that could not check it, and
without the ability to point a checker at a stored file the only options would
have been to re-derive 110 minutes of solving on a bigger machine, or to lose
the result. The move cost four minutes.

## 25. Final state (t+9h35)

Established and committed:

- `rado-r5-a3-b1-frontier` -- `R_5(3(x-y)=z) > 243`, the a^k law refuted at
  k=5. Reproduction of an existing preprint's result, certified.
- `rado-r4-a5-b1` -- `R_4(5(x-y)=z) = 625`. Replication of CDLW Table 10.
- `rado-r4-a5-b2` -- `R_4(5(x-y)=2z) = 625`. **New.**
- `crates/axeyum-search/examples/akb2_frontier.rs` -- the driver, six modes,
  including the `check` mode the tree lacked.

Open, with the exact stopping point recorded in RESULT.md: `(5,3,4)` at 625,
`(6,1,4)` at 1296, `(4,1,5)` at 1024, `(2,1,5)`. Every one of them has its
lower bound established and its refutation not.

No processes of mine are left running on any host.
