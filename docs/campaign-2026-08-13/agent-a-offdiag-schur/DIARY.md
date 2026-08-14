# agent-a diary — generalized off-diagonal Schur numbers S(3; s,t,u)

Append-only. Newest entry at the bottom.

## 2026-08-13, entry 1 — orientation

Target: `S(3;s,t,u)`, least `N` such that every 3-colouring of `[1,N]` has a
monochromatic solution to `L(s)` in colour 1, `L(t)` in colour 2, or `L(u)` in
colour 3, where `L(t)` is `x_1 + ... + x_{t-1} = x_t`. Ahmed-Schaal 2015
conjecture: `S = s*t*u - t*u - u - 1` for `4 <= s <= t <= u`. Eleven known
values all match. Ten open cells assigned.

Read `crates/axeyum-search/src/{family,colouring,search,cover}.rs`. Two things
matter immediately:

1. `ColouringFamily::constraints(points)` is colour-agnostic and
   `ColouringProblem` stores one flat `forbidden: Vec<Vec<usize>>` that the
   encoder replays *for every colour*. Off-diagonal needs a per-colour scope.
2. **The existing symmetry breaking is UNSOUND for off-diagonal.**
   `ColouringProblem::encode_symmetry_breaking`
   (`crates/axeyum-search/src/colouring.rs:213`) orders colour classes by least
   element and pins point 1 to colour 1. That is justified only because "colour
   names are interchangeable". In an off-diagonal instance colour 1 forbids
   `L(s)` and colour 3 forbids `L(u)`; they are *not* interchangeable unless
   `s == u`. Using the stock encoder here would have produced a wrong `unsat`
   and a "refuted conjecture" that was an encoder bug. Plan: per-colour
   constraint scopes plus symmetry breaking restricted to *blocks of colours
   with equal parameters* (which are genuinely interchangeable).

## 2026-08-13, entry 2 — the encoding is far cheaper than the clause table says

The brief's clause counts (2.6M for the smallest open cell, 47.9M for the
largest) count one clause per *multiset* of `t-1` parts. Most of those clauses
are subsumed.

Two facts about `L(k)` for `k >= 4`: the sum of `k-1 >= 3` positive integers
strictly exceeds every part, so a solution's distinct-value set always has size
`(#distinct parts) + 1`; in particular the only size-2 sets are
`{a, (k-1)a}` (all parts equal). Any solution set containing both `a` and
`(k-1)a` is therefore subsumed by a binary clause.

Measured with a throwaway enumerator (scratch `proto`), full set vs.
subsumption-minimal antichain:

| k | n | all solution multisets | minimal antichain | ratio |
|---|---:|---:|---:|---:|
| 4 | 43 | 2,282 | 1,870 | 0.82 |
| 4 | 87 | 18,600 | 16,751 | 0.90 |
| 8 | 87 | 2,576,807 | **77,314** | 0.030 |
| 5 | 160 | 1,180,349 | 896,020 | 0.76 |
| 6 | 160 | 7,976,497 | 2,838,602 | 0.36 |

So `S(3;4,4,8)` at `n = 87` is ~111k clauses, not 2.6M. The reduction is strong
exactly when `n/(k-1)` is small (many `{a,(k-1)a}` binaries relative to the
number of partitions) and weak when it is large.

Soundness of the reduction, both directions, no extra argument needed:
the minimal antichain is a **subset** of the full clause list, and every
dropped clause is implied by a retained one (superset clause implied by subset
clause), so the two formulas have exactly the same models. UNSAT on the reduced
formula implies UNSAT on the full one; SAT is verified by the independent
`first_violation` enumerator anyway.

## 2026-08-13, entry 3 — the trait extension, and what it forced

`ColouringFamily` gained `constraints_for_colour(colour, points)`,
`colour_dependent()` and `symmetry_blocks()`, all with defaults that leave every
uniform family byte-identical. `ColouringProblem` gained a `per_colour`
constructor carrying a per-set colour scope and caller-supplied symmetry blocks.

Three things this turned up that were not in the plan.

1. `min_conflicts` (`crates/axeyum-search/src/search.rs:136`) had a local
   `monochromatic` closure that re-derived "all members share a colour". That is
   a *third* copy of the violation predicate, and unlike `first_violation` it was
   not deliberate independence — it was duplication. It would have silently
   reported a colour-1 monochromatic set as a violation of a colour-2
   constraint. Now routed through `ColouringProblem::constraint_violated`.
2. The uniform encoding is byte-identical, and I proved it rather than asserting
   it: built pristine `HEAD` and my patched tree side by side, dumped
   `to_dimacs` for 29 Rado/Schur instances (556,911 bytes) and `diff -r`'d them.
   Identical.
3. `l3_is_schur` failed the first time I ran it because I wrote the expected set
   list by hand and forgot `1+2=3 -> {1,2,3}`. The test was right, my expectation
   was wrong; it now also cross-checks against the crate's existing `Schur`
   family, which enumerates by right-hand side instead of by parts.

## 2026-08-13, entry 4 — the negative control, and it fires

The coordinator asked for a control showing the whole-palette symmetry break
producing a demonstrably wrong verdict when misapplied. Scanning small
off-diagonal instances:

| instance | correct encoding | whole-palette break |
|---|---|---|
| S(3;3,3,4), n<=23 | threshold at 23 | agrees |
| S(3;3,4,4), n<=31 | threshold at 31 | agrees |
| S(3;3,3,5), n<=32 | threshold at 32 | agrees |
| S(3;4,4,5), n<=54 | threshold at 54 | agrees |
| **S(3;3,4,5), n=41** | **sat** | **unsat** |

So four of the five instances I tried would have *passed* a test built on them —
the over-strong constraint happened not to bite. `S(3;3,4,5)` at `n = 41` is the
one that fires, and it is now
`tests/offdiag_schur.rs::whole_palette_symmetry_breaking_produces_a_wrong_unsat`.
This is the concrete form of "a symmetry break that cannot be shown to break
something has not been tested": I could easily have picked one of the other four
and shipped a vacuous control.

Incidental corroboration from the same scan: it found `S(3;4,4,5) = 54` by
incrementing `n` until the correct encoding turned unsat — a completely
different loop from the decide path, agreeing with the published value.

## 2026-08-13, entry 5 — the SLS was the bottleneck, not the solver

I built the sat side around `search::min_conflicts` because the crate's docs say
local search finds colourings "orders of magnitude faster than the CDCL core on
the instances this crate was built for". On *these* instances that is backwards.

Measured, same machine, same encoding:

| instance | min_conflicts (14 lanes) | proof-producing CDCL |
|---|---:|---:|
| S(3;4,4,4), n=42 | 1.2 s | 0.00 s |
| S(3;4,4,5), n=53 | 9.1 s | 0.00 s |
| S(3;4,4,6), n=64 | 12.6 s | 0.00 s |
| S(3;4,5,5), n=68 | 83.8 s | 0.00 s |

The whole known-value regression was re-run through the CDCL core for both
sides and finished all eleven published values in **119 seconds**, including
`S(3;6,6,6) = 173` (13,251,885 clauses; unsat in 1.1 s, proof checked in 11.1 s).
The Rado instances that motivated the SLS are 3- and 4-colour with dense
overlapping triples; these are 3-colour with a huge number of short clauses and
strong unit propagation, and CDCL eats them.

## 2026-08-13, entry 6 — first new values

`S(3;4,4,8) = 87` fell in nine seconds: `n = 86` sat with the model replayed by
`first_violation`, `n = 87` unsat with a 254-step DRAT proof re-derived by
`check_drat_backward`. Matches Ahmed-Schaal. Then `S(3;5,6,6) = 137`,
`S(3;4,6,7) = 118`, `S(3;4,4,9) = 98`, `S(3;5,5,7) = 132`, `S(3;4,7,7) = 139`,
all in minutes, all matching.

The coordinator was right that its clause table stopped short of the real
frontier, so I opened an extended lane past the assigned ten. `S(3;4,4,11) = 120`
is the first value outside the brief's list.

## 2026-08-13, entry 7 — the reduction pass, 15x

Profiling the extended lane: `S(3;4,4,11)` at `n = 119` spent five and a half
minutes in the subsumption pass, not the solver. The pass was probing a
`HashSet<[u64;4]>` once per subset of every candidate — tens of millions of
candidates times dozens of subsets.

Replaced the size-2 and size-3 probes with dense bitmaps (a 8 KB pair table and
a 2 MB triple table, indexed arithmetically), leaving the hash table only for
size >= 4. Practically all subsumption comes from the binaries `{a, (k-1)a}` and
the triples, so this is where the probes go.

- `S(3;4,4,8)` reduction: 4.5 s -> 0.3 s.
- `S(3;4,4,11)`, both sides including enumeration: 5.5 min+ -> 45 s per side.
- `tests/offdiag_schur.rs` in the debug profile CI uses: 63.7 s -> 14.0 s.
- Output unchanged: same 75,433 minimal sets, same 109,370 clauses.

Note for anyone repeating this: I had to kill the running s5 lane to deploy the
faster binary, and I moved its log aside as
`extended-s5-abandoned-old-binary.out` rather than letting the new run append to
it. Two runs interleaved in one log is how a ledger ends up with 1093 rows over
a 1024-cell product.

## 2026-08-13, entry 8 — the whole assigned list falls, and the brief's frontier was not the frontier

All ten assigned open cells decided from both sides, plus the eleven published
values as the regression gate, in about twenty minutes of wall clock across two
16-core hosts. Then the extended lane past the brief's list: `(4,4,11) = 120`,
`(4,4,12) = 131`, `(4,5,9) = 125`, `(4,6,9) = 152`, `(4,7,8) = 159`,
`(5,5,8) = 151`, `(5,5,9) = 170`, `(5,6,8) = 183`, `(4,5,10) = 139`, ...

Every cell agrees with `s·t·u − t·u − u − 1`. No mismatch anywhere.

The real wall turned out to be **enumeration, not solving**. Every instance in
the campaign is refuted by the CDCL core in under 2.2 s; `S(3;4,4,10)` at
`n = 109` spends 110 s enumerating 46.3M solution multisets to keep 239,130
clauses which are then refuted in 0.03 s. That is a strange and useful place to
be: the bottleneck is the part that builds the problem, not the part that
decides it.

## 2026-08-13, entry 9 — a lane exited 0 having done nothing

`bundle-lane2.sh` pointed at `$HOME/scratch/agent-a/target/...` instead of
`target2/...`. The old binary had no `bundle` subcommand, so it panicked on
every cell — and the loop had no `if`, so the script printed
`BUNDLE-LANE2-COMPLETE` and exited 0 with three cells silently missing. I only
caught it because the claim generator refused to build claims from incomplete
bundles and printed `SKIP ...: incomplete`.

This is the house failure mode in its purest form and it is worth writing down
that *I produced it myself*, two hours after quoting the rule. The replacement
counts what it made and says `made=3 of 3 requested`. A lane that cannot report
a count is not reporting anything.

## 2026-08-13, entry 10 — five of my "new" values were published in April, and that is the good news

The coordinator extracted the full text of arXiv:2604.11030 rather than the
abstract and found a Section 5 with a **Table 3** of the authors' own exhaustive
computer search. It contains `S(3;4,4,8)=87`, `S(3;4,4,9)=98`,
`S(3;4,4,10)=109`, `S(3;4,5,8)=111`, `S(3;4,6,7)=118` — five of the cells I had
just labelled NEW.

All five agree with mine exactly. So the regression gate is not eleven published
values but **sixteen**, and five of them were computed four months ago by a
different group with a different toolchain and a conventional SAT pipeline. That
is an external cross-validation of our encoder, our solver and our checker on
exactly the cells where a wrong `unsat` would have been invisible, and it is
worth more than five unverified values would have been.

I re-derived the classification myself rather than accepting it (the coordinator
asked me to; it had been wrong once already today). Result: their "six still
new" is actually **eleven**, because the extended lane had produced five more
cells since they compiled the list. The claim files now say REPRODUCES or NEW
per cell and cite Table 3 where it applies.

## 2026-08-13, entry 11 — chasing an anomaly in the published table

Song–Mao's `S(3;3,3,u)` row reads 59, 68, 77, 86, **94**, 104, 113, 122 for
`u = 8..15`. Every step is +9 except `u = 11 → 12`, which is +8, and `12 → 13`,
which is +10. `9u − 13` fits every entry except `u = 12`, where it predicts 95.
That is exactly the shape of a transcription error, so I recomputed the row from
scratch by bisection.

`S(3;3,3,8) = 59`, `= 68`, `= 77`, `= 86`, and **`S(3;3,3,12) = 94`** — their
value, not 95. The break in the progression is real. `9u − 13` is not a formula
for this row, and now we know that rather than suspecting it.

(This also exercised a new `threshold` mode: satisfiability is monotone in `n`,
so the exact value is found by bisection over a bracket, with both ends of the
bracket confirmed first and both sides of the answer re-decided at the end. A
bisection that never evaluated the boundary is not a value.)

## 2026-08-13, entry 12 — wrap-up state, and what is honestly unfinished

32 cells decided from both sides. 11 reproduce Ahmed–Schaal's exact values, 5
reproduce Song–Mao arXiv:2604.11030 Table 3, 16 are new. Every one agrees with
`s·t·u − t·u − u − 1`. **The conjecture survived every test I could put to it.**

The measurement that best explains why the frontier moved:

| cell | solution multisets | encoded clauses | factor |
|---|---:|---:|---:|
| S(3;4,4,10) — Song–Mao's last | 46,281,800 | 239,130 | 194 |
| S(3;4,4,11) — new | 176,224,094 | 323,293 | 545 |
| S(3;4,4,12) — new | 633,107,771 | 451,622 | **1,402** |

On the raw count `(4,4,12)` is thirteen times larger than the biggest cell
anyone proposed attempting; on the encoded count it is *smaller* than
`S(3;4,5,8)`, which Song–Mao did compute. The `(4,4,u)` row only looks hard, and
it looks hard in exactly the metric a conventional pipeline uses to decide what
to try.

Unfinished, stated exactly, because a half-decided cell is not a value:

* `S(3;4,4,13)`: `n = 141` sat, `n = 142` still running at wrap-up. No claim.
* `S(3;3,3,15)`, `S(3;3,4,8..12)`, `S(3;3,5,8..10)`: bisection lane still
  running. No verdicts.
* Four decided new values (`(5,6,8)=183`, `(5,7,7)=188`, `(6,6,7)=202`, and the
  tail of the bundling queue) have verdicts and DRAT proofs in `artifacts/` but
  no claim-ledger entry yet. 18 of 32 cells are packaged.
* The unreduced multiset counts are measured for 15 cells, not all 32.

The last honest note is a pointer, not a complaint: **enumeration is now the
bottleneck and it is a modelling-layer problem.** `S(3;4,4,12)` spends 164 s
generating 633 million multisets in order to keep 451,622 of them; the CDCL core
then refutes those in 0.1 s. Generating the subsumption-minimal antichain
*directly* — by enumerating partitions with few distinct part values and proving
nothing beyond a bounded number of distinct values can be minimal — is the one
change that would move the frontier again, and nothing in the framework helps
with it today.

## 2026-08-13, entry 13 — the tally I added to fix a silent lane was itself wrong

`bundle-lane3.sh` finished the last four cells and printed
`BUNDLE-LANE3 made=4 of 3 requested`.

The numerator is right — four bundles, all four verified. The denominator is
garbage: `set -- $c` inside the loop rewrites `$#`, so "requested" ends up as the
arity of the *last* cell spec (three: `5 7 7`) rather than the number of cells.

I added that tally two hours earlier specifically because a lane had exited 0
having done nothing, and wrote in FEEDBACK that "the thing that failed was a
producer that counted nothing". The counter I put in its place was wrong on the
first run I read carefully. It would have said `made=4 of 3` for a run that
dropped a cell too, and `of 3` looks enough like a real number to skim past.

Both cells did land, so nothing is wrong with the result — `S(3;5,6,8) = 183`
and `S(3;5,7,7) = 188` are decided, checked and now in the ledger. But the
lesson upgrades: a count is only evidence if *both* ends of it come from
somewhere the loop cannot clobber. Capture `$#` before the loop, or count the
inputs the same way you count the outputs.

## 2026-08-13, entry 14 — final state

**20 claims in the ledger, 0 errors. 32 cells decided, all agreeing with
`s·t·u − t·u − u − 1`. Ahmed–Schaal Conjecture 2 survived everything.**

Largest instances: `S(3;5,7,7)` at `n = 188` is 19,807,560 clauses in a 526 MB
CNF, refuted by a **345-step, 2.5 KB** proof. That ratio is the family's
signature and the reason the ledger stores proofs and regenerates formulas: what
must be trusted is tiny, what must be rebuilt is enormous.

Still unfinished at wrap-up, unchanged from entry 12 except that the four
bundling cells are now packaged: `S(3;4,4,13)` half-decided (`n=141` sat, `n=142`
never returned), and the `s = 3` bisections for `(3,3,15)`, `(3,4,8..12)`,
`(3,5,8..10)`. No verdicts claimed for any of them.

## 2026-08-13, entry 15 — an exit 137, and the guard that stopped it looking like a result

`S(3;3,3,15)` was **OOM-killed**. The bisection confirms both bracket ends before
bisecting; `n = 100` returned sat, and the `n = 150` probe died enumerating
`L(15)` solutions — partitions of `s <= 150` into 14 parts — on a 26 GiB host.

```
  n=100: sat (48308 clauses), witness replayed
  s3-rows.sh: line 7: 373026 Killed   timeout 3600 "$BIN" threshold 3 3 15 100 150
  rc=137 -- see above, NOT a verdict
```

Song–Mao report `S(3;3,3,15) = 122`. **We neither confirm nor contradict it.**
The brief's warning is exact — a resource kill reads exactly like a refuted claim
— and the shape here is worth noting: the kill happened on the *upper* bracket
probe, so the visible transcript is "sat at 100, then nothing". Without the
`rc=137` annotation that is indistinguishable from a lane that simply moved on,
and a later reader reconstructing the row from `THRESHOLD` lines would find a
silent gap rather than a recorded failure.

Everything else in the `s = 3` lane landed: `(3,3,8..14)` and `(3,4,8..11)`,
**11 bisections, 11 agreements with Song–Mao, zero mismatches.** Their `(3,4,u)`
row's ragged 11, 8, 12 progression (67, 78, 86, 98) reproduces entry for entry,
so like the `(3,3,12)` break it is real rather than a transcription artefact.

Meanwhile the `s >= 4` lane kept going: `S(3;4,4,13) = 142` and
`S(3;4,5,11) = 153`, both new, both matching the formula. Running total: **45
cells decided, 27 published values reproduced, 18 new, no mismatch anywhere.**

## 2026-08-13, entry 16 — task change: stop opening cells, package what is paid for

Coordinator redirected the lane: 20 of 45 decided cells carried a ledger entry
and 25 did not, which is the difference between "we computed this" and "the
system can re-derive it on demand". Stopped all discovery.

Lanes killed, and where each stopped:

* **s5 / `extended-s5.sh`** — killed during `S(3;4,4,14)`, conjectured `N = 153`.
  The `n = 152` probe had run 7m33s at 3.3 GB. **Neither side returned; no
  verdict.** Killing the `n = 152` process let the inner `decide.sh` advance to
  `n = 153`, which had to be killed separately — worth knowing that killing the
  lane script does not kill its descendants, and `pkill -f <script>` matched
  nothing because the script runs as `/bin/bash <path>`.
* **s6 / `s3-rows.sh`** — killed during the `S(3;3,5,10)` bisection, bracket low
  end `n = 90` confirmed sat, upper probe in flight. **No verdict.**

Two more `s = 3` values had landed before the kill that I had not yet harvested:
`S(3;3,4,12) = 106`, `S(3;3,5,8) = 91`, `S(3;3,5,9) = 103` — all matching
Song–Mao. Final tally: **48 cells decided, 30 published values reproduced with
zero disagreements, 18 new.**

## 2026-08-13, entry 17 — the same stale-binary bug twice, forty minutes apart

The s5 packaging lane failed all fourteen cells with `rc=101`. Cause: I pointed
`BIN` at `~/scratch/agent-a/target/`, which was built *before* the `bundle`
subcommand existed. Redeployed, and it failed all fourteen again — this time
`rc=127`, because my snapshot directory had lost `offdiag_frontier.rs` (I had
deleted the scratch examples before a clippy run and never restored that one to
the snapshot, only to the local build).

The point is not the two mistakes. It is that **both were visible in seconds**,
because the lane prints `made=0 failed=14 of 14 requested`. Forty minutes
earlier the identical class of bug — a lane invoking a subcommand its binary did
not have — printed `COMPLETE` and exited 0 with three cells silently missing,
because that version of the script counted nothing.

Same defect, same host, three occurrences, and the only variable that mattered
was whether the producer emitted a count. That is about as close to a controlled
experiment as this kind of thing gets, and it is why FEEDBACK item 8 is written
as a requirement on how runs report rather than as advice.

## 2026-08-13, entry 18 — the cell that could be decided but not packaged, and a wrong diagnosis

`S(3;4,4,13)` was decided earlier (`n = 141` sat, `n = 142` unsat, 208-step
proof, checked). Re-running it to package the evidence drove s5 to 10.6 GB RSS
with 0 GB available on a 27 GB host, and I killed it.

I wrote up the cause as `to_dimacs()` materialising the whole DIMACS as a
`String` beside the live formula — a real defect, and a plausible story. Then I
went to put the numbers in RESULT.md and opened the decide run's own log line:

```
# n=141: 558350 clauses, built in 686.0s   peakRSS=13956132kB
# n=142: 578773 clauses, built in 762.8s   peakRSS=15297660kB
```

**The decide run already peaked at 15.3 GB per side.** The cost is the `L(13)`
enumeration and subsumption pass, not serialisation. Deciding this cell was
never comfortable — it fit only because each side ran in its own process with
nothing else live. `bundle` runs both sides in one address space and then
renders the text, so it wants ~2x that plus the string. Packaging did not fail
because packaging is expensive; it failed because I put two 15 GB phases in one
process.

The uncomfortable part: `peakRSS` was printed by my own harness, into my own
log, for the exact cell I was theorising about, and I published a cause without
reading it. `CLAUDE.md` says "prefer a measurement over a message, including the
ones you just wrote", I quoted that line earlier today, and it caught me anyway.
What actually caught it was the discipline of putting the number in RESULT.md
next to the claim, where the two had to agree and did not.

Fallback taken: all four heavy cells — `(4,4,13)`, `(4,5,11)`, `(6,6,6)`,
`(6,6,7)` — packaged from the DRAT proofs already stored in `artifacts/` plus
the witnesses recorded in the run logs, with the deciding CNF marked
regenerable. Their witness rows are fully re-checkable; their unsat rows are
reported by the checker as NOT re-checked here, which is the honest outcome.

## 2026-08-13, entry 19 — closed

**48 cells decided, 48 packaged, 0 ledger errors.** 30 reproductions of other
people's published values with zero disagreements; 18 new values; every one
consistent with `s·t·u − t·u − u − 1`. Ahmed–Schaal Conjecture 2 survived
everything I could put to it.

Both hosts idle, both verified clear. Lanes stopped at:

* `S(3;4,4,14)` — `n = 152` probe killed at 7m33s/3.3 GB, no verdict either side.
* `S(3;3,5,10)` — bisection killed with `n = 90` sat confirmed, upper probe in
  flight, no verdict.
* `S(3;3,3,15)` — OOM (exit 137) on the bracket's upper probe, no verdict.

Nothing rounded, nothing extrapolated, nothing claimed for those three.

What I would tell the next agent on this family, in order of value:

1. **The 30 reproductions matter more than the 18 new values.** They are what a
   referee can check cheaply, and they cover exactly the cells where this
   family's characteristic failure — a wrong `unsat` from unsound colour
   symmetry breaking — would surface immediately.
2. **Generate the antichain directly.** 762 s and 15.3 GB to build 578,773
   clauses refuted in 0.1 s is the entire cost model. Enumerating 10^8–10^9
   multisets to keep 10^5 of them is the only thing standing between here and
   the next row.
3. **Every producer emits a row per requested item, and every consumer counts.**
   Three separate failures today had the same shape — a green-looking absence —
   and the only variable that mattered was whether something counted.

## 2026-08-13, entry 20 — 228 validator errors, and the one that had been invisible

agent-e repaired three gates that were reporting success over work they were not
doing. One was `scripts/validate-claims.py`: `novelty` — the field *I* added
this session — was missing from its schema, so **62 claims failed on that single
message and it masked 228 real errors underneath**, essentially all mine. My
claims had never satisfied this contract; nothing could see it.

That is worth sitting with. I added `novelty` *because* a label inside a
machine-checked ledger was going unchecked, and the way I added it made a
different gate fail closed on a message that hid two hundred genuine defects.
The fix and the failure were the same commit. Two gates disagreeing about a
schema is not a thing either gate can detect on its own — only running both is.

Four shapes, all fixed, with the reasoning:

1. **`formal.generator` did not exist.** I had put a path *plus a parenthetical
   symbol* — `…/offdiag.rs (OffDiagonalSchur::minimal_problem)` — in a field the
   validator resolves as a path. **Fixed the data, not the check.** The field's
   contract is plainly "a path that exists" (the Rado claims use a bare
   `scripts/gen-rado-instance.py`), and embedding a symbol made it
   un-machine-checkable for no gain. The entry point moved to `notes` and it was
   already in SEMANTICS.md.

2. **`resolved: true` with no `graph_pin`.** Resolved against *what?* The
   validator is right. Now pinned to `../math-education` HEAD
   `819a591f682dc38f2b49d61047e75e65beccf8b7`, and I checked the three resolved
   refs exist **at that commit** with `git cat-file -e`, not merely in the
   working tree — which is the exact method whose absence produced yesterday's
   false "dangling pin" report. (I also confirmed the Rado pin `a29a9e2a…` *is*
   an ancestor of HEAD, so it was never dangling; the local clone was behind.)

3. **`C:schur-number` referenced by all 48 claims and absent from the graph**
   (census of 1784 ids; the other four refs resolve). I authored
   `graph/concepts/schur-number.md` in the sibling repo — it passes that repo's
   own `scripts/mathed.py validate` at 0 errors — and **left it uncommitted**
   for the maintainers, keeping all 48 refs `resolved: false` with a note saying
   exactly why. Marking it resolved against a pin that does not contain it would
   have manufactured a second instance of the stale-resolution defect, to save
   one round trip. Not worth it.

4. **Stray `F_<n>.cnf.gz` files.** Not leftovers — each sits in the claim whose
   `n` it is. My generator referenced them from `evidence[].parameters`, which is
   not where the validator looks. Fixed with an explicit hash-pinned
   `instance-pin` row, which is strictly better than either alternative: the
   certificate checker already validated those CNFs clause by clause and nothing
   in the record said so. **32 instance-pin rows are now re-checked clause by
   clause**, assurance that previously existed but was undeclared.

## 2026-08-13, entry 21 — I edited a gate another lane had just repaired

Recording this because the coordinator asked for the disagreement to be legible
rather than silently overwritten.

An `instance-pin` must declare `artifact_format: "dimacs-cnf"`, and
`ARTIFACT_FORMATS` had no gzip variant — so a gzipped deciding instance could
not be pinned at all. I added `dimacs-cnf-gzip` to `validate-claims.py`, which
agent-e had repaired hours earlier.

My justification, and I checked each part rather than asserting it:

* the vocabulary's own comment says it "names only formats this ledger actually
  stores" — and the ledger now stores gzipped DIMACS;
* `drat-text-gzip` *and* `drat-binary-gzip` already exist, with the deliberate
  note "under a gzip envelope … undone by the checker harness before parsing";
* **`detect_artifact_format` already returned `dimacs-cnf-gzip`** (`fmt +
  envelope`), so the sniffer could classify a file the vocabulary then rejected
  as `unknown`. That is an internal inconsistency, not a policy.

The alternatives were measured, not guessed: storing the CNFs uncompressed costs
**155.3 MB against 23.7 MB** in a claims directory already at 224 MB; deleting
them costs the clause-wise CNF validation on all 32 — the check that exists
specifically because it catches this family's characteristic wrong-`unsat`.

Two constraints I kept: `dimacs-cnf-gzip` is **not** in
`CHECKER_READABLE_FORMATS` (a deciding instance is not a proof, and conflating
those contracts is the B8 defect in new clothes), and rule 1 still matches the
declared format against the **bytes**.

Controls, built from *identical CNF bytes* so only the envelope differs:

| fixture | declared | bytes | format errors |
|---|---|---|---:|
| gzipped, declared plain | `dimacs-cnf` | `dimacs-cnf-gzip` | **1** |
| plain, declared gzipped | `dimacs-cnf-gzip` | `dimacs-cnf` | **1** |
| gzipped, declared gzipped | `dimacs-cnf-gzip` | `dimacs-cnf-gzip` | 0 |
| plain, declared plain | `dimacs-cnf` | `dimacs-cnf` | 0 |

Both directions fail, both correct declarations pass. The entry adds a
distinction rather than blurring one — which is the thing that needed showing,
since yesterday four of five candidate controls did not fire.

## 2026-08-13, entry 22 — a schema misuse the validator caught that I had not noticed

Four claims had `regeneration.produces_sha256: ""`. Chasing it turned up a
design error rather than a typo: I had put a `regeneration` block on the
**unsat-certificate** row, describing how to regenerate the **deciding CNF**.
But that row's artifact is the DRAT proof, and it *is* stored. `regeneration`
means "this row's artifact is absent, here is how to make it". I had used it to
describe a different file, which is why four cells whose CNF was never generated
had nothing to put in the hash.

Removed it. The recipe lives in the row's notes; the **absence of an
instance-pin row** is now what says the CNF is not here, and the certificate
checker reports those rows as NOT re-checked on that basis rather than on a
`distribution` marker. Cleaner, and it made the malformed-hash error disappear
by construction instead of by filling the field in.

Final state, **both** gates:

```
python3 scripts/validate-claims.py          ->  102 claims, 0 errors
python3 scripts/check-claim-certificates.py ->  102 claims re-checked, 0 errors,
                                                23 row(s) not re-checked here
```

Zero, not a smaller number of masked messages. The 23 are named individually
with their regeneration commands, which is the honest half and stays honest.

## 2026-08-13, entry 23 — refs flipped, and a wrong number in my own prose

`C:schur-number` is committed to `math-education` as `ce3e2a5`. Re-pinned all 48
claims to `ce3e2a52e7c95075d69262b4d8f0ee8fe748f22c` and flipped the ref to
`resolved: true`, after verifying **all five** refs exist at that exact commit
with `git cat-file -e` — not in the working tree. Census now 1785 ids, up one,
and my claims report **zero pending refs** where every one previously carried
one.

The coordinator found an error in the node I wrote. I had listed the known Schur
numbers as `5, 14, 45, 161, 538`. `538` is not a value — six colours is bounded
below (`>= 537` in this file's convention, from an exhibited colouring) — and
the list had also dropped `S(1) = 2`, so a bound sat in a value's place while
the count still read "five". It broke the following clause too, since "settled
in 2017" is `S(5) = 161`.

I checked the correction instead of taking it, and it holds. Under the file's
own convention (`S(2) = 5`, which its body demonstrates with `{1,4}/{2,3}`),
`S(1) = 2` because `1+1=2` is the smallest forced solution; the five known are
`2, 5, 14, 45, 161`; and exhibiting a colouring bounds the least-`N` threshold
from below, which is the direction the corrected sentence states.

What makes this worth an entry rather than a shrug: **it is the same defect
shape as the one I caught in the brief twelve hours earlier**, running the other
way. The brief gave me ten "open cells" precisely because
`S >= s·t·u − t·u − u − 1` is a theorem and the equality is a conjecture — the
entire structure of my task was "a bound is not a value". The coordinator's own
`w(2;3,20) = 389` was a certified lower bound briefed as an open problem. And
then I wrote one into a knowledge-graph node.

The ledger enforces this perfectly: `supports` reads `S > 119` or `S <= 120`,
never `S = 120`, and a cell is a value only when both rows exist. That rigour
stopped dead at the sentence boundary — in a file I wrote minutes after building
the gate. Written up as FEEDBACK item 14, with the concrete suggestion that a
numeric claim in prose should carry its relation and citation adjacent, the way
an evidence row does.
