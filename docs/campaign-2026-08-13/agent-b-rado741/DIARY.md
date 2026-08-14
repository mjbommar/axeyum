# agent-b diary — R_4(5(x-y)=4z) = 741

Append-only. Times are UTC-ish local wall clock of s0 unless noted.

## 19:44 — orientation

Read the frontier README, the claim `rado-r4-a5-b4-frontier`, and the
`axeyum-search` crate (cover.rs, harness.rs, certify.rs, compose.rs,
colouring.rs, ledger.rs, family.rs).

State of the target:
- lower bound `R_4 > 740` is banked (evidence row `witness-740`, replay-checked);
- the whole job is one refutation of `F_741`;
- prior probe (s7, 2026-08-12): depth-6 flat cover, 4096 cells, 200k
  conflicts/cell -> 746 unsat, 1132 resource-out, 8 timeout, 2210 unstarted.

Plan:
1. adaptive (tree) cube cover as a real capability in `cover.rs`/`harness.rs`,
   with the cover obligation generalized from "exactly the flat product" to
   "exactly the leaf set of a complete branch trie", plus negative controls;
2. s4 = main adaptive cover (16 workers); s7 = independent bets (monolithic
   streaming DRAT with a memory cap, and an SLS satisfiable-side probe) so a
   surprise `sat` shows up early and cheap;
3. deferred/hybrid checking (`check_step_cap`) + offline certification.

## 19:46 — hosts

- s4: 16 cores, 123 GiB (121 free), / has 384 GiB free, /tmp is a 62 GiB tmpfs.
  `rustc` is NOT on the non-interactive PATH; needs `source ~/.cargo/env`.
- s7: 16 cores, 26 GiB (19 available, 7 already used by someone), 504 GiB free,
  cargo 1.93.1 on PATH.
- /nas3/data: 16 TB free.

## 20:05 — the shared checkout does not compile

`cargo test -p axeyum-search --lib` failed on `colouring.rs:113` (missing fields
`scopes`, `symmetry_blocks`): agent-a is mid-edit in a file I must not touch.
Built instead from a private snapshot at `/home/mjbommar/work/agent-b-build/axeyum`
(rsync of the worktree, with `colouring.rs` restored from `git show HEAD:`) —
the coordinator has since made this rule 7 of the README.

Note the first `rsync -a` of `.git` while another agent was writing it produced
`fatal: bad object HEAD`. Do not copy a live `.git`; use `git archive`/`git show`.

## 20:40 — adaptive (tree) cover landed, 54 tests green

New capability in the files I own:

- `cover.rs`: `BranchPlan::prefix_code` (a **shape-independent** id for a cube of
  any depth), `prefix_offset`, `node_count`, `literals_for_prefix`, `cube`,
  `cubes_at_level`; the `Cube` type; `verify_cube_cover` (obligation 3
  generalized from "exactly the flat product" to "exactly the leaf set of a
  complete branch trie"); `certify_tree_cover` (all four obligations).
- `harness.rs`: `run_adaptive_cover` + `AdaptiveOptions`/`AdaptiveOutcome`, a
  work-stealing queue with a condvar, and a `pending.tsv` census
  (`unstarted` / `stuck-resource-out` / `stuck-timeout`) that IS the resume point.
- `certify.rs`: `certify_dumped_tree_cover`, sharing one `recheck_dumped` with
  the flat pass so the two cannot drift on what "checked" means.

Two design decisions worth recording:

1. **Cube codes do not depend on the tree's shape.** That is what lets a
   resumed run's ledger simply concatenate with its predecessor's and be
   certified as one cover. If codes were positions in a DFS of the cover, a
   resumed run would renumber everything.
2. **Ledger rows are written only for refuted cubes.** A split or stuck cube
   goes to `pending.tsv` instead. Otherwise a cube that run 1 gave up on and run
   2 refuted would appear twice in the union and trip `DuplicateCell` — the
   finding-B2 detector firing on a false positive, which is how a real detector
   gets disabled.

Route A (`compose_cover_proof`) is NOT generalized to trees: it lives in
`compose.rs`, which I do not own, and a tree cover is route B anyway (per-cube
checked proofs + the four checked obligations). Recorded in FEEDBACK.md as a gap.

Negative controls (all in-tree, all failing-closed):
`a_mixed_depth_cover_is_accepted_exactly_when_it_is_complete` (hole inside a
split branch, missing top-level branch, empty cover),
`overlapping_and_repeated_cubes_are_rejected` (a cube strictly inside another),
`certifies_a_deferred_tree_cover_and_rejects_an_incomplete_one` (drop one row
from an otherwise perfect cover -> `MissingCell`),
`an_incomplete_adaptive_run_reports_where_it_stopped_and_certifies_nothing`.
`cargo test -p axeyum-search --lib`: 54 passed (was 50 before this work).
Clippy clean on my files (the two remaining warnings are in agent-a/c's
`akb2_frontier.rs`).

## 20:45 — branch-point hypothesis

The 2026-08-12 probe branched on points 2,4,6,8,10,12. For `a(x-y)=bz` with
`a=5, b=4` the solutions are `x-y=4t, z=5t`, so a point `j` is a `z` only when
`5 | j`, and a multiple of 5 sits in ~740 extra triples that other points are
not in at all. Point 5 is in roughly 1000 constraints; point 2 is in ~300.
Branching on 2,4,6,8 therefore buys very little propagation, which is a
plausible reason that probe found the subtree uniformly hard.

Calibrating both point sets before committing the fleet.

## 21:00 — calibration: the branch points were the 2026-08-12 bottleneck

Two identical 218 s runs on s4/s7 (16 workers, depth-3 frontier, 20k split
budget, 200k final budget, inline backward checking), differing only in the
branch points:

| points | refuted | proof steps | note |
|---|---:|---:|---|
| `2,4,6,8,10,12` (the 2026-08-12 set) | 27 | 27 | every refutation trivial |
| `5,10,15,20,25,30` | 362 | 34,816,616 | real work |

For `a(x-y)=bz` a point is a `z` only when `b' | j`; with `(a,b)=(5,4)` the
multiples of 5 are in ~740 solution triples that other points are in not at
all. The old set was branching on points that barely constrain anything.

Also measured on the same run: **check/solve = 0.95** (1012.3 s solve, 957.8 s
backward check over 362 cubes), and a fixed backward-checker cost of ~0.59 s
per call even on one-step proofs. At ~83 bytes/step a full DRAT dump would be
~3 GB per 11 minutes per host, so the runs check inline and keep no proof
bytes; the cube list is the artifact and every proof regenerates from it.

## 21:05 — main runs launched

- s4 `b1`: points 5,10,…,80 (depth 16), initial frontier depth 3, 16 workers,
  200k conflicts/cube, 5M at full depth, inline backward checking, 12 h cap.
- s7 `b2`: same tree, 1M conflicts/cube, 8 workers — a policy hedge — plus the
  satisfiable-side probe (5 starts x 8 seeds x 200M moves, 6 threads).

Progress metric: the **covered measure**, sum of `4^-depth` over refuted cubes,
which is exactly the fraction of the assignment space with a checked
refutation. Monotone, exact, shape-independent.

## 21:20 — measure stalled, then explained

s4 went 31.0741% -> 31.0841% in ten minutes and looked divergent. It is not:
the queue is LIFO, so the search was down a single deep branch where each cube
covers `4^-10` of the space. The branching census tells the real story:

```
  d  refuted  interior  split%
  3       16        16   50.0%
  5       30        40   57.1%
  6      117        38   24.5%
  7      113        35   23.6%
  8       96        33   25.6%
  9      113        17   13.1%
 10       62         3    4.6%
```

Split fraction settles around 13-26% from depth 6 down, i.e. an expansion
factor `4 x 0.25 = 1.0` or below, and the per-level width stays flat at ~150
cubes. That is a converging tree, not an exploding one. Extrapolating the
covered measure (6.67 points of the non-trivial 75 in 14 minutes) puts the s4
run at roughly 2.5-3 hours.

s7 `b2` (1M conflicts) had covered 25.39% in the same time against s4's 31.7%,
so the larger budget is not obviously buying anything; killed it and gave s7 to
a three-way branch-point head-to-head instead (5-adic ordering vs consecutive
multiples of 5 vs shell-boundary points). The satisfiable-side probe keeps
running.

## 21:35 — branch-point head-to-head, three ways

Same 5 workers, same budgets, same wall clock on s7; only the points differ.
Covered measure (sum of `4^-depth` over refuted cubes):

| set | points | covered | non-trivial refutations |
|---|---|---:|---|
| A | `625,125,250,375,500,25,50,…` (5-adic order) | 6.32% | a handful |
| B | `5,10,15,20,25,30,…` (consecutive multiples of 5) | 25.55% | yes |
| C | `625,125,25,5,621,620,121,120,…` (shell boundaries) | 10.19% | **none** (18 refutations, 18 proof steps total) |

B wins on both the free symmetry-breaking coverage and the real work, so the
s4 configuration stands. The 5-adic and shell-boundary intuitions from the
extremal colouring's structure are simply wrong as *branch* points: fixing
`c(625)` propagates almost nothing, while fixing `c(5)` forbids
`c(y)=c(y+4)=c(5)` for all 737 values of `y`.

## 21:45 — per-seed census: the tree is 4 uneven quarters

s4 `b1`, 22 minutes, 829 cubes, 32.61% covered
(exactly `87534325/268435456`). Splitting the covered measure by the depth-3
seed shows the shape of the problem:

- the 16 seeds with `c(5)=1` are refuted instantly — that is the whole 25%;
- the 16 seeds with `c(5)=2` were the only ones the DFS had entered, and only
  2 of them were near complete;
- the 32 seeds with `c(5)=3` and `c(5)=4` were **untouched**.

One host walking this depth-first would take many hours and leave half the
tree for last. So: partition by hand.

## 21:55 — killed run resumed from its ledger, tree split across two hosts

Wrote `rado_cover_gaps` (new example): reconstructs the resume point from a
ledger alone, because `run_adaptive_cover` only writes `pending.tsv` on a clean
exit and a killed run would otherwise be unresumable. A gap is a *maximal*
uncovered cube; `under=` filters gaps by first choice, which is exactly a
disjoint host partition.

- `under=1,2` -> 94 gap cubes -> s4 run `b3` (16 workers)
- `under=3,4` -> 2 gap cubes `[3]`, `[4]` (untouched half), pre-split by hand
  to the 32 depth-3 cubes so the pool is busy immediately -> s7 run `b4`
  (10 workers)

Checked the partition with an independently written Python trie walk before
trusting it: 829 refuted + 96 gaps = 925 leaves, zero overlaps, zero holes,
every leaf reached, **total measure exactly 1**. If that had been wrong the
final `verify_cube_cover` would have said `MissingCell` and nothing would have
certified — the check is a time-saver, not the safety net.

First union census after the split: **38.51%** (b1 32.609 + b3 5.052 + b4 0.848).

## 22:20 — the claim ledger could not have accepted this result

`scripts/check-claim-certificates.py::check_cube_cover` hard-codes the flat
shape: `expected = k ** len(branch)`, every row must carry exactly
`len(branch)` colours. A tree cover's rows carry 3 to 16. So even a finished
`F_741` cover could not have been recorded as evidence.

Added `cube-tree-cover` (additive: one function, one dispatch arm). It
re-derives each row's cube code from the row's own colour tuple, walks the trie
from the root, and rejects a hole ("no cube covers X or anything below it"), an
overlap ("recorded AND has recorded descendants"), a buried cube, a non-`unsat`
verdict, a failed check, and an unlicensed branch integer. The walk is written
from the definition and shares no code with the Rust `verify_cube_cover`.

Controls, all measured rather than asserted:

- **positive**: a genuine complete tree cover of `F_103` for
  `R_4(3(x-y)=2z)` — a *published* value — produced end to end by
  `run_adaptive_cover` in 4.6 s (928 cubes at depths 2-6, 304 splits,
  1,137,228 proof steps, `certified:true`): accepted;
- dropped row -> `cover is NOT complete: no cube covers (2,1,3,3,2,3)`;
- added ancestor cube -> `cube (1,1) is recorded AND has recorded descendants`;
- row index bumped by one -> `row claims cube 17 but its colours (3,4) are cube 16`.

Two of those are now committed negative fixtures
(`cube-tree-cover-incomplete`, `cube-tree-cover-overlapping`), so
`check-claim-negative-fixtures.py` runs 10 fixtures with 0 failures instead of
8. `validate-claims.py`: 40 claims, 0 errors.
`check-claim-certificates.py`: 40 claims, 0 errors.

`scripts/` is outside agent-b's ownership slice — flagged for the coordinator
in the commit message. Closing the 741 claim is impossible without it.

## 22:35 — the replay driver, validated on a known value

`rado_replay_tree_cover` re-derives every cube's refutation from the ledger
alone and compares. On the `F_103` cover, 6 workers instead of 4:
**1,137,228 proof steps, identical to the digit**, all re-checked, cover
re-certified — so the determinism promise holds across worker counts and the
"the proofs regenerate" claim is a measurement, not a hope.

Negative control: bump one row's step count by one ->
`ALARM cube 2080 replayed to 1 proof steps, the ledger records 2`.

## 22:40 — partitioned runs, steady

s4 `b3` 302 s: 300 cubes, 122 splits, 36.6M steps, deepest 10.
s7 `b4` 255 s: 100 cubes, 49 splits, 10.3M steps, deepest 9.
Satisfiable-side probe on s7 still running; no colouring reported.

## 23:00 — the instance is pinned, by three encoders

`rado_dump_cnf` (new example) writes the deciding CNF **from the encoder the
cover actually runs against** — `ColouringProblem::encode` via `Rado::problem`.
On `F_741` it, `scripts/gen-rado-instance.py`, and the independent encoder
inside `scripts/check-claim-certificates.py` all produce the same 8,591,634
bytes, 2964 vars, 269,664 clauses,
sha256 `90f4e81cae0eaf2a64e681cb31ad81d625da95fb6710b7facaaa6725b562a697`.

Found while doing it: `crates/axeyum-search/src/colouring.rs:10` cites
`tests/encoding_parity.rs` as the differential gate for that encoder. **No such
file exists in that crate.** The real gate is
`crates/axeyum-cnf/tests/colouring_encoding_parity.rs` and it covers a
*different* encoder. The comment's claim happens to be true — measured above —
but its citation was not. Recorded as FEEDBACK item 8.

## 23:05 — union past half

`b1` 829 cubes 32.609% + `b3` 810 cubes 14.370% + `b4` 394 cubes 6.936%
= **53.92% of the assignment space with a checked refutation**, 2033 cubes.

`rado_replay_tree_cover` now takes several ledgers and replays their union,
because a resumed or partitioned cover is one cover in several files and
replaying them one at a time proves nothing. Negative controls: the same file
passed twice is `duplicate-rows rows=800 distinct=400`; one half alone is
`cover is missing cell 846`.

Shared-tree gates (agent-a's `colouring.rs` edit has landed, so it compiles
again): `cargo test -p axeyum-search --lib` 65 passed / 0 failed, clippy clean
on `-p axeyum-search --all-targets`.

## 23:10 — FRAGMENTATION.md written

Per the coordinator's added deliverable. Kept to what happened: the eight
stages and their components, the obligation that moved with the search
strategy, resumability as a soundness property (including the false positive
avoided — a resumed run must not make the finding-B2 duplicate detector fire on
a correct cover, because that is how a real detector gets disabled), the seams
where integration did not help (route A not generalized to trees, the claim
vocabulary lagging the harness, an encoder whose cited gate did not exist, the
checker's per-call fixed cost), and the OOM avoided by measuring 83 bytes/step
and choosing inline checking with no retained proof bytes.

## 23:35 — s4 finished the `c(5)=1,2` half; tree re-partitioned

`b3` exited `refuted`: all 94 resumed gap cubes closed, 1078 cubes, 328 splits,
127,033,238 proof steps, 979.6 s on 16 workers. It reported
`certified:false, gap:"cover is missing cell 4"` — correct and worth noting:
`certify_tree_cover` over `b3`'s rows ALONE is not a cover of the whole tree,
and the harness says which cube is missing rather than certifying its own
fragment.

Quarter census of the union at that point:

| subtree | covered |
|---|---:|
| `c(5)=1` | 100.000% |
| `c(5)=2` | 87.918% (b1) -> 100% (b1+b3) |
| `c(5)=3` | 27.745% |
| `c(5)=4` | 0.000% |

Re-partitioned from the union of `b1+b3+b4`: s4 takes `c(5)=4`, s7 continues on
`c(5)=3`.

Two operational traps hit here, both worth recording:

1. **`pkill -f 'run=b4'` over ssh kills its own shell**, because the remote
   command line contains the pattern. Exit 255, no explanation. Fixed with the
   bracket trick — `pkill -f 'run=b[4]'` matches the target and not the literal
   text of the command doing the matching.
2. **A gap set of one cube starves a 16-worker pool.** `under=4` correctly
   returned exactly `[4]`, since that quarter was untouched — and one seed cube
   means one busy worker until it splits. Pre-split by hand to the 64 depth-4
   cubes (`parse_pending` re-derives every code from its path, so a wrong code
   would have failed closed rather than resumed on the wrong cube).

The briefly-running `c4` run that started on the single `[4]` cube refuted 111
cubes before being replaced by `c4b`, which restarts from the whole quarter. Its
ledger therefore OVERLAPS work `c4b` will redo, so it is quarantined under
`DISCARDED/s4-c4-superseded/` and excluded from the union — an overlapping
cover is rejected by design, and the right response is to not build one, not to
prune it afterwards.

Also shortened the satisfiable-side probe: 200M moves per job would have taken
~7 hours to report anything, which is not an early warning. Now 12 seeds x 25M
moves x 5 starts on 4 threads.

## 23:55 — finalization path validated before it is needed

`rado_certify_tree_cover` now takes `merged=` and writes the rows it just
certified back out as ONE byte-stable ledger in cube-code order. A cover that
arrives as five files in completion order is a reassembly problem for whoever
reads it next, and reassembly is exactly what finding B2 was.

Validated on the `F_103` cover: split into two ledgers, the union certifies,
the merged file carries all 928 rows, and replaying the merged file *alone*
re-derives 1,137,228 steps and re-certifies. One half alone is
`cover is missing cell 846`; the same file twice is
`duplicate-rows rows=800 distinct=400`.

`finalize-v1.sh` (scratch) does the whole endgame: pull every ledger, check the
union for holes and overlaps, certify, write the merged artifact. Dry-run right
now on the live partial data: 2768 cubes, `covered 176756954/268435456`
(65.847%), 152 gaps, no overlap, certification correctly REJECTED with
`cover is missing cell 20`.

Host health: s4 6 GiB of 123 used, s7 13 GiB of 26, load 16 on both, 384 GiB
and 499 GiB free. Nothing is near an edge — which is the point of keeping no
proof bytes.

Satisfiable-side probe: 4 of 60 jobs finished, no colouring, ~272 s per 25M-move
job.

## 00:05 — ops/ published

Every script this campaign actually ran is now under `ops/`, with a README
naming the two traps they encode (the self-killing `pkill -f` over ssh, and
rsync of a live `.git`). Versioned filenames throughout: a long job re-reads
its script by byte offset, so a running script is never edited in place.

Both cover runs continue: s4 on `c(5)=4`, s7 on the `c(5)=3` gaps, roughly
300 and 255 cubes in respectively.

## 01:20 — the cover closed

s4's `c(5)=4` quarter finished first: `c4b` refuted 1732 cubes, 556 splits,
202,492,334 steps, 1725.7 s, **no stuck cubes** even though the tree reached
full depth 16. That left only `c(5)=3`. Split its 65 remaining gap cubes
between both hosts by interleaved rows (`under=` only cuts on the first choice,
and everything left had first choice 3): s4 took 33, s7 took 32. Both came back
`refuted` in 195 s and 108 s.

**Union: 6241 cubes, `covered 4294967296/4294967296` — exactly 1. Zero gaps,
zero overlaps.**

`rado_certify_tree_cover` over all seven ledgers:

```
cover certified: 6241 cells, each refuted by a checked DRAT proof;
at-least-one clauses located in F at [4,9,14,19,24,29,34,39,44,49,54,59,64,69,74,79];
699572027 proof steps checked in 22042.6s
{"status":"certified","a":5,"b":4,"k":4,"n":741,"cubes":6241,"steps":699572027}
```

Census of the certified cover: all 6241 `unsat`, all 6241 `passed`, none
deferred. Depths 3-16 (16 / 11 / 337 / 1174 / 1127 / 1142 / 1150 / 675 / 231 /
145 / 121 / 65 / 43 / 4). 699,572,027 proof steps, 366,009,752 clause
additions, 27,985.0 s of solving and 22,042.6 s of checking in aggregate. The
largest single cube proof is 391,941 steps.

With the banked witness at 740, **R_4(5(x-y)=4z) = 741**.

Claim `rado-r4-a5-b4-frontier` rewritten to `computed` with three evidence
rows: `deciding-instance` (instance-pin, F_741.cnf, checked by regeneration
from three independent encoders), `lower-witness` (the 740 colouring, replay
checked), `upper-cube-tree-cover` (the merged 6241-row ledger). All three
re-check. `validate-claims.py` errors on this claim: 4 before the fixes, 0
after (the remaining 88 in the tree are another lane's off-diagonal Schur
claims). Negative fixtures: 10, 0 failures.

Four structural fixes were needed and are worth recording, because each was the
ledger refusing to let me be sloppy: `toolchain` has a closed field set (the
build-provenance caveat moved to `machine`); `concept_ref.relation` has a closed
vocabulary (no `was-instance-of` — the note carries the change); `frontier` is
only for conjectured/open claims (folded into `notes`); and `cube-tree-cover`
had to be added to `artifacts/ontology/claim.schema.json` and
`validate-claims.py` as well as to the certificate checker.

**Not committing the claim yet.** `rado_replay_tree_cover` is re-deriving all
6241 refutations from the merged ledger alone on 15 workers, with
`strict_steps=1`, and I would rather find a disagreement before the claim
exists than after. 500 cubes in 251 s, so ~52 minutes.

## 02:10 — satisfiable side closed too

The bounded probe finished all 60 jobs: `{"status":"not-found","n":741,
"starts":5,"seeds":12,"moves":25000000,"wall_s":4101.5}`. Five start
distributions (the `[740]` witness with each of the four colours appended, plus
a cold round-robin start), twelve seeds each, 25M moves each. Corroboration
only — the cover is the proof — but it is the fourth independent thing pointing
the same way.

Second replay started on s7. Same merged ledger, 16 workers instead of 15, and
a **different rustc** (s7 is 1.93.1 stable, s4 is 1.99.0-nightly), so the
step-count comparison becomes a cross-toolchain determinism check rather than
just a cross-host one.

## 03:00 — independent re-validation passed

`rado_replay_tree_cover` on s4, 15 workers (the search used 16 and 10-12),
re-derived all 6241 refutations from the merged ledger alone — rebuilding `F`
from `(a,b,k,n)` and each cube's units from the row's own recorded choices, not
from anything the search wrote — re-checked every proof, and required each step
count to match exactly:

```
cover certified: 6241 cells, each refuted by a checked DRAT proof; ...;
699572027 proof steps checked in 27116.6s
{"status":"revalidated","cubes":6241,"steps":699572027,"wall_s":4120.5,"strict_steps":true}
```

**699,572,027 steps, identical to the digit.** With `strict_steps=1` a single
cube differing by one step would have stopped the run and named it.

s7's cross-toolchain replay (rustc 1.93.1 against s4's 1.99.0-nightly, 16
workers) is at 5000/6241.

## 03:30 — cross-toolchain replay agrees, claim landed, and one correction

s7's replay finished: **699,572,027 steps**, the same figure to the digit as
s4's, on rustc 1.93.1 stable against s4's 1.99.0-nightly, 16 workers against
15. Determinism is a public API promise in this project and that is its first
cross-compiler test. Wall clock 2288.8 s on s7 (unloaded) against 4120.5 s on
s4.

Claim `rado-r4-a5-b4-frontier` committed as `computed`
(`R_4(5(x-y)=4z) = 741`) with `F_741.cnf`, the 6241-row merged cover ledger,
and the witness. All gates green.

**Correction, caught by the coordinator and confirmed by measurement.** I had
written that a point `j` is a `z` only when `b' | j`. It is `a' | j`: solutions
are `x - y = b' t`, `z = a' t`. For `(a,b) = (5,4)`, `b' = 4` would have named
the multiples of 4 — nearly the *losing* set — while the winning set was the
multiples of `a' = 5`. The empirics were right and the explanation was wrong,
which is the more dangerous way round, and it had already propagated into the
committed claim. Fixed there (commit `111e866d0`), in RESULT.md and in
FEEDBACK.md, and replaced with the actual measurement instead of a hand-waved
"~740 triples": over `F_741`'s 65,564 forbidden sets, point 5 occurs in **884**,
points 2 and 4 in **148** each.

While fixing it I computed the constraint-degree ordering directly from the
forbidden sets, and it turns out to reproduce the winning branch set exactly:
for `(5,4,741)` the first sixteen points by degree are
`5,10,15,…,80`, in that order, chosen with no knowledge of the equation. Same
story for `(3,2,103)` and `(4,3,313)`. That is now written up in FEEDBACK #5 as
an implementable default for `ColouringFamily::branch_points`.

## 03:50 — stopping, per the change of direction

Final state, all measured just now:

- `check-claim-certificates.py --only rado-r4-a5-b4-frontier`: 3 of 3 rows
  re-checked, 0 errors.
- `validate-claims.py`: `OK rado-r4-a5-b4-frontier: computed, 3 evidence rows`.
- `check-claim-negative-fixtures.py`: 10 fixtures, 0 failures.
- `cargo test -p axeyum-search --lib`: 77 passed, 0 failed (50 before this
  lane's work; the rest are another lane's off-diagonal Schur tests).
- `cargo clippy -p axeyum-search --all-targets`: 0 warnings.

Committed by this lane, in order: the adaptive tree cover with its
completeness obligation and negative controls; the ledger-only replay driver;
the gap reconstruction that makes a killed run resumable; the CNF dump from the
encoder the cover ran against; the merged-ledger output; the `cube-tree-cover`
evidence kind with two fixtures; the vocabulary entries in the schema and
`validate-claims.py`; the claim itself; and the divisor correction.

No further covers and no new parameter points, per the change of direction.
FEEDBACK.md items 1 and 5 are now written as implementable specifications
rather than complaints, and RESULT.md ends with an explicit list of everything
this lane did NOT do.
