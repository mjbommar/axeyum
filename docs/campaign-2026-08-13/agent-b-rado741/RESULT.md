# agent-b result — `R_4(5(x-y)=4z) = 741`

**Both sides are established and machine-checked, 2026-08-13.** The
repository's standing open claim is closed.

| side | statement | evidence |
|---|---|---|
| lower | `R_4(5(x-y)=4z) > 740` | a 4-colouring of `[740]` with no monochromatic solution, replayed by an `O(n^2)` enumerator sharing no code with the encoder |
| upper | `R_4(5(x-y)=4z) <= 741` | a **complete adaptive cube cover** of `F_741`: 6241 cubes, every one refuted, every DRAT proof checked by axeyum's own backward checker |

No external solver and no external proof checker appears anywhere in the
pipeline. The construction predicted 741 exactly
(`741 = 5^4 + 5^3 - 2*5 + 1`); the prediction held.

## The deciding instance

`a=5, b=4, k=4, n=741` gives 2964 variables, 269,664 clauses, 8,591,634 bytes,

```
sha256 90f4e81cae0eaf2a64e681cb31ad81d625da95fb6710b7facaaa6725b562a697
```

**Three independently written encoders produce those bytes exactly**: the
`axeyum-search` encoder the cover itself ran against (`rado_dump_cnf`),
`scripts/gen-rado-instance.py`, and the encoder inside
`scripts/check-claim-certificates.py`, which re-derives the CNF from the four
parameters and requires byte-identity. The 313 bound shipped for a while with
cover ledgers and no identified subject; this one does not.

## The cover

```
cover certified: 6241 cells, each refuted by a checked DRAT proof;
at-least-one clauses located in F at [4,9,14,19,24,29,34,39,44,49,54,59,64,69,74,79];
699572027 proof steps checked in 22042.6s
{"status":"certified","a":5,"b":4,"k":4,"n":741,"cubes":6241,"steps":699572027}
```

| | |
|---|---|
| cubes | 6241, all `unsat`, all `passed`, **none deferred** |
| shape | an adaptive **tree**, depths 3-16, not a flat product |
| depth census (3..16) | 16 / 11 / 337 / 1174 / 1127 / 1142 / 1150 / 675 / 231 / 145 / 121 / 65 / 43 / 4 |
| branch integers | `5,10,15,20,25,30,35,40,45,50,55,60,65,70,75,80` |
| proof steps | 699,572,027 (366,009,752 clause additions) |
| aggregate solve | 27,985.0 s |
| aggregate check | 22,042.6 s (`check_drat_backward`, ADR-0382, in the worker that produced each proof) |
| largest single proof | 391,941 steps |
| covered measure | **exactly `4294967296/4294967296`** — zero holes, zero overlaps |
| produced by | seven runs on two hosts: `b1, b3, c4b, da` (s4, 16 workers) and `b4, c3, db` (s7, 10-12 workers) |
| DRAT bytes retained | **none** — at ~83 bytes/step a full dump is ~58 GB, and every proof regenerates deterministically from the ledger |

Artifact: `artifacts/cube-tree-cover.tsv` here, and
`artifacts/claims/rado/rado-r4-a5-b4-frontier/cube-tree-cover.tsv` in the
repository (sha256
`eb61dce9f4df7eef09d832f4e80e0cfdbfd288ee27b78d552920f0f6fc472cd1`).

### The four obligations, and where each is discharged

1. **every cube refuted with a checked proof** — `check_drat_backward` inline,
   6241/6241 passed, 0 deferred;
2. **every branch integer's at-least-one clause present verbatim in `F`** —
   located at clause indices 4, 9, 14, …, 79;
3. **the cubes are exactly the leaf set of a complete branch trie** —
   `cover::verify_cube_cover`; a hole is `MissingCell` naming the largest
   uncovered node, a cube inside another is `DuplicateCell` naming the buried
   one;
4. **no duplicate rows** — enforced at ledger parse and again over the union.

Obligation 3 is the one that had to be *generalized* for this result: the
strategy moved from a flat product to a budget-driven tree, and the
completeness check moved with it, in the same commit, with negative controls.

## Independent re-validation

`rado_replay_tree_cover` re-derives every cube's refutation from the merged
ledger alone — rebuilding `F` from `(a,b,k,n)` and each cube's units from the
row's own recorded choices — re-checks each proof, and requires the step count
to match **exactly**, since determinism is a public API promise.

**It was run twice, and both agree exactly.**

| host | workers | rustc | steps re-derived | wall |
|---|---:|---|---:|---:|
| s4 | 15 | 1.99.0-nightly | **699,572,027** | 4120.5 s |
| s7 | 16 | 1.93.1 stable | **699,572,027** | 2288.8 s |

Identical to the digit, on two hosts, two worker counts and **two compilers** —
the first cross-compiler test of the project's determinism promise. Both runs
re-checked every proof and re-certified the cover. A single cube differing by
one step would have stopped the run and named it.

The same driver was validated end to end beforehand on the `F_103` cover for
`R_4(3(x-y)=2z)`, where a replay at a different worker count reproduced
1,137,228 proof steps identical to the digit, and alarmed on a one-step
tampering of the ledger.

## Satisfiable side

A bounded min-conflicts probe of `F_741` (5 start distributions x 12 seeds x
25M moves, warm-started from the `[740]` witness with each of the four colours
appended) found **no** 4-colouring in any of its 60 jobs:
`{"status":"not-found","n":741,"starts":5,"seeds":12,"moves":25000000,"wall_s":4101.5}`.
Corroboration only; the cover is the proof. Any colouring it had found would
have been replayed through `ColouringFamily::first_violation` before being
called one.

## Prior art: recorded negative result

Searched during this campaign (coordinator's audit, 2026-08-13), recorded so
nobody repeats it:

* **`R_4(5(x-y)=4z)` appears nowhere in the literature.** Chang-De
  Loera-Wesley (arXiv:2210.03262) Table 10 leaves `(a,b) = (5,4)` blank; of its
  20 cells, 13 are populated and only 12 are exact. Also blank: `(5,2)`,
  `(4,3)`, `(5,3)`, `(2,4)`, `(3,4)`, `(4,4)`.
* The companion prediction `R_4(6(x-y)=5z) = 1501` likewise returns nothing.
* The one other active group here (A. C. Li, SSRN 6814341; artifacts at
  `crabsatellite/rado-numbers-sat`) works the `x + by = bz` family, which maps
  onto the `b = 1` column and says nothing about `b = 4`.

**Scale.** Same source: their largest *completed* four-colour refutation is
`b = 5` at `n = 624` in 523 s with CaDiCaL 1.5.3, and they mark `b = 6, k = 4`
as "n=1296 UNSAT **needs cluster**" and `b = 7` as "too large for desktop".
This instance is `n = 741` at `k = 4`, closed on two 16-core boxes.

## What made it tractable — measured, not folklore

1. **Branch on integers that are `z`-values of the equation.** Solutions are
   `x - y = b' t`, `z = a' t`, so a point `j` occurs as a `z` **iff `a' | j`**
   (`a' = a/gcd(a,b)`; for `(a,b) = (5,4)` that is the multiples of 5). Fixing
   such a point's colour forbids `c(y) = c(y + b't) = c(z)` for every `y` at
   once. Measured on `F_741`, over its 65,564 forbidden sets: point 5 occurs in
   **884** of them, points 2 and 4 in **148** each. Head-to-head at
   equal budget and wall clock: `2,4,6,8,10,12` refuted **27** cubes with
   **27 proof steps in total** (every one a trivial symmetry refutation);
   `5,10,15,20,25,30` refuted **362** with **34,816,616** steps. The
   2026-08-12 probe that concluded "needs fleet time" used the former.
   Two other structurally motivated orderings were measured and rejected:
   5-adic (`625,125,250,…`, 6.32% covered) and the extremal colouring's shell
   boundaries (`625,125,25,5,621,620,…`, 10.19% and not one non-trivial
   refutation).
2. **Adaptive splitting.** A cube that exhausts its 200k-conflict budget is
   split on the next branch integer and its children queued. The flat depth-6
   product left 1132 of 1946 finished cells resource-out; the tree closed with
   1861 splits and no stuck cube anywhere, even at full depth 16.
3. **Inline checking with no retained proof bytes.** Checking costs about as
   much as solving (0.95 ratio, measured), so inline checking is a 2x tax —
   paid because it removes 58 GB of DRAT and the OOM risk that killed a
   monolithic `F_313` run at exit 137. The artifact is the cube list; the
   proofs regenerate.
4. **Shape-independent cube codes.** A cube's identity depends on the plan and
   its path, never on the tree's shape, so seven runs across two hosts — three
   of them resumed from a killed predecessor — union into one cover instead of
   seven fragments.

## What is NOT claimed

* This is **route B**: four checked cover obligations, not a single composed
  DRAT proof of `F_741`. `compose::compose_cover_proof` is written for a flat
  product and is not generalized to trees, so the step "checked refutations of
  every cube of a complete cover imply `F` is unsatisfiable" is discharged as
  four checked obligations rather than by a checker accepting one proof. See
  FEEDBACK.md item 1 and FRAGMENTATION.md.
* No DRAT bytes are distributed. They regenerate deterministically from the
  ledger, and the replay driver is what demonstrates it.
* `R_4(6(x-y)=5z) = 1501`, the construction's next prediction, is untested.

## Unfinished, named exactly

Nothing here blocks the result; each is a thing this lane did not do.

1. **Route A for tree covers.** No single composed DRAT proof of `F_741`
   exists, so the final implication is a checked meta-argument rather than a
   certificate. Design written up in FEEDBACK.md item 1, including the part
   that is not free (the composed artifact would be ~58 GB, so it needs
   streaming composition and a checker that can verify a proof larger than
   memory).
2. **The branch-point heuristic is specified but not implemented.**
   `ColouringFamily::branch_points` still defaults to `2,4,6,…`. FEEDBACK.md
   item 5 has the rule, the signature change it needs, and the regression pin.
3. **`R_4(6(x-y)=5z)`**, predicted 1501 by the same construction, is untested.
   Deliberately not started: the campaign turned to fixing axeyum itself.
4. **A concurrent double-`sat` can leave the model file disagreeing with the
   reported cell** (FEEDBACK.md item 11). Not a soundness break — both models
   satisfy `F` — but the persisted artifact may not be the one the outcome
   names. Not fixed here; it is in `handle_sat`, which this lane owns, but a
   fix needs a two-worker test and the campaign stopped first.
5. **No live queue depth** in `run_adaptive_cover` (FEEDBACK.md item 9).
   Worked around by reconstructing the census offline with `rado_cover_gaps`.
6. **The backward checker's ~0.59 s per-call fixed cost** (FEEDBACK.md item 2)
   is unaddressed; it is a real fraction of this cover's 22,042.6 s of checking.
7. **`crates/axeyum-search/src/colouring.rs:10` still cites a test that does
   not exist** (FEEDBACK.md item 8). The encoders were verified equal by
   measurement today, but the citation was not fixed — it is in a file this
   lane does not own.
8. **One quarantined ledger.** `artifacts/s4/DISCARDED/s4-c4-superseded/`
   holds 111 refuted cubes from a run whose restart made it overlap work being
   redone. They are valid refutations, excluded because an overlapping cover is
   refused by design. Nothing depends on them.

## Reproducing

```
# the instance, from the encoder the cover ran against
rado_dump_cnf a=5 b=4 k=4 n=741 out=F_741.cnf

# re-derive and re-check every cube from the ledger, on any host
rado_replay_tree_cover a=5 b=4 k=4 n=741 \
  points=5,10,15,20,25,30,35,40,45,50,55,60,65,70,75,80 \
  ledger=artifacts/claims/rado/rado-r4-a5-b4-frontier/cube-tree-cover.tsv workers=16

# re-check the claim's three evidence rows
python3 scripts/check-claim-certificates.py --only rado-r4-a5-b4-frontier
```

Everything this campaign actually ran is in `ops/`, with a README. Live
artifacts and logs are under `artifacts/` and `logs/` here.

## Claim ledger

`artifacts/claims/rado/rado-r4-a5-b4-frontier/` is now `computed` with three
evidence rows — `deciding-instance` (instance-pin), `lower-witness`
(witness-replay), `upper-cube-tree-cover` (cube-tree-cover) — and all three
re-check. `validate-claims.py` reports 0 errors on this claim (the 88 that
remain in the tree belong to another lane's off-diagonal Schur claims);
`check-claim-negative-fixtures.py` runs 10 fixtures with 0 failures.
