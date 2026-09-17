# ADR-2134 — the pinned re-run at head and the held-out draw

Lane `AX-2134-HELDOUT`, 2026-09-17. Finishes the measurement ADR-2134 left one
quarter short: the held-out 200-file `QF_NRA` draw reached 23 of 200 when the
previous round closed, so the ship criterion — **0 stable losses AND 0 flips
AND ≥1 stable gain on BOTH the pinned and the held-out lists** — was never
evaluated and `CAD_DEFAULT` stayed `CadPolicy::SINGLE_CELL`.

## 0. What is being measured, at which head

* **Head:** `43f1e0f90` (main, after ADR-2142 and ADR-2145's SAT-core
  changes; 60+ commits past ADR-2134's own A/B at `863694052`/`df2dfc0f…`).
* **`CAD_DEFAULT`** in `crates/axeyum-solver/src/nra_real_root.rs` at this
  head: `CadPolicy::SINGLE_CELL` (arm name `single-cell`).
* **`CadPolicy::ALL`** at this head, in order: `default`, `wide`,
  `single-cell`, `single-cell-sat`, `clause-loop`, `algebraic-witness`. The
  harness derives the accepted arm names from a copy of that source
  (`nra_real_root.rs`, staged beside the binary) rather than from a literal.
* **One binary**, `smtcomp_cli`, built `--release --features full` from
  `scripts/lane-snapshot.sh HEAD` (snapshot of `43f1e0f90`), sha256 in
  `binary-sha256.txt`: `d3606850e01ba5c8d63de14d03eda10b52746d8ca500db2f274f3bfbdfe7e5ee`.
* **Two env values:** A = `AXEYUM_NRA_CAD=single-cell` (the shipped default,
  named EXPLICITLY so arm A is the default by resolution and not by the
  catch-all), B = `AXEYUM_NRA_CAD=algebraic-witness`.
* **Host s7**, physical core pairs `1,9` (shard 0) and `3,11` (shard 1), host
  idle at launch (load 0.50). 24 s wall, 8 GiB `ulimit -v`, both arms
  interleaved per file on the same core back to back, arm order alternating
  per file (`ab-cad-env.sh`).
* **Timing** is `$EPOCHREALTIME`; s7's uutils `date` prints nanoseconds under
  `%3N`. The 200 ms sleep self-check read 205 ms (shard 0) and 203 ms (shard 1)
  before any solve.
* **Smoke test before launch** on
  `QF_NRA/meti-tarski/atan/problem/2/atan-problem-2-chunk-0014.smt2` (one of
  ADR-2134's four movers): `single-cell` → `unknown` at 12.4 s,
  `algebraic-witness` → `sat` at 0.11 s, and the deliberately misspelled arm
  `nonsense` → `unknown` at 12.4 s (resolves to the default, as documented —
  which is exactly why the harness refuses an unknown arm name).

## 1. The populations

* **Pinned:** `qfnra-shard0.txt` + `qfnra-shard1.txt` = ADR-2134's
  `qfnra-200.txt` (itself `bench-results/board-ab-20260915/QF_NRA.tsv`'s
  list), 200 files, split as ADR-2134 split it.
* **Held-out:** `heldout-shard0.txt` + `heldout-shard1.txt` = ADR-2134's
  `heldout-qfnra-200.txt`, which is **byte-identical, after sorting, to
  ADR-2126's `bench-results/nra-cell-exact-20260916/heldout-qfnra-200.txt`**
  (same draw script, same `SEED = 20260916`). So this is ADR-2126's held-out
  population, not a fresh one; it has been scored once before (ADR-2126:
  109 → 109, zero movers) but never by this lever.
* **Disjointness, checked:** `LC_ALL=C comm -12` of the sorted pinned and
  held-out lists is **0 of 200**; both lists have 200 distinct entries; the
  four shard files re-sort to exactly their 200-line lists; and re-running
  `bench-results/nra-algebraic-witness-20260916/draw-heldout-qfnra.py` at this
  head (corpus 12,154, excluded 200 = training 200 + ledger 200, pool 11,954)
  reproduces the committed held-out list byte for byte.

## 2. Results

Both sweeps and the recheck ran 2026-09-17 10:44–11:31 on s7. `summarize.py`
produces the tables and exits nonzero on a `:status` disagreement or a flip; `recheck-movers-env.sh`
(ADR-2134's, verbatim — the two-binary `recheck-movers.sh` refuses an env A/B
because both arms share one SHA) re-runs every raw mover 3× per arm with the
arms alternating within the passes.

### 2a. Pinned 200 at head (`qfnra-shard0.tsv`, `qfnra-shard1.tsv`, `summary-qfnra.md`)

| measure | A = `single-cell` (shipped) | B = `algebraic-witness` |
| --- | ---: | ---: |
| files | 200 | 200 |
| decided | 124 | **128** |
| sat / unsat | 55 / 69 | 59 / 69 |
| PAR-2 (ms, 24 s budget) | 18832 | 17872 |
| wall on the 124 both-decided files (ms) | 118460 | 117771 |

* delta **+4**; raw gains 4, raw losses **0**, `sat`↔`unsat` flips **0**,
  `:status` disagreements **0 over 250** comparable verdicts, arm runs without
  a verdict token 0, nonzero exit rows 0, timing-unit failures 0.
* The four gains are the SAME four files ADR-2134 measured on s5 at
  `df2dfc0f…`, every one `unknown → sat`, every one in
  `meti-tarski/atan/problem/2/` (the pinned list holds 9 files of that family;
  the other 5 are decided by both arms):

  | file | A | B |
  | --- | --- | --- |
  | `atan/problem/2/atan-problem-2-chunk-0014.smt2` | unknown @ 12413 ms | sat @ 105 ms |
  | `atan/problem/2/weak/atan-problem-2-weak-chunk-0018.smt2` | unknown @ 18918 ms | sat @ 105 ms |
  | `atan/problem/2/weak/atan-problem-2-weak-chunk-0089.smt2` | unknown @ 14214 ms | sat @ 206 ms |
  | `atan/problem/2/weak/atan-problem-2-weak-chunk-0159.smt2` | unknown @ 13513 ms | sat @ 206 ms |

* **Recheck** (`recheck-qfnra.tsv`, s7 core pair `5,13`, 3× per arm with the
  arms alternating within the passes): **4 STABLE-GAIN, 0 STABLE-LOSS,
  0 UNSTABLE, exit status 0 on all 24 runs.** A `unknown/0 ×3`,
  B `sat/0 ×3` on every row.

So the pinned half of the criterion holds at head exactly as it held at
ADR-2134's own commit: the SAT-core changes between the two heads (ADR-2142,
ADR-2145) moved neither arm's count on this list.

### 2b. Held-out 200 (`heldout-shard0.tsv`, `heldout-shard1.tsv`, `summary-heldout.md`)

| measure | A = `single-cell` (shipped) | B = `algebraic-witness` |
| --- | ---: | ---: |
| files | 200 | 200 |
| decided | 109 | **109** |
| sat / unsat | 52 / 57 | 52 / 57 |
| PAR-2 (ms, 24 s budget) | 22176 | 22186 |
| wall on the 109 both-decided files (ms) | 67258 | 69157 |

* delta **0**; raw gains **0**, raw losses **0**, flips **0**, `:status`
  disagreements **0 over 216** comparable verdicts, arm runs without a verdict
  token 0, nonzero exit rows 0, timing-unit failures 0.
* **Zero movers of any kind, so there is nothing to recheck** — the recheck
  step is NOT RUN on this population because its input list is empty
  (`movers-heldout.txt`, 0 lines), not because it was skipped.
* Arm A's 109 is the number ADR-2126 measured on this same population with
  its own arm A (109 → 109), so the population reproduces across two heads
  and two hosts.
* Where the pinned gain lives and why the held-out cannot show it: all four
  pinned movers are `meti-tarski/atan/problem/2/` files. The held-out list
  holds 4 files of that family and **both arms decide all four** (2 `unsat`,
  2 `sat`, each in 105–209 ms). The 91 files both arms leave `unknown` on the
  held-out list are 33 `meti-tarski` (none from `atan/problem/2`),
  21 `LassoRanker`, 11 `hycomp`, 9 `Sturm-MBO`, 5 `Pine`, and 12 others.

## 3. The decision, by the criterion

The ship criterion for moving `CAD_DEFAULT` is **0 stable losses AND 0 flips
AND ≥ 1 stable gain on BOTH the pinned and the held-out lists.**

| list | stable losses | flips | stable gains | criterion half |
| --- | ---: | ---: | ---: | --- |
| pinned 200 | 0 | 0 | 4 | **holds** |
| held-out 200 | 0 | 0 | **0** | **fails on the gain clause** |

**The lever does not ship.** `CAD_DEFAULT` stays `CadPolicy::SINGLE_CELL`;
`AXEYUM_NRA_CAD=algebraic-witness` remains selectable by name, OFF by default;
ADR-2134 stays `proposed` with this measurement written into it.

What the two lists together say, read plainly: the algebraic final coordinate
is a real, reproducible, loss-free gain (4 STABLE-GAIN at 3× on two hosts and
two heads) on one narrow shape — `meti-tarski/atan/problem/2` chunks whose
last-level sample is an irrational root — and a null everywhere else it has
been pointed. Nothing measured here says it is harmful; the criterion is
written to require that a default move be earned on a population the lever was
not built against, and on that population it earned nothing. A future lane
that wants to re-open this must draw a NEW held-out population (change the
seed in `draw-heldout-qfnra.py` and say so); re-running this one would be
re-scoring a set that has now been scored twice.

## 4. What did NOT run

* **The eight nonlinear z3 differential fuzzes — NOT RUN.** They are mandatory
  only if the default moves; it does not.
* **The binary-against-binary A/B pricing the `sign_at` exactness fix — NOT
  RUN**, as in ADR-2134. That fix is in BOTH arms of every number above.
* **A cause census on the held-out undecided files — NOT RUN.** ADR-2134
  measured that the `nra-real-root` first-wins decline slot is non-predictive
  of this lever (3 of its 4 movers were sized `non-conjunctive`), so a census
  here could not say whether the lever was reached and refused or never
  reached; it would be a number without a meaning.

## 5. Reproducing

```sh
# on s7, from a copy of this directory beside the binary
./drive-shard.sh 0 1,9  <workdir> <smtcomp_cli>     # pinned shard 0, then held-out shard 0
./drive-shard.sh 1 3,11 <workdir> <smtcomp_cli>     # pinned shard 1, then held-out shard 1
python3 summarize.py --movers movers-qfnra.txt   qfnra-shard0.tsv   qfnra-shard1.tsv
python3 summarize.py --movers movers-heldout.txt heldout-shard0.tsv heldout-shard1.tsv
AXEYUM_ARMS_SRC=<nra_real_root.rs> ./recheck-movers-env.sh movers-qfnra.txt recheck-qfnra.tsv 5,13 <smtcomp_cli> single-cell algebraic-witness
```

`summarize.py` exits 1 on a flip or a `:status` disagreement and 2 on a
timing-unit failure; both sweeps exited 0. `shard0.done` / `shard1.done` carry
the per-population exit status of the harness (0, 0, 0, 0).
