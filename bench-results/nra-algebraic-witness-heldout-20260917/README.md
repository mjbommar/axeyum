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

Filled in below as the sweeps land. `summarize.py` produces the tables and
exits nonzero on a `:status` disagreement or a flip; `recheck-movers-env.sh`
(ADR-2134's, verbatim — the two-binary `recheck-movers.sh` refuses an env A/B
because both arms share one SHA) re-runs every raw mover 3× per arm with the
arms alternating within the passes.

_pending_
