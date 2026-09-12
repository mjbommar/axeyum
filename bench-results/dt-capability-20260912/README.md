# ADR-1935 A/B — array/UF datatype fields and Ackermann congruence over datatype arguments

**2026-09-12, lane `dt-capability`.** Baseline `611b72958` (`main`'s tip)
against the candidate; 1,000 files; per-file interleaved.

## Protocol

Every part of it is load-bearing and most of it is inherited from
[`../dt-divisions-headtohead-20260912/`](../dt-divisions-headtohead-20260912/README.md),
which is what makes the numbers comparable.

* **The lists are the committed parity lists**, unchanged and unsampled:
  `../parity-lists/{AUFDTLIRA,UFDTLIRA,UFDT,QF_DT,UF}.txt`, 200 files each,
  stride-pinned and committed before any of this work
  (`49a0e2698` / `62e55bdd1`). `QF_DT` and `UF` are **controls** — divisions we
  already do well and that this change should not touch.
* **Both arms run file N before either runs file N+1**, on the same pinned core
  pair, with the arm that goes first **alternating per file** so neither
  systematically benefits from a warm page cache. The comparison is therefore a
  per-file diff, not a difference of two aggregates.
* **10 s wall, 8 GiB address space** per run, wrapper timeout `10 + 16 s`. Each
  run records its own outcome (`WRAPPER-KILLED`, `RC134-ABORT`, `SIGKILL`)
  rather than being silently scored — an earlier census used a short headroom
  under load and produced rows that read as "no reason".
* Each 200-file list is split into **12 modulo-interleaved shards** (`NR%12`) so
  every shard spans the whole division rather than one author directory; four
  shards per box on `s5`/`s6`/`s7` (Ryzen 7 7840HS, load < 0.15 at launch), two
  pinned cores each, eight of sixteen cores used so the boxes are not
  oversubscribed.

Runner: `ab-shard.sh`, `make-shards.sh`, `run-host.sh`. Analysis: `analyze.py`.
Rows: `out/<division>.tsv` (the twelve shards merged and re-sorted into path
order, so the artifact does not encode the shard split), one row per file
carrying both arms' verdict, wall time and give-up reason. `analyze.py` reads
either the merged files or the runner's per-shard ones.

## The rows

| division | n | base | new | delta | gain | loss | flip | base wall | new wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 41 | **69** | **+28** | 28 | 0 | 0 | 136 s | 223 s |
| UFDTLIRA | 200 | 72 | **82** | **+10** | 10 | 0 | 0 | 84 s | 122 s |
| UFDT | 200 | 26 | **27** | **+1** | 1 | 0 | 0 | 388 s | 480 s |
| QF_DT *(control)* | 200 | 169 | 169 | 0 | 0 | 0 | 0 | 52 s | 52 s |
| UF *(control)* | 200 | 88 | 88 | 0 | 0 | 0 | 0 | 1,374 s | 1,377 s |

**+39 net, 0 decided→undecided, 0 `sat`↔`unsat` flips.**

**Soundness — 0 disagreements, three independent checks, on all 39 newly decided
files.** Each was re-run at 24 s against both oracles and its declared status
(`verify-gains.sh`, rows in `verify-gains.tsv`); units differ and getting one
wrong cripples a reference silently, so `z3 -T:24` (SECONDS) and
`cvc5 --tlimit 24000` (MILLISECONDS):

| | rows |
|---|---:|
| axeyum `unsat` / z3 `unsat` / cvc5 `unsat` / declared `unsat` | **39 of 39** |
| any disagreement, any pair | **0** |

Neither arm disagrees with a declared `:status` anywhere in the 1,000 rows
either.

`verify-gains.tsv` is that check against the binary the A/B ran
(`ce97d2680`). `verify-gains-final.tsv` repeats it against the final source
(`816c32e25`, a pedantic-clippy refactor that split one function and swapped two
`match`es for `if let`): **39 of 39 still `unsat`, 0 disagreements**. The
refactor is behaviour-neutral because it was measured to be, not because it
looks it.

### Reading them

* **The base arm reproduces the committed board rows exactly** — 41 / 72 / 26,
  the same three numbers as
  `../dt-divisions-headtohead-20260912/guarded/`. That is the check that the two
  arms are measuring what the board measured, and it is worth more than either
  arm alone.
* **The cost is wall clock and it is real.** A query the field refusal used to
  end in 44 ms now runs the whole twenty-rung ladder: `AUFDTLIRA` 135 s → 224 s
  (+66 %), `UFDTLIRA` 83 s → 122 s (+46 %), `UFDT` 388 s → 480 s (+24 %) over
  200 files each. Both controls moved within noise (0.0 s of 52 s; 3 s of
  1,374 s), so the cost is confined to the divisions this change touches. This
  is the same trade ADR-1927 recorded and it should be quoted with the gains,
  not separately.
* **The gap is against z3/cvc5 at 24 s, not against these numbers.** The board's
  references decide 176 / 181 / 78 on these lists at 24 s. `AUFDTLIRA` 41 → 69
  closes 28 of a 135-file gap. Nothing here is parity.
* **`UFDT` gains one file and pays 24 % more wall clock for it**, and that is
  the honest way to quote it. Its datatypes are the Barrett/Reynolds
  codatatypes, 561 of whose 931 declarations have genuine datatype-typed fields
  — the class neither half of this change reaches.

## `out-run1/` — the run that found the defect

Kept deliberately. Run 1 was **+28 / +10 / −1** (and 0 / 0 on the controls): one `UFDT` file that `main`
answers `unsat` returned `backend failure: datatype sat model replay failed at
assertion #6488`. The replay was right to reject the candidate; the defect was
that a replay failure on the exact path raises `SolverError::Backend`, which
ends the dispatch, so the ladder never reached the route that decides the file.

An Ackermann-expanded query's model reconstruction is partial by construction,
so it is a relaxed query and a replay failure is a decline. Fixed in
`ce97d2680`, the binary rebuilt, and the whole 1,000-file run repeated from
scratch — `out/` is that second run, not a patched copy of the first.

## The residual census

Taken on the NEW arm over the three target divisions, undecided files only:

| refusal | files |
|---|---:|
| UF applied to a datatype term that is **not a free variable** | **173** |
| congruence over a datatype argument whose **expansion is not exact** | 50 |
| a UF whose **RESULT sort mentions a datatype** | 47 |
| e-matching instantiation did not refute within the round budget | 39 |
| `is`/`select` over a non-variable datatype term | 22 |
| quantified solve budget exhausted after e-matching | 17 |

The top row did not appear on any earlier census, because the refusal it names
did not exist until this change: it is a **constructor term as a UF argument**
(`p(mk(a,b))`). Its argument equality is structurally exact and cheap, so it is
the obvious next slice. The 50-file row is the datatype-field class this work
deliberately does not reach.

Read this table the way ADR-1927 says to read any blocker census: it says which
refusal fires first, not how many files a fix would win. The sizing that turns
one into the other is
`../../docs/research/03-measurements/the-adr-1920-slice-is-6-of-600-files-2026-09-12.md`.
