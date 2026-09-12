# The four datatype divisions — the first board rows

**2026-09-12, lane `dt-divisions`.** `UFDT` (4,569), `UFDTLIRA` (7,749),
`AUFDTLIRA` (11,043), `UFDTNIRA` (4,424) — **27,785 files** — have never carried
a parity row. These are the first.

## Protocol

200 files per division from the stride-pinned lists in
`bench-results/parity-lists/`, committed **before** anything was run
(`UFDT` at `49a0e2698`, the other three at `62e55bdd1`). Per file: **24 s wall,
8 GiB address space**, three solvers **interleaved per file** (all three finish
file N before any starts N+1) on the same pinned core pair of the same idle
homogeneous box (`s5`/`s6`/`s7`, Ryzen 7 7840HS), with the solver that goes
first rotating per file. Units differ and are set accordingly:
`z3 -T:24`, `cvc5 --tlimit=24000`.

The 200 files of each division were split into three modulo-interleaved shards
(`NR%3`) so each shard spans the whole division; a shard is the unit that runs,
and the merged TSV is re-ordered back into the pinned list's order, so the
artifact does not encode the shard split.

**The wrapper timeout is `24 + 16 = 40 s`, not `24 + 8`.** A previous census
used +8 under load, killed 17 processes, and produced rows that read as "no
reason". Every run records its own outcome in a `*_k` column: `ok`,
`wrapper-killed`, `rc134` (the 8 GiB address-space cap firing), `sigkill`.
No row in these boards is `wrapper-killed`.

## Rows

| division | files | axeyum | z3 | cvc5 |
|---|---:|---:|---:|---:|
| UFDTLIRA | 200 | **66** | 181 | 158 |
| AUFDTLIRA | 200 | **0** | 176 | 176 |
| UFDT | 200 | *(running)* | | |
| UFDTNIRA | 200 | *(running)* | | |

**Soundness: 0 disagreements, three independent checks**, on every division
scored so far — against the file's declared `:status`, against z3, and against
cvc5. `AUFDTLIRA` decides nothing, so its zero is vacuous and is not evidence;
`UFDTLIRA`'s 66 (60 `unsat` + 6 `sat`) is not.

## Reading them

- **The reference is not one solver.** On `UFDTLIRA`, z3 decides 23 files cvc5
  does not and cvc5 decides **0** that z3 does not, so z3 — not the
  datatype solver of record — is the leader in this division. Name the
  reference whenever you quote a gap.
- Two `AUFDTLIRA` rows have `cvc5_k=rc134`: cvc5 aborted on the 8 GiB
  address-space cap. Per the parity protocol those count as not solved, which
  is why cvc5's 176 is a floor.
- `UFDTLIRA` at 24 s decides 66/200 (33 %), while a 40-file 3 s census on
  2026-09-12 put it at 19/40 (47.5 %). Different samples, and 40 files carry a
  wide interval; the 200-file board is the number to quote.
