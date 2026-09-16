# `nra-cell-exact-20260916` — ADR-2126 artifacts

Lane `NRA-CELL-EXACT`. Everything here is reproducible from the committed
scripts; each one prints the control it passed before its result.

## Sizing (exit criterion 1, the instrument committed before the measurement)

ADR-2121 reported `CadDecline::Projection` at **2 of its 24 in-bounds QF_NRA
files** and said in its own closing section that the number was an **upper
bound**, because the bucket held four failures with four different fixes: the
Sylvester dimension cap, an identically-zero resultant, a derivative overflow
and a coefficient overflow. Only the first is what a fraction-free (Bareiss)
determinant would remove.

- `inbounds-24.txt` — the same 24 files, taken from ADR-2121's
  `cause-inbounds-24.tsv` so the two tables describe one population.
- `cause-scan.sh` — ADR-2121's runner, unchanged, re-run against this lane's
  binary under `AXEYUM_NRA_CAD=single-cell`.
- `recause-inbounds-24.tsv` — the scan.
- `recause-report.py` / `recause-report.txt` — the re-bucketing and its run.
- `binary-sha256.txt` — the binary the scan used.

**Result, and it halves a ceiling:**

| files | cause | what would fix it |
|---:|---|---|
| 12 | `non-conjunctive` | the clause loop |
| 6 | `algebraic-witness` | an algebraic sample |
| 2 | *decided* | nothing — the route decides these |
| 1 | `certificate-rejected` | the checker accepting what the producer built |
| 1 | `projection-arithmetic` | wider coefficient arithmetic |
| **1** | **`projection-sylvester-dim`** | **a fraction-free (Bareiss) determinant** |
| 1 | `root-ordering` | exact ordering of two critical values |
| **24** | **total** | |

So the determinant lever is worth **1 file** in this slice, not 2.

**And the other six rows are a control, not just context.** This scan ran under
the EXACT delineability checker (`8bb5cb970`), and `certificate-rejected` is
still 1 and *decided* is still 2 — exactly ADR-2121's numbers. Strengthening the
checker cost zero files on the population where it could have cost them.

`recause-report.py` refuses to report unless the row set equals the file list it
was handed, the row count is 24, every row carries a recognised cause, and every
cause has a recorded fix. Its exit status depends on the finding: truncating the
TSV to 19 rows gives exit 1 with two named control failures (checked, not
assumed).

## The A/B

`ab-sweep.sh` drives `ab-run.sh` over three divisions, four shards each, one
shard per pinned core (s5 cores 1, 9, 3, 11), 24 s wall and 8 GiB `ulimit -v`.
The arms:

- **A** = `AXEYUM_NRA_CAD` set and EMPTY. `parse_cad_arm("")` is `CAD_DEFAULT`,
  which ADR-2121 moved to `CadPolicy::SINGLE_CELL_SAT` — so arm A is **the
  shipped default**, not the pre-route engine, and its score reproducing the
  board is the control on the whole measurement.
- **B** = `single-cell`, the full arm. The two differ in exactly `emit_unsat`,
  so this A/B prices the route's `unsat` half **alone** — which is the half
  ADR-2121 withheld and the half ADR-2126's exact check exists to make
  shippable.

One binary, two env values; its sha256 is written beside the results by the
sweep itself, because "one binary" is a claim and not a convention.

QF_NIA shares the nonlinear code, so a regression there is the one a QF_NRA-only
sweep would miss. QF_LRA is the **control**: nothing linear goes near this
route, and `ab-report.py` exits non-zero if it moves.

The shard lists (`shard<N>-<div>.txt`) and the 200-file division lists are
committed even though a stride over the latter reproduces the former, because
"which core ran which file" is part of an interleaved A/B's frame and a later
reader should not have to re-derive it. They are ADR-2121's lists, copied
deliberately: the two A/Bs are then over the same files and their numbers can be
put side by side.

## What is deliberately not here

`bench-results/frontier/*.json` — the `progress_frontier` ratchet rewrites five
of them on every run; they are restored, never staged.
