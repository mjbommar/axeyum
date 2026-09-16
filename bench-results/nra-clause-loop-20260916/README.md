# `nra-clause-loop-20260916` — ADR-2131 artifacts

Lane `NRA-CLAUSE-LOOP`. Everything here is reproducible from the committed
scripts, and every script prints the control it passed before its result.

## Sizing (exit criterion 1) — the instrument committed with the measurement

The question ADR-2126 left: of the QF_NRA files we do not decide, how many does
the clause loop's shape actually reach?

- `size-scan.sh` — one `--trace` pass per file through `scripts/ledger-run-one.sh`,
  which keeps the FULL stdout rather than one verdict token. So "did we decide
  it" and "why not" come from the SAME run; ADR-2126's scan needed two.
- `size-A-captures.tar.gz` — the 200 kept captures.
- `size-report.py` / `size-A.txt` / `size-A.tsv` — the verdict and cause table.
- `shape-report.py` / `shape-34.txt` / `shape-34.tsv` — the Boolean shape of the
  files whose cause is `non-conjunctive`.
- `qfnra-200.txt` — the pinned draw, identical to ADR-2126's (checked, not
  assumed).

Run on s5 (idle, load 0.02 at start), cores 1/9/3/11, 24 s wall, 8 GiB
`ulimit -v`, one file per invocation.

### What it says

**124 decided (55 sat, 69 unsat), 76 undecided.** The 2026-09-15 board records
122 for this draw; re-deriving on a quiet box is exactly why the brief asked for
it, and it is the reason a lane must never size itself from a committed board
snapshot.

Causes on the 76:

| files | cause |
|---:|---|
| 34 | `non-conjunctive` |
| 22 | `slice-bounds` |
| 6 | `algebraic-witness` |
| 4 | ABSENT — no `nra-real-root` attempt (the watchdog killed the run first) |
| 3 | `coefficient-range` |
| 2 | `projection-resultant-zero` |
| 1 | `declined/not-applicable` |
| 1 | `root-ordering` |
| 1 | `projection-arithmetic` |
| 1 | `projection-sylvester-dim` |
| 1 | `certificate-rejected` |
| **76** | **total** |

`size-report.py` refuses to report an unrecognised cause into an "other"
bucket — an "other" bucket is how a new cause hides — so its exit status
depends on every row being attributable. It failed twice while being written,
once on the trace detail being a sentence rather than a key and once on a
`declined/not-applicable` outcome that carries no cause at all; both are now
named rather than absorbed.

### And the ceiling is **16**, not 34

`shape-report.py` parses the assertions of every `non-conjunctive` file (an
s-expression reader with `let` expansion under a 2,000,000-node budget and an
8 GB address-space limit; the budget never fired, so every number is exact):

| | 34 undecided | all 118 `non-conjunctive` |
|---|---:|---:|
| `n_bool_vars > 0` — the loop cannot abstract these | 1 | 46 |
| `n_atoms > 48` — over `MAX_CLAUSE_ATOMS` | 18 | 63 |
| **neither — admissible** | **16** | **55** |

Note the denominator trap in that table, because it is the kind that inflates a
ceiling: the cause filter alone selects **118** files, but **84 of them are
already DECIDED** by a later rung of the ladder and can gain nothing. The
ceiling is the intersection with "we do not decide it", and `shape-report.py`'s
control is on that number.

Three things about the shape that change what is worth building:

- **Zero files use `ite`, `=>`, `xor` or `distinct`**, and `or` is binary in
  every file but one (arity 4). The clause loop's handling of those connectives
  is correctness surface, not reach.
- **`n_atoms` is sharply bimodal and the 48-atom cap sits in the empty gap.**
  Over all 118: fifty-five files at 3..12 atoms, ONE at 103, then sixty-two from
  125 to 63,180. Moving `MAX_CLAUSE_ATOMS` anywhere from 13 to 102 changes
  nothing at all. Raising the cap is not a lever on this corpus.
- **The Bool-leaf decline predicts nothing the atom cap does not already
  predict** on the 34: its single Bool-carrying file has 321 atoms and is over
  the cap anyway.

## The A/B

- `build.sh` — builds the one binary and publishes it to
  `/nas3/data/axeyum/lanes/nra-clause-loop/` with its sha256, so the sweep host
  reads the same bytes the build host produced.
- `ab-launch.sh` drives `ab-run.sh` over four divisions, four shards each, one
  shard per pinned core, divisions serial.
- `ab-report.py` joins the shards and refuses to report a flip or a `:status`
  disagreement without failing.
- `recheck-movers.sh` re-runs every mover 3× per arm on one pinned core;
  `arm-a-default.sh` / `arm-b-clause-loop.sh` are the two wrappers it needs (its
  same-binary guard compares executables, and "one binary, two env values" has
  to stay true underneath).

Arms: **A** = `AXEYUM_NRA_CAD` set and empty, which is the shipped default
(`CadPolicy::SINGLE_CELL`); **B** = `clause-loop`.

**ADR-2131 rebased arm B before running this.** ADR-2126 built the arm on
`SINGLE_CELL_SAT` when that was the default, then moved the default to
`SINGLE_CELL`. From that moment the two arms differed in `emit_unsat` as well as
`clause_loop`: the treatment arm would have had the single-cell route's `unsat`
half switched OFF, and every verdict that half contributes would have read as a
loss caused by the loop. The arm now carries `emit_unsat: true` and
`the_single_cell_arm_differs_in_exactly_the_route` reads the comparison arm out
of `CAD_DEFAULT` rather than naming it, so repointing the default without
rebasing the arm fails the test rather than producing a clean, wrong number.

Divisions: QF_NRA (target), QF_NIA (shares the nonlinear code), QF_LRA
(control — a mover there is a finding about the harness), and the held-out
QF_NRA draw, which is ADR-2126's, reused with its own seed and **checked
disjoint from the pinned draw: overlap 0 of 200**.
