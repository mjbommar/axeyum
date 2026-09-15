# Lane: lra-trace — what the same simplex does differently on `QF_LRA` (ADR-2111)

<!-- plan-section: lane-status -->

**Lane LRA-TRACE (`WIP`, lra-trace, 2026-09-15).** `QF_LRA` reads ours 107 of
200 against z3 166 — 59 behind — and every reference decides those files with
the same Dutertre–de Moura simplex we ship, so the lane's question was what ours
does differently with a trace on both sides, not which algorithm is missing.
ADR-2111 is **`proposed`**, not accepted: no lever ships `On`.

**Census of all 93 undecided rows, four cause channels, 0 without a capture**
(the give-up string alone loses the largest bucket, [ADR-2045]): **40 `rc=134`
allocation aborts, 36 `budget/other`, 7 `incomplete`, 5 `bound-no-decline`, 5
`not-applicable`**. **34 of 93 are bound inside `lra.rs` before the simplex gets
a system**; **only 23 of 93 ever reach the online CDCL(T) engine**. The typed
decline name types nothing here — all 36 budget rows carry `Budget::Other`.

**Shape census with the 107 decided as a control.** Atoms separate the halves
**1,351×**; **coefficient size does not** (max 10 digits on both halves against
`i128`'s 38), which kills the "big coefficients" reading before a trace is read.

**Reference trace, same envelope and cores.** z3 `smt.arith.solver=6` 57 of 93,
`=2` 56, agreeing on 53 — **`lar_solver` accounts for four files**, so "their
newer simplex is better" is not the explanation. **33 of 93 are decided by
nobody at 24 s: the prize is 60, not 93.** And the largest bucket by COUNT is
not the largest by ADDRESSABILITY — the 40 aborts are 50 % reachable, the 32
`lra.rs` rows are **86–91 %**.

**Shipped:** `Tableau` is sparse (`row_val` aligned with the `row_nz` index that
already existed, plus a `col_rows` transpose), as the only path, with a
soundness-negative fill-in fixture. On the median abort row that is **1.62
billion cells holding 147,440 nonzeros — 48.4 GiB against an 8 GiB ceiling —
becoming a clean `unknown` at 203 MB**. Two levers, **both `Off`/default**:
`AXEYUM_LRA_TABLEAU_RESERVE` and `AXEYUM_LRA_ATOM_SCREEN`.

**Two negatives worth more than the positive.** `TableauReserve::Sparse` is
**inert** on the population it was aimed at — the screen that refuses those rows
is an atom count at `lra_theory.rs:305`, not the tableau reserve — so its A/B
was deliberately **not run**, because `net +0` from an inert arm cannot be told
from `net +0` from a working one. And `git log -S` on the atom screen found
**three cost models built to replace it and all three falsified by the corpus**;
the third bounded Fourier–Motzkin correctly and still let
`miplib/danoint-266.smt2` reach 7.8 GB **with `simplex_rows=n/a`** — the simplex
did not exist, so those bytes were never the tableau and the sparse storage
cannot have removed them.

**Next:** the six-division A/B is running (QF_LRA at 160 of 200 reads **net +0,
0 gains, 0 losses, 0 flips, 0 disagreements at a comparable denominator of 75,
32 exit statuses moving `134 → 0`** — so **0 abort rows decide at 24 s**, and
with 0 movers the 3× recheck has a comparable denominator of 0). Then the atom
screen's own A/B on the 34 `lra.rs` rows plus its two named controls. The
largest unpulled lever remains the touched-driven bound scan and the bound
axioms: a median **19** theory propagations against **836,531** decisions.

<!-- plan-section: landed-changes -->

| 2026-09-15 | `894b960a2` | lra-trace: `screen-ab.sh`, with its two named control files wired in rather than remembered |
| 2026-09-15 | `ee8f64513` | lra-trace: the atom screen becomes `AXEYUM_LRA_ATOM_SCREEN` (default 1); three falsified cost models say why raising it is a trap |
| 2026-09-15 | `9e691e0fd` | lra-trace: A/B resume helper, and the duplicate-writer near-miss that shaped its warning |
| 2026-09-15 | `2e234c144` | lra-trace: three measurements converge on the online engine rather than the route |
| 2026-09-15 | `be6b10a65` | lra-trace: `TableauReserve::Sparse` is INERT on its target population; its A/B deliberately NOT run |
| 2026-09-15 | `0f9c8b788` | lra-trace: reference trace — z3's two simplexes differ by FOUR files of 93, 33 decided by nobody at 24 s |
| 2026-09-15 | `d4c3d9c63` | lra-trace: registry entries for the sparse rate; the mechanism on the median abort row |
| 2026-09-15 | `e85b52917` | lra-trace: ADR-2111, the mutation registration, and the reference/A-B instruments |
| 2026-09-15 | `81ed00d56` | lra-trace: the simplex tableau is sparse (nobody else stores a dense one); `TableauReserve` lever ships `Dense` |
| 2026-09-15 | `2b66f2d50` | lra-trace: all 93 undecided rows bucketed over four channels — 40 aborts, 34 die in `lra.rs` before the simplex, 23 reach the online engine |
| 2026-09-15 | `28280dbfb` | lra-trace: `QF_LRA` shape census — undecided are 1,351x the decided in ATOMS and identical in COEFFICIENT SIZE, with the 107 decided as a control |
