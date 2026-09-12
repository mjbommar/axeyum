# Lane: dt-divisions — the four datatype divisions get a board, and the board finds a dispatch bug

<!-- plan-section: lane-status -->

**Lane dt-divisions (`DONE`, dt-divisions, 2026-09-12).** `UFDT` (4,569),
`UFDTLIRA` (7,749), `AUFDTLIRA` (11,043), `UFDTNIRA` (4,424) — **27,785 files**
— had never carried a parity row. They have four now, and producing them found
a dispatch defect worth more than the rows.

**The boards.** 200 files per division from stride-pinned lists committed before
anything was run (`49a0e2698`, `62e55bdd1`), 24 s / 8 GiB, three solvers
**interleaved per file** on one pinned core pair of one idle homogeneous box,
first-mover rotating. Wrapper timeout `24 + 16 s`, with every run's own outcome
recorded per solver — an earlier census used `+8` under load, killed 17
processes, and produced rows that read as "no reason". Rows and protocol:
[`bench-results/dt-divisions-headtohead-20260912/`](../../../bench-results/dt-divisions-headtohead-20260912/README.md).

| division | files | axeyum | z3 4.13.3 | cvc5 1.3.4 |
|---|---:|---:|---:|---:|
| UFDTLIRA | 200 | **66** | 181 | 158 |
| UFDT | 200 | **22** | 66 | 78 |
| UFDTNIRA | 200 | **5** | 173 | 183 |
| AUFDTLIRA | 200 | **0** | 176 | 176 |

**0 disagreements on all four, three independent checks** (declared `:status`,
z3, cvc5). Two warnings the rows carry: the reference is **z3** in `UFDTLIRA`
(it decides 23 files cvc5 does not; cvc5 decides 0 that z3 does not) and cvc5
elsewhere; and cvc5's `UFDT` 78 is a badly depressed floor — 100 of its 200 runs
hit the 8 GiB address-space cap (5 re-run at 24 GiB returned `unknown`, which is
a spot check, not a clearance).

**`AUFDTLIRA` scored 0 of 200 while z3 and cvc5 each scored 176** — and a zero
against references that decide 88 % of the same files in under a tenth of a
second is not what a capability gap looks like. `--trace` said `attempts=2` on a
twenty-rung ladder, at 1 ms, quoting a `QF_UFBV` Ackermann restriction for a
quantified benchmark with no bit-vector in it.

**Verdict BUILD, landed, decided by
[ADR-1927](../../research/09-decisions/adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md)
on [the measurement](../../research/03-measurements/the-dt-blocker-census-was-measuring-the-ladder-2026-09-12.md).**
Three quantified-ladder rungs — valid-universal elimination, the e-graph
refuter, the MBQI pass — ran a *speculative sub-solve over a rewritten query*
and propagated its `SolverError::Unsupported` with a bare `?`. A backend
refusing the fragment of a query the solver had **built itself** therefore became
the file's answer, and the seventeen rungs below never ran. The rung directly
above them already had the rule in its own words ("this is an optional
accelerator; it must never turn a query the established portfolio can handle
into an operational error"); these three had the same contract and not the
guard.

Per-file A/B against the same binary without the guards, arms alternating,
10 s / 8 GiB, 200-file stride samples:

| division | base | guarded | new | lost | flips |
|---|---:|---:|---:|---:|---:|
| AUFDTLIRA | 0 | **62** | 62 | 0 | 0 |
| UFDTLIRA | 70 | **75** | 5 | 0 | 0 |
| UFDT | 23 | **26** | 3 | 0 | 0 |
| UFDTNIRA | 10 | 10 | 0 | 0 | 0 |
| **UF (control)** | 83/189 | 83/189 | 0 | 0 | 0 |

All 70 new verdicts are `unsat` and carry **0 disagreements on three independent
checks** — the declared `:status`, z3 4.13.3 and cvc5 1.3.4 — with all 70
*comparable* on all three, so no check was silently vacuous. `UF` is the control
that says the change costs an already-working quantified division nothing;
`UFDTNIRA` is the honest null (it is more than half clock-bound at 10 s).

**Mutation control:** delete the valid-universal guard and 2 of the 3 tests die;
delete the e-graph guard or the MBQI guard and 1 dies. Each is individually
load-bearing. The e-graph and MBQI guards are **not** separable by a
verdict-level test and that is structural, not a gap: they are consecutive rungs
on one path, so deleting the earlier one stops the dispatch before the later one
is reachable. A **fourth** guard was written for `checked_quantified_fast_path`,
scanned over 800 corpus files with the trail inspected for its own decline
label, found to fire **0 times**, and REMOVED — an unreachable guard is the
un-failable checker this repository keeps deleting.

**Also fixed, and it was red before this lane touched it:**
`tests/unknown_reason_coverage.rs` had two failing tests on local `main`.
Proved pre-existing by re-running at HEAD with this lane's diff reverted —
identical failure. ADR-1930's chosen selector interpretation made that suite's
"the dispatch ERRORS on this" fixture **decide `sat`**: two lanes green apart,
composing red. The fixture is replaced (per the file's own instruction) with a
UF-over-datatype-argument script that still errors.

**The finding worth more than the 70 files: the census this lane was dispatched
on was measuring the ladder.** Before the guards, 174 of 200 undecided
`AUFDTLIRA` files reported "eager Ackermann … array-valued function results".
After, that message is **3 of 200**, and the real top blocker is
`datatype_native` refusing array/UF-sorted datatype FIELDS (70), then UF applied
to a datatype argument (32). Bisecting the guards in one at a time produced
**four different "blockers" for one unchanged file**. *A blocker census taken
through a ladder that stops at its first refusal measures the ORDER OF THE
LADDER* — reproducible, stable across samples, and confidently wrong.
`attempts=` in `--trace` is the check.

**What to build next is now named twice independently.** Across the three
divisions where the ladder runs to the end (600 files), the corrected census's
top two are **UF applied to a datatype argument (143)** and **array/UF-sorted
datatype fields in `datatype_native` (152)**. The first is exactly ADR-1920's
"BUILD NEXT" — Ackermann congruence over expanded datatype arguments, restricted
to datatypes whose fields are all scalar. The second is the half that
restriction excludes, and these divisions are SPARK/Ada verification conditions
and the Barrett/Reynolds codatatype family, whose records are array-valued.
**Doing only the ADR-1920 slice leaves 152 of 600 sampled files where they
are.** Price both or neither.

**The cost, stated because it is real:** a query the ladder refused in 1 ms now
runs all twenty rungs and can spend its whole budget. The A/B lost **0** verdicts
to that at 10 s, but a sweep over these divisions is much slower than it was.
The old speed was the speed of being wrong.

<!-- plan-section: landed-changes -->

| 2026-09-12 | `b191b1f3e` | ADR-1927: three quantified-ladder rungs decline a sub-solve's `Unsupported` instead of propagating it; `tests/quant_ladder_rung_refusal_declines.rs` (3, incl. a soundness-negative) |
| 2026-09-12 | `8cd15bf3a` | first parity board rows for `UFDTLIRA` (66/200) and `AUFDTLIRA` (0/200), 0 disagreements on three checks |
| 2026-09-12 | `62e55bdd1` | `UFDTLIRA` / `AUFDTLIRA` / `UFDTNIRA` 200-file stride lists pinned before any measurement |
