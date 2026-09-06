# SMT/SAT parity plan: root causes across all eleven divisions, 2026-09-05

Status: **active**. This is the plan the user asked for after the 2026-09-05
board: address the root cause of every division's gap, then execute until each
division reaches its reference or better. It is a plan of record for lanes;
the ordered queue entry is A12 in
[`docs/plan/global/20-next-actions.md`](global/20-next-actions.md). Every
number here is read from a committed artifact named beside it. Nothing below
is authorized on a feeling: each slice names the files it is scored on and the
gate that fails if it does not move them.

Companion documents, all landed today:

- [the performance and architecture review](../research/11-design-review/2026-09-05-sat-smt-performance-and-architecture-review.md)
- [the re-measured board](../research/11-design-review/2026-09-05-parity-remeasured.md)
- [arithmetic timeout profiles](../research/11-design-review/2026-09-05-arith-timeout-profiles.md)
- [ADR-1701 slice-1 measurement](../research/11-design-review/2026-09-05-adr-1701-slice-1-measured.md)
- [ADR-1701 slice-2 design memo](adr-1701-slice-2-design-2026-09-05.md)
- [native core vs Kissat search statistics](../research/11-design-review/2026-09-05-native-core-vs-kissat-search-stats.md)
- [gate (b) measurement](../research/11-design-review/2026-09-05-gate-b-sat-core-measured.md)

## Progress log

### 2026-09-06, end of the first execution day

**Landed on `main`, each verified after merge (workspace check, full solver
sweep, corpus sweep, z3 differential fuzzes for arithmetic changes, clippy,
wasm, merge hygiene):** S1 watched-literal propagation in `CdclT`
(`eff6a464b`), S2 admission preflight and the watchdog stage line
(`b4d042ae4`), S4 the O(rows) simplex pivot update and whole-form implied
bounds (`69742894a`), S5 ADR-1704 the two-stream proof contract
(`5c9b3a7c2`), S3 the loss census of all 403 reference-only files
(`4339eb793`), S6 the one-word tagged `Reason` in the native core
(`3b6d42f6c`), plus one composition fix (`287ca85c0`: two clean branches
produced a clippy failure on merge).

**The board after those slices**, latest ledger entry per division, idle
hosts, zero disagreements everywhere
([`bench-results/PARITY.md`](../../bench-results/PARITY.md)):

| Division | Solver commit | Ours | Theirs | Ratio | both / ours / theirs | Gap |
|---|---|---:|---:|---:|---|---:|
| QF_SLIA | `9914a1c0e` | 193 | 194 | 99.5% | 187 / 6 / 7 | 1 |
| QF_BV | `9914a1c0e` | 188 | 194 | 96.9% | 188 / 0 / 6 | 6 |
| QF_UF | `c28d7b7c6` | 196 | 200 | 98.0% | 196 / 0 / 4 | 4 |
| UF | `b32377dc5` | 85 | 93 | 91.4% | 61 / 24 / 32 | 8 |
| QF_ABV | `9914a1c0e` | 179 | 197 | 90.9% | 178 / 1 / 19 | 18 |
| QF_RDL | `b32377dc5` | 128 | 154 | 83.1% | 127 / 1 / 27 | 26 |
| QF_LIA | `b32377dc5` | 112 | 139 | 80.6% | 110 / 2 / 29 | 27 |
| QF_IDL | `b32377dc5` | 86 | 123 | 69.9% | 84 / 2 / 39 | 37 |
| QF_UFLIA | `5c9b3a7c2` | 123 | 180 | 68.3% | 123 / 0 / 57 | 57 |
| QF_LRA | `5c9b3a7c2` | 93 | 145 | 64.1% | 93 / 0 / 52 | 52 |
| QF_NIA | `9914a1c0e` | 39 | 87 | 44.8% | 26 / 13 / 61 | 48 |

Total gap to parity: **284 files, down from 356** at the start of the plan
(ours 1,422 of 1,706 reference decisions; QF_UF re-measured at `c28d7b7c6`
after the S1b + S11a merges, 190 -> 196, zero disagreements; the other five
re-measured divisions are pending below). S1 and S2 together moved 65 files
(QF_IDL +16, QF_RDL +21, QF_UF +28; the measuring commit `b32377dc5` contains
both, so the split between them is not measured); S4 moved 3 (QF_LRA +2,
QF_UFLIA +1). The two
QF_LIA files that appeared lost under S1 were traced by S1b to S2's admission
preflight, not to the watched literals (see the S1b status file). QF_SLIA,
QF_BV, QF_ABV and QF_NIA have not been re-measured since `9914a1c0e` because
no landed slice targets them yet.

**What the census changed** ([note](../research/11-design-review/2026-09-05-parity-loss-census.md)):
of 403 losses, 217 are admission declines on constants, 137 search timeouts,
41 other, 6 unsupported shapes, 2 parser rejects. QF_IDL's 46 of 54 were the
S1/S2 signature and have largely converted. UF and QF_UF's 70 were one
admission cap on eager Ackermann expansion with no timeouts; S11a is on it.
QF_SLIA and QF_NIA both hit the int-blast width ladder, a shared S11/S12
target not previously named. Two constants are in play and both are real:
the ladder's top rung is `DEFAULT_INT_WIDTH = 32` (`lia.rs`, the "bounded
integer width 32" the census records) and the rewrite-level admission ceiling
is `MAX_INT_BLAST_WIDTH = 64` (`axeyum-rewrite/src/int_blast.rs`, the number
S9's ablation names). One QF_LIA file overflows `i128` inside
the simplex, not the parser, so S9's parser fix alone will not close it.

**Three more slices finished in worktrees after the pause, gates green,
awaiting merge behind the push freeze** (status files under
`docs/plan/status/`):

- **S1b** (`worktree-agent-a03c88d2048b0e8ba`, `649a12add`): VSIDS order heap
  and recursive clause minimization in `CdclT`. QF_IDL timeout population
  **11 -> 27 of 50** on idle s5; `RVpredict_13` makes identical decisions in
  both arms and falls 15.5 s -> 1.8 s, so the cost was the linear decision
  scan alone. The two QF_LIA files "lost" under S1 were S2's admission
  preflight declining before the online probe that used to refute them
  (`bofill-scheduling/SMT_real_LIA/ex3000_2400_100`, `ex4320_2400_100`); an S2
  follow-up should let the size-gated route still run the online probe.
- **S9** (`worktree-agent-a464d7d70f97462cc`, `d975a1fbb`): wide integer
  literals as sibling `WideIntConst`/`WideInt` variants; the parser admits
  them; every route declines at its boundary; a **panic on user input** in
  the replay evaluator is fixed. The plan's "+6 against cvc5" for the 26
  QF_UFLIA files is **unsupported**: ADR-0376's ablation re-run on today's
  HEAD gives 0 of 6 either way, so the binding constraint is the 64-bit
  int-blast width, not the literal type. Also fixed: the mutation harness
  could not name a `should_panic` death.
- **S11a** (`worktree-agent-aca5ca910320deff7`, `5801c2d4b`): **the census's
  UF/QF_UF attribution was wrong for 67 of 70 files**, two ways: the census
  `class` is the last route's message (on 35 QF_UF files `euf-online` is
  entered first and times out at 23.5 s; the Ackermann decline that named the
  class costs milliseconds after the budget is gone), and `explain_corpus` is
  not the front door (all 32 UF files end at quantifier-instantiation limits
  there, none at the CEGAR bound). `euf-online` was already first in dispatch.
  On today's main 26 of the 38 QF_UF "losses" already decide. The cap
  genuinely blocked 3 files; fixed by no longer discarding a replay-confirmed
  `sat` in `check_qf_ufbv_lazy` and passing a terminal-rung pair bound
  (16,384) where nothing runs after it. 38-file population 27 -> 29, 0 flips.

Two corrections to the census method follow from S11a: classify by the
route that spent the budget, not the last message, and classify through the
front door, never through `explain_corpus`. The UF/QF_UF lever is S1b's heap
and S7's engine, not a cap.

**In flight at the pause:** none; every dispatched slice has reported.

**Next steps, in order:**
1. ~~Merge S1b, S9, S11a~~ **done** (`5fa2e3feb`, `97ce06aff`,
   `5f4c38c32` + `b40a0f309`; see the later entry above). Still owed from
   this step: the full 200-file QF_UF and UF sweeps S11a did not run.
2. Re-measure QF_IDL, QF_RDL, QF_UF, UF, QF_LIA and QF_UFLIA on idle hosts at
   the merged commit; append entries; fresh sidecars, no resume across
   binaries.
3. S7, move CDCL(T) onto the native core behind the measured hooks, now that
   S5 (contract) and S6 (reason word) are landed; scoring target the QF_IDL
   and QF_LRA populations; every verdict unchanged across the corpus suite.
4. S8 native-core throughput against Kissat's conflicts-per-second on the
   p4dfa CNFs, after S7 so the gain reaches every division.
5. S11 remainder by census class: the 32-bit int-blast width ladder shared by
   QF_SLIA and QF_NIA; QF_ABV's three array shapes; the QF_LIA simplex
   overflow (S9's wide path applied inside `simplex.rs`).
6. S10 the 1,024-atom LRA cap as a measured memory budget once S7 lands.
7. S12 the NIA coefficient-width rung, last, scored on the 32 one-live-rung
   files and on files outside the `VeryMax/ITS` family.

Standing rules learned this day, now in the contributor notes: a `.lock` file
under `/data0/axeyum/prepush/` is a permanent flock target, never a held-lock
signal; a hold notice from any coordinator session blocks landing until that
session says "clean"; two green branches can fail `clippy -D warnings` on
merge through a size-threshold lint, so the post-merge gate is check plus
clippy on every crate either branch touched.

### 2026-09-06, later: S1b, S11a and S9 merged onto `main`

All three finished branches are on `main`, in that order, each as a
`--no-ff` merge verified before the next: S1b `5fa2e3feb` (hygiene PASS,
workspace check, clippy on solver and bench, 39 cdclt tests, corpus sweep),
S11a `97ce06aff` (hygiene PASS, workspace check, clippy, 77 EUF tests, corpus
sweep), S9 `5f4c38c32` plus the composition fix `b40a0f309`. The three
branches are now 0 commits ahead of `main`. Not pushed yet; the next push
window is coordinated with the math-department session.

**S9 did not compose with `main`.** Main commit `52ebb81de` had removed the
IR crate's direct `num-bigint`/`num-integer`/`num-traits` dependencies and
routed the names through `axeyum_arith::big`; S9's new `int_wide.rs`, its
differential fuzz and one `ir.rs` test imported the crates directly. The
merge auto-resolved with no conflict (no manifest was touched) and `main`
failed with `E0432 unresolved import`. The fix is import rewrites only
(`b40a0f309`, 3 files, 11 lines). Third shape of the same lesson: a merge
that touches no manifest can still remove a dependency a branch relies on,
so the workspace check runs BEFORE "clean", never after.

**S9's harness conflict** in `scripts/tests/mutation_controls.py` was the
mid-item shape (both sides shared the closing three lines of the last
suite); resolved as `main`'s file plus S9's two appended suites and its
`should panic` regex fix, verified by import (101 suites) and the control
suite (34 of 35; the one failure, an ambiguous anchor in
`cas-summation-and-gaussian` against `axeyum-cas/src/lib.rs`, fails
identically on `main` before S9 and in the S9 worktree, is in the CAS area,
and was reported to that coordinator rather than touched).

**Gate state of the merged `main` (from `b40a0f309`), all green:** merge
hygiene PASS, gen-plan clean, workspace check, workspace clippy
`-D warnings`, every IR suite, smtlib lib (90), solver lib `--features full`
(1,460 passed), corpus sweep, the three z3 differential fuzzes (5 + 1 + 1),
the wasm build, `cargo fmt --all --check`. One non-gating observation: the
wasm build on default features prints three dead-code warnings
(`TheoryLayerStats`, its `total`, and `memory_budget::parse_vm_rss_kb`),
because those diagnostics are only constructed behind `full`; a `cfg` on
the module is a cheap follow-up for whichever lane next touches `layers.rs`.

**Re-measurement launched** at `c28d7b7c6` (first result: QF_UF 196/200,
98.0%, 0 disagreements, 4 reference-only left) (solver code identical to
`b40a0f309`; the later commits are docs and a harness anchor fix) on idle
s5 (QF_IDL, QF_RDL), s6 (QF_UF, UF), s7 (QF_LIA, QF_UFLIA), fresh
`~/axeyum-parity-m1` checkouts from a bundle, fresh sidecars, no resume.

**Next:** step 2 of the list below, re-measuring QF_IDL, QF_RDL, QF_UF, UF,
QF_LIA and QF_UFLIA on idle hosts at `b40a0f309` with fresh sidecars, then
the full 200-file QF_UF and UF sweeps S11a did not run, then S7.

### 2026-09-06, plan audited against the ledger, the census artifacts and `main`

Every number in the progress-log board was rebuilt from
`bench-results/PARITY.md` (latest entry per division) and matches: 290 gap,
1,416 of 1,706, zero disagreements in all eleven. Every code claim was checked
on `main` at `27dd9142c`: the `CdclT` rescan loop is gone and watch lists are
present (S1); `arith_dpll_admission_preflight` and the
`; theory-layer unavailable` line exist (S2); `engine_counters` and the
O(rows) pivot exist (S4); the native core's `Reason` is the tagged word (S6).
`TrustId::SatRefutationModuloTheory` exists only in ADR-1704, not in code:
S5 landed the contract, and the "then implement" half of row S5 is S7's.
The three unmerged branches are still 6 / 9 / 4 commits ahead of `main`.

Corrections applied to the body below in this audit, each marked
**Corrected 2026-09-06** where it sits: the S4 warm-start premise (the warm
start already existed; the cost was one redundant pass in the pivot); the
S9 "+6 against cvc5" claim (refuted by ablation; expected yield 0); the
§2.5 census verdict that S1 "lands nothing" for UF/QF_UF (S1 moved QF_UF
+28 and S11a found the census class misattributed on 67 of 70 files); the
QF_LRA atom-cap count (23 by the census, not the August 29); the row S3
scope (all eleven divisions were censused, not seven); and the stale
"(census needed)" headings. §4 now carries a status column and rows for
S1b and S11a.

## 0. The rule this plan runs under

**Parity is a count on a pinned list, measured by `scripts/parity-run.sh` on an
idle host, at zero disagreements.** A division is at parity when Axeyum's
decided count on its 200-file list is at least the reference's on the same
run; "or better" is a positive axeyum-only column. A slice lands only if its
scoring files move under that protocol. Soundness is not a trade: a wrong
verdict anywhere voids the entry and stops the lane.

Two lessons from today are rules here:

1. **Name the hot function from a measurement on the failing files before
   scoping a fix.** A 7x micro-benchmark ratio was read as data-structure
   polish; the profile showed a missing algorithm. Every slice below cites the
   measurement that names its function, or starts with the census that will.
2. **Read counts when the reference count moves.** Three ratios fell today
   while our count rose or held, because cvc5 gained files on an idle host.

## 1. The board and where the losses are

**This is the starting board, kept as the baseline every slice is scored
against.** The current board is the one in the progress log above.

At solver commit `9914a1c0e`, idle hosts, 24 s / 8 GiB, plain references
([`bench-results/PARITY.md`](../../bench-results/PARITY.md)):

| Division | Reference | Ours | Theirs | Ratio | Ours only | Theirs only | Gap to parity |
|---|---|---:|---:|---:|---:|---:|---:|
| QF_SLIA | cvc5 | 193 | 194 | 99.5% | 6 | 7 | 1 |
| QF_BV | Bitwuzla | 188 | 194 | 96.9% | 0 | 6 | 6 |
| UF | cvc5 | 85 | 93 | 91.4% | 24 | 32 | 8 |
| QF_ABV | Bitwuzla | 179 | 197 | 90.9% | 1 | 19 | 18 |
| QF_LIA | cvc5 | 114 | 139 | 82.0% | 2 | 27 | 25 |
| QF_UF | cvc5 | 162 | 200 | 81.0% | 0 | 38 | 38 |
| QF_RDL | cvc5 | 107 | 154 | 69.5% | 0 | 47 | 47 |
| QF_UFLIA | cvc5 | 122 | 180 | 67.8% | 0 | 58 | 58 |
| QF_LRA | cvc5 | 91 | 145 | 62.8% | 0 | 54 | 54 |
| QF_IDL | cvc5 | 70 | 123 | 56.9% | 1 | 54 | 53 |
| QF_NIA | cvc5 | 39 | 87 | 44.8% | 13 | 61 | 48 |

Total gap to parity: **356 files**, of which **266 (75%) are in the five
arithmetic divisions** (QF_RDL, QF_UFLIA, QF_LRA, QF_IDL, QF_NIA). The plan is
therefore arithmetic-first by weight, but every division has a slice.

## 2. Root causes, measured or to be measured

Two divisions were profiled today on their timeout files with the
stage-attribution and route-timing instruments that landed this morning. The
rest have a **loss census** as their first slice: run every reference-only
file through `smtcomp_cli --trace` and `explain_corpus --json --timed-trace`
on an idle host and classify each loss as one of `search-timeout`,
`admission-decline(constant)`, `route-decline(unsupported)`, `parser-reject`,
`dispatch-overrun`, with the declining route and the dominant stage named.
The census is the measurement rule 1 demands; no slice for a censused division
is authorized before it. **Done (S3, `4339eb793`)** for all eleven divisions,
403 files; each subsection below carries its result. Two method corrections
from S11a apply when reading any census row: the `class` column is the LAST
route's message, not the route that spent the budget, and `explain_corpus`
is not the front door (see §6).

### 2.1 Difference logic: QF_IDL and QF_RDL, 101 files (measured)

**Cause (fixed by S1, `eff6a464b`; S2, `b4d042ae4`).** `CdclT::unit_propagate`
(`crates/axeyum-solver/src/cdclt.rs`) was a full clause-database rescan per
fixpoint pass with no watch lists and no blocking literals, and it cloned the
reason clause on every implication. On the five traced QF_IDL timeouts it is
19.4 s of a 24 s budget (87% of wall) with the theory at 0 ms
([profiles](../research/11-design-review/2026-09-05-arith-timeout-profiles.md)).
The 2026-08-21 diagnosis's "dl-online runs out of clock" was this function.

**Second cause.** Dispatch overrun: `dl-online` spends 18 to 21 s, then
`lia-dpll` spends a fixed ~8 s declining on a size constant it could have
evaluated at t = 0, so the sum exceeds the budget and the watchdog kills the
process before any statistics print (3 of 5 traced IDL files). The
2026-08-21 diagnosis priced the reserve at 6 s; today's measurement says ~8 s.

**Lever (landed).** Two-watched-literal propagation with blocking literals inside
`CdclT`, ported verbatim from `proof_sat.rs`'s `Watch`/`ClauseHeader` design so
the later engine unification is a deletion rather than a reconciliation
([memo §6](adr-1701-slice-2-design-2026-09-05.md)). Separately, make
`lia-dpll` evaluate its size admission before consuming its reserve. Result at
`b32377dc5`: QF_IDL 70 -> 86, QF_RDL 107 -> 128. S1b (unmerged) adds the VSIDS
order heap and recursive minimization: the 50-file IDL timeout population goes
11 -> 27 decided on idle s5, zero verdict changes.

**Census (S3, 2026-09-05/06).** QF_IDL 54/54 losses classified: 46
admission-decline (all `lia-dpll`'s pre-SAT resource boundary, but
`dominant_stage` is `dl-online` at 18-21 s in every one -- this dispatch-
overrun signature, not five files but 46), 6 search-timeout, 2 other.
QF_RDL 47/47: 24 admission-decline (23 the 1,024-atom LRA cap, 1
Fourier-Motzkin), 22 search-timeout, 1 other. Full detail and the S1/S2
argument this drives: [parity loss census](../research/11-design-review/2026-09-05-parity-loss-census.md).

### 2.2 Linear real arithmetic: QF_LRA, 54 files, and the LRA half of QF_UFLIA (measured)

**Cause.** `LraTheory::final_check` → `feasibility` → `simplex::Incremental`
is 84% of wall on the traced QF_LRA timeouts, called 1,150 to 15,000 times per
file at 1.3 to 15 ms per call; Boolean propagation is 10%. The interface
widening (ADR-1701 slice 1) moved the cost from `assert` to `final_check` as
designed and converted 2 of 33 timeouts; the simplex itself is now the cost.
A further 23 QF_LRA files (by the S3 census; the August diagnosis counted 29
on an older list) are refused at the 1,024-atom admission cap, which the
diagnosis measured as load-bearing protection (removing it: 0 new decides, 54
memory aborts).

**Corrected 2026-09-06 (S4, `69742894a`).** Lever (a) below rested on a
false premise: the S4 lane wired six engine counters before changing anything
and measured `simplex_cold_restarts = 0` across 6,571 checks on the traced
file. The tableau was already warm; each check cost 2.3 pivots, and each pivot
paid a second `O(rows x columns)` value pass that recomputed what the update
already determined. S4 replaced it with Dutertre-de Moura's `O(rows)`
`pivotAndUpdate` (4.5x on the simplex bench, 20x on a traced file with
byte-identical search) and made implied bounds work over the whole linear
form (before, `unit_bound` returned `None` for any multi-variable atom, so
propagation offered 79 literals in 6,571 checks). Measured yield on the board:
QF_LRA +2, QF_UFLIA +1. The remaining 31 QF_LRA timeouts are now S7's
(engine) and the per-call simplex cost's.

**Lever (as written 2026-09-05).** (a) Warm-start each final check from the previous tableau instead
of re-deciding feasibility; (b) theory propagation of implied bounds through
the propagate hook so the Boolean search stops proposing assignments the
theory rejects, cutting the call count; (c) once the atom cap is a memory
bound rather than an overflow guard (ADR-1702 landed the opt-in wide
rationals in the simplex), revisit the 29 refusals with a measured memory
budget instead of a constant.

**Census (S3, 2026-09-05/06).** QF_LRA 54/54 losses classified: 31
search-timeout (route `nra`), 23 admission-decline (all the 1,024-atom
online CDCL(T) LRA cap) -- no `other`, no route-decline, a clean two-way
split. Full detail: [parity loss census](../research/11-design-review/2026-09-05-parity-loss-census.md).

### 2.3 Combination: QF_UFLIA, 58 files (partly measured)

**Cause.** The 2026-08-21 diagnosis traced 82 of 82 misses to the lazy
UF/arith CEGAR loop, and 26 files never reach the solver: `Int` literals above
2^127 (EVM 2^256 words) are rejected at the parser on `Value::Int(i128)`. cvc5
decides 6 of those 26 (they are the 6 `route-decline` rows in the census
below). Today's +9 came from the widened interface; the remaining 58 have not
been re-censused since.

**Corrected 2026-09-06 (S9, unmerged at `d975a1fbb`).** Lever (b)'s "+6
measured against cvc5" was never an axeyum measurement; it was cvc5's count.
ADR-0376's ablation, re-run on today's HEAD at 24 s: rescale every wide numeral
to a distinct `2^60 + i`, 6 of 6 still `unknown`; delete every assert that
mentions one, 6 of 6 still `unknown` (the runner is not vacuous: 2 `sat`, 2
`unsat` on four control files). The binding constraint is the decision
procedure's width (`MAX_INT_BLAST_WIDTH = 64`, with a measured cliff between
2^24 and 2^32), not the literal type. S9 therefore lands the parser and the
evaluator (all 26 files parse, every route declines by name, a panic on user
input in the replay evaluator is fixed) with an **expected QF_UFLIA yield of
0**. The 6 files are S11/S12 width-ladder work.

**Lever.** (a) Re-census after today's changes; (b) ADR-1702 slice 2:
`Value::Int` and the SMT-LIB integer-literal parser gain the same opt-in
wide path the simplex has (the "+6" here is refuted, see above); (c) the LRA levers
above apply to the arithmetic half; (d) the CEGAR loop's refinement policy
gets the route-timing instrument before any change.

**Census (S3, 2026-09-05/06, re-censused as (a) called for).** QF_UFLIA
58/58 losses classified: 31 search-timeout (`uf-arith-lazy-overbound`, the
lazy CEGAR loop, S1), 21 admission-decline (the same CEGAR loop declining
`inconclusive` on an application/function-group count), 6
route-decline(unsupported:ingest:wide-integer-literal) (the ADR-1702 slice
2 target, S9). All three named levers present, in that order by size. Full
detail: [parity loss census](../research/11-design-review/2026-09-05-parity-loss-census.md).

### 2.4 Nonlinear integers: QF_NIA, 48 files to parity, 13 ours-only (measured 2026-08-21)

**Cause.** One benchmark family, `20170427-VeryMax/ITS`, is 134 of the 200
files and 74 of the misses; excluding it we are at 74% of cvc5. Every
specialised nonlinear route declines and the generic `int-blast-ladder`
decides 158 of 161 undecided files; its width ladder admits a rung only if
every integer **literal** fits, so a 2^30 Farkas coefficient leaves one live
rung on 32 files, of which we decide zero. Three cheap levers were built and
refuted (0, +1, +3 files); 4x the clock buys 0 of 20 timeouts. cvc5's own
count on this list has read 89, 76, 76, 81, 83, 87 across six sweeps.

**Lever.** The one unpriced hypothesis: admit a rung when a **coefficient**
rather than a bound is large, via an eager small-domain product split
(`nia_linearize.rs:750-777` already implements the lemma and its width-4
limit matches the `[-2,2]` boxes these benchmarks declare) reached without the
lazy refinement loop that fails. Scored on the 32 one-live-rung files. This
division is last by design; "parity" here is against a reference whose count
moves by 13 files run to run, so the honest target is the axeyum count.

**Census (S3, 2026-09-05/06).** QF_NIA 61/61 losses classified: 30
search-timeout (`int-blast-ladder`), 18 admission-decline (17 the ladder's
CNF-clause size cap at 64,000,000, 1 an ingest `distinct`-arity cap), 13
other (11 bounded-width-32 model incompleteness, 2 divergence). The width 32
is the ladder's top rung `DEFAULT_INT_WIDTH`; the rewrite ceiling
`MAX_INT_BLAST_WIDTH` is 64. Full
detail: [parity loss census](../research/11-design-review/2026-09-05-parity-loss-census.md).

### 2.5 Uninterpreted functions: UF, 32 theirs / 24 ours; QF_UF, 38 theirs / 0 ours at the start (now 10 theirs), censused

**What is known.** UF's remaining losses are finite-model-finding benchmarks
(2026-08-21 gap analysis §5), a technique gap rather than general UF weakness;
cvc5 runs plain here, without `--finite-model-find`, and still takes 32. Our
24 axeyum-only files are the widest such column on the board. QF_UF is a
first entry: cvc5 solves all 200; nothing is known about our 38 losses except
that the quantifier-free EUF route is the online e-graph on `CdclT`, so the
propagation defect in 2.1 is a candidate.

**Lever.** Census first. If QF_UF's losses are search timeouts, 2.1's fix
lands them for free; if they are size admissions in the e-graph or Ackermann
paths, that is a separate slice. For UF, a bounded finite-model-finding
extension of the existing MBQI loop, scored on the 32.

**Census (S3, 2026-09-05/06).** UF 32/32 losses classified: all 32
admission-decline, all one shape (`declared-sort lazy CEGAR refuses N
congruence pairs, bound 64`, route `ufbv-declared-sort-lazy`) -- a single
uniform S11 target, not a mix. QF_UF 38/38 losses classified: all 38
admission-decline, split 35 eager-Ackermann-elimination congruence-count
(route `qf-bv`) / 3 the same bound-64 CEGAR shape as UF. The census then
concluded that neither division had a search-timeout file and that 2.1's fix
would land nothing here. Full
detail: [parity loss census](../research/11-design-review/2026-09-05-parity-loss-census.md).

**Corrected 2026-09-06 (S1 measured; S11a, unmerged at `5801c2d4b`).** That
conclusion was wrong two ways. S1's watched literals moved QF_UF 162 -> 190
at `b32377dc5`, so 28 of the 38 were search timeouts after all. S11a then
re-measured the remaining files through the front door: on 35 QF_UF files
`euf-online` is entered first and spends 23.5 s of the 24 s budget, and the
`qf-bv` Ackermann decline that named the census class is a millisecond tail
after the budget is gone; `euf-online` carries no admission constant to
raise. On all 32 UF files the census class is an artifact of
`explain_corpus` (flat assertion view; at the front door none of them ends at
the CEGAR bound). The cap genuinely blocked 3 QF_UF files, and S11a converts
them (a replay-confirmed `sat` is no longer discarded in `check_qf_ufbv_lazy`;
the terminal rung passes a 16,384-pair bound because nothing runs after it):
38-file population 27 -> 29, zero flips. The UF/QF_UF lever is therefore
S1b's heap and S7's engine, not a cap; UF's 32 still have no front-door cause
named, and the finite-model-finding hypothesis above is unmeasured.

### 2.6 Linear integers: QF_LIA, 27 theirs / 2 ours at the start (29 theirs after S2), censused

**What is known.** QF_LIA runs the LIA DPLL(T) driver (`dpll_lia.rs`), the
same family as QF_UFLIA, plus cuts. It gained one file today with the
reference unchanged. The 2026-08-21 core-minimisation fix (ADR-0538) moved
QF_UFLIA +22 and QF_LIA 0, which says QF_LIA's losses are not wide theory
cores.

**Lever.** Census. Expect a split between search timeouts (2.1's fix) and
cut-generation limits (a slice on the Gomory/branching budget, scored on the
27).

**Note (S1b).** QF_LIA fell 114 -> 112 at `b32377dc5`. Both files
(`bofill-scheduling/SMT_real_LIA/ex3000_2400_100`, `ex4320_2400_100`) were
refuted in 8.1 s by the online probe that S2's admission preflight now
declines at 109 ms before it runs; an S2 follow-up should let the size-gated
route still run that probe. Not a watched-literal regression.

**Census (S3, 2026-09-05/06).** QF_LIA 27/27 losses classified: 15
admission-decline (`lia-dpll`'s pre-SAT resource boundary, the same family
as QF_IDL's dominant class), 4 search-timeout, 4 other
(explain-corpus-crash on large files; `smtcomp_cli` itself timed out
normally on all four), 3 other (branch-and-bound node-cap incompleteness),
1 other (i128 overflow in the exact-rational simplex -- a second S9 data
point beyond QF_UFLIA's parser case). Admission-decline outweighs
search-timeout more than 3:1. Full detail: [parity loss census](../research/11-design-review/2026-09-05-parity-loss-census.md).

### 2.7 Arrays over bit-vectors: QF_ABV, 19 theirs / 1 ours, censused

**What is known.** First entry, 90.9%. The route is read-over-write plus
Ackermann elimination to QF_BV, with lazy ROW inside the canonical CDCL(T)
search for the online path. The breadth corpus puts QF_ABV at 88% against Z3
with 24 unsupported files, so some losses are likely `route-decline`
(nested arrays are structurally rejected, per the gap analysis) rather than
timeouts.

**Lever.** Census splits the 19 into unsupported shapes and timeouts. The
unsupported half is a capability slice (nested arrays or the array-valued
shapes the ADR-0084/0085 boundary still declines); the timeout half rides
2.1 and 2.8.

**Census (S3, 2026-09-05/06).** QF_ABV 19/19 losses classified: 8
search-timeout (`array-fast-path`), 4 other (flat-view/front-door
divergence, not a capability finding), 4 other (explain-corpus worker
hangs on array-heavy inputs, externally killed; `smtcomp_cli` completed
normally on all four), 3 other (a genuine array-shape gap in the lazy
ROW/extensionality path -- the ADR-0084/0085 boundary confirmed on 3
files, smaller than hypothesized). Full detail: [parity loss census](../research/11-design-review/2026-09-05-parity-loss-census.md).

### 2.8 Bit-vectors: QF_BV, 6 theirs / 0 ours (measured at the SAT level)

**Cause.** The six are Bitwuzla's exclusive files on every sweep since July.
At the SAT level, on identical p4dfa CNF our native core needs about the same
number of conflicts as Kissat and processes them about 1.5x slower, and
Kissat spends only 26% of its own time inprocessing
([search stats](../research/11-design-review/2026-09-05-native-core-vs-kissat-search-stats.md)).
So the gap is per-conflict throughput, not simplification. The gate (b) sweep
at 20 s has Kissat 11 / CaDiCaL 10 / native 6 on the 113 p4dfa files.

**Lever.** Profile the native core's `propagate` and `analyze` on the p4dfa
CNFs (no `perf` on the fleet; use counters and the criterion benches on
`proof_sat_solve`), then the standard throughput items in measured order:
clause-arena layout and watch-list locality, `reduce_db` tiering, restart
policy. Bitwuzla's word-level rewriting is the other half; the six files'
route trace says which. Every gain here lifts every division once the engine
is unified.

**Census (S3, 2026-09-05/06).** QF_BV 6/6 losses classified: 5
search-timeout (route `qf-bv`), 1 other (explain-corpus worker crash;
`smtcomp_cli`'s own ~25 s wall time is consistent with the same
search-timeout pattern). Confirms 2.8's framing: this is a throughput
problem, not an admission cap or capability gap. Full detail: [parity loss census](../research/11-design-review/2026-09-05-parity-loss-census.md).

### 2.9 Strings: QF_SLIA, 7 theirs / 6 ours (partly measured)

**Cause.** The gap analysis §4.4: `sat` is strong, `unsat` is weak;
`StringGate` refuses to certify most bounded refutations, so unsat coverage
is far below what the encoder suggests.

**Lever.** Census the 7. If they are unsat refusals, the slice is a
length-abstraction refutation route the gate can certify; if timeouts, 2.1.
One file from parity; this is the cheapest division to close.

**Census (S3, 2026-09-05/06).** QF_SLIA 7/7 losses classified: 1
`other(string-gate-unconfirmed)` (exactly the 2.9 hypothesis), 4 other
(the `int-blast-ladder`'s bounded integer width 32 -- a shape not
previously named here, shared with QF_NIA), 2 parser-reject (`str.replace_all`
over a non-constant operand, an S9-adjacent parser gap). The
certification hypothesis explains 1 of 7, not the majority. Full detail:
[parity loss census](../research/11-design-review/2026-09-05-parity-loss-census.md).

## 3. The engine question, decided

Three Boolean search engines exist. ADR-1703 retired BatSat; the native core
(`proof_sat.rs`) is the SAT engine, and `CdclT` remains under every theory
route. The spike measured that theory hooks in the native core cost nothing
when gated on a compile-time constant (design B: -0.2%; design A: +6.3%), so
unification is not blocked by cost. It is blocked by a **proof contract**: a
theory lemma is not RUP against the CNF, so learning one silently turns the
native core's DRAT refutation into a refutation modulo theory with nothing in
the artifact saying so ([memo §6.1](adr-1701-slice-2-design-2026-09-05.md)).

Decision for this plan: **fix propagation in place first (route B), unify
second (route A), and write the proof-contract ADR between them.** Route B is
where the IDL headroom is and is a stepping stone to A only if the native
design is copied verbatim. The recommended contract is two streams: RUP-only
DRAT for the Boolean part plus an enumerated list of theory lemmas as
assumptions, so the assumption count is a visible metric.

**Decided, 2026-09-06 (S5): [ADR-1704](../research/09-decisions/adr-1704-cdclt-unsat-is-two-streams-a-boolean-refutation-over-cnf-plus-enumerated-theory-lemmas.md)**
adopts the two-stream contract — the Boolean DRAT/LRAT stream is checked over
the CNF **extended by the enumerated theory lemmas as input clauses**, the
lemma count is read off the artifact and printed as `theory_lemmas_unchecked`,
and a refutation modulo N ≥ 1 lemmas is graded at a new
`TrustId::SatRefutationModuloTheory` rather than at `SatRefutation`. The
checkers are unchanged. The boundary is pinned by
`crates/axeyum-cnf/tests/theory_lemma_proof_contract.rs`. S7 is no longer
blocked on the contract.

## 4. The slices, in order, with scoring files and exit criteria

Scoring populations are committed:
`bench-results/adr-1701-slice-1-20260905/qf_idl_population.tsv` (50 QF_IDL
timeouts) and `qf_lra_population.tsv` (33 QF_LRA timeouts); the per-division
reference-only lists come from the parity sidecars on the measuring hosts and
are to be committed by the census slice as `bench-results/parity-losses-20260905/<DIV>.txt`.

| # | Slice | Division(s) | Scoring files | Exit criterion | Gate | Status 2026-09-06 |
|---|---|---|---|---|---|---|
| S1 | **Two-watched-literal propagation in `CdclT`**, blocking literals, ported verbatim from `proof_sat.rs`; no trait, caller or proof change | QF_IDL, QF_RDL, QF_UF, UF, QF_LIA, QF_LRA (Boolean part) | 50-file IDL population; 33-file LRA population | `TheoryLayerStats::boolean_propagate` falls on the 5 traced IDL files; IDL population decided rises from 0; zero verdict changes | solver `--lib --features full`, corpus sweep, cdclt suites, z3 fuzzes, frontier, then `parity-run.sh QF_IDL` and `QF_RDL` on an idle host | **landed** `eff6a464b`; QF_IDL +16, QF_RDL +21, QF_UF +28 with S2 |
| S1b | **VSIDS order heap and recursive clause minimization in `CdclT`**, ported verbatim from `proof_sat.rs` | QF_IDL, QF_RDL, QF_UF, UF, QF_LIA, QF_LRA (Boolean part) | 50-file IDL population; 33-file LRA population | IDL population decided rises; zero verdict changes | as S1 | **merged** `5fa2e3feb` (branch tip `649a12add`); IDL population 11 -> 27 of 50, PAR-2 -40.1%, zero flips |
| S2 | **Dispatch overrun fix**: `lia-dpll` evaluates its size admission before consuming its reserve; a declined route's budget returns to the pool | QF_IDL, QF_RDL, QF_LRA | the 3 of 5 traced IDL files that print no stats | every timeout prints a `; theory-layer` line; no verdict changes | route-trace tests, corpus sweep | **landed** `b4d042ae4`; QF_LIA -2 is its preflight, follow-up owed (§2.6) |
| S3 | **Loss census** for QF_UF, UF, QF_LIA, QF_ABV, QF_SLIA, QF_BV, QF_UFLIA: classify every reference-only file | the six censused divisions plus QF_UFLIA | one TSV per division with class, declining route, dominant stage; committed lists | measurement only | none (docs and artifacts) | **landed** `4339eb793`; all eleven divisions, 403 files, not seven |
| S4 | **Simplex per-check cost** (planned as warm start; landed as the O(rows) pivot update), and **implied-bound propagation** through the propagate hook | QF_LRA, QF_UFLIA, QF_LIA | 33-file LRA population; QF_UFLIA reference-only list | `theory_final_check_ms` per call and call count both fall on the 5 traced LRA files; LRA population decided rises from 5 | as S1 plus `parity-run.sh QF_LRA`, `QF_UFLIA` | **landed** `69742894a`; premise corrected (§2.2): O(rows) pivot + whole-form bounds; QF_LRA +2, QF_UFLIA +1 |
| S5 | **ADR: the proof contract under theory lemmas** (two streams, assumptions counted), then implement | all CDCL(T) divisions | none; a contract | a CDCL(T) `unsat` produces an artifact whose theory assumptions are enumerable and counted | evidence suites | **ADR landed** `5c9b3a7c2` (ADR-1704, boundary pinned by 11 tests); the implementation half is S7's |
| S6 | **Reason representation** in the native core (`Option<CRef>` → tagged `Reason`), measured alone | prerequisite for S7 | criterion `proof_sat_solve_php_6_7`; 20 p4dfa CNFs | within the noise band; p4dfa decided unchanged | cnf suites, corpus | **landed** `3b6d42f6c`; `Reason` 16 B -> 8 B, DRAT byte-identical, p4dfa 9/20 unchanged |
| S7 | **Move CDCL(T) onto the native core** behind the measured hooks; `TheoryLayerStats` ported first; `CdclT::new` signature preserved | every theory division | full board | `cdclt_solve_php_6_7` closes most of the gap to `proof_sat_solve_php_6_7`; every verdict unchanged; then the full eleven-division parity sweep | everything in S1 plus the full sweep | next; S5 and S6 satisfied |
| S8 | **Native-core throughput**: profile propagate/analyze on p4dfa CNF by counters; arena locality, `reduce_db` tiering, restarts, in measured order | QF_BV first, all after S7 | 113 p4dfa CNFs at 20 s; the 6 Bitwuzla-only files | conflicts/s ratio to Kissat rises from 0.6 toward 1; p4dfa decided rises from 6 toward 11 | gate (b) rerun, `parity-run.sh QF_BV` | after S7 |
| S9 | **ADR-1702 slice 2**: `Value::Int` and the integer-literal parser gain the opt-in wide path | QF_UFLIA (0 expected), QF_LIA, QF_NIA | the 26 rejected QF_UFLIA files | they reach the solver and every route declines by name; zero verdict changes; the 6 cvc5 decides are width-ladder work | ir and solver suites, z3 fuzzes, corpus | **merged** `5f4c38c32` + composition fix `b40a0f309`; "+6" refuted, expected yield 0 (§2.3) |
| S10 | **Dynamic atom registration** via the widened trait, retiring driver side tables; then revisit the 1,024-atom cap as a memory budget | QF_LRA | the 23 atom-cap refusals | a measured memory budget replaces the constant; refusals convert or are reported as memory-bound with the number | as S4 | after S7; 23 refusals by census, not 29 |
| S11 | **Per-division capability slices from the census**: nested arrays or ADR-0085 boundary shapes (QF_ABV); certifiable string refutations (QF_SLIA); bounded finite-model finding (UF); cut budget (QF_LIA) | as named | each division's committed loss list | division count rises by the classified files | division suites plus its `parity-run.sh` | S11a **merged** `97ce06aff` (+3 QF_UF, §2.5); remainder by census class |
| S11a | **UF/QF_UF Ackermann and declared-sort CEGAR cap**, scored on the 70 census files | UF, QF_UF | the 38 QF_UF and 32 UF census lists | the census's cap attribution measured through the front door; classified files convert | uf suites, `parity-run.sh QF_UF`, `UF` | **merged** `97ce06aff`; census wrong on 67 of 70, 3 real cap losses fixed, full 200-file sweeps not yet run |
| S12 | **NIA coefficient-width rung** via eager small-domain product split | QF_NIA | the 32 one-live-rung files | decided rises from 0 on those 32; zero verdict changes | nia suites, corpus, `parity-run.sh QF_NIA` | last |

Dependencies (as of 2026-09-06, evening): S1 through S6, S1b, S9 and S11a
are all on `main`. S7 is unblocked (S5 contract,
S6 reason word) and is the next engine slice; S8 after S7 so the gain reaches
every division. S10 waits on S7. S11's remainder and S12 are independent of
the engine work and are scheduled by census class, read with the two S11a
method corrections.

## 5. What "parity or better" means per division, and when to stop

| Division | Parity count | Realistic path in this plan | Stop condition |
|---|---:|---|---|
| QF_SLIA | 194 | S11 string refutations, 7 files | at or above 194 with 0 disagreements |
| QF_BV | 194 | S8, 6 files, Bitwuzla-only since July | at or above 194 |
| UF | 93 | S1 (landed, +0), S1b, S7; the finite-model-finding hypothesis is unmeasured and the census class was an artifact (§2.5) | at or above 93; the 24 axeyum-only stay |
| QF_ABV | 197 | S1 plus S11 array shapes | at or above 197 |
| QF_LIA | 139 | S1, S4, S11 cuts | at or above 139 |
| QF_UF | 200 | S1 landed (+28), S11a (+3), then S1b and S7 for the timeouts | 200 |
| QF_RDL | 154 | S1, S2 | at or above 154 |
| QF_UFLIA | 180 | S1, S4 (landed, +1), S7; S9 yields 0 here, the 6 wide files are width-ladder work | at or above 180 |
| QF_LRA | 145 | S4, S10 | at or above 145 |
| QF_IDL | 123 | S1, S2 | at or above 123 |
| QF_NIA | 87 | S12; reference count unstable | axeyum count above 61 (the current theirs-only) with the family split reported; ratio not the target |

A division that reaches its count stays on the board and is re-measured with
every later slice; the freshness gate (14-day budget) and the timing ratchet
make regression visible.

## 6. Measurement protocol for every slice

- Idle hosts s5, s6, s7; `taskset -c 0-7`; `scripts/parity-run.sh` with no
  knobs; one division per host; the detached queue script used today
  (`~/parity-queue.sh`) so a sweep does not depend on an agent surviving.
- Before/after arms from `scripts/lane-snapshot.sh` builds, binaries confirmed
  different by `sha256sum`, files interleaved between arms.
- Stage attribution (`smtcomp_cli --trace`) and route timing
  (`explain_corpus --json --timed-trace`) on five files per population, before
  and after, in every report.
- Every slice's Rust change runs the full solver unit sweep, the corpus sweep,
  the three z3 differential fuzzes for arithmetic changes, the frontier suite
  (capability and timing ratchets), clippy, workspace check, and the WASM
  build before merge; the coordinator reruns them on main after merge.
- A verdict change on any file is P0 and stops the lane.
- **Added 2026-09-06 (from S11a).** A loss is classified by the route that
  spent the budget (read the timed trace), never by the last route's message;
  and it is classified through the front door (`solve_smtlib`, as
  `smtcomp_cli` runs it), never through `explain_corpus`, which runs the flat
  assertion view and disagrees with the front door on 134 of 397 benchmarks.
  The S3 census predates both rules; its `class` column is reliable only where
  a later slice has confirmed it.

## 7. What this plan does not claim

- Ratios against cvc5 on QF_NIA are not a stable target; the axeyum count is.
- The census divisions' causes are as reliable as the census method (§6,
  last bullet): confirmed for QF_IDL, QF_RDL, QF_LRA and QF_UFLIA by the
  slices that acted on them, refuted for UF/QF_UF by S11a, and unconfirmed
  for QF_LIA, QF_ABV, QF_SLIA, QF_BV and QF_NIA until a slice re-measures them
  through the front door.
- The 24 s budget is the competition convention; nothing here says what a
  longer budget shows.
- Beating the references on decided counts is the floor. The lead this
  project is built for is the checked artifact behind every `unsat` and the
  counted trusted base, which S5 extends to theory reasoning; no reference
  publishes that.
